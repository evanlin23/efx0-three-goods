"""REC-S and its iteration RSD at every hard start (k4/oc1max_multi.md §15; the integrator's census, k4/oc1_hall.md §24.3).

RSD at a perfect start (strict values): try Theorem S (relaxed, h in J + {Y_z}; theorem_s.s_cases) in the current
reduced instance; accept a case if its allocation, with every settled agent keeping its pair, is EFX0 in the full
instance (raw).  Otherwise settle one more dangerous agent k of the current instance by its earliest-wanter chain E(k)
(the order restricted to the current agents) with an improving pool pair T, delete k and T (Lemma SD-E: the new state
is the SD outcome of the order minus k; Lemma LIFT: moves lift), and recurse, up to DEPTH settlements.
REC-S is RSD with exactly one settlement; depth 0 is Theorem S at the picks.
Per start: the least depth at which RSD completes (or 'none'), and for REC-S failures a classification: (i) D = {k}
with no useful pair, (ii) a RING start (regimes.mechanism ED), (iii) other.

FORCE1=1 forbids completing at the picks (so depth 1 is exactly REC-S, the integrator's (a)); ANY=1 also accepts, as the
last step, any official move of the reduced instance with any one-absorber completion (lifted, raw EFX0 in the full
instance), the integrator's (b) with a general last step.

    DEPTH=2 [FORCE1=1] [ANY=1] python3 k4/oc1max_multi/rsd.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from dred import apply_chain
from reduce_check import reduced
from theorem_s import s_cases
from reduce_s import earliest_chain

DEPTH = int(os.environ.get('DEPTH', '3'))
FORCE1 = os.environ.get('FORCE1') == '1'
ANY = os.environ.get('ANY') == '1'


def rsd(I0, I, b, order, agents, goods, fixed, depth):
    """I: current reduced instance (agents[j], goods[g] give the labels in I0); fixed: {agent of I0: pair};
    returns the least number of further settlements that completes, or None"""
    best = None
    terminal = not (FORCE1 and not fixed)          # FORCE1: exactly REC-S (no Theorem S at the picks themselves)
    if terminal and ANY:                           # ANY: any official move + any one-absorber completion as the last step
        from mmlib import moves, oa_absorbers
        for B2 in [b] + list(moves(I, b)):
            for o, X in oa_absorbers(I, B2, want_witness=True).items():
                A = [list(fixed.get(a, [])) for a in range(I0.n)]
                for j, a in enumerate(agents): A[a] = [goods[g] for g in X[j]]
                if I0.efx0(A): return 0
    for *_, X, how in (s_cases(I, b, dangerous(I, b), True, True) if terminal else []):
        if X is None: continue
        A = [list(fixed.get(a, [])) for a in range(I0.n)]
        for j, a in enumerate(agents): A[a] = [goods[g] for g in X[j]]
        if I0.efx0(A): return 0
    if depth == 0: return None
    J = junk(I, b); p = [I.V(i, b[i]) for i in range(I.n)]
    for k in dangerous(I, b):
        P = earliest_chain(I, b, k, order)
        for T in itertools.combinations([g for g in J + list(b[P[-1]]) if g in I.R[k]], 2):
            if I.V(k, T) <= p[k]: continue
            nb = apply_chain(I, b, P, T); I2, b2, keep = reduced(I, nb, k)
            g2 = [goods[g] for g in range(I.m) if g not in set(T)]
            ord2 = [keep.index(a) for a in order if a != k]
            f2 = dict(fixed); f2[agents[k]] = [goods[g] for g in T]
            r = rsd(I0, I2, b2, ord2, [agents[a] for a in keep], g2, f2, depth - 1)
            if r is not None:
                if r == 0: return 1
                best = r + 1 if best is None else min(best, r + 1)
    return best


def study(rec):
    I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m']); b = base_from_picks(tuple(rec['picks']))
    orders = rec.get('orders') or [rec['order']]
    res = None
    for o in orders:
        r = rsd(I, I, b, list(o), list(range(I.n)), list(range(I.m)), {}, DEPTH)
        if r is not None and (res is None or r < res): res = r
    return rec, res


if __name__ == '__main__':
    from collect import records
    from regimes import mechanism
    recs = [r for fn in sys.argv[1:] for r in records(fn)]
    T = collections.Counter(); ex = {}
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        out = pool.map(study, recs, chunksize=8)
    for rec, res in out:
        I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
        T['starts'] += 1; T['least number of settlements: %s' % res] += 1
        if res is None or res > 1:
            D = rec['D']; mech, _ = mechanism(I, rec)
            cls = '(ii) RING start' if mech == 'ED' else ('(i) D = {k}' if len(D) == 1 else '(iii) other')
            T[('REC-S fails', cls, 'mechanism ' + mech)] += 1
            sz = (I.n, I.m)
            if cls not in ex or sz < ex[cls][0]: ex[cls] = (sz, rec['name'], rec['picks'], rec.get('order'))
    print('$ DEPTH=%d FORCE1=%d ANY=%d python3 k4/oc1max_multi/rsd.py' % (DEPTH, FORCE1, ANY), *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    for k, v in sorted(ex.items()): print('smallest REC-S failure', k, v)
