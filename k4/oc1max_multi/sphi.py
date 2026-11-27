"""Theorem S^phi (k4/oc1max_multi.md §16): Theorem S with phantoms, the inductive step of RSD.

RSD as in rsd.py (settlements by E(k) with an improving pool pair, no chain ending at a phantom-frozen agent), with
Theorem S (relaxed) in the current instance as the last step.  At the last step the census evaluates S^phi's two new
hypotheses
  (S-phi1) W threatens no phantom phi at tau_phi = v_phi(T_phi);
  (S-phi2) the receiver's good is not phantom-wanted (v_phi(good) <= tau_phi for every phantom),
and the invariant (P2) (no phantom's pair threatens another phantom), and checks the theorem's conclusion with the raw
EFX0 definition in the full instance: every case meeting them must be EFX0 (0 violations), and every raw-EFX0 case
should meet them (the hypotheses are then exact).  Per start: the least number of settlements with an S^phi case.

    DEPTH=2 python3 k4/oc1max_multi/sphi.py FILE.jsonl[.gz] [...]   (rows: sets, vals, picks, order or orders)
"""
import sys, os, json, gzip, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from dred import apply_chain
from reduce_check import reduced
from theorem_s import s_cases
from reduce_s import earliest_chain

DEPTH = int(os.environ.get('DEPTH', '2'))
TMAX = int(os.environ.get('TMAX', '2'))
ZERO = os.environ.get('ZERO') == '1'      # ZERO=1 also ends with a completion at once (no last move), as matching's RSD      # TMAX=3 also settles by improving pool triples (matching's RSD)


def run(I0, I, b, order, agents, goods, fixed, depth, C):
    """fixed: {I0 agent: pair}.  Returns (least total moves from here) - 1: -1 = completes now with no move (ZERO),
    0 = an S^phi move now, d + r for d further settlements; None if nothing within the depth"""
    tau = {f: I0.V(f, T) for f, T in fixed.items()}
    pwant = lambda g: any(I0.v[f].get(g, 0) > tau[f] for f in fixed)          # phantom-wanted good (I0 label)
    if fixed and ZERO:                # the reduced start completes with no further move (one-absorber, lifted, raw EFX0)
        from mmlib import oa_absorbers
        for o, X in oa_absorbers(I, b, want_witness=True).items():
            A = [list(fixed.get(a, [])) for a in range(I0.n)]
            for j, a in enumerate(agents): A[a] = [goods[g] for g in X[j]]
            if I0.efx0(A): C['completions at once after settlements'] += 1; return -1
    if fixed:
        p2 = all(not I0.threat(f, tau[f], fixed[e]) for f in fixed for e in fixed if e != f); found = False
        for *_, X, how in s_cases(I, b, dangerous(I, b), True, True):
            if X is None: continue
            A = [list(fixed.get(a, [])) for a in range(I0.n)]
            for j, a in enumerate(agents): A[a] = [goods[g] for g in X[j]]
            k2 = max(range(I.n), key=lambda j: len(X[j]))                     # the owner (the bundle W)
            W = A[agents[k2]]
            rec = [j for j in range(I.n) if j != k2 and len(X[j]) == 2]
            s1 = not any(I0.threat(f, tau[f], W) for f in fixed)
            s2 = all(not pwant(goods[g]) for j in rec for g in X[j])
            hyp = s1 and s2 and p2; ok = I0.efx0(A)
            C['last-step cases'] += 1; C['  S^phi hypotheses hold'] += hyp; C['  raw EFX0'] += ok
            if hyp and not ok: C['VIOLATION: hypotheses hold, not EFX0'] += 1
            if ok and not hyp: C['raw EFX0 without the hypotheses'] += 1
            if hyp and ok: found = True
        if found: return 0
    if depth == 0: return None
    J = junk(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; best = None
    for k in dangerous(I, b):
        P = earliest_chain(I, b, k, order)
        if pwant(goods[b[P[-1]][0]]): C['settlement chains ending at a phantom-frozen agent (skipped)'] += 1; continue
        pool = [g for g in J + list(b[P[-1]]) if g in I.R[k]]
        for T in [T for r in range(2, TMAX + 1) for T in itertools.combinations(pool, r)]:
            if I.V(k, T) <= p[k]: continue
            nb = apply_chain(I, b, P, T); I2, b2, keep = reduced(I, nb, k)
            if len(T) >= 3:          # (L*): a triple must threaten no other agent of the current instance (not automatic)
                if any(I.threat(i, I.V(i, nb[i]), T) for i in range(I.n) if i != k): C['triples failing (L*) (skipped)'] += 1; continue
                C['triple settlements tried'] += 1
            f2 = dict(fixed); f2[agents[k]] = [goods[g] for g in T]
            r = run(I0, I2, b2, [keep.index(a) for a in order if a != k], [agents[a] for a in keep],
                    [goods[g] for g in range(I.m) if g not in set(T)], f2, depth - 1, C)
            if r is not None:
                best = r + 1 if best is None else min(best, r + 1)
    return best


def study(rec):
    I = Inst(rec['sets'], rec['vals']); b = base_from_picks(tuple(rec['picks'])); C = collections.Counter(); res = None
    for o in (rec.get('orders') or [rec['order']]):
        r = run(I, I, b, list(o), list(range(I.n)), list(range(I.m)), {}, DEPTH, C)
        if r is not None and (res is None or r < res): res = r     # run's value + 1 = total moves
    return C, res


if __name__ == '__main__':
    T = collections.Counter()
    for fn in sys.argv[1:]:
        recs = [json.loads(l) for l in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))]
        with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
            for (C, res), rec in zip(pool.imap(study, recs, chunksize=8), recs):
                T.update(C); T['starts'] += 1; T['least total moves (settlements + last move): %s' % (None if res is None else res + 1)] += 1
                if res is None: T['uncovered: %s#%s' % (rec.get('list', ''), rec.get('idx', rec.get('name', '')))] += 1
    print('$ DEPTH=%d TMAX=%d ZERO=%d python3 k4/oc1max_multi/sphi.py' % (DEPTH, TMAX, ZERO), *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
