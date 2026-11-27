"""Theorem REC-S (k4/oc1max_multi.md §12): OC2-REC's part (b) from Theorems U and S in the reduced instance.

At a failing start (no one-move repair), take a canonical first chain P1 from k in D in which k takes an improving pool
pair T, with Lemma LIFT's hypothesis (every other agent with a relevant good values each good of T below its value
after P1).  Delete k and T (reduce_check.reduced).  If the reduced state B1- is a serial-dictatorship outcome of I-
(a perfect start), Theorems U and S (theorem_s.s_cases, relaxed form, h in J- + {Y_z}) apply to it in I- with the
dangerous agents of I-; each case gives an explicit EFX0 allocation X- of I- after one move.  If no bundle of X-
threatens k at v_k(T), Lemma LIFT lifts it: X- with X_k = T is EFX0 in I, after the two moves P1 and the I- move.

Lemma SD-E (strict values): for the earliest-wanter chain E(k) (x_1 the earliest wanter of Y_k in the order, x_2 the
earliest wanter of Y_{x_1}, ...), B1- is the SD outcome of the order with k deleted; checked here ('E(k) only' lines,
violations tagged SD-E).

Census per failing start: some P1 with (a) SD; some P1 with (a) and a U/S case in I-; some with a lifted EFX0
allocation (raw EFX0 in I).  Checks: every U/S allocation is EFX0 in I- (Theorems U, S), and every lifted allocation
with k unthreatened is EFX0 in I (Lemma LIFT).

    python3 k4/oc1max_multi/reduce_s.py FILE.jsonl[.gz]     (rows with sets, vals, picks)
"""
import sys, os, json, gzip, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from dred import canonical_chains, apply_chain
from reduce_check import reduced, is_sd
from theorem_s import s_cases


def earliest_chain(I, b, k, order):
    """E(k): x_1 the earliest (in the order) wanter of Y_k, x_2 the earliest wanter of Y_{x_1}, ..., up to an agent
    nobody wants (Lemma SD-E)"""
    pos = {a: i for i, a in enumerate(order)}; p = [I.V(i, b[i]) for i in range(I.n)]; P = [k]
    while True:
        y = b[P[-1]][0]; ws = [i for i in range(I.n) if i != P[-1] and I.v[i].get(y, 0) > p[i]]
        if not ws: return tuple(P)
        P.append(min(ws, key=lambda i: pos[i]))


def study(rec, only_E=False):
    I = Inst(rec['sets'], rec['vals']); b = base_from_picks(tuple(rec['picks'])); J = junk(I, b)
    D = dangerous(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; st = set(); bad = []
    for k in D:
        chains = [earliest_chain(I, b, k, rec['order'])] if only_E else canonical_chains(I, b, k)
        for P in chains:
            pool = [g for g in J + list(b[P[-1]]) if g in I.R[k]]
            for T in itertools.combinations(pool, 2):
                if I.V(k, T) <= p[k]: continue
                nb = apply_chain(I, b, P, T); val = [I.V(i, nb[i]) for i in range(I.n)]
                I2, b2, keep = reduced(I, nb, k)
                if only_E:     # Lemma SD-E (any pair T inside the pool): B1- is the SD outcome of the order without k
                    st.add('SD-E tests'); oo = [keep.index(a) for a in rec['order'] if a != k]
                    if I2.sd(oo) != tuple(x[0] if x else None for x in b2): bad.append(('SD-E', rec, P, T)); continue
                if any(i != k and I.R[i] and any(I.v[i].get(g, 0) >= val[i] for g in T) for i in range(I.n)): continue
                st.add('P1 with LIFT hypothesis')
                if not only_E and not is_sd(I2, b2): continue
                st.add('(a) SD')
                for k2, P2, h, H0, X2, how in s_cases(I2, b2, dangerous(I2, b2), True, True):
                    if X2 is None: continue
                    st.add('(a) and a Theorem U/S case in I-')
                    if not I2.efx0(X2): bad.append(('S in I-', rec, P, T, P2, h)); continue
                    X = [[] for _ in range(I.n)]; X[k] = list(T)
                    back = {i2: g for g, i2 in [(g, j) for j, g in enumerate([g for g in range(I.m) if g not in set(T)])]}
                    for j2, i in enumerate(keep): X[i] = [back[g] for g in X2[j2]]
                    tk = I.V(k, T)
                    if any(I.threat(k, tk, X[j]) for j in range(I.n) if j != k): continue
                    st.add('lifted, k unthreatened')
                    if not I.efx0(X): bad.append(('LIFT', rec, P, T, P2, h))
                    else: st.add('OC2 by REC-S')
    return st, bad


def _both(rec):
    return study(rec), study(rec, True)


if __name__ == '__main__':
    recs = [json.loads(l) for l in (gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1]))]
    T = collections.Counter(); bad = []; miss = None
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for ((st, b), (st2, b2)), rec in zip(pool.imap(_both, recs, chunksize=4), recs):
            T['failing starts'] += 1; bad += b + b2
            for s in st: T[s] += 1
            for s in st2: T['E(k) only: ' + s] += 1
            if 'OC2 by REC-S' not in st and (miss is None or len(rec['sets']) < len(miss['sets'])): miss = rec
    print('$ python3 k4/oc1max_multi/reduce_s.py', *sys.argv[1:])
    for k in sorted(T, key=lambda k: -T[k]): print(T[k], k)
    print('violations (Theorem U/S in I-, LIFT, or SD-E):', len(bad), [x[0] for x in bad[:5]])
    print('a smallest start not covered:', json.dumps(miss))
