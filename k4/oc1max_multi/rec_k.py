"""The no-threat condition (K) of Theorem REC-S, locally (k4/oc1max_multi.md §14).

k keeps T; outside T it values only Y_k and at most one more good l (|R_k| <= 4).  Y_k alone never threatens k
(v_k(Y_k) = p_k < v_k(T)), and junk alone never does ((G2)).  So the allocation X of the reduced instance threatens k
only if
  (K-a) one bundle holds both Y_k and l, worth more than T to k after the least good is removed; or
  (K-b) l is a pick with v_k(l) > v_k(T) (k wants l over T) and l sits in a bundle of two or more goods.
Census, at every failing start, over E(k) (every order), every improving pool pair T and every Theorem S case of I-:
how often (K) fails and by which clause; and whether k's *best* pool pair T* (largest v_k(T)) alone already has a case
meeting (R) and (K).

    python3 k4/oc1max_multi/rec_k.py FILE.jsonl[.gz]
"""
import sys, os, json, gzip, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from dred import apply_chain
from reduce_check import reduced
from theorem_s import s_cases
from reduce_s import earliest_chain


def study(rec):
    I = Inst(rec['sets'], rec['vals']); b = base_from_picks(tuple(rec['picks'])); J = junk(I, b)
    D = dangerous(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; C = collections.Counter(); best_ok = False
    for order in (rec.get('orders') or [rec['order']]):
        for k in D:
            P = earliest_chain(I, b, k, order)
            pairs = [T for T in itertools.combinations([g for g in J + list(b[P[-1]]) if g in I.R[k]], 2) if I.V(k, T) > p[k]]
            if not pairs: continue
            top = max(I.V(k, T) for T in pairs)
            for T in pairs:
                nb = apply_chain(I, b, P, T); I2, b2, keep = reduced(I, nb, k)
                goods = [g for g in range(I.m) if g not in set(T)]; tk = I.V(k, T)
                rest = [g for g in I.R[k] if g not in T]
                for *_, X2, how in s_cases(I2, b2, dangerous(I2, b2), True, True):
                    if X2 is None: continue
                    X = [[goods[g] for g in x] for x in X2]
                    C['(R) cases'] += 1
                    ka = any(set(rest) <= set(x) and len(rest) == 2 and I.threat(k, tk, x) for x in X)
                    kb = any(len(x) >= 2 and any(g in x and g != b[k][0] and I.v[k][g] > tk for g in rest) for x in X)
                    if ka: C['(K-a) fails'] += 1
                    if kb: C['(K-b) fails'] += 1
                    thr = any(I.threat(k, tk, x) for x in X)
                    if thr != (ka or kb): C['MISMATCH: (K) fails iff (K-a) or (K-b)'] += 1
                    if not thr and tk == top: best_ok = True
    return C, best_ok


if __name__ == '__main__':
    recs = [json.loads(l) for l in (gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1]))]
    T = collections.Counter()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C, ok in pool.imap(study, recs, chunksize=8):
            T.update(C); T['starts'] += 1; T['best pool pair T* has a case with (R) and (K)'] += ok
    print('$ python3 k4/oc1max_multi/rec_k.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
