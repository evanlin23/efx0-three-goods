"""Witnesses for Theorem REC-S (k4/oc1max_multi.md §12) at every start of a two-move export (default: the certifier's
n = 4 export, results/k4_matching/data/two_move_starts_n4.json.gz on proof/k4-matching; every start with no one-move
repair).  For each start: an order, the dangerous agent k, its earliest-wanter chain E(k), the pool pair T, and in the
reduced instance a Theorem S case (k', longest chain P', kept-out good h, improving H0'), given back in the labels of the
full instance, with the final allocation.  Checked independently by check_recs.py.

    python3 k4/oc1max_multi/recs_witness.py EXPORT.json.gz OUT.json.gz
"""
import sys, os, json, gzip, itertools, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from dred import apply_chain
from reduce_check import reduced
from theorem_s import s_cases
from reduce_s import earliest_chain


def witness(row):
    I = Inst(row['sets'], row['vals']); b = base_from_picks(tuple(row['picks'])); J = junk(I, b)
    D = dangerous(I, b); p = [I.V(i, b[i]) for i in range(I.n)]
    for order in row['orders']:
        for k in D:
            P = earliest_chain(I, b, k, order)
            pool = [g for g in J + list(b[P[-1]]) if g in I.R[k]]
            for T in itertools.combinations(pool, 2):
                if I.V(k, T) <= p[k]: continue
                nb = apply_chain(I, b, P, T); val = [I.V(i, nb[i]) for i in range(I.n)]
                if any(i != k and I.R[i] and any(I.v[i].get(g, 0) >= val[i] for g in T) for i in range(I.n)): continue
                I2, b2, keep = reduced(I, nb, k); goods = [g for g in range(I.m) if g not in set(T)]
                for k2, P2, h, H0, X2, how in s_cases(I2, b2, dangerous(I2, b2), True, True):
                    if X2 is None or not I2.efx0(X2): continue
                    X = [[] for _ in range(I.n)]; X[k] = sorted(T)
                    for j2, i in enumerate(keep): X[i] = sorted(goods[g] for g in X2[j2])
                    if any(I.threat(k, I.V(k, T), X[j]) for j in range(I.n) if j != k) or not I.efx0(X): continue
                    return {'order': list(order), 'k': k, 'P1': list(P), 'T': sorted(T),
                            'P2': [keep[a] for a in P2], 'H0_2': sorted(goods[g] for g in H0), 'h': goods[h],
                            'X': X}
    return None


if __name__ == '__main__':
    d = json.load(gzip.open(sys.argv[1]))
    rows = [{'list': hg['list'], 'idx': hg['idx'], 'sets': hg['sets'], 'vals': s['vals'], 'picks': s['picks'],
             'orders': s['orders']} for hg in d['hypergraphs'] for s in hg['starts']]
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        ws = pool.map(witness, rows, chunksize=64)
    out = [dict(r, witness=w) for r, w in zip(rows, ws)]
    json.dump({'what': 'Theorem REC-S witnesses (k4/oc1max_multi.md §12), one per start of the export; checked by '
                       'k4/oc1max_multi/check_recs.py', 'export': sys.argv[1], 'starts': out},
              gzip.open(sys.argv[2], 'wt'))
    print('$ python3 k4/oc1max_multi/recs_witness.py', *sys.argv[1:])
    print('starts', len(out), 'with a witness', sum(1 for w in ws if w), 'without', sum(1 for w in ws if not w))
