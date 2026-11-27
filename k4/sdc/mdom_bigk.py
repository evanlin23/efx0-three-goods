"""Matching domination at larger k (k4/sdc.md §28): random strict instances in which agents value 2..K goods (K up to
m, as in sdc_bigk.py); every maximal matching is tested for value domination by a complete EFX0 allocation (mdom.py),
and the partial allocations with at most one two-good bundle (pdom.py, PAIRS = 1).

    python3 k4/sdc/mdom_bigk.py SEED T n M K"""
import sys, random, json, collections, time
import _paths
from sdclib import Enc
from mdom import matchings
from vdom import dominated
from pdom import allocations, efx0_partial, dominated_vec

if __name__ == '__main__':
    seed, T, n, M, K = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/mdom_bigk.py', *sys.argv[1:], flush=True)
    for t in range(T):
        m = rng.randint(n + 1, M)
        sets, vals = [], []
        for i in range(n):
            R = sorted(rng.sample(range(m), rng.randint(2, min(K, m))))
            sets.append(R); vals.append(rng.sample(range(1, 100), len(R)))
        if len(set().union(*map(set, sets))) < m: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        ms = matchings(E); bad = [Y for Y in ms if not dominated(E, Y)]
        C['maximal matchings'] += len(ms); C['matchings not dominated'] += len(bad)
        if bad: print('MD FAILS', json.dumps((sets, vals)), 'matching', bad[0], flush=True)
        vecs = {}
        for B in allocations(E, 1):
            u = tuple(E.val(i, B[i]) for i in range(E.n))
            if u not in vecs and efx0_partial(E, B): vecs[u] = B
        top = [u for u in vecs if not any(w != u and all(a >= b for a, b in zip(w, u)) for w in vecs)]
        bad1 = [u for u in top if not dominated_vec(E, u)]
        C['one-pair vectors'] += len(top); C['one-pair not dominated'] += len(bad1)
        if bad1: print('MD1 FAILS', json.dumps((sets, vals)), 'allocation', vecs[bad1[0]], flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
