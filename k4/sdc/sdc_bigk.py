"""SD-C and NOF2 at larger k (k4/sdc.md §22): random strict instances in which agents value up to K goods (K up to m);
for SD-C count the extendable serial-dictatorship outcomes (sdc_climb.count, SAT), for NOF2 test the neediest-first
order with at most two deferrals (nof2.nof2).  A failure at large k can then be reduced toward k = 4 (phi_reduce.py's
method).

    python3 k4/sdc/sdc_bigk.py SEED T n M K"""
import sys, random, json, collections, time
import _paths
from sdc_climb import count
import nof2 as N2

if __name__ == '__main__':
    seed, T, n, M, K = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/sdc_bigk.py', *sys.argv[1:], flush=True)
    for t in range(T):
        m = rng.randint(n + 1, M)
        sets, vals = [], []
        for i in range(n):
            R = sorted(rng.sample(range(m), rng.randint(2, min(K, m))))
            sets.append(R); vals.append(rng.sample(range(1, 100), len(R)))
        if len(set().union(*map(set, sets))) < m: continue
        C['instances'] += 1
        c = count(sets, vals, m, False)
        if c == 0:
            C['SD-C FAILS'] += 1; print('SD-C FAILS', json.dumps((sets, vals)), flush=True)
        r = N2.nof2(sets, vals, m)
        C['NOF2: deferrals needed %s' % r] += 1
        if r is None: print('NOF2 FAILS', json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
