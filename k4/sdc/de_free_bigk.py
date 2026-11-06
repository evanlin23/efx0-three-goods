"""The one-chain repair at larger k (k4/sdc.md §29): random strict instances in which agents value 2..K goods (as in
sdc_bigk.py); from every order's serial-dictatorship start, the least number of improving chain moves (de_free.py,
chains only, |H| and bases up to K) after which the bases extend.

    python3 k4/sdc/de_free_bigk.py SEED T n M K [oc1]
oc1: the one-absorber completion (oc_absorb.extends_A, A = 1) at the start and after the chain instead of the free one."""
import sys, random, json, collections, time, itertools
import _paths
import de_free as DF
from sdclib import Enc
from sdc_orders import sd

if __name__ == '__main__':
    seed, T, n, M, K = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    DF.CHAIN_ONLY = True; DF.HMAX = K; DF.BMAX = K
    if 'oc1' in sys.argv[6:]:
        from oc_absorb import extends_A
        DF.extends = lambda E, b: extends_A(E, b, 1)
    print('$ python3 k4/sdc/de_free_bigk.py', *sys.argv[1:], flush=True)
    for t in range(T):
        m = rng.randint(n + 1, M)
        sets, vals = [], []
        for i in range(n):
            R = sorted(rng.sample(range(m), rng.randint(2, min(K, m))))
            sets.append(R); vals.append(rng.sample(range(1, 100), len(R)))
        if len(set().union(*map(set, sets))) < m: continue
        E = Enc(sets, vals, m); memo = {}; C['instances'] += 1; res = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y not in res:
                base = [-1] * m
                for i, g in enumerate(Y):
                    if g is not None: base[g] = i
                res[Y] = DF.search(E, tuple(base), memo)
            C['starts'] += 1; C['start: least depth %s' % res[Y]] += 1
        bad = [Y for Y, d in res.items() if not isinstance(d, int)]
        if bad: print('NO MONOTONE REPAIR', json.dumps((sets, vals)), 'picks', bad[0], res[bad[0]], flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
