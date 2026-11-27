"""P1 at n = 2 (kgen/charity.md §9): is every Pareto maximum of a two-agent additive instance complete?  Random
instances with every good relevant to both agents (k = m), and with random supports; exact per instance
(chlib.pm_with_pool, CEGAR over Pareto maxima).

    python3 kgen/charity/p1_n2.py SEED T MMIN MMAX"""
import sys, random, collections, json
from chlib import Inst, pm_with_pool, pool_of

if __name__ == '__main__':
    seed, T, MMIN, MMAX = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/charity/p1_n2.py', *sys.argv[1:], flush=True)
    for t in range(T):
        m = rng.randint(MMIN, MMAX); full = t % 2 == 0
        vmax = rng.choice([3, 10, 50])
        v = [{g: rng.randint(1, vmax) for g in range(m) if full or rng.random() < 0.7} for _ in range(2)]
        I = Inst(2, m, v)
        X, st = pm_with_pool(I, 1)
        C['%s: Pareto maximum with a pool %s' % ('all goods relevant' if full else 'random supports', X is not None)] += 1
        if X is not None:
            print('FOUND', json.dumps({'inst': I.to_json(), 'X': [sorted(B) for B in X]}), flush=True)
    for k in sorted(C):
        print(k, C[k])
