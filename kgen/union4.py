"""Disjoint unions of two two-agent instances as candidate n = 4 counterexamples to OC1 / OC with k <= K.

OC1 allows one chain and one absorber in total.  If each two-agent component needs an absorber or a chain at its picks,
their disjoint union (agents of one component value nothing of the other) may need two.  Chains may still cross
components, so this is only a generator: every union is tested by the brute force kgen/ocn.c (all 24 orders).

    python3 kgen/union4.py SEED N K MMAX_COMPONENT"""
import sys, random, json, itertools, collections, time
from ocnlib import brute_n
from oc2 import efx0, sd


def comp(rng, m, K):
    while True:
        v = [[0] * m for _ in range(2)]
        for i in range(2):
            S = rng.sample(range(m), rng.randint(2, min(K, m)))
            for g, x in zip(S, rng.sample(range(1, 60), len(S))): v[i][g] = x
        if all(v[0][g] or v[1][g] for g in range(m)): return v


def needs_absorber(v):
    """some order of the component whose picks have no completion where nobody gets 2+ junk goods"""
    m = len(v[0]); res = []
    Xs = [[{g for g in range(m) if a[g] == i} for i in range(2)] for a in itertools.product(range(2), repeat=m)]
    Xs = [X for X in Xs if efx0(v, X)]
    for o in [(0, 1), (1, 0)]:
        y = sd(v, o)
        B = [{y[i]} if y[i] is not None else set() for i in range(2)]
        res.append(not any(all(B[i] <= X[i] for i in range(2)) and all(len(X[i] - B[i]) <= 1 for i in range(2)) for X in Xs))
    return any(res)


def union(v1, v2):
    m1, m2 = len(v1[0]), len(v2[0])
    return [r + [0] * m2 for r in v1] + [[0] * m1 + r for r in v2]


if __name__ == '__main__':
    seed, N, K, MC = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 kgen/union4.py', *sys.argv[1:], flush=True)
    pool = []
    while len(pool) < 60:
        v = comp(rng, rng.randint(3, MC), K)
        if needs_absorber(v): pool.append(v)
    for t in range(N):
        v1, v2 = rng.choice(pool), rng.choice(pool)
        v = union(v1, v2)
        if len(v[0]) > 11: continue
        orders, r = brute_n(v); C['unions'] += 1
        bad = [k for k in range(len(r)) if r[k]['CODE'] == 0]
        badoc = [k for k in range(len(r)) if r[k]['FREEOC'] == 0]
        C['unions failing OC1 (t>=0)'] += bool(bad); C['unions failing OC'] += bool(badoc)
        if bad and C['shown'] < 6:
            C['shown'] += 1
            print('UNION FAILS OC1', json.dumps(v), 'order', orders[bad[0]], 'picks', r[bad[0]]['picks'],
                  'OC fails too' if badoc else 'OC holds', 'k', max(sum(1 for x in row if x > 0) for row in v), flush=True)
    for k in sorted(C):
        if k != 'shown': print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
