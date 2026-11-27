"""SD-C on random instances with k relevant goods per agent (k up to m)."""
import sys, random, json, collections
from sdsat import solve
seed, N, n, m, k = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter()
for t in range(N):
    while True:
        sets = [sorted(rng.sample(range(m), rng.randint(max(1, k - 1), k))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    vals = [rng.sample(range(1, 60), len(s)) for s in sets]
    ok, w = solve(sets, vals, m); C[ok] += 1
    if not ok and C['shown'] < 3: C['shown'] += 1; print('FAIL', json.dumps((sets, vals)), flush=True)
print('k', k, 'n', n, 'm', m, dict(C))
