"""Exact P1 test by brute force on random instances: degrees k3 (all agents 3 goods) or k4 (3 or 4)."""
import sys, random, itertools, json
from p1_brute import analyse
def rand_inst(rng, n, m, sizes):
    while True:
        R = [sorted(rng.sample(range(m), rng.choice(sizes))) for _ in range(n)]
        if set().union(*map(set, R)) == set(range(m)): break
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        while True:
            vals = rng.sample(range(1, 12), len(R[i]))
            if max(vals) < sum(vals) - max(vals): break
        for g, x in zip(R[i], vals): v[i][g] = x
    return R, v
if __name__ == "__main__":
  seed, n, m, T, kind = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
  sizes = [3] if kind == 'k3' else [4] if kind == 'k4p' else [3, 4]
  rng = random.Random(seed); c = 0
  for t in range(T):
      R, v = rand_inst(rng, n, m, sizes)
      comp, npm, bad, badut, badlm = analyse(n, m, v)
      if bad:
          c += 1
          if c <= 3: print('P1-FAIL', json.dumps((R, [[v[i][g] for g in R[i]] for i in range(n)])), bad, flush=True)
  print(kind, n, m, 'instances', T, 'P1 failures', c)
