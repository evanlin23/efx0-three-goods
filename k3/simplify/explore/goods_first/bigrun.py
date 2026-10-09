"""Larger evidence for one candidate (single process): S random profiles per certified core with n = 6 (three balanced
realizations), K random ranking profiles with n <= 9 and K/2 random general instances with n <= 9.

  python3 bigrun.py "EXPR" S K SEED
"""
import sys, random, time
from common import core_profiles, check_rank, rand_general, explain, efx0
import algos

expr = sys.argv[1]; S, K, seed = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
alg = eval(expr, vars(algos))
print(f"== {alg.__name__}   ({expr})", flush=True)
t = time.time(); tot = bad = 0; first = None
for n, m, rank in core_profiles(6, sample=S, minn=6, seed=seed):
    tot += 1
    for real in ((4, 3, 2), (10, 9, 2), (10, 6, 5)):
        ok, X = check_rank(alg, n, m, rank, real)
        if not ok:
            bad += 1; first = first or (n, m, rank, X, real); break
print(f"  core n=6 sample ({S}/core, seed {seed}): {tot} profiles x 3 realizations, failing profiles {bad}  [{time.time() - t:.0f}s]", flush=True)
if first: print(f"  first: m={first[1]} rankings {first[2]} real {first[4]}"); [print("    " + l) for l in explain(*first[:4], first[4])]
rng = random.Random(seed); t = time.time(); bad = 0; first = None
for _ in range(K):
    n = rng.randint(2, 9); m = rng.randint(max(3, n), 2 * n + 3)
    rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
    ok, X = check_rank(alg, n, m, rank)
    if not ok:
        bad += 1
        if first is None or (n, m) < first[:2]: first = (n, m, rank, X)
print(f"  random ranking profiles n<=9: {K}, failures {bad}  [{time.time() - t:.0f}s]", flush=True)
if first: print(f"  smallest: n={first[0]} m={first[1]} rankings {first[2]}"); [print("    " + l) for l in explain(*first)]
t = time.time(); bad = 0; first = None
for _ in range(K // 2):
    n, m, v = rand_general(rng, 9)
    X = alg(n, m, v)
    if X is None or None in X or not efx0(n, m, v, X):
        bad += 1
        if first is None or (n, m) < first[:2]: first = (n, m, v, X)
print(f"  random general instances n<=9: {K // 2}, failures {bad}  [{time.time() - t:.0f}s]", flush=True)
if first: print(f"  smallest: {first}")
