"""Full test protocol for one candidate (single process):
  every ranking profile for (2, 3..6), (3, 4..7), (4, 5..6); the n = 5 core sample (200 random profiles per core, three
  balanced realizations); K random ranking profiles and K random general instances with n <= 8.

  python3 full.py "EXPR" [K]          e.g.  python3 full.py "envypool('draft','greedy')" 20000
"""
import sys
from common import run_small, run_core5, run_random, explain, SMALL
import algos

expr = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
alg = eval(expr, vars(algos))
print(f"== {alg.__name__}   ({expr})", flush=True)
res, first = run_small(alg, SMALL)
tot = sum(t for t, b, _ in res.values()); bad = sum(b for t, b, _ in res.values())
print(f"  small total: {tot} profiles, failures {bad}")
if first:
    n, m, rank, X = first
    print(f"  smallest failure: n={n} m={m} rankings {rank}")
    for line in explain(n, m, rank, X): print("    " + line)
t, b, f = run_core5(alg)
if f:
    print(f"  smallest core failure: m={f[1]} rankings {f[2]} realization {f[4]}")
    for line in explain(f[0], f[1], f[2], f[3], f[4]): print("    " + line)
bp, bg, fp, fg = run_random(alg, K)
if fp:
    print(f"  smallest random profile failure: n={fp[0]} m={fp[1]} rankings {fp[2]}")
    for line in explain(fp[0], fp[1], fp[2], fp[3]): print("    " + line)
if fg: print(f"  smallest random general failure: n={fg[0]} m={fg[1]} v={fg[2]} X={fg[3]}")
