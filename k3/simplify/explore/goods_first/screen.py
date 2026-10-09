"""Screen candidates: every ranking profile for the small sets (stopping a candidate's run at the first set where
it fails, unless --full), then the n = 5 core sample and random profiles for candidates that survive.

  python3 screen.py NAME [NAME ...] [--full] [--core] [--rand K]
NAME is a Python expression over algos.py, e.g. "ece('idx','bestval',True)".
"""
import sys, time
from common import run_small, run_core5, run_random, explain, SMALL
import algos
from algos import *   # noqa: F401,F403

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    full = '--full' in sys.argv; core = '--core' in sys.argv
    K = next((int(a.split('=')[1]) for a in sys.argv if a.startswith('--rand=')), 0)
    sets = SMALL if '--n4m6' in sys.argv else [s for s in SMALL if s != (4, 6)]
    for expr in args:
        alg = eval(expr, vars(algos))
        print(f"== {alg.__name__}   ({expr})", flush=True)
        res, first = run_small(alg, sets, stop=None if full else (lambda r: True))
        if first:
            n, m, rank, X = first
            print(f"  smallest failure: n={n} m={m} rankings {rank}")
            for line in explain(n, m, rank, X): print("    " + line)
        if (first is None or full) and core:
            tot, bad, f = run_core5(alg)
            if f: print(f"  first core failure: m={f[1]} rankings {f[2]} real {f[4]}"); [print("    " + l) for l in explain(f[0], f[1], f[2], f[3], f[4])]
        if (first is None or full) and K:
            bp, bg, fp, fg = run_random(alg, K)
            if fp: print(f"  random profile failure: n={fp[0]} m={fp[1]} rankings {fp[2]}")
            if fg: print(f"  random general failure: n={fg[0]} m={fg[1]} v={fg[2]} X={fg[3]}")
        sys.stdout.flush()

if __name__ == '__main__':
    main()
