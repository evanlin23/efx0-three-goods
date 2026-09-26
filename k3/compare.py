"""K3ALG (k3algo.fast) and LS2 (ls2.ls2) on the same random cores: running time and output shape. EVIDENCE only.

The cores come from ls2.random_true_core (every agent three goods, balanced; every good valued; at most one private
good per agent; m about 3n/2), half with values from a few levels (ties), half uniform. Both outputs are checked
against the raw EFX0 definition and for at most one bundle of more than two goods. Times are medians in seconds.

Usage: python3 k3/compare.py [--max-n=N] [--reps=R] [--seed=S]
"""
import sys, os, time, random, math, statistics, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3algo import fast, raw_efx0
from ls2 import ls2, random_true_core

def main():
    opt = {a.split('=')[0]: a.split('=')[1] for a in sys.argv[1:] if '=' in a}
    maxn = int(opt.get('--max-n', 5000)); reps = int(opt.get('--reps', 3)); rng = random.Random(int(opt.get('--seed', 1)))
    ns = [n for n in [20, 50, 100, 200, 500, 1000, 2000, 5000, 10000] if n <= maxn]
    print(f"python {sys.version.split()[0]}; {reps} random cores per n; median seconds; slope = log-log growth")
    print(f"{'n':>6} {'m':>6} {'K3ALG':>9} {'slope':>6} {'LS2':>9} {'slope':>6} {'LS2 steps/n':>11}  K3ALG branch / LS2 phase 2")
    prev = None
    for n in ns:
        tk, tl, st, notes, ms = [], [], [], [], []
        for r in range(reps):
            n_, m, v = random_true_core(n, rng, levels=(r % 2 == 1))
            ms.append(m)
            t0 = time.perf_counter(); X1, i1 = fast(n, m, v); t1 = time.perf_counter()
            X2, i2 = ls2(n, m, v); t2 = time.perf_counter()
            for X in (X1, X2):
                big = sum(1 for s in collections.Counter(X).values() if s > 2)
                if not raw_efx0(n, m, v, X) or big > 1: print("FAIL", n, m); sys.exit(1)
            tk.append(t1 - t0); tl.append(t2 - t1); st.append(i2['steps'] / n)
            notes.append(f"{i1['branch']}/{i2['phase2']}")
        k, l = statistics.median(tk), statistics.median(tl)
        sk = sl = ''
        if prev:
            pn, pk, pl = prev
            sk = f"{math.log(k / pk) / math.log(n / pn):6.2f}"; sl = f"{math.log(l / pl) / math.log(n / pn):6.2f}"
        print(f"{n:>6} {statistics.median(ms):>6.0f} {k:>9.4f} {sk:>6} {l:>9.4f} {sl:>6} {max(st):>11.2f}  "
              + ', '.join(notes))
        prev = (n, k, l); sys.stdout.flush()

if __name__ == '__main__':
    main()
