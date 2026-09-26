"""Timing of algorithm K3ALG (k3algo.py) on random instances: EVIDENCE only.

For each n, a few random instances of three families:
- core:    every agent values exactly three goods, balanced, values from a few levels (ties) or uniform in 1..100,
           m = 3n/2 goods (so Stage R peels little and LB+ does the work);
- core2m:  the same with m = 2n goods (more junk, so LB+ usually needs an owner and sometimes rotates);
- general: every agent values 0-3 goods with arbitrary positive values (top-heavy agents and ties occur), m = 2n.
`fast` is timed on its own (the input is already in memory); the raw EFX0 check of the output is timed separately.
`mirror` (the literal transcription of the Lean definitions, O(n^4 + n^2 m)) is timed on the smaller n.
The log-log slope between consecutive n estimates the growth exponent of the median time.

Usage: python3 k3/timing.py [--max-n=N] [--mirror-max-n=K] [--reps=R] [--seed=S]
"""
import sys, os, time, random, math, statistics
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3algo import fast, mirror, raw_efx0, random_instance

def core_instance(n, m, rng):
    v = []
    for _ in range(n):
        S = rng.sample(range(m), 3)
        if rng.random() < 0.5:
            x = rng.choice([(3, 2, 2), (4, 3, 2), (2, 2, 2), (5, 4, 2), (3, 3, 2)])
        else:
            while True:
                x = sorted((rng.randint(1, 100) for _ in range(3)), reverse=True)
                if x[0] < x[1] + x[2]: break
        v.append(dict(zip(S, x)))
    return v

def main():
    opt = {a.split('=')[0]: a.split('=')[1] for a in sys.argv[1:] if '=' in a}
    maxn = int(opt.get('--max-n', 100000)); mmax = int(opt.get('--mirror-max-n', 80))
    reps = int(opt.get('--reps', 3)); rng = random.Random(int(opt.get('--seed', 1)))
    ns = [n for n in [10, 20, 40, 80, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000] if n <= maxn]
    print(f"python {sys.version.split()[0]}; {reps} instances per (family, n); times in seconds (median)")
    for fam in ['core', 'core2m', 'general']:
        print(f"\nfamily {fam}")
        print(f"{'n':>7} {'m':>7} {'fast':>9} {'slope':>6} {'check':>8} {'mirror':>9} {'slope':>6}  branches, peeled, core size")
        prev = None
        for n in ns:
            m = 3 * n // 2 if fam == 'core' else 2 * n
            tf, tc, tm, notes = [], [], [], []
            for _ in range(reps):
                v = core_instance(n, m, rng) if fam.startswith('core') else random_instance(n, m, rng)
                t0 = time.perf_counter(); X, info = fast(n, m, v); t1 = time.perf_counter()
                ok = raw_efx0(n, m, v, X); t2 = time.perf_counter()
                if not ok: print("NOT EFX0", n, m); sys.exit(1)
                tf.append(t1 - t0); tc.append(t2 - t1)
                if n <= mmax:
                    t0 = time.perf_counter(); Xm, _ = mirror(n, m, v); t1 = time.perf_counter()
                    if Xm != X: print("MISMATCH", n, m); sys.exit(1)
                    tm.append(t1 - t0)
                notes.append(f"{info['branch']}/{info['peeled']}/{info['core_n']}")
            f, c = statistics.median(tf), statistics.median(tc)
            mm = statistics.median(tm) if tm else None
            sf = sm = ''
            if prev:
                pn, pf, pm = prev
                sf = f"{math.log(f / pf) / math.log(n / pn):6.2f}"
                if mm and pm: sm = f"{math.log(mm / pm) / math.log(n / pn):6.2f}"
            print(f"{n:>7} {m:>7} {f:>9.4f} {sf:>6} {c:>8.4f} {(f'{mm:9.3f}' if mm else '        -'):>9} {sm:>6}  "
                  + ', '.join(notes))
            prev = (n, f, mm)
            sys.stdout.flush()

if __name__ == '__main__':
    main()
