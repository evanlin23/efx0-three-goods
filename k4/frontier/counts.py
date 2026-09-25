"""Core counts for n agents: nauty genbg graphs per number n4 of 4-good agents (connected, agent degrees 3-4 with exactly
n4 of degree 4, good degree >= 1; before the private-goods filter), and, for the given n4 values, the k = 4 cores after
the filter (search4.cores: at most d - 2 private goods for an agent of degree d). Usage: counts.py n [n4,n4,..]"""
import os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import search4 as S4

if __name__ == '__main__':
    n = int(sys.argv[1])
    post = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else []
    print(f"command: python3 k4/frontier/counts.py {' '.join(sys.argv[1:])}", flush=True)
    for n4 in range(1, n + 1):
        e, per = 3 * n + n4, {}
        for m in range(4, 3 * n + 1):
            if e < n + m - 1: continue
            r = subprocess.run([S4.GENBG, '-c', '-u', f'-d3:1', f'-D4:{n}', str(n), str(m), f'{e}:{e}'], capture_output=True, text=True)
            c = int([l for l in r.stderr.splitlines() if l.startswith('>Z')][0].split()[1])
            if c: per[m] = c
        print(f"n={n} n4={n4}: genbg graphs before the private-goods filter: {sum(per.values())} {per}", flush=True)
    for n4 in post:
        t = time.time()
        per = {m: len(S4.cores(n, m, n4 == n, None if n4 == n else n4)) for m in range(4, 3 * n + 1)}
        per = {m: c for m, c in per.items() if c}
        print(f"n={n} n4={n4}: k = 4 cores (after the filter): {sum(per.values())} {per} [{time.time() - t:.0f}s]", flush=True)
