#!/usr/bin/env python3
"""Random evidence for conjecture C4min (k4/c4x.md §5) beyond the enumerated core lists.

Draws random connected k = 4 cores (agents with 3 or 4 goods, every good valued, at most |R_i| - 2 private goods, two
private goods p, q only with p + q < s + t, connected: `k4/check4.py`'s is_core and core_domains) with random strict
types, and runs `k4/c4x.c -1s -R` on each profile: it reports the fewest frozen agents and whether some pre-allocation
with that many frozen agents has deficit <= 0 (stopping at the first). A profile where none has is printed as FAIL.

usage: python3 k4/c4x_random.py N M N4 COUNT [--seed=S]
  N agents, M goods, N4 agents with four goods (the rest three), COUNT random profiles (each on a fresh random core)."""
import sys, os, random, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import is_core, core_domains
import c4x_run

def random_core(rng, n, m, n4):
    for _ in range(100000):
        sizes = [4] * n4 + [3] * (n - n4)
        sets = [sorted(rng.sample(range(m), d)) for d in sizes]
        ok, _ = is_core(n, m, sets, False)
        if ok: return sets
    return None

def main():
    n, m, n4, count = map(int, sys.argv[1:5])
    seed = 1
    for a in sys.argv[5:]:
        if a.startswith('--seed='): seed = int(a[7:])
    rng = random.Random(seed)
    b = c4x_run.binary()
    fails = done = 0
    minF = {}
    for k in range(count):
        sets = random_core(rng, n, m, n4)
        if sets is None: print('no core found'); return
        doms = core_domains(sets, m, False)
        vals = [rng.choice(D) for D in doms]
        lines = [f'{n} {m}']
        for S, v in zip(sets, vals):
            lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1')
            lines.append(' '.join(str(v[g]) for g in S))
        lines.append('0 1')
        out = subprocess.run([b, '-1s', '-R', '-p', '6'], input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True).stdout
        st = [l for l in out.splitlines() if l.startswith('STREAM')][0].split()
        de = [l for l in out.splitlines() if l.startswith('DEFICIT')][0]
        f = int(st[4]); minF[f] = minF.get(f, 0) + 1
        ok = 'with deficit <= 0: 0' not in de
        done += 1
        if not ok:
            fails += 1
            print('FAIL', sets, [[v[g] for g in S] for S, v in zip(sets, vals)], de, flush=True)
    print(f'RANDOM n={n} m={m} n4={n4} profiles {done} fails {fails} fewest-frozen distribution {dict(sorted(minF.items()))}')

if __name__ == '__main__':
    main()
