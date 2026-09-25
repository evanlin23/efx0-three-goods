#!/usr/bin/env python3
"""Random instances for k4/hall.c: n agents, each with 3 or 4 goods out of m and a random strict balanced type
(k4/check4.py's representatives). Not necessarily cores: goods may be valued by nobody or by one agent only.
Used to test statements whose proofs do not use the core conditions (k4/hall.md).

usage: python3 k4/hall_random.py N M COUNT [--seed=S] [--p4=0.5] [hall options...]
Runs k4/hall.c on COUNT random instances (one profile each) and sums its counters."""
import os, random, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import strict_balanced_types
from hall_run import binary

def main():
    n, m, cnt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seed, p4, opts = 1, 0.5, []
    for a in sys.argv[4:]:
        if a.startswith('--seed='): seed = int(a[7:])
        elif a.startswith('--p4='): p4 = float(a[5:])
        else: opts.append(a)
    rng = random.Random(seed)
    T3, T4 = strict_balanced_types(3), strict_balanced_types(4)
    b = binary()
    tot = {}
    for r in range(cnt):
        lines = [f'{n} {m}']
        for i in range(n):
            d = 4 if rng.random() < p4 else 3
            S = rng.sample(range(m), d)
            v = list(rng.choice(T4 if d == 4 else T3)); rng.shuffle(v)
            lines.append(f'{d} ' + ' '.join(map(str, S)) + ' 1'); lines.append(' '.join(map(str, v)))
        lines.append('0 1')
        out = subprocess.run([b, '-1'] + opts, input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True).stdout
        for line in out.splitlines():
            w = line.split()
            if line.startswith('EX'): print(f'inst {r}: {line}')
            elif w and w[0] in ('G0', 'F0'):
                cur = tot.setdefault(w[0], [0] * (len(w) - 1))
                for q, x in enumerate(w[1:]): cur[q] += int(x)
            elif line.startswith('RESULT'):
                for k, x in zip(w[1::2], w[2::2]): tot[k] = tot.get(k, 0) + int(x)
    print(f'RANDOM n={n} m={m} count={cnt} seed={seed} p4={p4} ' + ' '.join(f'{k} {v}' for k, v in tot.items()))

if __name__ == '__main__':
    main()
