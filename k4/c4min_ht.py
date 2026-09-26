#!/usr/bin/env python3
"""k4/c4min.c on the cores H_t of k4/c4.md §7, one profile each (the values of §7), for Corollary Z (k4/c4min.md §3.4).

H_t is built by k4/c4_verify_H/hcore.py (the independent construction of PR #33's review); every agent gets the one
type of §7. c4min.c takes at most 12 agents, so t <= 2 (n = 4t + 1). Prints the sha1 of k4/c4min.c, then c4min's
RESULT and PHI lines per core.
usage: python3 k4/c4min_ht.py T [T ...] [c4min options, e.g. -f 0 -p 9,16]"""
import hashlib, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'c4_verify_H'))
from c4min_run import binary
from hcore import build_H


def main():
    args = sys.argv[1:]; k = 0
    while k < len(args) and args[k].isdigit(): k += 1
    ts, opts = [int(a) for a in args[:k]], args[k:]
    print(f"# k4/c4min.c sha1 {hashlib.sha1(open(os.path.join(HERE, 'c4min.c'), 'rb').read()).hexdigest()}")
    b = binary()
    for t in ts:
        agents, goods, v = build_H(t)
        n, m = len(agents), len(goods)
        lines = [f'{n} {m}']
        for i in range(n):
            S = [g for g in range(m) if v[i][g] > 0]
            lines += [f'{len(S)} ' + ' '.join(map(str, S)) + ' 1', ' '.join(str(v[i][g]) for g in S)]
        r = subprocess.run([b] + opts, input='\n'.join(lines) + '\n0 1\n', capture_output=True, text=True, check=True)
        print(f'H_{t}: n = {n}, m = {m}')
        for line in r.stdout.splitlines(): print('  ' + line)
        sys.stdout.flush()


if __name__ == '__main__':
    main()
