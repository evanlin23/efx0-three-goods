#!/usr/bin/env python3
"""Sums the counters of k4/f2_shapes.py logs (one group per argument: NAME=GLOB) into the tables of k4/f2.md §1.
usage: python3 k4/f2_table.py 'main=results/k4_f2/shapes_[0-7].log' 'n5=results/k4_f2/shapes5_*.log' ..."""
import collections, glob, re, sys

ROWS = [('profiles', 'profiles read'), ('profiles f>=2, omega>=1', 'profiles with f >= 2, omega >= 1'),
        ('def>0 states', 'def > 0 states'), ('T3-stage', 'T3-stage states'),
        ('T3-stage f=2', '  f = 2'), ('T3-stage f=3', '  f = 3'),
        ('T3-stage not T4-optimal', '  not T4-optimal'),
        ('case A-S1', 'case A-S1 (S1 shape)'), ('case A-z', 'case A-z (free needer, not the owner)'),
        ('case B-S1c', 'case B-S1c (frozen needers only; owner at the free end of a need path)'),
        ('case B', 'case B (frozen needers only; owner not a free end)'), ('case C', 'case C (no single frozen blocker)'),
        ('chain-only', 'an improving (T3⁺) move but no improving (T3) move (DL_RT4 fails)'),
        ('FAILURE of DL_RC (T3 stage, no improving T3+ move)', 'no improving (T3⁺) move (DL_RC fails)'),
        ('keys def*>0', 'keys with def* > 0'),
        ('key graph: no single T3/T4 edge to a smaller def* (RT4)', '  without a (T3)/(T4) edge to a smaller def*'),
        ('KEY-GRAPH FAILURE: no single T3+/T4 edge to a smaller def* (R_C)', '  without a (T3⁺)/(T4) edge to a smaller def*')]


def read(globpat):
    cnt = collections.Counter(); files = sorted(glob.glob(globpat)); done = 0
    for fn in files:
        lines = open(fn).read().splitlines()
        if any(l.startswith('# done') for l in lines) or any(l.startswith('profiles ') for l in lines): done += 1
        for l in lines:
            m = re.match(r'^(\S.*?)\s{2,}(\d+)$', l)
            if m and not l.startswith(('smallest', '#', 'FAILURE ', 'KEYFAIL', 'CHAINONLY')):
                k = m.group(1)
                if k.startswith('DL_RT4 fails (only chains'): cnt['chain-only'] += int(m.group(2))
                cnt[k] += int(m.group(2))
    return cnt, len(files), done


def main(argv):
    groups = [a.split('=', 1) for a in argv]
    data = [(name,) + read(g) for name, g in groups]
    print('| | ' + ' | '.join('%s (%d/%d logs complete)' % (n, d, f) for n, _, f, d in data) + ' |')
    print('|---' * (len(data) + 1) + '|')
    for key, label in ROWS:
        print('| %s | %s |' % (label, ' | '.join('{:,}'.format(c[key]) for _, c, _, _ in data)))
    print()
    print('Certificates of k4/f2_shapes.py (plain role swaps, k4/dl13.md Corollaries 9.1, 11.1, 8.2), by case:')
    for name, c, _, _ in data:
        cells = sorted(k for k in c if k.startswith('cert '))
        print('- %s: %s' % (name, '; '.join('%s %s' % (k[5:], '{:,}'.format(c[k])) for k in cells)))


if __name__ == '__main__':
    main(sys.argv[1:])
