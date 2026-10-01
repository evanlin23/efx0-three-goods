#!/usr/bin/env python3
"""The input table of k4/dl13.md §1 from the logs of k4/dl13_stuck.py (results/k4_dl13_stuck/stuck_*.log).
usage: python3 k4/dl13_table.py results/k4_dl13_stuck/stuck_*.log"""
import collections, os, re, sys

GROUPS = [('suite', 'the suite (cores, n ≤ 6)'), ('gap_n3', 'n = 3 catalogue, every record'),
          ('gap_n4', 'n = 4 catalogues (every 4th; f ≥ 2 every record)'), ('hard_hunt', 'hard hunt (n = 4)'),
          ('hunt_n4', 'n = 4 hunt catalogues (every 10th; f ≥ 2 every record)'),
          ('gap_n5', 'n = 5 catalogues (every 20th; f ≥ 2 every 4th)'), ('hunt_n5', 'n = 5 hunt catalogues (every 2nd)'),
          ('certs_3', 'random, n = 3 (2,000 per core)'), ('certs_4', 'random, n = 4 (100 per core)'),
          ('certs_5', 'random, n = 5 (4 per core)')]


def main(files):
    tot = {g: collections.Counter() for g, _ in GROUPS}
    for fn in files:
        b = os.path.basename(fn)[len('stuck_'):]
        g = next(g for g, _ in GROUPS if b.startswith(g))
        for line in open(fn):
            if line.startswith('#'): continue
            m = re.match(r'(.*?)\s{2,}(\d+)\s*$', line.rstrip()) or re.match(r'(DL13 failures): (\d+)', line)
            if m: tot[g][m.group(1).strip()] += int(m.group(2))
    cols = ['profiles f>=1, omega>=1', 'def>0 states', 'T1-stuck', 'T1-stuck f=1', 'T1-stuck f=2', 'T1-stuck f=3',
            'T1-stuck, every T3 repair has a helper', 'DL13 failures']
    print('| input | profiles with f ≥ 1, ω ≥ 1 | def > 0 states | T1-stuck | f = 1 / 2 / 3 | every repair has a helper '
          '| DL₁₃ failures |')
    print('|---|---|---|---|---|---|---|')
    S = collections.Counter()
    for g, name in GROUPS:
        c = tot[g]
        for k in cols: S[k] += c[k]
        print('| %s | %s | %s | %s | %s / %s / %s | %s | %s |' % (name, *('{:,}'.format(c[k]) for k in cols)))
    print('| **total** | %s | %s | **%s** | %s / %s / %s | %s | **%s** |' % tuple('{:,}'.format(S[k]) for k in cols))


if __name__ == '__main__':
    main(sys.argv[1:])
