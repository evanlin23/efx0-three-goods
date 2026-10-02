#!/usr/bin/env python3
"""Summary table of the scans of k4/thetab.md §4 (workstream proof/k4-thetab) from results/k4_thetab/scan_*.log.

Columns, per input (def > 0 states with f = 1, counted per state):
  (H) at the T3 stage: states / W, K or G1 (a plain swap) / G1h only (a swap with one helper) / some plain swap lowers
  the deficit (exact);
  (H), T1-stuck but not at the T3 stage: the same; (H), other stages: the same;
  two or more needers, not (H), at the T3 stage: the same;
  one needer: states where G1 or G1h applies / states (conclusion asserted);
  T3-stage states with no improving (T3) move at all (a failure of DL_RT4 at f = 1; expected 0).
usage: python3 k4/thetab_table.py results/k4_thetab/scan_*.log"""
import collections, re, sys


def parse(fn):
    c = collections.Counter(); label = None
    for l in open(fn):
        if l.startswith('# input'): label = l[len('# input '):].strip()
        m = re.match(r'\s+(n=\d+ \|.*?)\s+(\d+)$', l)
        if not m: continue
        parts = [p.strip() for p in m.group(1).split('|')]
        k = int(m.group(2))
        if parts[1] == 'one needer':
            c['one needer'] += k
            if parts[2] == 'G1 or G1h applies': c['one needer G1'] += k
            continue
        typ, st, thm, cert, res = parts[1:6]
        H = typ == '(H)'
        grp = ('H ' if H else 'notH ') + st
        c[grp] += k
        if thm.split()[-1] in ('W', 'K', 'G1'): c[grp + ' covered'] += k
        if thm.split()[-1] == 'G1h': c[grp + ' helper'] += k
        if res.startswith('plain swap'): c[grp + ' plain'] += k
        if 'NO (T3) MOVE' in res: c['T3FAIL'] += k
    return label, c


def main(files):
    tot = collections.Counter()
    print('| input | (H), T3 stage | (H), T1-stuck only | (H), other | not (H), T3 stage | one needer | no (T3) move |')
    print('|---|---|---|---|---|---|---|')
    for fn in files:
        label, c = parse(fn)
        tot.update(c)
        print(row(label, c))
    print(row('**total**', tot))


def row(label, c):
    def h(g): return '%d / %d / %d / %d' % (c[g], c[g + ' covered'], c[g + ' helper'], c[g + ' plain'])
    return '| %s | %s | %s | %s | %s | %d / %d | %d |' % (label, h('H T3stage'), h('H T1stuck'), h('H other'),
                                                          h('notH T3stage'), c['one needer G1'], c['one needer'],
                                                          c['T3FAIL'])


if __name__ == '__main__':
    main(sys.argv[1:])
