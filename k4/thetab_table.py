#!/usr/bin/env python3
"""Summary table of the scans of k4/thetab.md §4 (workstream proof/k4-thetab) from results/k4_thetab/scan_*.log.

Columns, per input (def > 0 states with f = 1, counted per state):
  (H) at the T3 stage: states | covered by W, K or G1 | some plain swap lowers the deficit;
  (H), T1-stuck but not at the T3 stage: states | covered | plain swap;
  (H), other stages: states | covered | plain swap;
  two or more needers, not (H), at the T3 stage: states | covered by G1 | Lemma G certifies a plain swap | plain swap;
  one needer: states where G1 applies (its conclusion asserted).
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
            if parts[2] == 'Corollary G1 applies': c['one needer G1'] += k
            continue
        typ, st, thm, cert, res = parts[1:6]
        H = typ == '(H)'
        grp = ('H ' if H else 'notH ') + st
        c[grp] += k
        if thm.split()[-1] in ('W', 'K', 'G1'): c[grp + ' covered'] += k
        if cert == 'Lemma G certifies': c[grp + ' cert'] += k
        if res.startswith('plain swap'): c[grp + ' plain'] += k
        if 'NO (T3) MOVE' in res: c[grp + ' T3FAIL'] += k
    return label, c


def main(files):
    tot = collections.Counter()
    print('| input | (H), T3 stage: states / W, K or G1 / plain swap | (H), T1-stuck only | (H), other | not (H), T3 stage: '
          'states / G1 / Lemma G / plain swap | one needer: G1 applies / states |')
    print('|---|---|---|---|---|---|')
    for fn in files:
        label, c = parse(fn)
        tot.update(c)
        print(row(label, c))
    print(row('**total**', tot))


def row(label, c):
    def h(st): return '%d / %d / %d' % (c['H ' + st], c['H %s covered' % st], c['H %s plain' % st])
    nh = '%d / %d / %d / %d' % (c['notH T3stage'], c['notH T3stage covered'], c['notH T3stage cert'],
                                c['notH T3stage plain'])
    return '| %s | %s | %s | %s | %s | %d / %d |' % (label, h('T3stage'), h('T1stuck'), h('other'), nh,
                                                     c['one needer G1'], c['one needer'])


if __name__ == '__main__':
    main(sys.argv[1:])
