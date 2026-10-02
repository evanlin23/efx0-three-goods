#!/usr/bin/env python3
"""Summary tables of the scans of k4/thetab.md §4 (workstream proof/k4-thetab) from results/k4_thetab/scan_*.log.

Table 1, the T3-stage states (def > 0, f = 1, two or more needers; at f = 1 these are the deficit-minimal states of
their key), per input:
  (H) / not (H): states / W, K or G1 applies at P (a plain swap) / only G1h (one helper) / none of them;
  single step: states where no (T3) move from P lowers the deficit;
  key form: states whose key has a (T3) move to a key of smaller least deficit (from P / only from the key) / none;
  Corollary G1 certifies a (T3) move below the key's least deficit: from P / only from another state of the key / none.
Table 2, the other states: (H), T1-stuck but not at the T3 stage, and (H), other stages: states / W, K or G1 / G1h
only / some plain swap lowers the deficit; one needer: G1 or G1h applies / states.
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
        thm = thm.split()[-1]
        H = 'H' if typ == '(H)' else 'notH'
        if st == 'T3stage':
            g = 'T3 ' + H
            c[g] += k
            c[g + (' thm' if thm in ('W', 'K', 'G1') else (' G1h' if thm == 'G1h' else ' none'))] += k
            if 'NO (T3) MOVE' in res: c['T3 single fail'] += k
            dl, kc = parts[6], parts[7]
            c['T3 dl ' + ('P' if dl.endswith('from P') else ('key' if dl.endswith('from the key') else 'NONE'))] += k
            c['T3 kc ' + ('P' if 'from P,' in kc else ('other' if 'another state' in kc else 'none'))] += k
        else:
            g = H + ' ' + st
            c[g] += k
            c[g + (' thm' if thm in ('W', 'K', 'G1') else (' G1h' if thm == 'G1h' else ' none'))] += k
            if res.startswith('plain swap'): c[g + ' plain'] += k
    return label, c


def main(files):
    rows = [parse(fn) for fn in files]
    tot = collections.Counter()
    for _, c in rows: tot.update(c)
    rows.append(('**total**', tot))
    print('| input | T3 stage, (H) | T3 stage, not (H) | no (T3) move from P | (T3) to a better key: from P / from the key / none '
          '| G1 certifies: from P / from the key / none |')
    print('|---|---|---|---|---|---|')
    for label, c in rows:
        def h(g): return '%d / %d / %d / %d' % (c[g], c[g + ' thm'], c[g + ' G1h'], c[g + ' none'])
        print('| %s | %s | %s | %d | %d / %d / %d | %d / %d / %d |' % (
            label, h('T3 H'), h('T3 notH'), c['T3 single fail'], c['T3 dl P'], c['T3 dl key'], c['T3 dl NONE'],
            c['T3 kc P'], c['T3 kc other'], c['T3 kc none']))
    print()
    print('| input | (H), T1-stuck only | (H), other | one needer: G1 or G1h / states |')
    print('|---|---|---|---|')
    for label, c in rows:
        def h(g): return '%d / %d / %d / %d' % (c[g], c[g + ' thm'], c[g + ' G1h'], c[g + ' plain'])
        print('| %s | %s | %s | %d / %d |' % (label, h('H T1stuck'), h('H other'), c['one needer G1'], c['one needer']))


if __name__ == '__main__':
    main(sys.argv[1:])
