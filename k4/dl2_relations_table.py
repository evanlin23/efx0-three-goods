#!/usr/bin/env python3
"""Table of the DL_R runs (k4/dl2.md §3) from the logs of k4/dl2_relations.py.
usage: python3 k4/dl2_relations_table.py results/k4_dl2_relations/*.log > results/k4_dl2_relations/table.md"""
import os, re, sys


def parse(fn):
    head = None; rel = {}
    for l in open(fn):
        if l.startswith('profiles'):
            m = re.match(r'profiles (\d+), def>0 states (\d+), nearest-distance histogram (.*)', l.strip())
            head = (int(m.group(1)), int(m.group(2)), m.group(3))
        m = re.match(r'(\S+)\s+fails at (\d+) states of (\d+) profiles', l)
        if m: rel[m.group(1)] = (int(m.group(2)), int(m.group(3)))
    return head, rel


def main(files):
    rows = [(os.path.basename(f).replace('.log', ''),) + parse(f) for f in files]
    rows = [r for r in rows if r[1]]
    names = []
    for r in rows:
        for k in r[2]:
            if k not in names: names.append(k)
    print('# DL_R on the data (generated)\n')
    print('command: `python3 k4/dl2_relations_table.py %s`\n' % ' '.join(files))
    print('Entries: states (profiles) at which DL_R fails, i.e. a min-frozen P with def(P) > 0 has no min-frozen R-neighbour')
    print('with a smaller deficit. Relations: `k4/dl2_relations.py` RELATIONS; R_T is `RT`.\n')
    print('| input | profiles | def > 0 states | nearest distance | ' + ' | '.join(names) + ' |')
    print('|---|---|---|---|' + '---|' * len(names))
    tot = [0, 0]; totf = {k: [0, 0] for k in names}
    for name, (np_, ns, hist), rel in rows:
        tot[0] += np_; tot[1] += ns
        cells = []
        for k in names:
            a, b = rel.get(k, (None, None))
            if a is None: cells.append('–'); continue
            totf[k][0] += a; totf[k][1] += b
            cells.append('0' if a == 0 else '%d (%d)' % (a, b))
        print('| %s | %d | %d | %s | %s |' % (name, np_, ns, hist, ' | '.join(cells)))
    print('| **total** | %d | %d | | %s |' % (tot[0], tot[1], ' | '.join(
        '0' if totf[k][0] == 0 else '%d (%d)' % tuple(totf[k]) for k in names)))


if __name__ == '__main__':
    main(sys.argv[1:])
