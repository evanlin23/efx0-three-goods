#!/usr/bin/env python3
"""Table of the DL_R runs (k4/dl2.md §3) from the logs of k4/dl2_relations.py.
usage: python3 k4/dl2_relations_table.py [--compact=R1,R2,...] [--fmin=1] results/k4_dl2_relations/*.log
  (the full table goes to results/k4_dl2_relations/table.md; --compact groups the inputs by n; --fmin=1 counts only the
  states whose profile has at least one frozen agent at the minimum, f >= 1)"""
import ast, os, re, sys


def parse(fn):
    head = None; rel = {}; fh = None; last = None; relf = {}
    for l in open(fn):
        if l.startswith('profiles'):
            m = re.match(r'profiles (\d+), def>0 states (\d+), nearest-distance histogram (.*)', l.strip())
            if m: head = (int(m.group(1)), int(m.group(2)), m.group(3))   # other logs (xcheck.log) are skipped
        if l.startswith('def>0 states by fewest frozen agents f:'):
            fh = ast.literal_eval(l.split(':', 1)[1].strip())
        m = re.match(r'(\S+)\s+fails at (\d+) states of (\d+) profiles', l)
        if m: rel[m.group(1)] = (int(m.group(2)), int(m.group(3))); last = m.group(1)
        if l.strip().startswith('failures by f:') and last:
            relf[last] = ast.literal_eval(l.split(':', 1)[1].strip())
    return head, rel, fh, relf


def group_of(name):
    if name.startswith('suite'): return 'suite (cores, n ≤ 6)'
    for n in '2345':
        if name.startswith(('gap_n' + n, 'certs_' + n, 'hunt_n' + n)): return 'n = ' + n
    if name.startswith('hard_hunt'): return 'n = 4'
    return name


def fsum(d, fmin):
    return sum(v for k, v in (d or {}).items() if k >= fmin)


def compact(rows, cols, fmin):
    """rows grouped by n, selected relations; with fmin, only the states with f >= fmin"""
    G = {}
    for name, (np_, ns, hist), rel, fh, relf in rows:
        g = G.setdefault(group_of(name), [0, 0, {c: 0 for c in cols}, [], set(), {0: 0, 1: 0}])
        g[0] += np_; g[3].append(name)
        g[1] += ns if not fmin else fsum(fh, fmin)
        if fh is not None:
            g[5][0] += fh.get(0, 0); g[5][1] += fsum(fh, 1)
        for c in cols:
            if c not in rel or (fmin and c not in relf): g[4].add(c); continue
            g[2][c] += rel[c][0] if not fmin else fsum(relf[c], fmin)
    print('| inputs | profiles | def > 0 states%s | f = 0 / f ≥ 1 | ' % (' (f ≥ %d)' % fmin if fmin else '')
          + ' | '.join(cols) + ' |')
    print('|---|---|---|---|' + '---|' * len(cols))
    note = False
    for k in sorted(G):
        np_, ns, rel, names, miss, fs = G[k]
        note = note or bool(miss)
        print('| %s (%s) | %d | %d | %d / %d | %s |' % (k, ', '.join(names), np_, ns, fs[0], fs[1], ' | '.join(
            ('%d' % rel[c]) + ('†' if c in miss else '') for c in cols)))
    if note:
        print('\n† Some inputs of the group were run without this relation (or without the split by f) and are not '
              'counted in this column.')


def main(argv):
    cols = None; fmin = 0; files = []
    for a in argv:
        if a.startswith('--compact='): cols = a[10:].split(',')
        elif a.startswith('--fmin='): fmin = int(a[7:])
        else: files.append(a)
    rows = [(os.path.basename(f).replace('.log', ''),) + parse(f) for f in files]
    rows = [r for r in rows if r[1]]
    if cols:
        compact(rows, cols, fmin); return
    names = []
    for r in rows:
        for k in r[2]:
            if k not in names: names.append(k)
    print('# DL_R on the data (generated)\n')
    print('command: `python3 k4/dl2_relations_table.py %s`\n' % ' '.join(argv))
    print('Entries: states (profiles) at which DL_R fails, i.e. a min-frozen P with def(P) > 0 has no min-frozen R-neighbour')
    print('with a smaller deficit; in brackets after "f≥1:", the failing states whose profile has f ≥ 1. Relations:')
    print('`k4/dl2_relations.py` RELATIONS; R_T is `RTr`, R_T2 is `RT`, R_13 is `R13`. The profile counts are summed over')
    print('the runs (the n = 2 catalogue lies inside certs_2_all, and random draws are with replacement).\n')
    print('| input | profiles | def > 0 states (f = 0 / f ≥ 1) | nearest distance | ' + ' | '.join(names) + ' |')
    print('|---|---|---|---|' + '---|' * len(names))
    tot = [0, 0, 0, 0]; totf = {k: [0, 0, 0] for k in names}
    for name, (np_, ns, hist), rel, fh, relf in rows:
        tot[0] += np_; tot[1] += ns; tot[2] += (fh or {}).get(0, 0); tot[3] += fsum(fh, 1)
        cells = []
        for k in names:
            a, b = rel.get(k, (None, None))
            if a is None: cells.append('–'); continue
            totf[k][0] += a; totf[k][1] += b; totf[k][2] += fsum(relf.get(k), 1)
            cells.append('0' if a == 0 else '%d (%d) f≥1: %d' % (a, b, fsum(relf.get(k), 1)))
        print('| %s | %d | %d (%s) | %s | %s |' % (name, np_, ns, '%d / %d' % (fh.get(0, 0), fsum(fh, 1)) if fh else '?',
                                                hist, ' | '.join(cells)))
    print('| **total** | %d | %d (%d / %d) | | %s |' % (tot[0], tot[1], tot[2], tot[3], ' | '.join(
        '0' if totf[k][0] == 0 else '%d (%d) f≥1: %d' % tuple(totf[k]) for k in names)))


if __name__ == '__main__':
    main(sys.argv[1:])
