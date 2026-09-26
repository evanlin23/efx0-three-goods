#!/usr/bin/env python3
"""Summarize a run.py log: per predicate and implementation, the number of instances where it holds / fails / is n/a,
the failing instances, and the disagreements. usage: python3 k4/suite/summarize.py LOG"""
import re, sys, collections
cur = None; tab = collections.OrderedDict(); fails = collections.defaultdict(set); dis = []
for line in open(sys.argv[1]):
    if line.startswith('## '): cur = line[3:].split(':')[0]; tab[cur] = collections.defaultdict(collections.Counter); continue
    if cur is None or not line.startswith('  '): continue
    iid = line.split()[0]
    for impl, verdict in re.findall(r'(\S+): (holds|FAILS|n/a) \(', line):
        tab[cur][impl][verdict] += 1
        if verdict == 'FAILS': fails[cur].add(iid)
    if 'DISAGREE' in line: dis.append((cur, iid))
for p, d in tab.items():
    print('%-12s ' % p + '  '.join('%s: %d holds, %d fails, %d n/a' % (k, c['holds'], c['FAILS'], c['n/a']) for k, c in d.items())
          + ('   failing: %s' % ', '.join(sorted(fails[p])) if fails[p] else ''))
print('disagreements:', dis or 'none')
