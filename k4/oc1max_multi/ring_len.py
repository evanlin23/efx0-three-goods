"""RING residue (k4/oc1max_multi.md §10): at every start whose first mechanism is ED (the 45 RING starts), the shortest
repairing move with an S* completion (path length; whether its ends are dangerous), by |D_T|, with the smallest start
of each kind.

    python3 k4/oc1max_multi/ring_len.py FILE.jsonl[.gz] [...]
"""
import sys, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collect import records
from mmlib import Inst, base_from_picks, frozen
from regimes import mechanism
T = collections.Counter(); ex = {}
for fn in sys.argv[1:]:
    for rec in records(fn):
        I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
        mech, DT = mechanism(I, rec)
        if mech != 'ED': continue
        D = rec['D']; best = None
        for r in rec['repairs']:
            if not r['ss']: continue
            P = r['path']; two = len(P) == 2 and P[0] in D and P[1] in D
            key = (len(P), 'both ends in D' if P[0] in D and P[-1] in D else 'x0 in D' if P[0] in D else 'x0 not in D')
            if best is None or key < best: best = key
        T[('|D_T|=%d' % len(DT), 'shortest S* repair', best)] += 1
        sz = (I.n, I.m)
        if best not in ex or sz < ex[best][0]: ex[best] = (sz, rec['name'], rec['picks'])
print("$ python3 k4/oc1max_multi/ring_len.py", *sys.argv[1:])
for k in sorted(T, key=str): print(T[k], k)
for k, v in sorted(ex.items(), key=str): print('smallest', k, v)
