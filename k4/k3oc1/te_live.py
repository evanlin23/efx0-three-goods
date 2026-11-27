"""Live-junk version of the release bound (k4/k3_oc1.md §12.1): on OMEGA2 lines of te_sample.py (least omega' >= 2),
recompute the least omega' counting only junk goods some agent values (dead goods excluded), and the least D'
likewise.  Are these <= 1?
    python3 k4/k3oc1/te_live.py FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts
from t2k_e import valid_rotations, topo
from te_wbound import D_of
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('OMEGA2'): continue
        mt = re.search(r'(\[\[.*?\]\]) (\d+) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(3))
        dead = set(g for g in range(m) if not any(g in r for r in rk))
        lo = min(len([g for g in P[1] if g not in dead]) - len(P[5]) for P in
                 (parts(rk, m, upgrade(rk, m, nb)) for k, p, nb in valid_rotations(rk, m, topo(rk, Y), Y)))
        C['dead goods %d: least live omega\' %d' % (len(dead), lo)] += 1
for k in sorted(C): print(C[k], k)
