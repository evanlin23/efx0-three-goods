"""Toward an induction on the last agent: for each hard draft Y of an instance I (order pi, last agent l), compare with
I - l (agent l removed, goods kept; its draft is Y without l's pick).  (a) Is Y- hard in I - l?  (b) If not, does
some trade through l repair Y?  (c) If so, does some repairing trade of Y- (as a trade of I) repair Y?
    python3 k4/k3oc1/induct_last.py LOG"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple
C = collections.Counter()
for line in read_lines(sys.argv[1]):
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    if not mt: continue
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
    Y = ast.literal_eval(mt.group(4)); n = len(rk); ell = order[-1]
    b = base_of(Y, m); mv = de_trades(rk, m, b); rep = [(nb, d) for nb, d in mv if lb_simple(rk, m, nb)]
    keep = [i for i in range(n) if i != ell]; rk2 = [rk[i] for i in keep]; Y2 = [Y[i] for i in keep]
    b2 = base_of(Y2, m)
    if lb_simple(rk2, m, b2):
        C['(a) Y- passes in I - l'] += 1
        C['(b) some repairing trade of Y passes through l: %s' % any(ell in d[1] for nb, d in rep)] += 1
    else:
        C['(a) Y- hard in I - l'] += 1
        rep2 = [d for nb, d in de_trades(rk2, m, b2) if lb_simple(rk2, m, nb)]
        # map trades of I - l to trades of I: relabel agents and compare by agent tuple and kind
        lab = {d[:2]: True for d in [(dd[0], tuple(keep[i] for i in dd[1])) for dd in rep2]}
        hit = any((d[0], d[1]) in lab for nb, d in rep)
        C['(c) a repairing trade of Y- also repairs Y: %s' % hit] += 1
for k in sorted(C): print(k, C[k])
