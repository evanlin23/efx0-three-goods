"""Structure behind the want-count bound (k4/k3_oc1.md §12.1): on GAP lines, the draft's numbers of top-, b- and
c-holders, the total rank deficit W = #b + 2 #c, the need 'W - (2n - m) - 1' that a rotation's climb plus upgrades
must meet for D' <= 1, and the best climb + upgrades over valid Rule E rotations.
    python3 k4/k3oc1/te_wstruct.py gapfile:FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from lbtest import upgrade, parts
from t2k_e import valid_rotations
def W_of(rk, base):
    n = len(rk); B = bundles(base, n)
    return sum(rk[i].index(B[i][0]) for i in range(n) if len(B[i]) == 1)
C = collections.Counter()
for arg in sys.argv[1:]:
    for line in read_lines(arg[8:] if arg.startswith('gapfile:') else arg):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4)); n = len(rk)
        bu = upgrade(rk, m, base_of(Y, m)); B = bundles(bu, n)
        a = sum(1 for i in range(n) if len(B[i]) == 1 and B[i][0] == rk[i][0]); W = W_of(rk, bu)
        need = W - (2 * n - m) - 1
        best = max([W - W_of(rk, upgrade(rk, m, nb)) for k, p, nb in valid_rotations(rk, m, ast.literal_eval(mt.group(3)), Y)], default=None)
        C['m=%d |T|=%s a=%d W=%d need=%d best=%s' % (m, mt.group(5), a, W, need, best)] += 1
for k in sorted(C): print(C[k], k)
