"""k4/k3_oc1.md §12 helper; see the log of the same name family in results/k4_k3oc1/ for the command line."""
import sys, re, json, ast, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import upgrade, parts, lb2_owners, lb2
from t2k_e import valid_rotations
C = collections.Counter(); seen = set()
for fn in sys.argv[1:]:
    for line in open(fn):
        if not line.startswith('FAIL'): continue
        mt = re.search(r'(\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+).*k (\d+) chain (\[.*?\])', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); n = len(rk)
        k = int(mt.group(6)); p = json.loads(mt.group(7)); e = p[-1]
        for k2, p2, nb in valid_rotations(rk, m, ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4))):
            if k2 != k: continue
            P = parts(rk, m, upgrade(rk, m, nb))
            kinds = [x for x, s in (('k', {k}), ('e', {e}), ('other terminal', set(P[5]) - {e, k}), ('other pair holder', set(i for i in range(n) if P[2][i]) - {k, e})) if lb2_owners(rk, m, nb, s)]
            C['|T| %s: owners that work: %s; e terminal after %s' % (mt.group(5), '+'.join(kinds) or 'NONE', e in P[5])] += 1
for k_, v in sorted(C.items()): print(v, k_)
