"""k4/k3_oc1.md §12 helper; see the log of the same name family in results/k4_k3oc1/ for the command line."""
import sys, re, json, ast, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import upgrade, parts, _owner_test
from t2k_e import valid_rotations
from t2k import simple_ok
C = collections.Counter(); ex = []
for fn in sys.argv[1:]:
    for line in open(fn):
        if not line.startswith('FAIL'): continue
        mt = re.search(r'(\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+).*k (\d+) chain (\[.*?\])', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); n = len(rk)
        k = int(mt.group(6))
        for k2, p2, nb in valid_rotations(rk, m, ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4))):
            if k2 != k: continue
            bu = upgrade(rk, m, nb); B, J, U, NA, F, T = parts(rk, m, bu)
            le_k = _owner_test(rk, m, bu, B, J, U, T, [i == k for i in range(n)], {'none', k, p2[-1]})
            C['simple Lemma 1 owner k: %s; LE with owner in none/k/e: %s; |J\'| %d |T\'| %d' % (simple_ok(rk, m, nb, k), le_k[:2] if le_k else None, len(J), len(T))] += 1
            if len(ex) < 2: ex.append((line.strip()[5:200], p2))
for k_, v in sorted(C.items()): print(v, k_)
for e in ex: print(e)
