"""k4/k3_oc1.md §12 helper; see the log of the same name family in results/k4_k3oc1/ for the command line."""
import sys, re, json, ast, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import upgrade, parts, lb2
from de_moves import de_trades
C = collections.Counter(); ex = None
for line in open(sys.argv[1]):
    if not line.startswith('MISS'): continue
    mt = re.search(r'(\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
    bu = upgrade(rk, m, base_of(Y, m))
    kinds = collections.Counter()
    for nb, d in de_trades(rk, m, bu):
        npa = sum(1 for h in d[2] if h is not None) if d[0] == 'DEring' else 0
        kinds[(d[0], npa, bool(lb2(rk, m, nb)))] += 1
    C[tuple(sorted(kinds.items()))] += 1
    if ex is None: ex = (rk, Y, kinds)
for k, v in C.items(): print(v, k)
print(ex)
