"""One-terminal perfect drafts (after LB's upgrades T = {l}): rotations (DE trades through l starting at an exposed
agent of l) after which l holds its top.  How often does one exist, and does every such rotation repair (lb2)?
    python3 k4/k3oc1/top_to_l.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from de_moves import de_trades
from lbtest import upgrade, parts, exposed, lb2
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        if any(g is None for g in Y): continue
        b0 = base_of(Y, m)
        if lb2(rk, m, b0): continue
        b = upgrade(rk, m, b0); B, J, U, NA, F, T = parts(rk, m, b)
        if len(T) != 1: continue
        ell = T[0]; E = set(exposed(rk, b, ell, B, J, U)); n = len(rk)
        C['one-terminal perfect hard'] += 1
        rot = [(nb, d) for nb, d in de_trades(rk, m, b) if ell in d[1] and (d[0] == 'DEring' or d[1][0] in E)]
        top = [(nb, d) for nb, d in rot if bundles(nb, n)[ell] == [rk[ell][0]]]
        if not top: C['no rotation gives l its top'] += 1; continue
        ok = [bool(lb2(rk, m, nb)) for nb, d in top]
        C['rotations giving l its top: all repair %s, some repair %s' % (all(ok), any(ok))] += 1
for k in sorted(C): print(k, C[k])
