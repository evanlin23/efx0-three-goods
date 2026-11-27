"""One-terminal hard drafts (after LB's upgrades T = {l}): rules over the rotations (DE trades through l, starting at
an exposed agent of l).  Does every rotation chosen by the rule repair (exact test lb2)?
    python3 k4/k3oc1/t1rules.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from de_moves import de_trades
from lbtest import upgrade, parts, exposed, lb2
from rules import score
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        b0 = base_of(Y, m)
        if lb2(rk, m, b0): continue
        b = upgrade(rk, m, b0); B, J, U, NA, F, T = parts(rk, m, b)
        if len(T) != 1: continue
        ell = T[0]; E = set(exposed(rk, b, ell, B, J, U)); n = len(rk)
        rot = [(nb, d) for nb, d in de_trades(rk, m, b) if ell in d[1] and (d[0] == 'DEring' or d[1][0] in E)]
        C['one-terminal exact-hard'] += 1
        if not rot: C['NO ROTATION'] += 1; continue
        ok = {nb: bool(lb2(rk, m, nb)) for nb, d in rot}
        C['some rotation repairs %s' % any(ok.values())] += 1
        def recv(nb):
            B2 = bundles(nb, n); h = B2[ell]
            return 4 if len(h) == 2 else (3 - rk[ell].index(h[0]) if h else 0)
        for name, key in [('best good for l, then score', lambda nb: (recv(nb), score(rk, nb))), ('max score', lambda nb: score(rk, nb)),
                          ('best good for l', lambda nb: recv(nb))]:
            best = max(key(nb) for nb, d in rot)
            C[name + ': all chosen repair %s' % all(ok[nb] for nb, d in rot if key(nb) == best)] += 1
for k in sorted(C): print(k, C[k])
