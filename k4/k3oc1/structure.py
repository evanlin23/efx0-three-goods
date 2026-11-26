"""Structure of the hard starts (HARD lines of oc1_lb / oc1_k3 logs), after LB's maximal upgrades:
NC at the draft, |T|, omega, E-agents; the repairing DE trades (kind, number of pair arrows, which terminals it
passes through) and the max-score trades.
    python3 k4/k3oc1/structure.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of
from de_moves import de_trades
from lbtest import lb2 as lb1, upgrade, parts
from rules import score
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
        Y = ast.literal_eval(mt.group(4)); b = base_of(Y, m); n = len(rk)
        ub = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, ub)
        nc = [x for x in range(n) if B[x] == [rk[x][0]] and rk[x][1] in J and rk[x][2] in J]
        C['hard'] += 1
        C['NC violators %d' % len(nc)] += 1
        C['|T| %d, omega %d' % (len(T), len(J) - len(T))] += 1
        C['E-agents %d' % sum(1 for i in range(n) if not B[i])] += 1
        C['upgrades %d' % sum(U)] += 1
        mv = de_trades(rk, m, b)
        rep = [(nb, d) for nb, d in mv if lb1(rk, m, nb)]
        def npair(d):
            if d[0] == 'DEchain': return 'chain'
            return 'ring with %d pair arrows' % sum(1 for h in d[2] if h is not None)
        best = max(score(rk, nb) for nb, d in mv)
        for nb, d in mv:
            if score(rk, nb) == best:
                C['max-score trade: %s' % npair(d)] += 1; break
        kinds = sorted(set(npair(d) for nb, d in rep))
        C['repairing kinds: ' + '; '.join(kinds)] += 1
for k in sorted(C): print(k, C[k])
