"""Which completion test is enough for "one DE trade" on the hard starts (HARD lines of a log)?
DE: paper/k3-simple Definition finish; simple / simple+up: lbtest.lb_simple without / with LB's maximal upgrades;
exact: lbtest.lb2.  For each test: starts where the draft passes, where some DE trade's result passes, where none.
    python3 k4/k3oc1/variants.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of
from de_moves import de_trades, de_can_finish
from lbtest import lb2, lb_simple
from rules import score
TESTS = {'DE': de_can_finish, 'simple': lambda rk, m, b: lb_simple(rk, m, b), 'simple+up': lambda rk, m, b: lb_simple(rk, m, b, True), 'exact': lb2}
C = collections.Counter(); ex = {}
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard (exact)'] += 1
        best = max(score(rk, nb) for nb, d in mv)
        for name, t in TESTS.items():
            if t(rk, m, b): r = 'draft passes'
            else:
                ok = [bool(t(rk, m, nb)) for nb, d in mv]
                r = 'some trade' if any(ok) else 'NO TRADE'
                if any(ok): C[name + ': every max-score trade passes %s' % all(o for o, (nb, d) in zip(ok, mv) if score(rk, nb) == best)] += 1
                if not any(ok) and name not in ex: ex[name] = line.strip()
            C[name + ': ' + r] += 1
for k in sorted(C): print(k, C[k])
for k, v in ex.items(): print('example', k, v)
