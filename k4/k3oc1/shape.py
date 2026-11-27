"""Shape of the max-score DE trade on hard starts: is the last agent on it; does every receiver on it get its top;
does the last agent end with its top; which agents end frozen.
    python3 k4/k3oc1/shape.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from de_moves import de_trades
from lbtest import lb_simple, parts
from rules import score
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1; n = len(rk)
        ell = order[-1]
        best = max(score(rk, nb) for nb, d in mv)
        sel = [(nb, d) for nb, d in mv if score(rk, nb) == best]
        nb, d = sel[0]
        B2 = bundles(nb, n)
        on = set(d[1])
        C['last agent on the max-score trade %s' % (ell in on)] += 1
        C['last agent ends with its top %s' % (B2[ell] == [rk[ell][0]])] += 1
        recv = [i for i in on if len(B2[i]) == 1]
        C['every single-good receiver gets its top %s' % all(B2[i] == [rk[i][0]] for i in recv)] += 1
        B, J, U, NA, F, T = parts(rk, m, b)
        C['every terminal of the draft on the trade %s' % all(t in on for t in T)] += 1
        C['some max-score trade passes through every terminal %s' % any(all(t in set(dd[1]) for t in T) for _, dd in sel)] += 1
for k in sorted(C): print(k, C[k])
