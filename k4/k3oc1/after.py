"""After the max-score DE trade on hard starts (simple test): omega = |J| - |T| before and after, the witness type,
and where the owner sits relative to the trade.
    python3 k4/k3oc1/after.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of
from de_moves import de_trades
from lbtest import lb_simple, parts
from rules import score
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1
        B, J, U, NA, F, T = parts(rk, m, b); w0 = len(J) - len(T)
        best = max(score(rk, nb) for nb, d in mv)
        for nb, d in mv:
            if score(rk, nb) != best: continue
            B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb); w1 = len(J2) - len(T2)
            wit = lb_simple(rk, m, nb)
            kind = wit[0]
            if kind == 'owner':
                o = wit[1]; kind += ' on the trade' if o in d[1] else ' off the trade'
                if o in d[1] and d[0] == 'DEchain' and o == d[1][0]: kind += ' (chain start)'
                if o == order[-1]: kind += ' = last agent'
            C['omega %d -> %d: %s' % (w0, w1, kind)] += 1
for k in sorted(C): print(k, C[k])
