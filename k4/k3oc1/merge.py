"""Merge test for the max-score argument.  On hard starts Y (HARD lines), for every DE trade tau from Y whose result
Y2 fails the simple test, is there a DE trade rho from Y2 such that rho(Y2) is the result of a single DE trade from Y
(so tau and rho merge into one trade of larger score)?  Also: is there such rho touching tau's agents?
    python3 k4/k3oc1/merge.py LOG [MAX_HARD]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple
from show import show
C = collections.Counter(); shown = 0
MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    if C['hard'] >= MAX: break
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
    b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1
    one = set(nb for nb, d in mv)
    for nb, d in mv:
        if lb_simple(rk, m, nb): continue
        kind = 'k=0 chain (x drops its top)' if d[0] == 'DEchain' and len(d[1]) == 1 else d[0]
        C['failing trades: ' + kind] += 1
        rhos = de_trades(rk, m, nb)
        if not rhos: C['failing trade with no further trade'] += 1; continue
        merged = [(nb2, d2) for nb2, d2 in rhos if nb2 in one]
        C['failing trade (%s): some rho merges %s' % (kind, bool(merged))] += 1
        if not merged and shown < 3 and not kind.startswith('k=0'):
            shown += 1; print('=== no merge'); print(show(rk, m, b)); print(' tau', d); print(show(rk, m, nb))
            for nb2, d2 in rhos: print('   rho', d2)
for k in sorted(C): print(k, C[k])
