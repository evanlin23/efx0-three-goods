"""Hard starts where the least omega after one DE trade is still >= 1: show the draft, the min-omega trades and their
LS witnesses.   python3 k4/k3oc1/minomega.py LOG MAX"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, parts
from show import show
MAX = int(sys.argv[2]); cnt = 0; C = collections.Counter()
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); o = ast.literal_eval(mt.group(3))
    b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b)
    om = lambda nb: (lambda P: len(P[1]) - len(P[5]))(parts(rk, m, nb))
    w = min(om(nb) for nb, d in mv); C['least omega after %d' % w] += 1
    if w >= 1 and cnt < MAX:
        cnt += 1; print('=== omega before %d, least after %d' % (om(b), w)); print(show(rk, m, b, o))
        for nb, d in mv:
            if om(nb) == w:
                print('   ', d, lb_simple(rk, m, nb)); print('\n'.join('      ' + l for l in show(rk, m, nb).split('\n')))
for k in sorted(C): print(k, C[k])
