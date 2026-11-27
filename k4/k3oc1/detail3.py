"""Hard starts with a filter, showing the max-score trade's result and its witness.
    python3 k4/k3oc1/detail3.py LOG MAX FILTER   (FILTER: T1E2 = one terminal, last agent's deficit >= 2; T2 = two terminals; ring2)"""
import sys, os, json, re, ast, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, parts, exposed
from rules import score
from show import show
MAX = int(sys.argv[2]); flt = sys.argv[3]; cnt = 0
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
    b = base_of(ast.literal_eval(mt.group(4)), m)
    B, J, U, NA, F, T = parts(rk, m, b); ell = order[-1]
    E = exposed(rk, b, ell, B, J, U)
    mv = de_trades(rk, m, b)
    if flt == 'T1E2' and not (len(T) == 1 and len(E) >= 2): continue
    if flt == 'T2' and len(T) != 2: continue
    if flt == 'ring2' and not any(d[0] == 'DEring' and sum(h is not None for h in d[2]) >= 2 for nb, d in mv): continue
    cnt += 1
    if cnt > MAX: break
    print('=== start (exposed for the last agent %d: %s)' % (ell, E)); print(show(rk, m, b, order))
    best = max(score(rk, nb) for nb, d in mv)
    for nb, d in mv:
        w = lb_simple(rk, m, nb)
        print('   %s%s %s %s' % ('REPAIRS' if w else 'fails  ', ' (max score %d)' % best if score(rk, nb) == best else '', d, w if w else ''))
        if score(rk, nb) == best: print('\n'.join('      ' + l for l in show(rk, m, nb).split('\n')))
