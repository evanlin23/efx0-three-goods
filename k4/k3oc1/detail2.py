"""Hard starts in detail: the state, each DE trade, whether it repairs (exact test lb2) and the witness.
    python3 k4/k3oc1/detail2.py LOG [MAX] [filter: T=2 | ring2 | maxonly]"""
import sys, os, json, re, ast
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of
from de_moves import de_trades
from lbtest import lb2, upgrade, parts
from rules import score
from show import show
MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3; flt = sys.argv[3] if len(sys.argv) > 3 else ''
cnt = 0
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
    Y = ast.literal_eval(mt.group(4)); b = base_of(Y, m)
    B, J, U, NA, F, T = parts(rk, m, upgrade(rk, m, b))
    mv = de_trades(rk, m, b)
    if flt == 'T=2' and len(T) != 2: continue
    if flt == 'ring2' and not any(d[0] == 'DEring' and sum(h is not None for h in d[2]) >= 2 and lb2(rk, m, nb) for nb, d in mv): continue
    cnt += 1
    if cnt > MAX: break
    print('=== start'); print(show(rk, m, b, order))
    best = max(score(rk, nb) for nb, d in mv)
    for nb, d in mv:
        w = lb2(rk, m, nb)
        print('   %s%s %s %s' % ('REPAIRS' if w else 'fails  ', ' (max score)' if score(rk, nb) == best else '', d, w if w else ''))
