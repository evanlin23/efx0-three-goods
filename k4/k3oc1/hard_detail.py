"""Hard starts where DE's first trade does not repair: print the state and every repairing DE trade.
    python3 k4/k3oc1/hard_detail.py LOG [MAX]"""
import sys, os, json, re, ast
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of, completion, vals
from de_moves import de_first, de_chains, de_rings
from show import show
cnt = 0; MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) chain', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); o = ast.literal_eval(mt.group(3))
    Y = ast.literal_eval(mt.group(4)); V = vals(rk); b = base_of(Y, m)
    f = de_first(rk, m, b)
    if f is not None and completion(rk, m, f[0], 1, V) is not None: continue
    cnt += 1
    if cnt > MAX: break
    print('=== start'); print(show(rk, m, b, o))
    print(' DE first:', f[1] if f else None)
    for nb, d in de_chains(rk, m, b) + de_rings(rk, m, b):
        X = completion(rk, m, nb, 1, V)
        print(' ', 'REPAIRS' if X else 'fails  ', d, ('-> ' + str(X)) if X else '')
