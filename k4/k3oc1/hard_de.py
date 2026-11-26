"""On the hard starts of oc1_k3 logs (picks without a one-absorber completion): does DE's own first trade repair?
does some DE trade (chain or ring) repair?  Repair = a one-absorber completion exists afterwards.

    python3 k4/k3oc1/hard_de.py LOG..."""
import sys, os, json, collections, ast, re
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of, completion, chains, vals
from de_moves import de_first, de_chains, de_rings
C = collections.Counter(); shown = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) chain', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        Y = ast.literal_eval(mt.group(4)); V = vals(rk); b = base_of(Y, m)
        C['hard'] += 1
        f = de_first(rk, m, b)
        okf = f is not None and completion(rk, m, f[0], 1, V) is not None
        C['DE first trade repairs %s' % okf] += 1
        mv = de_chains(rk, m, b) + de_rings(rk, m, b)
        good = [d for nb, d in mv if completion(rk, m, nb, 1, V) is not None]
        C['some DE trade repairs %s' % bool(good)] += 1
        if good: C['kinds: ' + ','.join(sorted(set(d[0] for d in good)))] += 1
        if not good and shown['nodemove'] < 5:
            shown['nodemove'] += 1; print('NO DE TRADE REPAIRS', line.strip())
for k in sorted(C): print(k, C[k])
