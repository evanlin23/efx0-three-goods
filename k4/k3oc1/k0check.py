"""DE chains of length zero (a free x with b_x, c_x junk drops a_x for its pair) are not improving chains in k4/sdc.md
§29's sense (there x keeps its base and adds the junk).  On hard starts: is a max-score trade ever such a chain, and
does the state where x instead keeps a_x and adds b_x, c_x have a one-absorber completion (exact test, k3lib)?
    python3 k4/k3oc1/k0check.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, completion
from de_moves import de_trades
from lbtest import lb_simple
from rules import score
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1
        best = max(score(rk, nb) for nb, d in mv)
        sel = [(nb, d) for nb, d in mv if score(rk, nb) == best]
        k0 = [(nb, d) for nb, d in sel if d[0] == 'DEchain' and len(d[1]) == 1]
        if not k0: continue
        C['some max-score trade is a length-zero chain'] += 1
        C['every max-score trade is one %s' % (len(k0) == len(sel))] += 1
        for nb, d in k0:
            x = d[1][0]; nb2 = list(b); nb2[rk[x][1]] = x; nb2[rk[x][2]] = x
            C['x keeps a_x and adds its pair: one-absorber completion %s' % (completion(rk, m, tuple(nb2), 1) is not None)] += 1
for k in sorted(C): print(k, C[k])
