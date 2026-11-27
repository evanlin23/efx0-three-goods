"""Properties of the states reached by max-score DE trades from hard drafts: acyclic want graph? any further DE trade
(Pareto-optimal among valid states otherwise)? DE's own finishing test passes?
    python3 k4/k3oc1/maxprops.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades, de_can_finish, info
from lbtest import lb_simple
from rules import score
C = collections.Counter()
def acyclic(rk, m, base):
    n = len(rk); B, J, rank, U, wants, wanters, free = info(rk, m, base)
    adj = {j: (wanters.get(B[j][0], []) if len(B[j]) == 1 else []) for j in range(n)}
    state = [0] * n
    def dfs(v):
        state[v] = 1
        for w in adj[v]:
            if state[w] == 1 or (state[w] == 0 and not dfs(w)): return False
        state[v] = 2; return True
    return all(state[v] or dfs(v) for v in range(n))
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1
        best = max(score(rk, nb) for nb, d in mv)
        for nb, d in mv:
            if score(rk, nb) != best: continue
            C['max-score result: acyclic %s, further trade %s, DE finishes %s' % (acyclic(rk, m, nb), bool(de_trades(rk, m, nb)), bool(de_can_finish(rk, m, nb)))] += 1
for k in sorted(C): print(k, C[k])
