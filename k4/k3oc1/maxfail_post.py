"""Post-process the MAXFAIL lines of oc1_fast.py (max-score DE trade fails the simple test): does every max-score
trade pass the exact test lb2?  every least-omega trade the simple / the exact test?  some trade the simple test?
    python3 k4/k3oc1/maxfail_post.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, lb2, parts
from rules import score
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.search(r'MAXFAIL (\[.*?\]\]) (\d+) picks (\(.*?\))', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); b = base_of(ast.literal_eval(mt.group(3)), m)
        mv = de_trades(rk, m, b); C['max-score fails the simple test'] += 1
        sc = {nb: score(rk, nb) for nb, d in mv}; om = {nb: (lambda P: len(P[1]) - len(P[5]))(parts(rk, m, nb)) for nb, d in mv}
        bs, bo = max(sc.values()), min(om.values())
        C['every max-score trade passes the exact test %s' % all(lb2(rk, m, nb) for nb in sc if sc[nb] == bs)] += 1
        C['every least-omega trade passes the simple test %s' % all(lb_simple(rk, m, nb) for nb in om if om[nb] == bo)] += 1
        C['every least-omega trade passes the exact test %s' % all(lb2(rk, m, nb) for nb in om if om[nb] == bo)] += 1
        C['every (least omega, then max score) trade passes the simple test %s' % all(lb_simple(rk, m, nb) for nb in om if om[nb] == bo and sc[nb] == max(sc[x] for x in om if om[x] == bo))] += 1
for k in sorted(C): print(k, C[k])
