"""On hard starts: do all DE trades whose resulting score vector is Pareto-maximal among DE trades repair?  And all
DE trades whose agent set is inclusion-maximal?  Prints failures.
    python3 k4/k3oc1/pareto_rule.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from k3lib import base_of, completion, vals, bundles
from lbtest import lb2 as lb1
from de_moves import de_trades
from show import show

def svec(rk, base):
    n = len(rk); B = bundles(base, n); s = []
    for i in range(n):
        if len(B[i]) == 2: s.append(4)
        elif len(B[i]) == 1: s.append(3 - rk[i].index(B[i][0]))
        else: s.append(0)
    return tuple(s)

C = collections.Counter(); shown = 0
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) chain', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        Y = ast.literal_eval(mt.group(4)); V = vals(rk); b = base_of(Y, m)
        mv = de_trades(rk, m, b); C['hard'] += 1
        rep = {nb: lb1(rk, m, nb) is not None for nb, d in mv}
        vs = {nb: svec(rk, nb) for nb, d in mv}
        dom = lambda u, w: all(x >= y for x, y in zip(u, w)) and u != w
        pm = [(nb, d) for nb, d in mv if not any(dom(vs[o], vs[nb]) for o, _ in mv)]
        okp = all(rep[nb] for nb, d in pm); C['Pareto-maximal trades all repair %s' % okp] += 1
        sets = {nb: set(d[1]) for nb, d in mv}
        im = [(nb, d) for nb, d in mv if not any(sets[nb] < sets[o] for o, _ in mv)]
        oki = all(rep[nb] for nb, d in im); C['inclusion-maximal trades all repair %s' % oki] += 1
        C['every trade repairs %s' % all(rep.values())] += 1
        if (not okp) and shown < 3:
            shown += 1; print('=== Pareto-maximal trade fails'); print(show(rk, m, b))
            for nb, d in pm: print('  ', 'REPAIRS' if rep[nb] else 'fails', d, vs[nb])
for k in sorted(C): print(k, C[k])
