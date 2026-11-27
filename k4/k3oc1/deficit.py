"""Deficits at hard drafts: for each owner o (terminal), d(o) = minhit(E_o) - (|T| - 1); the least deficit over
owners, the deficit of the last agent, and whether a Theorem-B-type trade (a DE chain or a ring with ONE pair arrow,
starting at an exposed agent of some owner) repairs.
    python3 k4/k3oc1/deficit.py LOG..."""
import sys, os, json, re, ast, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, parts, exposed, min_hit
C = collections.Counter()
def mh(sets):
    goods = sorted(set(g for s in sets for g in s))
    for r in range(len(goods) + 1):
        for H in itertools.combinations(goods, r):
            if all(set(s) & set(H) for s in sets): return r
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = ast.literal_eval(mt.group(3))
        b = base_of(ast.literal_eval(mt.group(4)), m); C['hard'] += 1
        B, J, U, NA, F, T = parts(rk, m, b)
        d = {}
        for o in T:
            E = exposed(rk, b, o, B, J, U)
            d[o] = mh([[g for g in (rk[x][1], rk[x][2]) if g in J] for x in E]) - (len(T) - 1)
        C['least deficit %d' % min(d.values())] += 1
        C['deficit of the last agent %d' % d[order[-1]]] += 1
        mv = de_trades(rk, m, b)
        short = [(nb, dd) for nb, dd in mv if dd[0] == 'DEchain' or sum(h is not None for h in dd[2]) <= 1]
        C['some short trade repairs %s' % any(lb_simple(rk, m, nb) for nb, dd in short)] += 1
for k in sorted(C): print(k, C[k])
