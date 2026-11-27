"""Stronger completion targets after one DE trade, on hard starts: (Z) omega <= 0, or some owner (terminal or pair
holder) with no exposed agent at all, or an empty-handed owner with omega <= 1.  Does some trade reach (Z)?  Does the
max-score / least-omega trade?
    python3 k4/k3oc1/zero_exp.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, parts, exposed
from rules import score

def zed(rk, m, b):
    B, J, U, NA, F, T = parts(rk, m, b)
    if len(J) <= len(T): return 'omega <= 0'
    for o in T + [u for u in range(len(rk)) if U[u]]:
        if not B[o] and len(J) <= len(T) + 1: return 'empty owner'
        if not exposed(rk, b, o, B, J, U): return 'owner without exposed agents'
    return None

C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        if not line.startswith('HARD'): continue
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b); C['hard'] += 1
        z = [zed(rk, m, nb) for nb, d in mv]
        C['some trade reaches Z %s' % any(z)] += 1
        best = max(score(rk, nb) for nb, d in mv)
        C['every max-score trade reaches Z %s' % all(zz for zz, (nb, d) in zip(z, mv) if score(rk, nb) == best)] += 1
        om = [(lambda P: len(P[1]) - len(P[5]))(parts(rk, m, nb)) for nb, d in mv]
        C['every least-omega trade reaches Z %s' % all(zz for zz, o in zip(z, om) if o == min(om))] += 1
for k in sorted(C): print(k, C[k])
