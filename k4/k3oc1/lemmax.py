"""Lemma X data: for every DE trade tau from a hard draft whose result fails LS (simple test), the trades tau* with
smaller omega after; how they relate to tau (same start, same end terminal, superset of agents, ...).
    python3 k4/k3oc1/lemmax.py LOG [SHOW]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, parts
from show import show
SHOW = int(sys.argv[2]) if len(sys.argv) > 2 else 0; C = collections.Counter(); shown = 0
def om(rk, m, nb):
    P = parts(rk, m, nb); return len(P[1]) - len(P[5])
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); o = ast.literal_eval(mt.group(3))
    b = base_of(ast.literal_eval(mt.group(4)), m); mv = de_trades(rk, m, b)
    w = {nb: om(rk, m, nb) for nb, d in mv}
    for nb, d in mv:
        if lb_simple(rk, m, nb): continue
        if d[0] == 'DEchain' and len(d[1]) == 1: C['failing k=0 chain'] += 1; continue
        C['failing trade'] += 1
        better = [(nb2, d2) for nb2, d2 in mv if w[nb2] < w[nb]]
        if not better: C['NO BETTER-OMEGA TRADE'] += 1; continue
        rel = set()
        for nb2, d2 in better:
            if d2[1][0] == d[1][0] and d2[0] == d[0]: rel.add('same start')
            if set(d[1]) < set(d2[1]): rel.add('superset of agents')
            if d2[1][-1] == d[1][-1]: rel.add('same last agent')
            if not set(d[1]) & set(d2[1]): rel.add('disjoint')
        C['better trades: ' + ', '.join(sorted(rel))] += 1
        if shown < SHOW:
            shown += 1; print('=== failing', d, 'omega', w[nb]); print(show(rk, m, b, o))
            for nb2, d2 in better: print('    better', d2, 'omega', w[nb2])
for k in sorted(C): print(k, C[k])
