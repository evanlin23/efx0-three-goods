"""print the reverse-SD levels of one start: python3 show.py '<json sets,vals>' 'picks' [order]"""
import sys, json, itertools
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, bundles_of, picks_base, threatened
from e2_paths import sub_completions
sets, vals = json.loads(sys.argv[1]); Y = json.loads(sys.argv[2])
m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m)
J = sorted(set(range(m)) - set(g for g in Y if g is not None))
print('junk', J, 'wanted by', wanted_by(I, Y))
for i in range(I.n): print(' agent', i, sorted(zip(I.sets[i], I.vals[i]), key=lambda t: -t[1]), 'pick', Y[i])
orders = [o for o in itertools.permutations(range(I.n)) if list(sd(I, o)[0]) == Y]
if len(sys.argv) > 3: orders = [tuple(json.loads(sys.argv[3]))]
cache = {}
for pi in orders:
    seq = list(pi)[::-1]; print('order', pi, 'insertion', seq)
    for k in range(1, I.n + 1):
        A = sub_completions(I, Y, seq[:k], cache)
        print('  level', seq[:k], len(A), 'completions:', [dict(zip(J, a.tolist())) for a in A[:12]])
