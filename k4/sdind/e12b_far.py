"""print free-BOTH cases at distance >= 3 with the completion X' and a nearest completion of I"""
import sys, itertools, collections, json
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base, bundles_of
from e1_delete import load
shown = 0
for name, sets, vals, m in load(sys.argv[1]):
    if len(sets) > 5 or len(sets) < 2: continue
    I = Inst(sets, vals, m); seen = set()
    for o_ in itertools.permutations(range(I.n)):
        Y = list(sd(I, o_)[0])
        if tuple(Y) in seen: continue
        seen.add(tuple(Y)); W = wanted_by(I, Y)
        both = [u for u in range(I.n) if Y[u] is not None and not W[u] and Y[u] == max(I.R[u], key=lambda h: (I.V[u, h], -h))]
        if not both: continue
        J, A = completions(I, picks_base(I, Y), None)
        for u in both:
            I2, amap, gmap = delete(I, [u], [Y[u]]); inv = {b: a for a, b in amap.items()}
            Y2 = [None] * I2.n
            for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
            J2, A2 = completions(I2, picks_base(I2, Y2), None)
            for x2 in A2:
                X = np.array([inv[b] for b in x2]); D = (A != X[None, :]).sum(axis=1)
                if D.min() >= 3 and shown < int(sys.argv[2]):
                    shown += 1
                    near = A[D.argmin()]
                    print(name, json.dumps((sets, vals)), 'picks', Y, 'u', u, 'wanted-by', W)
                    print("   X' bundles", bundles_of(picks_base(I, Y), J, X), ' -> nearest', bundles_of(picks_base(I, Y), J, near), 'd', D.min())
