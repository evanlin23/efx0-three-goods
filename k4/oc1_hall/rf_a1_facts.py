"""The facts (A1-i)-(A1-iv) behind Lemma RF-A1 (k4/oc1_hall.md §24.6), checked at every A1 start of the certifier's
complete n = 4 export: (i) d truly dangerous at Y with junk pair {g, h} and J' & R_d = {h}; (ii) u values exactly Y_d
and Y_u in w's bundle, with v_u(Y_d) + v_u(Y_u) < v_u(Y_w); (iii) the other truly dangerous agent k2 of Y does not want
Y_d; (iv) no frozen agent other than w, u, k2 values Y_d.

    python3 k4/oc1_hall/rf_a1_facts.py
"""
import os
os.chdir(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
import sys, os, json, gzip, collections
sys.path.insert(0, 'k4/oc1_hall'); sys.path.insert(0, 'k4/sdc')
from ohlib import Inst, picks, Picks, threatened
d = json.load(gzip.open('results/k4_oc1max/two_move_starts_n4.json.gz'))
C = collections.Counter()
for hg in d['hypergraphs']:
    sets = hg['sets']; m = 1 + max(max(s) for s in sets); seen = set()
    for st in hg['starts']:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]; P0 = Picks(I, Y)
        DT0 = [k for k in P0.D if threatened(I, k, P0.pv[k], P0.J)]
        for o in st['orders']:
            rf = [u] + [x for x in o if x != u]; Y2 = picks(I, rf)
            if (json.dumps(vals), Y2) in seen: continue
            seen.add((json.dumps(vals), Y2)); P = Picks(I, Y2)
            U2 = [i for i in range(I.n) if i not in P.F and Y2[i] is not None]
            DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
            if len(U2) != 1 or DT: continue
            dd = U2[0]; w = next(j for j in range(I.n) if Y[j] == Y2[u])
            if w == dd or Y2[w] != Y[dd] or Y2[dd] not in P0.J: continue
            h = max([x for x in P.J if x in I.R[dd]], key=lambda x: I.key[dd][x])
            X = [Y2[w]] + [x for x in P.J if x != h]
            vu = [x for x in X if x in I.R[u]]
            C['(ii) u values exactly {Y_d, Y_u} in X_w'] += set(vu) == {Y[dd], Y[u]}
            C['(ii) v_u(Y_d) + v_u(Y_u) < v_u(Y_w)'] += I.val(u, [Y[dd], Y[u]]) < I.v[u][Y[w]]
            k2 = [k for k in DT0 if k != dd][0]
            C['(iii) k2 does not want Y_d'] += not (I.v[k2].get(Y[dd], 0) > P.pv[k2])
            others = [q for q in P.F if q not in (w, u, k2) and Y2[w] in I.R[q]]
            C['(iv) no frozen agent other than w, u, k2 values Y_d'] += not others
            C['    u is frozen at Y\''] += u in P.F
            C['    k2 is frozen at Y\''] += k2 in P.F
            C['    J\' = J - g + Y_u'] += set(P.J) == (set(P0.J) - {Y2[dd]}) | {Y[u]}
            C['    d\'s junk at Y\' is exactly {h}'] += [x for x in P.J if x in I.R[dd]] == [h]
            C['A1 starts'] += 1
for k, c in sorted(C.items()): print(c, k)
