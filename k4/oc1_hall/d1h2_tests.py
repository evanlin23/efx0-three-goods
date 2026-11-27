"""The three test instances of open-core item 1 (k4/oc1_hall.md §23.4: D1-H2 in general), found by proof/k4-d1 and
re-verified here: D1H-X (the extension is needed; not a core), D1H-Y (the extension is needed; a strict core outside
K4.MC2), S2-X (an extra active agent), S1-X (three wanters) and T2-X (t = 2, a strict core).  For each:
is_core4 on the dense value matrix, hardness (brute force), D, the wanters of Y_k, the unfrozen agents valuing junk,
all-HEAD, and whether a canonical chain from k or an extension (x_0..x_{t-1}, u, u') -- u' another wanter of a taking
y_u plus junk -- leaves an S* completion owned by k with a minimal improving H_0 (D1-H2).

    python3 k4/oc1_hall/d1h2_tests.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, absorb_brute
from greedy_rules import canonical_paths, apply_chain
from d1_subcases import analyse
from chain_shapes import s_star_owners
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'c4_verify_H'))
from hcore import is_core4
CASES = [('D1H-X', [[0,1,5,7],[3,4,6,7],[0,2,5,7]], [[26,3,25,27],[19,17,25,30],[9,14,7,29]], (0,1,2)),
         ('S2-X', [[0,1,5,7],[3,4,6,7],[0,2,5,7],[8,6,7,3]], [[26,3,25,27],[19,17,25,30],[9,14,7,29],[14,11,1,7]], (0,1,2,3)),
         ('D1H-Y', [[0,4,3,5],[2,6,4,5],[0,1,3,5]], [[20,13,21,23],[17,14,18,23],[8,11,7,23]], (0,1,2)),
         ('T2-X', [[0,4,5,6],[0,1,2],[1,2,4],[1,3,5,6]], [[8,6,5,4],[4,3,2],[4,3,2],[8,4,3,2]], (0,1,2,3)),
         ('S1-X', [[0,7,5,6],[0,1,4,8],[0,2,7,5],[0,3,8,4]], [[37,13,33,25],[25,12,5,10],[24,15,12,6],[27,24,18,22]], (0,1,2,3))]


def minimal_improving(I, k, pk, ground):
    imp = [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]
    return [H for H in imp if not any(set(K) < set(H) for K in imp)]


for name, sets, vals, od in CASES:
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m, name); Y = picks(I, od); P = Picks(I, Y); base = base_of_picks(I, Y)
    dense = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): dense[i][g] = x
    k = P.D[0] if len(P.D) == 1 else None
    U = [i for i in range(I.n) if i not in P.F]
    print('=====', name, 'n', I.n, 'm', m, 'is_core4 problems', is_core4(dense), 'picks', Y, 'D', P.D, 'hard', not absorb_brute(I, base))
    if k is None: continue
    print('  wanters of Y_k', P.W[k], '; unfrozen agents valuing junk outside the wanters',
          [i for i in U if i not in P.W[k] and any(g in I.R[i] for g in P.J)])
    allhead = True; canon_rep = []
    for path in canonical_paths(I, P, k):
        if path[-1] in P.F: continue
        xt = path[-1]; Pik = [g for g in list(P.J) + [Y[xt]] if g in I.R[k]]
        for H0 in minimal_improving(I, k, P.pv[k], Pik):
            obs, comp = analyse(I, P, base, k, path, H0)[:2]
            allhead &= 'HEAD' in obs
            if comp is not None: canon_rep.append((path, H0))
    ext_rep = []
    for path in canonical_paths(I, P, k):
        if path[-1] in P.F: continue
        u = path[-1]; a = Y[path[-2]]
        for u2 in [w for w in P.W[path[-2]] if w not in path]:
            rest = [g for g in P.J if g in I.R[u2]]
            for r in range(0, len(rest) + 1):
                for S in itertools.combinations(rest, r):
                    if I.val(u2, [Y[u]] + list(S)) <= P.pv[u2]: continue
                    Pik = [g for g in list(P.J) + [Y[u2]] if g in I.R[k] and g not in S]
                    for H0 in minimal_improving(I, k, P.pv[k], Pik):
                        nb = list(base)
                        nb[Y[u2]] = -1
                        nb[Y[u]] = u2
                        for g in S: nb[g] = u2
                        for i in range(len(path) - 1, 0, -1): nb[Y[path[i - 1]]] = path[i]
                        for g in H0: nb[g] = k
                        if k in s_star_owners(I, tuple(nb)): ext_rep.append((path + (u2,), S, H0))
    print('  all-HEAD', allhead, '; canonical chains repairing (owner k)', canon_rep[:3], '; extensions repairing', ext_rep[:3])
    print('  D1-H2 holds:', bool(canon_rep or ext_rep))
