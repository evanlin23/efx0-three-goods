"""S2-X (proof/k4-d1, k4/d1/s2_probe.py on that branch), re-verified with this note's tools (k4/oc1_hall.md §23.4 item
1): a strict k = 4 core (hcore.is_core4), hard, D = {0}, all-HEAD, with a third agent unfrozen at the picks that values
junk.  This refutes S2 and S2'.  D1-H2 still holds there: a canonical chain repairs with owner k.

    python3 k4/oc1_hall/s2x_check.py
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
sets = [[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7], [8, 6, 7, 3]]; vals = [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29], [14, 11, 1, 7]]
I = Inst(sets, vals, 9); Y = picks(I, (0, 1, 2, 3)); P = Picks(I, Y); base = base_of_picks(I, Y)
dense = [[0] * 9 for _ in sets]
for i, (S, V) in enumerate(zip(sets, vals)):
    for g, x in zip(S, V): dense[i][g] = x
print('is_core4 problems (dense value matrix):', is_core4(dense))
U = [i for i in range(I.n) if i not in P.F]
print('picks', Y, 'J', P.J, 'F', P.F, 'D', P.D, 'wanters of Y_k', P.W[P.D[0]], 'unfrozen', U,
      'unfrozen agents valuing junk', [i for i in U if any(g in I.R[i] for g in P.J)])
print('hard (brute force):', not absorb_brute(I, base))
k = P.D[0]; heads = []
for path in canonical_paths(I, P, k):
    if path[-1] in P.F: continue
    xt = path[-1]; Pik = [g for g in list(P.J) + [Y[xt]] if g in I.R[k]]
    imp = [H for r in range(1, len(Pik) + 1) for H in itertools.combinations(Pik, r) if I.val(k, H) > P.pv[k]]
    for H0 in [H for H in imp if not any(set(K) < set(H) for K in imp)]:
        obs = analyse(I, P, base, k, path, H0)[0]; heads.append('HEAD' in obs)
        print('  canonical', path, 'H0', H0, 'obstacles', sorted(obs), 'S* owners', s_star_owners(I, apply_chain(I, P, base, path, H0)))
print('all-HEAD:', all(heads))
