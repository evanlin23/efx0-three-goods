"""D1H-X (found by proof/k4-d1, k4/d1/verify_cex.py on that branch), re-verified with this note's tools: a refutation of
Conjecture D1-LONG and Sub-lemma D1-H(ii) in their canonical form (k4/oc1_hall.md §21, attempts/k4-oc1-hall-d1-long.md).
n = 3, m = 8, order (0, 1, 2), D = {0}: hard (ohlib.absorb_brute and the SAT test agree); every canonical chain from k
has HEAD, and no canonical chain with any improving H_0 leaves a completion owned by k or by the head; an ED chain
whose head adds one junk good repairs with owner k (the ED-MIN form of §15 survives).

    python3 k4/oc1_hall/d1long_cex.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, absorb_brute, efx0
from greedy_rules import canonical_paths, apply_chain
from d1_subcases import analyse
from d1_rules import ed_paths, apply, subsets
from chain_shapes import s_star_owners
from sdclib import Enc
from oc_absorb import extends_A
sets = [[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]]; vals = [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29]]
I = Inst(sets, vals, 8, 'D1H-X'); E = Enc(sets, vals, 8); Y = picks(I, (0, 1, 2)); P = Picks(I, Y); base = base_of_picks(I, Y)
print('D1H-X', sets, vals, 'order (0, 1, 2) picks', Y, 'J', P.J, 'F', P.F, 'D', P.D, 'wanters of Y_k', P.W[P.D[0]])
print('one-absorber completion at the picks: brute force', bool(absorb_brute(I, base)), ', SAT', extends_A(E, base, 1))
k = P.D[0]; canon_ok = False
for path in canonical_paths(I, P, k):
    if path[-1] in P.F: continue
    xt = path[-1]; Pik = [g for g in list(P.J) + [Y[xt]] if g in I.R[k]]
    for H0 in [H for r in range(1, len(Pik) + 1) for H in itertools.combinations(Pik, r) if I.val(k, H) > P.pv[k]]:
        obs = analyse(I, P, base, k, path, H0)[0]; ow = s_star_owners(I, apply_chain(I, P, base, path, H0))
        canon_ok |= k in ow or xt in ow
        print('  canonical chain', path, 'H0', H0, 'obstacles', sorted(obs), 'S* owners after', ow)
print('some canonical chain leaves an S* completion owned by k or the head:', canon_ok)
for path in ed_paths(I, P, k, I.n):
    xt = path[-1]; pool0 = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] in I.R[k] else [])
    for H0 in subsets(pool0):
        if not H0 or I.val(k, H0) <= P.pv[k]: continue
        for Ht in subsets([g for g in P.J if g not in H0 and g in I.R[xt]]):
            if Ht and I.val(xt, [Y[path[-2]]] + list(Ht)) > P.pv[xt]:
                ow = s_star_owners(I, apply(I, P, base, path, H0, Ht))
                if ow: print('  ED chain with head junk', path, 'H0', H0, 'head junk', Ht, 'S* owners', ow)
print('completion [[1,5,2,4],[6,3],[7,0]] EFX0 (raw):', efx0(I, [[1, 5, 2, 4], [6, 3], [7, 0]]))
