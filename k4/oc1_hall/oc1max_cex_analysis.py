"""The two OC1^max counterexamples (coordinator, from compute/k4-oc1max-cert; k4/sdc.md §31 on claude/kind-lamport-y8fdme),
analysed with this note's §21 machinery (k4/oc1_hall.md §22).
Part 1, at the failing order: picks, nu, frozen and dangerous agents, a one-absorber completion at the picks and after
one move (SAT), ED repairs (ed_check.classify), and, for every canonical chain from every dangerous agent with every
minimal improving H_0: HEAD / CROWD, the other dangerous agents still threatened by the pool, S* and one-absorber
completions.
Part 2, every order: maximum matching, R1 priority, and whether the picks, one move or two sequential moves
(de_free.moves, chains and rings) reach a one-absorber completion.

    python3 k4/oc1_hall/oc1max_cex_analysis.py
"""
import os
os.chdir(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
import sys, itertools, json
sys.path.insert(0, 'k4/oc1_hall'); sys.path.insert(0, 'k4/sdc')
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, threatened
from greedy_rules import canonical_paths, apply_chain
from d1_subcases import analyse
from max_matching import nu
from sdclib import Enc
from oc_absorb import extends_A
from chain_shapes import s_star_owners
import de_free as DF
from ed_check import classify
DF.CHAIN_ONLY = False
for nm, sets, vals, od in [('cex1', [[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]], [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]], (0,3,2,1)),
                           ('cex2', [[0,4,5,6],[1,2,3,5],[1,3,5,6],[2,4,6]], [[2,3,10,6],[3,10,6,8],[5,3,7,6],[4,3,2]], (3,1,2,0))]:
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m, nm); E = Enc(sets, vals, m)
    Y = picks(I, od); P = Picks(I, Y); base = base_of_picks(I, Y)
    print('=====', nm, 'order', od, 'picks', Y, 'nu', nu(I), 'J', P.J, 'p', P.pv, 'F', P.F, 'D', P.D, 'W', P.W)
    for i in range(I.n): print('  agent', i, {g: I.v[i][g] for g in sorted(I.R[i], key=lambda g: -I.v[i][g])})
    print('  one-absorber at picks:', extends_A(E, base, 1), ' S* owners at picks:', s_star_owners(I, base))
    mv = DF.moves(E, base)
    print('  one-move states:', len(mv), ' any one-absorber after one move:', any(extends_A(E, b2, 1) for b2 in mv), ' any S*:', any(s_star_owners(I, b2) for b2 in mv))
    print('  ED classification (ed_check.classify):', sorted(classify(I, E, P, base)))
    for k in P.D:
        for path in canonical_paths(I, P, k):
            xt = path[-1]
            if xt in P.F: print('  chain', path, '(head frozen at picks: not canonical-complete)'); continue
            Pi = list(P.J) + ([Y[xt]] if Y[xt] is not None else []); Pik = [g for g in Pi if g in I.R[k]]
            imp = [H for r in range(1, len(Pik) + 1) for H in itertools.combinations(Pik, r) if I.val(k, H) > P.pv[k]]
            mins = [H for H in imp if not any(set(K) < set(H) for K in imp)]
            print('  k', k, 'chain', path, 'pool_k', Pik, 'value', I.val(k, Pik), 'vs p_k', P.pv[k], 'minimal H0', mins)
            for H0 in mins:
                obs, comp, F2, crowded, B2 = analyse(I, P, base, k, path, H0)
                b2 = apply_chain(I, P, base, path, H0); J2 = [g for g in range(m) if b2[g] < 0]
                pv2 = [I.val(i, B2[i]) for i in range(I.n)]
                otherD = [q for q in P.D if q != k and q in F2 and threatened(I, q, pv2[q], list(H0) + J2)]
                print('     H0', H0, 'obstacles', sorted(obs), 'crowded', crowded, 'frozen after', sorted(F2), 'other dangerous threatened by pool', otherD,
                      'S* owned by k', comp is not None, 'S* owners', s_star_owners(I, b2), 'one-absorber', extends_A(E, b2, 1))

print()
from sdc_orders import sd
for nm, sets, vals, od0 in [('cex1', [[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]], [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]], (0,3,2,1)),
                            ('cex2', [[0,4,5,6],[1,2,3,5],[1,3,5,6],[2,4,6]], [[2,3,10,6],[3,10,6,8],[5,3,7,6],[4,3,2]], (3,1,2,0))]:
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m, nm); E = Enc(sets, vals, m); N = nu(I)
    r1 = set(tuple(sd(E, list(od), True)[0]) for od in itertools.permutations(range(I.n)))
    seen = {}
    for od in itertools.permutations(range(I.n)):
        Y = picks(I, od)
        if Y in seen: continue
        base = base_of_picks(I, Y); P = Picks(I, Y)
        st = 'picks' if extends_A(E, base, 1) else None
        if st is None:
            mv = DF.moves(E, base)
            if any(extends_A(E, b2, 1) for b2 in mv): st = 'one move'
            else:
                two = []
                for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                    for b3, ds3 in DF.moves(E, b2, describe=True, all_desc=True).items():
                        if extends_A(E, b3, 1): two.append((ds[0][:2], ds3[0][:2]))
                st = 'two moves (%d pairs, e.g. %s)' % (len(two), two[:2]) if two else 'FAILS two moves'
        seen[Y] = st
        print(nm, 'order', od, 'picks', Y, 'max-matching', sum(1 for y in Y if y is not None) == N, 'R1-priority', Y in r1, 'D', P.D, '->', st)
