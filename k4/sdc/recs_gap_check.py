"""Coordinator replay of kgen-rounds' REC-S existence gaps at n = 5 (5_pure #773, #963, #38; certifier data
results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz): core status, SD orders, perfectness, frozen agents, improving junk
sets of size <= 2 (REC-S's pool pairs, Y_z options not included), OC1, least number of moves, and ROUND-P
(k4/sdc/roundp_check.py).  Own code only.
    python3 k4/sdc/recs_gap_check.py"""
import sys, itertools, json
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
import oc1max_climb as C, roundp_check as RP, three_move_hunt as H
cases = {
 '773': ([[0,2,7,8],[1,6,7,8],[2,6,7,8],[3,4,5,6],[3,4,5,8]], [[3,10,8,6],[2,7,4,8],[8,4,2,5],[3,2,4,8],[4,3,2,8]], (2,1,7,6,8)),
 '963': ([[0,1,5,7],[1,6,7,8],[2,3,4,6],[2,3,4,8],[5,6,7,8]], [[3,6,10,8],[2,8,4,7],[2,3,4,8],[2,4,3,8],[7,6,3,5]], (5,1,6,8,7)),
 '38':  ([[0,1,3,8],[2,3,7,8],[2,5,6,7],[4,5,6,8],[4,6,7,8]], [[2,4,8,7],[2,8,3,4],[3,10,4,8],[6,10,3,8],[5,3,6,7]], (3,2,5,8,7)),
}
for name, (S, V, P) in cases.items():
    I = Inst(S, V)
    ords = [o for o in itertools.permutations(range(I.n)) if I.sd(o) == P]
    J = [g for g in range(I.m) if g not in P]
    frozen = [k for k in range(I.n) if any(i != k and I.v[i].get(P[k], 0) > I.v[i][P[i]] for i in range(I.n))]
    # improving pool pairs/singles for frozen agents from J (plus any pick, to see Y_z options)
    imp = {k: [T for r in (1, 2) for T in itertools.combinations([g for g in J if g in I.R[k]], r) if I.V(k, T) > I.v[k][P[k]]] for k in frozen}
    print('5_pure#%s core %s MC2 %s | orders %d | perfect %s nu %d | junk %s | frozen %s' % (name, C.is_core(S, V, False), C.is_core(S, V, True), len(ords), None not in P, nu(I), J, frozen))
    print('   improving pool sets from junk only (|T|<=2):', {k: v for k, v in imp.items()})
    print('   OC1:', I.check(P), '| least moves:', H.depth(I, P, 2), '| ROUND-P (<=2 disjoint OC1prime moves):', RP.round_p(I, P, 2)[0])
