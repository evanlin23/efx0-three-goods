"""Coordinator's independent check of the certifier's n = 5 counterexamples to TTC's R2 (an OC1^max-failing start with
two receivers; 5_pure_s5o1, 2026-11-27): strict connected core, perfect SD picks, receivers, OC1 (raw, official moves),
and RF (receiver-first maximum-matching orders satisfy OC1).  Own code only (oc1_mc2_rand.Inst).
    python3 k4/sdc/r2_n5_cex_check.py"""
import itertools, json
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
import oc1max_climb as C

CASES = {
    '5_pure#650': ([[0,1,5,7],[0,5,6,7],[1,5,6,7],[2,3,4,6],[2,3,4,7]], [[3,6,7,5],[2,10,7,6],[2,8,4,3],[4,5,6,8],[5,4,6,8]], (5,0,1,6,7)),
    '5_pure#655': ([[0,1,6,7],[0,4,5,6],[1,5,6,7],[2,3,4,5],[2,3,4,7]], [[5,3,6,7],[4,1,8,6],[2,8,3,4],[4,5,6,8],[5,4,6,8]], (6,0,1,5,7)),
    '5_pure#1014': ([[0,6,7,8],[1,2,3,6],[1,2,3,7],[4,5,6,8],[4,5,7,8]], [[2,7,10,4],[3,5,6,7],[4,6,5,8],[3,5,7,6],[3,6,8,10]], (0,6,7,8,5)),
    '5_pure#1050': ([[0,2,3,4],[1,4,8,9],[2,3,8,9],[5,6,7,8],[5,6,7,9]], [[2,10,6,7],[1,4,6,8],[7,3,6,5],[6,5,4,8],[5,3,6,7]], (2,4,3,8,9)),
}
for name, (S, V, P) in CASES.items():
    I = Inst(S, V); N = nu(I)
    ords = [o for o in itertools.permutations(range(I.n)) if I.sd(o) == P]
    rec = [u for u in range(I.n) if all(I.v[i].get(P[u], 0) <= I.v[i].get(P[i], 0) for i in range(I.n) if i != u)]
    print(name, '| core', C.is_core(S, V, False), 'MC2', C.is_core(S, V, True), '| SD orders', len(ords), '| perfect', None not in P, 'nu', N,
          '| receivers', rec, '| OC1:', I.check(P))
    for u in rec:
        res = {}
        for rest in itertools.permutations([i for i in range(I.n) if i != u]):
            p = I.sd((u,) + rest)
            if p in res: continue
            res[p] = I.check(p) if sum(x is not None for x in p) == N else 'non-max'
        print('   RF with receiver', u, ':', sorted(set(res.values())))
