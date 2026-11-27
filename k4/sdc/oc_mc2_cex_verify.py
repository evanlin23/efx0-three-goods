"""Coordinator's independent replay (2026-11-26) of the TTC session's K4.MC2-class counterexample to OC (free completion after
one move) and OC1, every order (results/k4_ttc/oc1_mc2_counterexample.json on claude/k4-ttc).  Own code: oc1_mc2_rand.Inst
(raw EFX0, official moves), a free-completion brute force over all junk assignments, maximum matching size nu.
Result: strict MC2-class core, nu = 5; the 12 failing orders give 3 picks (non-maximum); all 50 maximum-matching orders
complete at the picks.  So OC1^max (k4/attack_log.md 21:56) survives."""
import itertools, collections
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from oc1max_climb import is_core
sets = [[0,3,6,8],[1,4,7,6],[2,5,8,7],[0,1,2],[0,1,2]]
vals = [[10,6,5,7],[10,6,5,7],[10,6,5,7],[4,3,2],[2,4,3]]
I = Inst(sets, vals)
print('core (any):', is_core(sets, vals, False), '| core in MC2 class:', is_core(sets, vals, True), '| nu', nu(I))
def free(I, base):
    J = [g for g in range(I.m) if all(g not in b for b in base)]
    for asg in itertools.product(range(I.n), repeat=len(J)):
        B = [list(b) for b in base]
        for g, a in zip(J, asg): B[a].append(g)
        if I.efx0(B): return True
    return False
picks = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
C = collections.Counter()
for pk, c in picks.items():
    size = sum(p is not None for p in pk); base = [[g] if g is not None else [] for g in pk]
    oc1 = I.check(pk)
    ocfree = free(I, base) or any(free(I, [list(b) for b in st]) for st in I.moves(base))
    C[('max' if size == nu(I) else 'non-max', oc1, 'OC free ok' if ocfree else 'OC free FAILS')] += c
    if oc1 == 'OC1 fails': print('failing picks', pk, 'orders', c, 'moves', len(I.moves(base)), 'free at picks', free(I, base))
for k in sorted(C): print(k, C[k])
