"""Coordinator's independent replay (2026-11-26) of the OC1^max counterexamples found by the ordinal CEGAR of
compute/k4-oc1max-cert (n = 4 core list 4_n4_3, idx 58 and 77).  Own code: oc1_mc2_rand.Inst (raw EFX0, official
moves), all EFX0 allocations by brute force (free completion = some EFX0 allocation contains the bases).
Result: both are strict connected MC2-class k = 4 cores with nu = n = 4; the failing order gives every agent a
pick (a perfect, maximum-matching start) and neither the picks nor any one-move state extend, not even freely.
So OC1^max, OC^max and OC1 at perfect starts are FALSE at k = 4.  Two sequential moves repair both; other
maximum-matching orders of the same instances complete at the picks."""
import itertools, collections
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from oc1max_climb import is_core
C = [([[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]], [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]], [0,3,2,1]),
     ([[0,4,5,6],[1,2,3,5],[1,3,5,6],[2,4,6]], [[2,3,10,6],[3,10,6,8],[5,3,7,6],[4,3,2]], [3,1,2,0])]
for sets, vals, order in C:
    I = Inst(sets, vals); N = nu(I)
    print('core', is_core(sets, vals, False), 'MC2', is_core(sets, vals, True), 'm', I.m, 'nu', N)
    p = I.sd(order); print(' order', order, 'picks', p, 'max' if sum(x is not None for x in p) == N else 'non-max')
    allX = []
    for asg in itertools.product(range(I.n), repeat=I.m):
        B = [[g for g in range(I.m) if asg[g] == i] for i in range(I.n)]
        if I.efx0(B): allX.append(B)
    print(' EFX0 allocations', len(allX))
    base = [[g] if g is not None else [] for g in p]
    ext = lambda b: any(all(set(b[i]) <= set(X[i]) for i in range(I.n)) for X in allX)
    M = I.moves(base)
    print(' picks extend (free):', ext(base), '| one-absorber:', I.one_absorber(base), '| moves', len(M),
          '| free after a move', sum(ext([list(x) for x in s]) for s in M), '| check():', I.check(p))
    pk = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
    bad = [(q, c) for q, c in pk.items() if sum(x is not None for x in q) == N and I.check(q) == 'OC1 fails']
    print(' failing max pick vectors', bad)

print('--- surviving forms ---')
for sets, vals, order in C:
    I = Inst(sets, vals); N = nu(I)
    allX = []
    for asg in itertools.product(range(I.n), repeat=I.m):
        B = [[g for g in range(I.m) if asg[g] == i] for i in range(I.n)]
        if I.efx0(B): allX.append(B)
    ext = lambda b: any(all(set(b[i]) <= set(X[i]) for i in range(I.n)) for X in allX)
    p = I.sd(order); base = [[g] if g is not None else [] for g in p]
    two = 0; twoA = 0
    for s1 in I.moves(base):
        b1 = [list(x) for x in s1]
        for s2 in I.moves(b1):
            b2 = [list(x) for x in s2]
            if ext(b2): two += 1
            if I.one_absorber(b2): twoA += 1
    pk = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
    res = collections.Counter((('max' if sum(x is not None for x in q) == N else 'non-max'), I.check(q)) for q in pk)
    sdc = sum(ext([[g] if g is not None else [] for g in q]) for q in pk)
    print(' two sequential moves: states with a free completion', two, '| one-absorber', twoA,
          '| distinct pick vectors by outcome', dict(res), '| pick vectors that extend (SD-C)', sdc, 'of', len(pk))
