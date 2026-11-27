"""Is PW5's failing start (k4/ksens.md §1, k = 5; refereed CORRECT, k4/referee/ksens.md) a maximum-matching start?
Coordinator's own check with oc1_mc2_rand.Inst (raw EFX0, official moves including additions and rings) and a
free-completion brute force.  Result: yes: nu = 5 and the order (0, 1, 2, 3, 4) gives every agent a pick, so OC^max
(free completion) and OC1^max both FAIL at k = 5.  The maximum-matching restriction is specific to k <= 4."""
import itertools, collections
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

sets = [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]]
vals = [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]]
I = Inst(sets, vals); N = nu(I)
print('PW5: n = 5, m = 9, nu =', N)


def free(base):
    J = [g for g in range(I.m) if all(g not in b for b in base)]
    for asg in itertools.product(range(I.n), repeat=len(J)):
        B = [list(b) for b in base]
        for g, a in zip(J, asg): B[a].append(g)
        if I.efx0(B): return True
    return False


C = collections.Counter()
for p, c in collections.Counter(I.sd(o) for o in itertools.permutations(range(5))).items():
    base = [[g] if g is not None else [] for g in p]; kind = 'max' if sum(x is not None for x in p) == N else 'non-max'
    r = I.check(p); C[(kind, r)] += c
    if r == 'OC1 fails':
        M = I.moves(base)
        print('failing start: picks', p, '(%s, %d orders)' % (kind, c), '| free completion at the picks:', free(base),
              '| states after one move:', len(M), '| with a free completion:', sum(free([list(b) for b in st]) for st in M))
for k in sorted(C): print(k, C[k])
