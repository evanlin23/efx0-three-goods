"""Conjecture OL and P1 on the three-agent example of Chaudhury-Garg-Mehlhorn, "EFX exists for three agents",
arXiv 2002.05119, Section 5, Table 3 and Theorem 21 (read): goods g1..g7 = 0..6, the partial allocation
X = ({g2, g3, g4}, {g1, g5}, {g6}) with g7 unallocated is EFX and no complete EFX allocation Pareto-dominates it.
Checks: X is EFX0 with strong charity; it is a Pareto maximum (chlib.improve); the fewest agents worse off in a
complete EFX0 allocation (losers.fewest_losers); a brute force over all 3^7 complete allocations for the same.

    python3 kgen/charity/cgm_check.py"""
import itertools
from chlib import Inst, efx0, pool_ok, pool_of, improve
from losers import fewest_losers

V = [{0: 8, 1: 2, 2: 12, 3: 2, 5: 17, 6: 1},       # a1 (value 0 for g5)
     {0: 5, 2: 9, 3: 4, 4: 10, 6: 3},              # a2 (0 for g2, g6)
     {4: 9, 5: 10, 6: 2}]                          # a3
X = [{1, 2, 3}, {0, 4}, {5}]

if __name__ == '__main__':
    print('$ python3 kgen/charity/cgm_check.py')
    I = Inst(3, 7, V)
    print('values of X:', [I.val(i, X[i]) for i in range(3)], 'EFX0', efx0(I, X), 'strong charity', pool_ok(I, X),
          'pool', sorted(pool_of(I, X)), '| max relevant goods per agent', I.k())
    print('Pareto maximum (no partial EFX0 allocation dominates it):', improve(I, X) is None)
    k, L, Y = fewest_losers(I, X)
    print('fewest losers over complete EFX0 allocations: %d (agents %s), e.g. %s with values %s' % (
        k, L, [sorted(B) for B in Y], [I.val(i, Y[i]) for i in range(3)]))
    u = [I.val(i, X[i]) for i in range(3)]; best = None; cnt = 0
    for asg in itertools.product(range(3), repeat=7):
        Z = [set(g for g in range(7) if asg[g] == a) for a in range(3)]
        if efx0(I, Z):
            cnt += 1
            l = sum(1 for i in range(3) if I.val(i, Z[i]) < u[i])
            best = l if best is None or l < best else best
    print('brute force: %d complete EFX0 allocations; fewest losers %d' % (cnt, best))
