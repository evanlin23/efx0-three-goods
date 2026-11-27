"""P1 fails at n = 3, k = 5 (kgen/charity.md §9).  The instance was found by ol_synth.run(3, 5, [3, 2, 1], 1, L=1)
(z3, `ol_synth_n3_k5_p1.log`, first FOUND row), with values scaled here by 24 to integers.  Three agents, seven
goods, every agent valuing exactly five goods; X = ({0, 1, 2}, {3, 4}, {5}), good 6 unallocated.
Checks, none of them z3 (own brute force over raw definitions, plus chlib's SAT routines as a second method):
  1. X is EFX0 with strong charity;
  2. brute force over all 3^7 complete allocations: every complete EFX0 allocation leaves some agent worse off than
     in X (so no complete EFX0 allocation weakly dominates X), and the fewest such agents (OL asks for <= 1);
  3. brute force over all 4^7 partial allocations: the Pareto maxima weakly above X (in values; then most goods
     allocated) are all incomplete; so P1 (Pareto maxima are complete) fails;
  4. chlib.improve (SAT) on X and losers.fewest_losers (SAT), for agreement.

    python3 kgen/charity/p1_n3k5.py"""
import itertools
from fractions import Fraction
from chlib import Inst, efx0, pool_ok, pool_of, improve
from losers import fewest_losers

RAW = [{0: '1', 1: '19/12', 2: '13/6', 4: '8/3', 6: '17/8'},
       {0: '37/12', 2: '1', 3: '1', 4: '41/8', 5: '43/6'},
       {0: '13/12', 2: '127/24', 3: '1', 5: '89/12', 6: '19/6'}]
V = [{g: int(Fraction(x) * 24) for g, x in d.items()} for d in RAW]
assert all(Fraction(x) * 24 == V[i][g] for i, d in enumerate(RAW) for g, x in d.items())
X = [{0, 1, 2}, {3, 4}, {5}]
n, m = 3, 7


def val(i, B):
    return sum(V[i].get(g, 0) for g in B)


def efx0_raw(Y):
    return all(not Y[j] or val(i, Y[j]) - min(V[i].get(h, 0) for h in Y[j]) <= val(i, Y[i])
               for i in range(n) for j in range(n) if i != j)


if __name__ == '__main__':
    print('$ python3 kgen/charity/p1_n3k5.py')
    print('values (x 24):', V)
    print('relevant goods per agent:', [len(d) for d in V])
    u = [val(i, X[i]) for i in range(n)]
    P = set(range(m)) - set().union(*X)
    print('X =', [sorted(B) for B in X], 'values', u, 'pool', sorted(P), '| EFX0', efx0_raw(X),
          '| strong charity', all(val(i, P) <= u[i] for i in range(n)))
    assert efx0_raw(X) and all(val(i, P) <= u[i] for i in range(n)) and max(len(d) for d in V) == 5
    cnt = 0; best = None; hist = {}
    for asg in itertools.product(range(n), repeat=m):
        Y = [{g for g in range(m) if asg[g] == a} for a in range(n)]
        if efx0_raw(Y):
            cnt += 1
            L = sum(1 for i in range(n) if val(i, Y[i]) < u[i]); hist[L] = hist.get(L, 0) + 1
            if best is None or L < best[0]:
                best = (L, [sorted(B) for B in Y], [val(i, Y[i]) for i in range(n)])
    print('complete allocations: %d EFX0; by number of agents worse off than in X: %s' % (cnt, dict(sorted(hist.items()))))
    print('fewest worse off: %d, e.g. %s with values %s' % best)
    assert best[0] >= 1
    above = []
    for asg in itertools.product(range(n + 1), repeat=m):      # a = n: unallocated
        Y = [{g for g in range(m) if asg[g] == a} for a in range(n)]
        w = [val(i, Y[i]) for i in range(n)]
        if all(w[i] >= u[i] for i in range(n)) and efx0_raw(Y):
            above.append((w, sum(len(B) for B in Y), [sorted(B) for B in Y]))
    dom = lambda a, b: all(x >= y for x, y in zip(a[0], b[0])) and (a[0] != b[0] or a[1] > b[1])
    pmax = [a for a in above if not any(dom(b, a) for b in above)]
    print('EFX0 allocations weakly above X in every value: %d; Pareto maxima among them: %d' % (len(above), len(pmax)))
    for w, s, Y in pmax:
        print('  Pareto maximum %s values %s, %d of %d goods allocated' % (Y, w, s, m))
    assert pmax and all(s < m for w, s, Y in pmax)
    I = Inst(n, m, V)
    assert efx0(I, X) and pool_ok(I, X)
    print('chlib.improve(X) (SAT): %s' % ('no dominating EFX0 allocation: X is a Pareto maximum'
                                         if improve(I, X) is None else 'X is dominated'))
    k, Lw, Y = fewest_losers(I, X)
    print('losers.fewest_losers (SAT): %d' % k)
    assert k == best[0]
    print('verified: P1 fails at n = 3, k = 5 (no complete EFX0 allocation weakly dominates X; every Pareto maximum '
          'above X leaves a good unallocated); OL holds here (fewest losers %d)' % best[0])
