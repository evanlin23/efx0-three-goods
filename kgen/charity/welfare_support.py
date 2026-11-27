"""Question W (kgen/charity.md §6): can a per-agent rescaling v_i -> lambda_i v_i (which changes neither EFX0 nor the
Pareto order) make a stranded Pareto maximum the welfare maximum?  Exactly when its value vector u is a supported
point: some lambda >= 1 has lambda . (u - w) >= 0 for every value vector w of a partial EFX0 allocation.  The vectors
are enumerated by brute force over all (n + 1)^m partial allocations, and the LP is solved with scipy (HiGHS).

    python3 kgen/charity/welfare_support.py"""
import itertools
import scipy.optimize as so
from refute_pm import build, value, efx0


def vectors(vals, m):
    n = len(vals); out = {}
    for asg in itertools.product(range(n + 1), repeat=m):
        Y = [set(g for g in range(m) if asg[g] == a) for a in range(n)]
        if efx0(vals, Y):
            w = tuple(value(vals, a, Y[a]) for a in range(n)); p = sum(1 for x in asg if x == n)
            out[w] = min(p, out.get(w, m))
    return out


def supported(u, vecs):
    n = len(u)
    A = [[w[i] - u[i] for i in range(n)] for w in vecs if w != u]
    r = so.linprog(c=[0] * n, A_ub=A, b_ub=[0] * len(A), bounds=[(1, None)] * n, method='highs')
    return r.status == 0, (list(r.x) if r.status == 0 else None)


if __name__ == '__main__':
    print('$ python3 kgen/charity/welfare_support.py')
    gm4e = [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}]
    Xg = [{0, 4}, {1, 3}, {2}, {5}]
    vals, X, m, P = build(2, 3)
    for name, vv, XX, mm in (('GM4-E (k = 4)', gm4e, Xg, 7), ("S'(2, 3)", vals, X, m)):
        vecs = vectors(vv, mm)
        u = tuple(value(vv, a, XX[a]) for a in range(len(vv)))
        ok, lam = supported(u, vecs)
        best = max(sum(w) for w in vecs)
        print('%s: stranded state values %s (welfare %d), %d distinct EFX0 value vectors, largest welfare %d; '
              'some rescaling makes the stranded state a welfare maximum: %s %s' % (
                  name, u, sum(u), len(vecs), best, ok, '' if lam is None else 'lambda = %s' % lam), flush=True)
