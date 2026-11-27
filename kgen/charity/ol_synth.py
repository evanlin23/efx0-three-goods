"""Exact test of Conjecture OL for small n (kgen/charity.md §9): is there an additive instance with n agents, every agent
valuing at most k goods, and an EFX0 state X with strong charity such that every complete EFX0 allocation leaves at
least two agents worse off than in X?

Reductions (proved in kgen/charity.md §9, Lemma OL0): a counterexample can be taken (a) with every good valued by
someone, m <= nk, and (b) with X a Pareto maximum, hence a robust CKMS stopping state: no pool good can be added to
any bundle, X has >= q + 1 sources (q = |pool|), every source holds >= 2 goods, every bundle is nonempty.
X is fixed up to symmetry by its bundle sizes and q.  CEGAR (z3, real values in {0} u [1, oo), at most k positive per
agent):
  outer: X is EFX0 with strong charity and the stopping-state conditions above, and every complete allocation Y found
         so far is not EFX0 or has >= 2 agents i with v_i(Y_i) < v_i(X_i);
  inner: with the outer model's values, a complete EFX0 Y with <= 1 such agent.
UNSAT of the outer problem rules out these sizes.  FOUND models are re-checked with Fractions and, when small, by brute
force over all complete allocations.

    python3 kgen/charity/ol_synth.py N K SIZEMAX MMAX [TLIM]"""
import sys, itertools, time
from fractions import Fraction
import z3
from w_synth import efx0_frac


def run(n, k, sizes, q, tlim=900, L=2):
    """L: the counterexample must force >= L losers in every complete EFX0 allocation (OL: L = 2; L = 1 is P1)."""
    B = []; g0 = 0
    for s in sizes:
        B.append(list(range(g0, g0 + s))); g0 += s
    P = list(range(g0, g0 + q)); m = g0 + q
    v = [[z3.Real('v_%d_%d' % (i, g)) for g in range(m)] for i in range(n)]
    pos = [[z3.Bool('b_%d_%d' % (i, g)) for g in range(m)] for i in range(n)]
    S = z3.Solver(); S.set('timeout', tlim * 1000)
    for i in range(n):
        for g in range(m):
            S.add(z3.If(pos[i][g], v[i][g] >= 1, v[i][g] == 0))
        S.add(z3.PbLe([(pos[i][g], 1) for g in range(m)], k))
    for g in range(m):                                  # (a) every good valued by someone
        S.add(z3.Or([pos[i][g] for i in range(n)]))
    val = lambda i, G: z3.Sum([v[i][g] for g in G]) if G else z3.RealVal(0)
    for i in range(n):                                  # X EFX0 with strong charity
        for j in range(n):
            if i != j:
                for h in B[j]:
                    S.add(val(i, [g for g in B[j] if g != h]) <= val(i, B[i]))
        S.add(val(i, P) <= val(i, B[i]))
    for g in P:                                         # (b) U0 inapplicable
        for j in range(n):
            C = B[j] + [g]
            S.add(z3.Or([val(i, [h2 for h2 in C if h2 != h]) > val(i, B[i]) for i in range(n) if i != j for h in C]))
    src = [z3.And([val(i, B[j]) <= val(i, B[i]) for i in range(n) if i != j]) for j in range(n)]
    S.add(z3.PbGe([(src[j], 1) for j in range(n)], q + 1))
    for j in range(n):
        if len(B[j]) < 2:
            S.add(z3.Not(src[j]))
    x = [[z3.Bool('x_%d_%d' % (g, a)) for a in range(n)] for g in range(m)]
    cuts = 0; t0 = time.time()
    while True:
        r = S.check()
        if r == z3.unsat:
            return 'UNSAT', cuts, time.time() - t0, None
        if r != z3.sat:
            return 'UNKNOWN', cuts, time.time() - t0, None
        M = S.model()
        V = [[Fraction(str(M.eval(v[i][g], model_completion=True).as_fraction())) for g in range(m)] for i in range(n)]
        u = [sum(V[i][g] for g in B[i]) for i in range(n)]
        T = z3.Solver(); T.set('timeout', tlim * 1000)
        for g in range(m):
            T.add(z3.PbEq([(x[g][a], 1) for a in range(n)], 1))
        hv = lambda i, a, excl=None: z3.Sum([z3.If(x[g][a], z3.RealVal(V[i][g]), z3.RealVal(0))
                                            for g in range(m) if g != excl and V[i][g] != 0] or [z3.RealVal(0)])
        for i in range(n):
            own = hv(i, i)
            for j in range(n):
                if i != j:
                    for h in range(m):
                        T.add(z3.Implies(x[h][j], hv(i, j, excl=h) <= own))
        T.add(z3.Sum([z3.If(hv(i, i) < z3.RealVal(u[i]), 1, 0) for i in range(n)]) <= L - 1)
        rt = T.check()
        if rt == z3.unsat:
            assert efx0_frac(V, B) and all(sum(V[i][g] for g in P) <= u[i] for i in range(n))
            return 'FOUND', cuts, time.time() - t0, V
        if rt != z3.sat:
            return 'UNKNOWN(inner)', cuts, time.time() - t0, None
        TM = T.model()
        Y = [[g for g in range(m) if z3.is_true(TM.eval(x[g][a], model_completion=True))] for a in range(n)]
        assert efx0_frac(V, Y) and sum(1 for i in range(n) if sum(V[i][g] for g in Y[i]) < u[i]) <= L - 1
        viol = [val(i, [g for g in Y[j] if g != h]) > val(i, Y[i]) for i in range(n) for j in range(n) if i != j
                for h in Y[j]]
        S.add(z3.Or(viol + [z3.Sum([z3.If(val(i, Y[i]) < val(i, B[i]), 1, 0) for i in range(n)]) >= L]))
        cuts += 1


if __name__ == '__main__':
    N, K, SMAX, MMAX = map(int, sys.argv[1:5]); TLIM = int(sys.argv[5]) if len(sys.argv) > 5 else 900
    print('$ python3 kgen/charity/ol_synth.py', *sys.argv[1:], flush=True)
    cnt = {}
    for q in range(1, N):
        for sizes in itertools.product(range(1, SMAX + 1), repeat=N):
            if list(sizes) != sorted(sizes, reverse=True) or sum(sizes) + q > min(MMAX, N * K):
                continue
            if sum(1 for x in sizes if x >= 2) < q + 1:
                cnt['pruned'] = cnt.get('pruned', 0) + 1
                continue
            res, cuts, dt, V = run(N, K, list(sizes), q, TLIM)
            cnt[res] = cnt.get(res, 0) + 1
            print('q %d sizes %s m %d: %s after %d cuts, %.1f s' % (q, sizes, sum(sizes) + q, res, cuts, dt),
                  flush=True)
            if res == 'FOUND':
                print('  COUNTEREXAMPLE values', [{g: str(x) for g, x in enumerate(row) if x} for row in V], flush=True)
                m = sum(sizes) + q
                if N ** m <= 3_000_000:
                    B = []; g0 = 0
                    for s in sizes:
                        B.append(list(range(g0, g0 + s))); g0 += s
                    u = [sum(V[i][g] for g in B[i]) for i in range(N)]
                    best = None
                    for asg in itertools.product(range(N), repeat=m):
                        Y = [[g for g in range(m) if asg[g] == a] for a in range(N)]
                        if efx0_frac(V, Y):
                            L = sum(1 for i in range(N) if sum(V[i][g] for g in Y[i]) < u[i])
                            best = L if best is None or L < best else best
                    print('  brute force: fewest losers over complete EFX0 allocations = %s' % best, flush=True)
    print('summary', cnt)
