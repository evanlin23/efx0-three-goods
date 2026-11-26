"""Exact test of W(k, p - 1) for small n (kgen/charity.md §6): is there an additive instance with n agents, every agent
valuing at most k goods, whose welfare maximum (among those with the fewest unallocated goods) leaves >= p goods out?

The stranded state X is fixed up to symmetry by its bundle sizes (agents' valuations and the goods are free): bundle
i holds the next sizes[i] goods, the last p goods are unallocated.  Valuations are real variables (z3, linear real
arithmetic), v_i(g) = 0 or >= 1 (per-agent scaling would change welfare, so only the global scale is fixed, which
the >= 1 normalisation does), at most k positive per agent.  CEGAR:
  outer (z3, reals): X is EFX0 with strong charity, and welfare(Y) < welfare(X) or Y is not EFX0, for every Y found so
      far (Y ranges over allocations leaving <= p - 1 goods out);
  inner (z3, Booleans with the outer model's rational values): an EFX0 allocation Y leaving <= p - 1 goods out with
      welfare(Y) >= welfare(X).  None: the outer model is a counterexample (re-checked exactly with Fractions).
UNSAT of the outer problem proves that no real valuation makes X (with these sizes) a counterexample.
Every bundle may be assumed to hold at most one good worthless to everyone (kgen/charity.md §6, the reduction there),
and no unallocated good is worthless to everyone (it could be added to a source).

    python3 kgen/charity/w_synth.py N K P SIZEMAX MMAX [TLIM [Q]]
Q (default P): the number of goods the stranded state leaves out; it must beat every allocation leaving <= P - 1 out.
A welfare maximum leaving p* >= P goods out is found with Q = p*; since p* < number of sources <= N, the values
Q = P, ..., N - 1 cover every case.
enumerates every nonincreasing size vector with entries in 0..SIZEMAX and sum + P <= MMAX; vectors with an empty
bundle or fewer than P + 1 bundles of size >= 2 are skipped (an envied agent holds a good; there are >= P + 1 sources
and each holds >= 2 goods: CKMS Theorem 8 and Lemmas CH0, CH2, valid at a welfare maximum by CH6)."""
import sys, itertools, time
from fractions import Fraction
import z3


def bundles(sizes, p):
    B = []; g = 0
    for s in sizes:
        B.append(list(range(g, g + s))); g += s
    return B, list(range(g, g + p)), g + p


def efx0_frac(V, Y):
    n = len(Y)
    for i in range(n):
        own = sum(V[i][g] for g in Y[i])
        for j in range(n):
            if i != j and Y[j]:
                tot = sum(V[i][g] for g in Y[j]); mn = min(V[i][g] for g in Y[j])
                if tot - mn > own:
                    return False
    return True


def run(n, k, p, sizes, tlim=600, fixed=None, vmax=None, q=None):
    """fixed = (B, P, m, support): a given stranded state and the relevant sets (values free on them, 0 elsewhere).
    q: the number of goods the state X leaves out (default p); X must beat every EFX0 allocation leaving <= p - 1 out."""
    if q is None:
        q = p
    if fixed is None:
        B, P, m = bundles(sizes, q)
    else:
        B, P, m, support = fixed
    mk = (lambda nm: z3.Int(nm)) if vmax else (lambda nm: z3.Real(nm))
    v = [[mk('v_%d_%d' % (i, g)) for g in range(m)] for i in range(n)]
    pos = [[z3.Bool('b_%d_%d' % (i, g)) for g in range(m)] for i in range(n)]
    S = z3.Solver(); S.set('timeout', tlim * 1000)
    for i in range(n):
        for g in range(m):
            S.add(z3.If(pos[i][g], v[i][g] >= 1, v[i][g] == 0))
            if vmax:
                S.add(v[i][g] <= vmax)
            if fixed is not None:
                S.add(pos[i][g] if g in support[i] else z3.Not(pos[i][g]))
        S.add(z3.PbLe([(pos[i][g], 1) for g in range(m)], k))
    val = lambda i, G: z3.Sum([v[i][g] for g in G]) if G else (z3.IntVal(0) if vmax else z3.RealVal(0))
    for g in P:                                            # pool goods are valued by someone
        S.add(z3.Or([pos[i][g] for i in range(n)]))
    for j in range(n):                                     # at most one good worthless to all in each bundle
        for g, h in itertools.combinations(B[j], 2):
            S.add(z3.Or([pos[i][g] for i in range(n)] + [pos[i][h] for i in range(n)]))
    for i in range(n):                                     # X is EFX0, strong charity
        for j in range(n):
            if i != j:
                for h in B[j]:
                    S.add(val(i, [g for g in B[j] if g != h]) <= val(i, B[i]))
        S.add(val(i, P) <= val(i, B[i]))
    # necessary conditions at a welfare maximum with the fewest unallocated goods (a robust stopping state, CH6):
    # no pool good can be added to any bundle (U0), and at least p + 1 agents are envied by nobody (CKMS Thm 8)
    for g in P:
        for j in range(n):
            C = B[j] + [g]
            S.add(z3.Or([val(i, [h2 for h2 in C if h2 != h]) > val(i, B[i]) for i in range(n) if i != j for h in C]))
    src = [z3.And([val(i, B[j]) <= val(i, B[i]) for i in range(n) if i != j]) for j in range(n)]
    S.add(z3.PbGe([(src[j], 1) for j in range(n)], len(P) + 1))
    for j in range(n):                                     # a source holds >= 2 goods (CH2), an envied agent >= 1
        if len(B[j]) < 2:
            S.add(z3.Not(src[j]))
    WX = z3.Sum([val(i, B[i]) for i in range(n)])
    # inner problem variables
    x = [[z3.Bool('x_%d_%d' % (g, a)) for a in range(n + 1)] for g in range(m)]
    cuts = 0; t0 = time.time()
    while True:
        r = S.check()
        if r == z3.unsat:
            return 'UNSAT', cuts, time.time() - t0, None
        if r != z3.sat:
            return 'UNKNOWN', cuts, time.time() - t0, None
        M = S.model()
        V = [[Fraction(str(M.eval(v[i][g], model_completion=True).as_fraction() if not vmax
                           else M.eval(v[i][g], model_completion=True).as_long())) for g in range(m)] for i in range(n)]
        wX = sum(V[i][g] for i in range(n) for g in B[i])
        # inner: EFX0 Y with pool <= p - 1 and welfare >= wX
        T = z3.Solver(); T.set('timeout', tlim * 1000)
        for g in range(m):
            T.add(z3.PbEq([(x[g][a], 1) for a in range(n + 1)], 1))
        T.add(z3.PbLe([(x[g][n], 1) for g in range(m)], p - 1))
        hv = lambda i, a, excl=None: z3.Sum([z3.If(x[g][a], z3.RealVal(V[i][g]), z3.RealVal(0))
                                            for g in range(m) if g != excl and V[i][g] != 0] or [z3.RealVal(0)])
        for i in range(n):
            own = hv(i, i)
            for j in range(n):
                if i != j:
                    for h in range(m):                     # if h in Y_j: v_i(Y_j - h) <= v_i(Y_i)
                        T.add(z3.Implies(x[h][j], hv(i, j, excl=h) <= own))
        T.add(z3.Sum([hv(i, i) for i in range(n)]) >= z3.RealVal(wX))
        rt = T.check()
        if rt == z3.unsat:
            assert efx0_frac(V, B), 'outer model: X not EFX0'
            assert all(sum(V[i][g] for g in P) <= sum(V[i][g] for g in B[i]) for i in range(n))
            assert all(sum(1 for g in range(m) if V[i][g]) <= k for i in range(n))
            return 'FOUND', cuts, time.time() - t0, V
        if rt != z3.sat:
            return 'UNKNOWN(inner)', cuts, time.time() - t0, None
        TM = T.model()
        Y = [[g for g in range(m) if z3.is_true(TM.eval(x[g][a], model_completion=True))] for a in range(n + 1)]
        assert efx0_frac(V, Y[:n]) and len(Y[n]) <= p - 1
        assert sum(V[i][g] for i in range(n) for g in Y[i]) >= wX
        # cut: welfare(Y) < welfare(X) or Y is not EFX0
        viol = []
        for i in range(n):
            for j in range(n):
                if i != j:
                    for h in Y[j]:
                        viol.append(val(i, [g for g in Y[j] if g != h]) > val(i, Y[i]))
        S.add(z3.Or([z3.Sum([val(i, Y[i]) for i in range(n)]) < WX] + viol))
        cuts += 1


if __name__ == '__main__':
    N, K, P, SMAX, MMAX = map(int, sys.argv[1:6]); TLIM = int(sys.argv[6]) if len(sys.argv) > 6 else 600
    Q = int(sys.argv[7]) if len(sys.argv) > 7 else P
    print('$ python3 kgen/charity/w_synth.py', *sys.argv[1:], flush=True)
    cnt = {}
    for sizes in itertools.product(range(SMAX + 1), repeat=N):
        if list(sizes) != sorted(sizes, reverse=True) or sum(sizes) + Q > MMAX:
            continue
        if min(sizes) < 1 or sum(1 for x in sizes if x >= 2) < Q + 1:   # CH0/CH2 + CKMS: pruned, cannot strand Q
            cnt['pruned'] = cnt.get('pruned', 0) + 1
            continue
        res, cuts, dt, V = run(N, K, P, list(sizes), TLIM, q=Q)
        cnt[res] = cnt.get(res, 0) + 1
        print('sizes %s m %d: %s after %d cuts, %.1f s' % (sizes, sum(sizes) + Q, res, cuts, dt), flush=True)
        if res == 'FOUND':
            print('  COUNTEREXAMPLE values', [{g: str(x) for g, x in enumerate(row) if x} for row in V], flush=True)
            m = sum(sizes) + Q
            if (N + 1) ** m <= 2_000_000:                   # independent brute force over all partial allocations
                best = None
                for asg in itertools.product(range(N + 1), repeat=m):
                    if sum(1 for a in asg if a == N) > P - 1:
                        continue
                    Y = [[g for g in range(m) if asg[g] == a] for a in range(N)]
                    if efx0_frac(V, Y):
                        w = sum(V[i][g] for i in range(N) for g in Y[i])
                        best = w if best is None or w > best else best
                B, Pl, _ = bundles(list(sizes), Q)
                wX = sum(V[i][g] for i in range(N) for g in B[i])
                print('  brute force: best welfare with <= %d unallocated %s < %s: %s' % (P - 1, best, wX,
                                                                                       best is None or best < wX))
    print('summary', cnt)
