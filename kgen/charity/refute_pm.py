"""Independent check of Proposition CH-E (kgen/charity.md §5): Pareto maxima can leave sigma - 1 goods out at k = 3.

Standalone: it imports nothing from this folder and uses no SAT solver.  It rebuilds S'(sigma, k) from the written
description, checks the state with its own raw EFX0 / charity code, and decides Pareto-maximality exactly:
  1. enumerate every family (S_a) of pairwise disjoint S_a subset of R_a with v_a(S_a) >= u_a (u = the state's values);
     any EFX0 state Y with values >= u gives such a family, S_a = Y_a cap R_a;
  2. for each family, enumerate every placement of the other goods (to the pool or to an agent that values them 0),
     and test the raw EFX0 definition and domination (someone strictly better, or fewer goods unallocated).
For sigma = 2 it also enumerates all (n + 1)^m partial allocations, as the P1 refutation did for GM4-E, and lists the
complete EFX0 allocations with the agent each one leaves worse off.

    python3 kgen/charity/refute_pm.py K SIGMA_MAX"""
import sys, itertools


def build(sigma, k):
    """S'(sigma, k): sources s_j hold {x_j, x'_j} (each worth 2 to s_j) and value their <= k-2 children at 5; relays
    hold {z} (worth 4 to them) and value their <= k-1 children at 5; champion c(g, j) holds {y} and values y 10,
    x_j 6, g 6; the champions c(., j-1) form the leaves of s_j's tree; pool g_0..g_{sigma-2}."""
    p = sigma - 1
    goods = {}

    def G(name):
        return goods.setdefault(name, len(goods))
    vals, hold = [], []
    for j in range(sigma):
        G(('x', j)); G(('xp', j))
    for g in range(p):
        G(('g', g))
    for j in range(sigma):
        for g in range(p):
            vals.append({G(('y', g, j)): 10, G(('x', j)): 6, G(('g', g)): 6}); hold.append({G(('y', g, j))})
    cnt = 0
    for j in range(sigma):
        level = [G(('y', g, (j - 1) % sigma)) for g in range(p)]
        while len(level) > k - 2:
            nxt = []
            for a in range(0, len(level), k - 1):
                cnt += 1; z = G(('z', cnt))
                d = {h: 5 for h in level[a:a + k - 1]}; d[z] = 4
                vals.append(d); hold.append({z}); nxt.append(z)
            level = nxt
        d = {h: 5 for h in level}; d[G(('x', j))] = 2; d[G(('xp', j))] = 2
        vals.append(d); hold.append({G(('x', j)), G(('xp', j))})
    return vals, hold, len(goods), {G(('g', g)) for g in range(p)}


def value(vals, a, B):
    return sum(vals[a].get(g, 0) for g in B)


def efx0(vals, Y):
    n = len(Y)
    for i in range(n):
        own = value(vals, i, Y[i])
        for j in range(n):
            if i != j and Y[j] and value(vals, i, Y[j]) - min(vals[i].get(h, 0) for h in Y[j]) > own:
                return False
    return True


def families(vals, u, m):
    n = len(vals); out = []
    order = sorted(range(n), key=lambda a: len(vals[a]))

    def rec(t, used, fam):
        if t == n:
            out.append(dict(fam)); return
        a = order[t]; R = [g for g in vals[a] if g not in used]
        for r in range(len(R) + 1):
            for S in itertools.combinations(R, r):
                if sum(vals[a][g] for g in S) >= u[a]:
                    fam[a] = set(S); rec(t + 1, used | set(S), fam)
        fam.pop(a, None)
    rec(0, frozenset(), {})
    return out


def dominated(vals, X, m, limit=5_000_000):
    """Exact search for an EFX0 state dominating X; returns (witness or None, number of families, placements tried)."""
    n = len(X); u = [value(vals, a, X[a]) for a in range(n)]
    poolX = m - sum(len(B) for B in X)
    fams = families(vals, u, m); tried = 0
    for fam in fams:
        rest = [g for g in range(m) if not any(g in S for S in fam.values())]
        opts = [[a for a in range(n) if g not in vals[a]] + [None] for g in rest]
        for choice in itertools.product(*opts):
            tried += 1
            assert tried <= limit, 'placement limit'
            Y = [set(fam[a]) for a in range(n)]
            for g, a in zip(rest, choice):
                if a is not None:
                    Y[a].add(g)
            if not efx0(vals, Y):
                continue
            better = any(value(vals, a, Y[a]) > u[a] for a in range(n))
            if better or sum(1 for a in choice if a is None) < poolX:
                return Y, len(fams), tried
    return None, len(fams), tried


if __name__ == '__main__':
    K, SMAX = int(sys.argv[1]), int(sys.argv[2])
    print('$ python3 kgen/charity/refute_pm.py', *sys.argv[1:], flush=True)
    for sigma in range(2, SMAX + 1):
        vals, X, m, P = build(sigma, K)
        n = len(vals)
        assert all(len(d) <= K for d in vals) and set().union(*X) | P == set(range(m))
        assert all(any(g in d for d in vals) for g in range(m)), 'every good is valued'
        ok = efx0(vals, X) and all(value(vals, a, P) <= value(vals, a, X[a]) for a in range(n))
        W, nf, tried = dominated(vals, X, m)
        print('S\'(%d, %d): n %d, m %d, max |R_i| %d, unallocated %d | EFX0 with strong charity %s | value-feasible '
              'families %d, placements tried %d | dominated: %s' % (sigma, K, n, m, max(len(d) for d in vals), len(P),
                                                                  ok, nf, tried, W is not None), flush=True)
        assert ok and W is None
        if sigma == 2:
            u = [value(vals, a, X[a]) for a in range(n)]; comp = 0; best = None
            for asg in itertools.product(range(n + 1), repeat=m):
                Y = [set(g for g in range(m) if asg[g] == a) for a in range(n)]
                if not efx0(vals, Y):
                    continue
                vv = [value(vals, a, Y[a]) for a in range(n)]
                pool = sum(1 for x in asg if x == n)
                assert not (all(vv[a] >= u[a] for a in range(n)) and (vv != u or pool < len(P))), 'brute: dominated'
                if pool == 0:
                    comp += 1
                    worse = [a for a in range(n) if vv[a] < u[a]]
                    assert worse
            print('  brute force over all %d^%d partial allocations: no dominating EFX0 state; %d complete EFX0 '
                  'allocations, each leaves some agent worse off than the state' % (n + 1, m, comp), flush=True)
    print('all checks passed')
