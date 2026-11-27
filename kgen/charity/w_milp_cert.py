"""Second, solver-independent re-check of an UNSAT answer of w_synth.run (kgen/charity.md §6): the outer problem with a
dumped cut list (or an unsat core of it, from w_cert.py --core) as a mixed-integer program (scipy.optimize.milp,
HiGHS), written separately from w_synth.py (z3) and w_cert.py (cvc5).

Homogeneous form.  Every constraint of the outer problem is linear and homogeneous in the values, apart from
v_i(g) >= 1 on supports and the strict inequalities.  Replace them by v_i(g) >= eps, strict gaps >= eps and
sum of all values <= 1, and maximise eps.  A solution of the original scales to one with eps > 0, and one with
eps > 0 scales back, so the original is infeasible iff the optimum is eps* = 0.  With sum v <= 1 every expression
used lies in [-1, 1], so big-M = 2 is exact for the disjunctions OR_t (expr_t >= eps).  Disjuncts with no positive
coefficient (always <= 0) are dropped and identical ones merged.

    python3 kgen/charity/w_milp_cert.py CUTFILE [COREFILE]"""
import sys, json, time, itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix


def build(D, cuts):
    n, k, p, B, P, m, sup = D['n'], D['k'], D['p'], D['bundles'], D['pool'], D['m'], D['support']
    var = {}

    def nv(key):
        var[key] = len(var); return var[key]
    for i in range(n):
        for g in range(m):
            if sup is None or g in sup[i]:
                nv(('v', i, g))
                if sup is None:
                    nv(('b', i, g))
    E = nv(('eps',))
    rows = []                                              # (dict var -> coef, lo, hi)
    integ = set(var[x] for x in var if x[0] == 'b')

    def val(i, G, c=1):
        return {var[('v', i, g)]: c for g in G if ('v', i, g) in var}

    def add(*ds):
        out = {}
        for d in ds:
            for a, c in d.items():
                out[a] = out.get(a, 0) + c
        return {a: c for a, c in out.items() if c != 0}
    for i in range(n):
        for g in range(m):
            if ('v', i, g) not in var:
                continue
            if sup is not None:
                rows.append(({var[('v', i, g)]: 1, E: -1}, 0, np.inf))          # v >= eps
            else:
                b = var[('b', i, g)]
                rows.append(({var[('v', i, g)]: 1, b: -1}, -np.inf, 0))         # v <= b
                rows.append(({var[('v', i, g)]: 1, E: -1, b: -1}, -1, np.inf))  # b = 1 -> v >= eps
        if sup is None:
            rows.append(({var[('b', i, g)]: 1 for g in range(m)}, -np.inf, k))
    rows.append(({var[x]: 1 for x in var if x[0] == 'v'}, -np.inf, 1))           # sum v <= 1
    pos = lambda i, g: (1 if g in sup[i] else 0) if sup is not None else {var[('b', i, g)]: 1}
    if sup is None:
        for g in P:
            rows.append((add(*[pos(i, g) for i in range(n)]), 1, np.inf))
        for j in range(n):
            for g, h in itertools.combinations(B[j], 2):
                rows.append((add(*[pos(i, g) for i in range(n)], *[pos(i, h) for i in range(n)]), 1, np.inf))
    else:
        assert all(len(s) <= k for s in sup) and all(any(g in sup[i] for i in range(n)) for g in P)
        for j in range(n):
            for g, h in itertools.combinations(B[j], 2):
                assert any(g in sup[i] or h in sup[i] for i in range(n))
    for i in range(n):                                     # X EFX0, strong charity
        for j in range(n):
            if i != j:
                for h in B[j]:
                    rows.append((add(val(i, [g for g in B[j] if g != h]), val(i, B[i], -1)), -np.inf, 0))
        rows.append((add(val(i, P), val(i, B[i], -1)), -np.inf, 0))
    ndisj = [0]

    def disj(exprs):
        """OR_t (expr_t >= eps); returns False if no disjunct can hold."""
        seen = set(); keep = []
        for e in exprs:
            if not any(c > 0 for c in e.values()):
                continue
            key = tuple(sorted(e.items()))
            if key not in seen:
                seen.add(key); keep.append(e)
        if not keep:
            return False
        zs = []
        for e in keep:
            z = nv(('z', ndisj[0])); ndisj[0] += 1; integ.add(z); zs.append(z)
            rows.append((add(e, {E: -1, z: -2}), -2, np.inf))                  # z = 1 -> e >= eps
        rows.append(({z: 1 for z in zs}, 1, np.inf))
        return True
    ok = True
    for g in P:                                            # no pool good can be added to a bundle
        for j in range(n):
            C = B[j] + [g]
            ok &= disj([add(val(i, [x for x in C if x != h]), val(i, B[i], -1)) for i in range(n) if i != j for h in C])
    S = []
    for j in range(n):
        if len(B[j]) < 2:
            ok &= disj([add(val(i, B[j]), val(i, B[i], -1)) for i in range(n) if i != j])
        else:
            s = nv(('s', j)); integ.add(s); S.append(s)
            for i in range(n):
                if i != j:
                    rows.append((add(val(i, B[j]), val(i, B[i], -1), {s: 1}), -np.inf, 1))   # s = 1 -> src
    rows.append(({s: 1 for s in S}, len(P) + 1, np.inf))
    WX = add(*[val(i, B[i]) for i in range(n)])
    for Y in cuts:
        assert len(Y) == n + 1 and sorted(g for Yi in Y for g in Yi) == list(range(m)) and len(Y[n]) <= p - 1
        ex = [add(WX, *[val(i, Y[i], -1) for i in range(n)])]
        for i in range(n):
            for j in range(n):
                if i != j:
                    for h in Y[j]:
                        ex.append(add(val(i, [g for g in Y[j] if g != h]), val(i, Y[i], -1)))
        ok &= disj(ex)
    return var, E, rows, integ, ok


def solve(D, cuts, tlim=3600):
    var, E, rows, integ, ok = build(D, cuts)
    if not ok:
        return 'trivially infeasible (a disjunction has no satisfiable disjunct)', 0.0, None, len(var)
    N = len(var); A = lil_matrix((len(rows), N)); lo = np.empty(len(rows)); hi = np.empty(len(rows))
    for r, (d, a, b) in enumerate(rows):
        for x, c in d.items():
            A[r, x] = c
        lo[r] = a; hi[r] = b
    c = np.zeros(N); c[E] = -1
    ub = np.ones(N); integrality = np.zeros(N)
    for x in integ:
        integrality[x] = 1
    res = milp(c, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=integrality, bounds=Bounds(0, ub),
               options={'time_limit': tlim, 'mip_rel_gap': 0})
    return res.message, -res.fun if res.fun is not None else None, getattr(res, 'mip_dual_bound', None), N


if __name__ == '__main__':
    print('$ python3 kgen/charity/w_milp_cert.py', *[a.split('/')[-1] for a in sys.argv[1:]], flush=True)
    D = json.load(open(sys.argv[1])); cuts = D['cuts']
    if len(sys.argv) > 2:
        core = json.load(open(sys.argv[2]))['core']; cuts = [cuts[t] for t in core]
    t0 = time.time()
    msg, eps, bound, N = solve(D, cuts)
    print('%s: n %d, m %d, %d cuts used; MILP with %d variables: %s; eps* = %s, dual bound %s (%.1f s)' % (
        sys.argv[1].split('/')[-1], D['n'], D['m'], len(cuts), N, msg, eps, None if bound is None else -bound,
        time.time() - t0), flush=True)
