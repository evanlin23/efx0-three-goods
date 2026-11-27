"""SAT: exists an order pi and serial-dictatorship picks Y (each agent its favourite good not picked before it) such that
some complete allocation X with Y_i in X_i is EFX0.  Equivalently: some Pareto-optimal one-good matching extends."""
import sys, os, json, itertools, random, time
from sdclib import Enc, decode, efx0
from pysat.solvers import Cadical153
def build(sets, vals, m, extra=None, slack=0):
    E = Enc(sets, vals, m, slack)
    cl = list(E.cl); top = [E.top]
    def new():
        top[0] += 1; return top[0]
    n = E.n
    for g in range(m): cl.append([-E.x[g][n]])          # complete
    # picks p[i][g] for g in R_i ; at most one per agent, at most one agent per good
    p = [{g: new() for g in E.R[i]} for i in range(n)]
    for i in range(n):
        L = list(p[i].values())
        for a, b in itertools.combinations(L, 2): cl.append([-a, -b])
        for g, l in p[i].items(): cl.append([-l, E.x[g][i]])   # pick kept in bundle
    for g in range(m):
        L = [p[i][g] for i in range(n) if g in p[i]]
        for a, b in itertools.combinations(L, 2): cl.append([-a, -b])
    # order o[i][j]: i before j; total strict order
    o = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            o[i][j] = new(); o[j][i] = -o[i][j]
    for i, j, k in itertools.permutations(range(n), 3):
        cl.append([-o[i][j], -o[j][k], o[i][k]])
    # q[j][g][i]: j picks g and j before i
    for i in range(n):
        Ri = sorted(E.R[i], key=lambda g: (-E.v[i][g], g))   # favourite first (ties by index)
        for r, g in enumerate(Ri):
            # if i does not pick any of Ri[0..r] (its goods ranked >= g), then g is picked by an agent before i
            better_or_eq = Ri[:r + 1]
            cond = [p[i][h] for h in better_or_eq]
            pickers = [j for j in range(n) if j != i and g in p[j]]
            qs = []
            for j in pickers:
                q = new(); qs.append(q)
                cl.append([-q, p[j][g]]); cl.append([-q, o[j][i]])
            cl.append(cond + qs)
            # and if i picks g, every better good is picked before i (covered by r-1 clause with cond) ok
    if extra: extra(E, p, o, cl)
    return E, p, o, cl
def solve(sets, vals, m):
    E, p, o, cl = build(sets, vals, m)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); mdl = S.get_model() if ok else None; S.delete()
    if not ok: return False, None
    pos = set(l for l in mdl if l > 0)
    asg = decode(E, mdl)
    Y = [next((g for g, l in p[i].items() if l in pos), None) for i in range(E.n)]
    order = sorted(range(E.n), key=lambda i: sum(1 for j in range(E.n) if j != i and ((o[j][i] > 0 and o[j][i] in pos) or (o[j][i] < 0 and -o[j][i] not in pos))))
    B = [[g for g in range(m) if asg[g] == i] for i in range(E.n)]
    assert efx0(E, B)
    # verify SD
    left = set(range(m))
    for i in order:
        av = [g for g in E.R[i] if g in left]
        best = max(av, key=lambda h: (E.v[i][h], -h)) if av else None
        assert best == Y[i], (i, best, Y[i])
        left.discard(best)
    return True, (order, Y, asg)
if __name__ == '__main__':
    d = json.loads(open(sys.argv[1]).read()) if not sys.argv[1].startswith('[') else json.loads(sys.argv[1])
    sets, vals = (d['sets'], d['vals']) if isinstance(d, dict) else (d[0], d[1])
    m = 1 + max(max(s) for s in sets)
    t0 = time.time(); ok, w = solve(sets, vals, m)
    print('SD-C', ok, 'n', len(sets), 'm', m, 'time %.1f' % (time.time() - t0))
    if ok: print('order', w[0]); print('picks', w[1])
