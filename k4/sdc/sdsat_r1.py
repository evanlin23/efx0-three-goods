"""SD-C restricted to R1-priority orders (an agent with all its goods still available is processed only when no
unprocessed agent has lost a good): LB-style Phase 1 outcomes with any insertion choices."""
import sys, json, itertools, time
from sdsat import build, decode, efx0
from pysat.solvers import Cadical153
def r1extra(E, p, o, cl):
    n = E.n
    top = [max(abs(l) for c in cl for l in c)]
    def new():
        top[0] += 1; return top[0]
    L = []
    for i in range(n):
        Li = new(); L.append(Li)
        qs = []
        for g in E.R[i]:
            for l in range(n):
                if l != i and g in p[l]:
                    q = new(); qs.append(q)
                    cl.append([-q, p[l][g]]); cl.append([-q, o[l][i]])
                    cl.append([q, -p[l][g], -o[l][i]])
        cl.append([-Li] + qs)
        for q in qs: cl.append([-q, Li])
    for i in range(n):
        for j in range(n):
            if i == j: continue
            for g in E.R[j]:
                for l in range(n):
                    if l in (i, j) or g not in p[l]: continue
                    # j after i, g picked by l before i  =>  i lost a good before its turn
                    cl.append([-o[i][j], -p[l][g], -o[l][i], L[i]])
def solve_r1(sets, vals, m):
    E, p, o, cl = build(sets, vals, m, extra=r1extra)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok
if __name__ == '__main__':
    import os
    import _paths; os.chdir(_paths.DE4)
    from ss_screen import screen_set
    c = [0, 0]
    for name, I in screen_set():
        vals = [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]
        ok = solve_r1(I.sets, vals, I.m); c[0] += 1; c[1] += (not ok)
        if not ok: print('NO-R1', name, I.n, I.m, json.dumps((I.sets, vals)), flush=True)
    print('SD-C-R1 instances', c[0], 'failures', c[1])
