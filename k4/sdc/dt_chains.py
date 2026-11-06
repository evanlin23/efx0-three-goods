"""Theorem DT after canonical chains (k4/sdc.md §30).  From the serial-dictatorship picks of an order:
  repeat: if some frozen agent x (its one-good base wanted by another agent) has junk worth more than its base
  ('excess'), apply a canonical chain from x: x_{i+1} = the first agent that wants the base of x_i, until the base of
  x_t is wanted by nobody; x takes a smallest improving set H_0 of goods of J + B_{x_t} that it values (ties: the most
  valuable); each x_i takes B_{x_{i-1}}; the rest of B_{x_t} becomes junk.  Every step is a Pareto improvement, so the
  loop stops.
With OWNER_RULE 'last' (default) the excess counts, besides the junk, the base of r, the last agent of the order
whose base is one good nobody wants (LB+'s owner), as in LB+'s bad case.
Then test for a one-absorber completion (oc_absorb.extends_A, A = 1).  Reports per start: the number of chains, whether
the final state completes, and whether it has a frozen agent with excess left (impossible) or a 3-good base.

    python3 k4/sdc/dt_chains.py screen|suite|special|logs|cores:FILES N SEED [order:nf]"""
import sys, os, json, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_orders import sd
from sdc_need import rule_order
from oc_absorb import extends_A
from min_frozen import load


OWNER_RULE = 'last'


def run(E, Y, maxsteps=50, order=None):
    n, m = E.n, E.m
    base = [-1] * m
    for i, g in enumerate(Y):
        if g is not None: base[g] = i
    val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
    steps = 0
    while steps < maxsteps:
        B = [[g for g in range(m) if base[g] == i] for i in range(n)]
        J = [g for g in range(m) if base[g] < 0]
        def wants(i, j):
            return i != j and len(B[j]) == 1 and E.v[i].get(B[j][0], 0) > val(i, B[i])
        frozen = [j for j in range(n) if any(wants(i, j) for i in range(n))]
        W_o = list(J)
        if OWNER_RULE == 'last' and order is not None:
            unw = [i for i in order if i not in frozen and len(B[i]) == 1]
            if unw: W_o = W_o + B[unw[-1]]
        exc = [x for x in frozen if val(x, [g for g in W_o if E.v[x].get(g, 0) > 0]) > val(x, B[x])]
        if not exc: return tuple(base), steps, B
        x = exc[0]; path = [x]
        while True:
            nxt = [i for i in range(n) if wants(i, path[-1]) and i not in path]
            if not nxt: break
            path.append(nxt[0])
        end = path[-1]
        pool = [g for g in J if E.v[x].get(g, 0) > 0] + ([g for g in B[end] if E.v[x].get(g, 0) > 0] if len(path) > 1 else [])
        best = None
        for r in range(1, len(pool) + 1):
            cands = [H for H in itertools.combinations(pool, r) if val(x, H) > val(x, B[x])]
            if cands: best = max(cands, key=lambda H: val(x, H)); break
        if best is None: return tuple(base), steps, None        # cannot happen when x has excess
        nb = list(base)
        if len(path) > 1:
            for g in B[end]: nb[g] = -1
            for i in range(len(path) - 1, 0, -1):
                for g in B[path[i - 1]]: nb[g] = path[i]
            for g in B[x]:
                if nb[g] == x: nb[g] = path[1]
        for g in best: nb[g] = x
        base = nb; steps += 1
    return tuple(base), steps, None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    NF = 'order:nf' in sys.argv
    print('$ python3 k4/sdc/dt_chains.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, [a for a in sys.argv if a != 'order:nf']):
        n = len(sets)
        if n > (9 if NF else 5): continue
        E = Enc(sets, vals, m); C['instances'] += 1; seen = {}
        orders = [rule_order(E, 'need2', False)[1]] if NF else list(itertools.permutations(range(n)))
        for od in orders:
            Y = tuple(sd(E, list(od))[0])
            if Y not in seen:
                b, steps, B = run(E, Y, order=od)
                ok = extends_A(E, b, 1) if B is not None else False
                seen[Y] = (ok, steps, B is not None and any(len(x) >= 3 for x in B))
            ok, steps, big = seen[Y]
            C['starts'] += 1; C['starts: chains used %d' % steps] += 1
            C['starts: completes'] += ok
            C['starts: a 3-good base at the end'] += big
            if not ok and C['shown'] < 4:
                C['shown'] += 1; print('FAILS', name, json.dumps((sets, vals)), 'order', od, 'chains', steps, flush=True)
        C['instances where some order completes'] += any(v[0] for v in seen.values())
        C['instances where every order completes'] += all(v[0] for v in seen.values())
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
