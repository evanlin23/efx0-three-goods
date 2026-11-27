"""Adversarial hill-climb against matching domination (k4/sdc.md §28).  Objective of a profile: over the matchings
whose value vectors are Pareto-maximal among matchings, the least number of complete EFX0 allocations (distinct in
the agents' relevant bundles, capped at CAP) that value-dominate the matching, then how many matchings attain it.
Minimized; 0 = counterexample to MD.  Mutations as in sdc_climb.py (strict balanced agents, 3 or 4 goods).

    python3 k4/sdc/mdom_climb.py SEED N STEPS ROUNDS [pair1] [seeds:screen-2pair]
pair1: the objective over the partial EFX0 allocations with at most one two-good bundle (pdom.py) instead of matchings;
seeds:screen-2pair: start each round from a screen instance on which two-pair domination fails (pdom.py PAIRS = 2).
"""
import sys, os, json, random, time
import _paths
from sdclib import Enc
from sdc_climb import mutate, start
from mdom import matchings
from pysat.solvers import Cadical153
CAP = 6


def count_dom(E, Y):
    cl = list(E.cl)
    for g in range(E.m): cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        if Y[i] is None: continue
        t = E.v[i][Y[i]]
        for S, y in E.y[i].items():
            if E.val(i, S) < t: cl.append([-y])
    S = Cadical153(bootstrap_with=cl); c = 0
    ys = [y for i in range(E.n) for y in E.y[i].values()]
    while c < CAP and S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        S.add_clause([-y for y in ys if y in mdl]); c += 1
    S.delete(); return c


def count_dom_vec(E, u):
    cl = list(E.cl)
    for g in range(E.m): cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        for S, y in E.y[i].items():
            if E.val(i, S) < u[i]: cl.append([-y])
    S = Cadical153(bootstrap_with=cl); c = 0
    ys = [y for i in range(E.n) for y in E.y[i].values()]
    while c < CAP and S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        S.add_clause([-y for y in ys if y in mdl]); c += 1
    S.delete(); return c


PAIR1 = False


def objective(sets, vals):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    vecs = {}
    if PAIR1:
        from pdom import allocations, efx0_partial
        for B in allocations(E, 1):
            u = tuple(E.val(i, B[i]) for i in range(E.n))
            if u not in vecs and efx0_partial(E, B): vecs[u] = B
        top = [u for u in vecs if not any(w != u and all(a >= b for a, b in zip(w, u)) for w in vecs)]
        cs = [(count_dom_vec(E, u), u) for u in top]
        lo = min(c for c, _ in cs)
        return (lo, sum(1 for c, _ in cs if c == lo)), [vecs[u] for c, u in cs if c == lo][0]
    for Y in matchings(E):
        u = tuple(E.v[i][Y[i]] if Y[i] is not None else 0 for i in range(E.n)); vecs.setdefault(u, Y)
    top = [u for u in vecs if not any(w != u and all(a >= b for a, b in zip(w, u)) for w in vecs)]
    cs = [(count_dom(E, vecs[u]), u) for u in top]
    lo = min(c for c, _ in cs)
    return (lo, sum(1 for c, _ in cs if c == lo)), [vecs[u] for c, u in cs if c == lo][0]


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5])
    PAIR1 = 'pair1' in sys.argv[5:]
    rng = random.Random(seed); t0 = time.time()
    seeds = None
    if 'seeds:screen-2pair' in sys.argv[5:]:
        from sdc_need import instances
        from pdom import allocations, efx0_partial, dominated_vec
        seeds = []
        for name, ss, vv, m in instances('screen'):
            if len(ss) != n: continue
            E = Enc(ss, vv, m); vecs = {}
            for B in allocations(E, 2):
                u = tuple(E.val(i, B[i]) for i in range(E.n))
                if u not in vecs and efx0_partial(E, B): vecs[u] = B
            if any(not dominated_vec(E, u) for u in vecs): seeds.append((ss, vv))
        print('seeds', len(seeds), flush=True)
    print('$ python3 k4/sdc/mdom_climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        sets, vals = start(rng, n) if seeds is None else [list(map(list, x)) for x in rng.choice(seeds)]
        c, Y = objective(sets, vals); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None: continue
            s2, v2 = mu
            if len(s2) != n: continue
            c2, Y2 = objective(s2, v2)
            if c2 <= c or rng.random() < 0.03:
                sets, vals, c, Y = s2, v2, c2, Y2
                best = min(best, c)
                if c[0] == 0:
                    print('COUNTEREXAMPLE', json.dumps((sets, vals)), 'matching', Y, flush=True); break
        print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
