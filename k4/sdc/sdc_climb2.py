"""Adversarial climb against SD-C / SD-C-R1 with a graded score: s* = the largest slack s such that some SD outcome extends
to an allocation with v_i(X_i) >= v_i(X_j minus h) + s for all i, j, h (-1: SD-C fails), then the number of extendable
SD outcomes at slack s* (capped).  Minimize."""
import sys, json, random, time
from sdsat import build
from sdsat_r1 import r1extra
from sdc_climb import mutate, start, balanced
from pysat.solvers import Cadical153
CAP = 20
def cnt(sets, vals, m, r1, s):
    E, p, o, cl = build(sets, vals, m, extra=r1extra if r1 else None, slack=s)
    S = Cadical153(bootstrap_with=cl); c = 0
    allp = [l for i in range(E.n) for l in p[i].values()]
    while c < CAP and S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        S.add_clause([-l for l in allp if l in mdl] + [l for l in allp if l not in mdl]); c += 1
    S.delete(); return c
def score(sets, vals, r1, smax=6):
    m = 1 + max(max(x) for x in sets)
    c0 = cnt(sets, vals, m, r1, 0)
    if c0 == 0: return (-1, 0)
    s = 0; c = c0
    while s < smax:
        c2 = cnt(sets, vals, m, r1, s + 1)
        if c2 == 0: break
        s += 1; c = c2
    return (s, c)
if __name__ == '__main__':
    seed, n, steps, rounds, r1 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] == 'r1'
    rng = random.Random(seed); t0 = time.time()
    print('$ sdc_climb2', ' '.join(sys.argv[1:]), flush=True)
    for r in range(rounds):
        sets, vals = start(rng, n)
        sc = score(sets, vals, r1); best = sc
        for st in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n: continue
            sc2 = score(mu[0], mu[1], r1)
            if sc2 <= sc or rng.random() < 0.02:
                (sets, vals), sc = mu, sc2
                best = min(best, sc)
                if sc[0] < 0:
                    print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', sc, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
