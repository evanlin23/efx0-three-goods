"""Adversarial hill-climb against SD-C (or SD-C-R1): minimize the number of distinct serial-dictatorship pick vectors
that extend to an EFX0 allocation (capped).  0 = counterexample."""
import sys, os, json, random, time
import _paths
from sdsat import build
from sdsat_r1 import r1extra
from pysat.solvers import Cadical153
CAP = 40
def count(sets, vals, m, r1):
    E, p, o, cl = build(sets, vals, m, extra=r1extra if r1 else None)
    S = Cadical153(bootstrap_with=cl); c = 0
    allp = [l for i in range(E.n) for l in p[i].values()]
    while c < CAP and S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        on = [l for l in allp if l in mdl]
        S.add_clause([-l for l in on] + [l for l in allp if l not in mdl])
        c += 1
    S.delete(); return c
def balanced(V): return max(V) < sum(V) - max(V)
def mutate(sets, vals, rng):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    r = rng.random(); n = len(sets); m = 1 + max(max(s) for s in sets)
    i = rng.randrange(n)
    if r < 0.6:
        k = rng.randrange(len(sets[i])); vals[i][k] = max(1, vals[i][k] + rng.choice([-3, -2, -1, 1, 2, 3]))
    elif r < 0.75:
        a, b = rng.sample(range(len(sets[i])), 2); vals[i][a], vals[i][b] = vals[i][b], vals[i][a]
    elif r < 0.9:      # move one of i's goods to another good
        k = rng.randrange(len(sets[i])); g = rng.randrange(m + 1)
        if g in sets[i]: return None
        sets[i][k] = g
    else:              # add or drop a good of i
        if len(sets[i]) == 4:
            k = rng.randrange(4); sets[i].pop(k); vals[i].pop(k)
        else:
            g = rng.randrange(m + 1)
            if g in sets[i]: return None
            sets[i].append(g); vals[i].append(rng.randint(1, 12))
    if not balanced(vals[i]) or len(set(vals[i])) < len(vals[i]): return None
    used = sorted(set(g for s in sets for g in s)); ren = {g: k for k, g in enumerate(used)}
    sets = [[ren[g] for g in s] for s in sets]
    # every good valued by >= 1 (by construction); keep connected-ish: skip check
    return sets, vals
def start(rng, n):
    m = rng.randint(n + 3, 2 * n + 2)
    while True:
        sets = [sorted(rng.sample(range(m), rng.choice([3, 4]))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    vals = []
    for s in sets:
        while True:
            V = rng.sample(range(1, 13), len(s))
            if balanced(V): break
        vals.append(V)
    return sets, vals
if __name__ == '__main__':
    seed, n, steps, rounds, r1 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] == 'r1'
    rng = random.Random(seed); t0 = time.time()
    print('$ sdc_climb', ' '.join(sys.argv[1:]), flush=True)
    if len(sys.argv) > 6:
        seeds = [json.loads(l) for l in open(sys.argv[6])]
    for r in range(rounds):
        sets, vals = start(rng, n) if len(sys.argv) <= 6 else rng.choice(seeds)[:2]
        m = 1 + max(max(s) for s in sets)
        c = count(sets, vals, m, r1); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None: continue
            s2, v2 = mu; m2 = 1 + max(max(x) for x in s2)
            if len(s2) != n: continue
            c2 = count(s2, v2, m2, r1)
            if c2 <= c or rng.random() < 0.03:
                sets, vals, c = s2, v2, c2
                if c < best: best = c
                if c == 0:
                    print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
