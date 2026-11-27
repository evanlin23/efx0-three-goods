"""Brute force: is every Pareto-maximal partial EFX0 allocation (tie-break: most goods allocated) complete?"""
import sys, random, itertools
def efx0(n, v, B):
    # B: list of bundles (lists of goods); v[i][g]
    for i in range(n):
        vi = v[i]; own = sum(vi[g] for g in B[i])
        for j in range(n):
            if j == i or len(B[j]) < 2: continue
            s = sum(vi[g] for g in B[j]); mn = min(vi[g] for g in B[j])
            if s - mn > own: return False
    return True
def analyse(n, m, v):
    best = {}  # value vector -> max allocated
    allocs = []
    for asg in itertools.product(range(n + 1), repeat=m):
        B = [[] for _ in range(n)]
        for g, a in enumerate(asg):
            if a < n: B[a].append(g)
        if not efx0(n, v, B): continue
        u = tuple(sum(v[i][g] for g in B[i]) for i in range(n))
        na = sum(1 for a in asg if a < n)
        if best.get(u, -1) < na: best[u] = na
    U = list(best)
    pm = [u for u in U if not any(all(a >= b for a, b in zip(w, u)) and w != u for w in U)]
    comp = any(best[u] == m for u in U)
    bad = [u for u in pm if best[u] < m]
    ut = max(sum(u) for u in U); um = [u for u in U if sum(u) == ut]
    badut = [u for u in um if best[u] < m]
    lm = max(tuple(sorted(u)) for u in U); lmu = [u for u in U if tuple(sorted(u)) == lm]
    badlm = [u for u in lmu if best[u] < m]
    return comp, len(pm), bad, badut, badlm
def rand_inst(rng, n, m, k=4):
    while True:
        R = [sorted(rng.sample(range(m), rng.choice([3, 4][:k-2]))) for _ in range(n)]
        if set().union(*map(set, R)) == set(range(m)): break
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        while True:
            vals = rng.sample(range(1, 30), len(R[i]))
            if max(vals) < sum(vals) - max(vals): break
        for g, x in zip(R[i], vals): v[i][g] = x
    return R, v
if __name__ == '__main__':
    seed, n, m, T = map(int, sys.argv[1:5])
    rng = random.Random(seed); c = [0, 0, 0, 0, 0]
    for t in range(T):
        R, v = rand_inst(rng, n, m)
        comp, npm, bad, badut, badlm = analyse(n, m, v)
        c[0] += 1; c[1] += (not comp); c[2] += bool(bad); c[3] += bool(badut); c[4] += bool(badlm)
        if bad and c[2] <= 2: print('PARETO-BAD', R, v, bad[:3])
        if badut and c[3] <= 2: print('UTIL-BAD', R, v, badut[:3])
        if badlm and c[4] <= 2: print('LEXIMIN-BAD', R, v, badlm[:3])
    print('inst', c[0], 'noEFX0', c[1], 'paretoBad', c[2], 'utilBad', c[3], 'leximinBad', c[4])
