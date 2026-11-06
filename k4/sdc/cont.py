"""Continuation test: walk values by unit steps; when an EFX0 allocation breaks, how far is the nearest EFX0 allocation of
the new values (number of goods that change owner)?"""
import sys, random, itertools, collections
from p1_brute import efx0
def all_efx0(n, m, v):
    out = []
    for asg in itertools.product(range(n), repeat=m):
        B = [[] for _ in range(n)]
        for g, a in enumerate(asg): B[a].append(g)
        if efx0(n, v, B): out.append(asg)
    return out
def dist(a, b): return sum(x != y for x, y in zip(a, b))
def balanced(vals): return max(vals) < sum(vals) - max(vals)
seed, n, m, T, L = map(int, sys.argv[1:6]); rng = random.Random(seed)
H = collections.Counter(); worst = None
for t in range(T):
    while True:
        R = [sorted(rng.sample(range(m), rng.choice([3, 4]))) for _ in range(n)]
        if set().union(*map(set, R)) == set(range(m)): break
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        while True:
            vals = rng.sample(range(1, 20), len(R[i]))
            if balanced(vals): break
        for g, x in zip(R[i], vals): v[i][g] = x
    E = all_efx0(n, m, v)
    for step in range(L):
        i = rng.randrange(n); g = rng.choice(R[i]); d = rng.choice([-1, 1])
        w = [row[:] for row in v]; w[i][g] += d
        if w[i][g] < 1 or not balanced([w[i][h] for h in R[i]]): continue
        E2 = all_efx0(n, m, w); S2 = set(E2)
        for X in E:
            if X in S2: continue
            dd = min(dist(X, Y) for Y in E2) if E2 else 99
            H[dd] += 1
            if worst is None or dd > worst[0]: worst = (dd, R, v, w, X)
        v, E = w, E2
print('repair distance histogram', sorted(H.items()))
print('worst', worst)
