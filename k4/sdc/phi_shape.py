"""Phi and LB4r's shape (k4/sdc.md §21).  D-shape: at most one bundle has more than two goods (Conjecture D's shape,
the shape of LB4r's outputs).  For small strict instances with at most K valued goods per agent, enumerate all EFX0
allocations and ask:
  (S1) does every Phi-maximizer among the D-shaped EFX0 allocations extend an SD outcome?
  (S2) is some Phi-maximizer among all EFX0 allocations D-shaped?
  (S3) is every Phi-maximizer among all EFX0 allocations D-shaped?

    python3 k4/sdc/phi_shape.py SEED T n M K"""
import itertools, random, sys, collections
from phi_check import efx0, fav, sd_consistent, Phi


def dshape(X): return sum(1 for B in X if len(B) > 2) <= 1


if __name__ == '__main__':
    seed, T, n, M, K = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/phi_shape.py', *sys.argv[1:], flush=True)
    for t in range(T):
        m = rng.randint(n, M); val = []
        for i in range(n):
            R = rng.sample(range(m), min(m, rng.randint(2, K))); vs = rng.sample(range(1, 80), len(R))
            val.append([vs[R.index(g)] if g in R else 0 for g in range(m)])
        if any(all(val[i][g] == 0 for i in range(n)) for g in range(m)): continue
        E = []
        for asg in itertools.product(range(n), repeat=m):
            X = [[g for g in range(m) if asg[g] == i] for i in range(n)]
            if efx0(val, X, n): E.append((Phi(val, X, n), dshape(X), X))
        if not E: C['no EFX0'] += 1; continue
        C['instances'] += 1
        D = [e for e in E if e[1]]
        if not D: C['no D-shaped EFX0 allocation'] += 1; print('NO D-SHAPE', val, flush=True); continue
        bd = max(p for p, _, _ in D); mxD = [X for p, _, X in D if p == bd]
        s1 = all(sd_consistent(val, X, n, m) for X in mxD)
        C['(S1) every Phi-max among D-shaped is SD-consistent'] += s1
        if not s1: print('S1 FAILS', val, [X for X in mxD if not sd_consistent(val, X, n, m)][0], flush=True)
        b = max(p for p, _, _ in E); mx = [(s, X) for p, s, X in E if p == b]
        C['(S2) some Phi-max is D-shaped'] += any(s for s, _ in mx)
        C['(S3) every Phi-max is D-shaped'] += all(s for s, _ in mx)
        C['Phi-max over D-shaped equals global Phi-max'] += bd == b
    for k in sorted(C): print(k, C[k])
