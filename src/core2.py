"""Core instances: every agent has exactly 3 relevant goods a>b>c, balanced (a < b+c), <=1 private good.
Claim (ordinal characterization): in an allocation where every bundle has <= 2 goods, agent i is EFX0-safe iff
  T: i holds a | P: i holds b and c | B: i holds b, and a is alone in its bundle
  C: i holds c, and a, b are each alone | E: a, b, c are each alone in their bundles."""
import itertools, random
from pysat.solvers import Minisat22
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from lemmas import efx0

def balanced_values(n, m, trip, rng):
    v = [[0] * m for _ in range(n)]
    for i, (a, b, c) in enumerate(trip):
        cc = rng.uniform(1, 10); bb = cc + rng.uniform(0.01, 10); aa = bb + rng.uniform(0.01, cc - 0.01)
        v[i][a], v[i][b], v[i][c] = aa, bb, cc
    return v

def ordinal_safe(i, trip, X):
    a, b, c = trip[i]
    size = {}
    for g, o in enumerate(X): size[o] = size.get(o, 0) + 1
    alone = lambda g: size[X[g]] == 1
    return (X[a] == i or (X[b] == i and X[c] == i) or (X[b] == i and alone(a))
            or (X[c] == i and alone(a) and alone(b)) or (alone(a) and alone(b) and alone(c)))

def rand_core(n, m, rng, need_deg3=True, tries=200000):
    for _ in range(tries):
        sets = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
        deg = [0] * m
        for S in sets:
            for g in S: deg[g] += 1
        if min(deg) == 0: continue
        if need_deg3 and max(deg) < 3: continue
        if any(sum(1 for g in S if deg[g] == 1) > 1 for S in sets): continue
        trip = [tuple(rng.sample(S, 3)) for S in sets]          # random order a>b>c
        return trip
    return None

def c2_sat(n, m, trip, allow="TPBCE", maxsize=2):
    pool = IDPool(); x = lambda g, j: pool.id(('x', g, j)); s = lambda g: pool.id(('s', g))
    cls = []
    for g in range(m):
        cls += CardEnc.equals(lits=[x(g, j) for j in range(n)], bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    for j in range(n):
        cls += CardEnc.atmost(lits=[x(g, j) for g in range(m)], bound=maxsize, vpool=pool, encoding=EncType.seqcounter).clauses
    for g in range(m):
        for j in range(n):
            for h in range(m):
                if h != g: cls.append([-s(g), -x(g, j), -x(h, j)])
    for i, (a, b, c) in enumerate(trip):
        opts = []
        if 'T' in allow: opts.append(x(a, i))
        for tag, conds in (('P', [x(b, i), x(c, i)]), ('B', [x(b, i), s(a)]),
                           ('C', [x(c, i), s(a), s(b)]), ('E', [s(a), s(b), s(c)])):
            if tag in allow:
                y = pool.id((tag, i)); cls += [[-y, l] for l in conds]; opts.append(y)
        cls.append(opts)
    with Minisat22(bootstrap_with=cls) as S:
        if not S.solve(): return None
        mdl = set(l for l in S.get_model() if l > 0)
    return [next(j for j in range(n) if x(g, j) in mdl) for g in range(m)]

if __name__ == "__main__":
    rng = random.Random(3)
    # (a) ordinal characterization == EFX0 on all allocations with bundles <= 2 (random balanced values)
    mism = checked = 0
    for t in range(60):
        n, m = rng.choice([(3, 6), (4, 7), (4, 8)])
        trip = rand_core(n, m, rng, need_deg3=False)
        v = balanced_values(n, m, trip, rng)
        for X in itertools.product(range(n), repeat=m):
            if max(X.count(j) for j in range(n)) > 2: continue
            checked += 1
            if efx0(n, v, X) != all(ordinal_safe(i, trip, X) for i in range(n)): mism += 1
    print(f"[ordinal characterization] allocations checked={checked} mismatches={mism}")
    # (b) SAT decoder soundness + (c) how often size<=2 EFX0 exists / protected-only (T,P) exists, random cores
    for (n, m) in [(5, 9), (6, 10), (6, 11), (7, 11), (7, 12), (7, 13), (8, 12), (8, 14), (8, 15), (10, 16), (12, 20)]:
        tot = c2_fail = tp_fail = bad = 0
        for t in range(400):
            trip = rand_core(n, m, rng)
            if trip is None: continue
            tot += 1
            X = c2_sat(n, m, trip)
            if X is None: c2_fail += 1
            else:
                v = balanced_values(n, m, trip, rng)
                if not efx0(n, v, X): bad += 1
            if c2_sat(n, m, trip, allow="TP") is None: tp_fail += 1
        print(f"n={n:2d} m={m:2d}: cores={tot:3d}  no size<=2 EFX0 (C2 fails)={c2_fail}  "
              f"protected-only T/P fails={tp_fail}  decoded-but-not-EFX0={bad}")
