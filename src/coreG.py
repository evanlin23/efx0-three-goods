"""General (any bundle size) exact model of EFX0 in a core. Balanced agent with a>b>c: the 8 subset sums are totally
ordered 0<c<b<a<b+c<a+c<a+b<a+b+c, so EFX0 is ordinal. Agent i is safe iff one of:
  T1/T2: holds a together with b or c | T3: holds a, and b,c are not together in any bundle of size >= 3
  P: holds b and c | B: holds b, a alone | C: holds c, a and b alone | E: a, b, c all alone."""
import itertools, random
from pysat.solvers import Minisat22
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from lemmas import efx0
from core2 import balanced_values, rand_core, c2_sat

def safe_general(i, trip, X):
    a, b, c = trip[i]
    size = {}
    for g, o in enumerate(X): size[o] = size.get(o, 0) + 1
    alone = lambda g: size[X[g]] == 1
    if X[a] == i and (X[b] == i or X[c] == i): return True
    if X[a] == i and not (X[b] == X[c] and size[X[b]] >= 3): return True
    return ((X[b] == i and X[c] == i) or (X[b] == i and alone(a))
            or (X[c] == i and alone(a) and alone(b)) or (alone(a) and alone(b) and alone(c)))

def general_sat(n, m, trip, forbid_size3_for_T=True):
    pool = IDPool(); x = lambda g, j: pool.id(('x', g, j)); s = lambda g: pool.id(('s', g))
    cls = []
    for g in range(m):
        cls += CardEnc.equals(lits=[x(g, j) for j in range(n)], bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    for g in range(m):
        for j in range(n):
            for h in range(m):
                if h != g: cls.append([-s(g), -x(g, j), -x(h, j)])
    for i, (a, b, c) in enumerate(trip):
        opts = []
        for tag, conds in (('T1', [x(a, i), x(b, i)]), ('T2', [x(a, i), x(c, i)]), ('P', [x(b, i), x(c, i)]),
                           ('B', [x(b, i), s(a)]), ('C', [x(c, i), s(a), s(b)]), ('E', [s(a), s(b), s(c)])):
            y = pool.id((tag, i)); cls += [[-y, l] for l in conds]; opts.append(y)
        y = pool.id(('T3', i)); cls.append([-y, x(a, i)]); opts.append(y)
        for j in range(n):
            for h in range(m):
                if h not in (b, c): cls.append([-y, -x(b, j), -x(c, j), -x(h, j)])
        cls.append(opts)
    with Minisat22(bootstrap_with=cls) as S:
        if not S.solve(): return None
        mdl = set(l for l in S.get_model() if l > 0)
    return [next(j for j in range(n) if x(g, j) in mdl) for g in range(m)]

if __name__ == "__main__":
    rng = random.Random(11)
    mism = checked = 0                           # general characterization vs definition, all allocations
    for t in range(40):
        n, m = rng.choice([(3, 6), (4, 7), (4, 8)])
        trip = rand_core(n, m, rng, need_deg3=False); v = balanced_values(n, m, trip, rng)
        for X in itertools.product(range(n), repeat=m):
            checked += 1
            if efx0(n, v, X) != all(safe_general(i, trip, X) for i in range(n)): mism += 1
    print(f"[general ordinal characterization] allocations={checked} mismatches={mism}")
    shown = False
    for (n, m) in [(5, 9), (6, 11), (7, 13), (8, 15), (9, 17), (10, 19)]:
        tot = f2 = fG = bad = 0
        for t in range(500):
            trip = rand_core(n, m, rng)
            if trip is None: continue
            tot += 1
            if c2_sat(n, m, trip) is not None: continue
            f2 += 1
            X = general_sat(n, m, trip)
            if X is None: fG += 1; print("NO EFX0 AT ALL?!", n, m, trip); continue
            if not efx0(n, balanced_values(n, m, trip, rng), X): bad += 1
            if not shown and n == 5:
                shown = True
                sizes = [X.count(j) for j in range(n)]
                print("  example size<=2 failure (agent: a>b>c):", trip)
                print("  its EFX0 allocation, bundles:", [[g for g in range(m) if X[g] == j] for j in range(n)], "sizes", sizes)
        print(f"n={n:2d} m={m:2d}: cores={tot}  size<=2 fails={f2}  of those with NO EFX0 at all={fG}  decode errors={bad}")
