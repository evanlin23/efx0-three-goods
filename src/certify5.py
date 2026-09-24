"""Independent certification: extract the witness allocation for every n=5 core profile and check it against the raw
EFX0 definition (lemmas.efx0) under two random balanced valuations realizing the ordering."""
import itertools, random, time, collections
from exhaust5 import reps_pi5, reps_pi4, build
from lemmas import efx0
rng = random.Random(5); t0 = time.time()
n, m = 5, 9
checked = bad = 0; dump_types = collections.Counter(); dump_sizes = collections.Counter()
for sets in reps_pi5() + reps_pi4():
    solvers = {md: build(n, m, sets, md) for md in ('C2', 'C3', 'G')}
    for prof in itertools.product(*[list(itertools.permutations(S)) for S in sets]):
        for md in ('C2', 'C3', 'G'):
            Sv, sel, x = solvers[md]
            if Sv.solve(assumptions=[sel[(i,) + prof[i]] for i in range(n)]): break
        mdl = set(l for l in Sv.get_model() if l > 0)
        X = [next(j for j in range(n) if x(g, j) in mdl) for g in range(m)]
        for _ in range(2):
            v = [[0.0] * m for _ in range(n)]
            for i, (a, b, c) in enumerate(prof):
                cc = rng.uniform(1, 10); bb = cc + rng.uniform(.01, 10); aa = bb + rng.uniform(.01, cc - .01)
                v[i][a], v[i][b], v[i][c] = aa, bb, cc
            checked += 1
            if not efx0(n, v, X): bad += 1
        if md == 'C3':
            j = max(range(n), key=lambda j: X.count(j)); a, b, c = prof[j]
            held = set(g for g in range(m) if X[g] == j)
            alone = lambda g: X.count(X[g]) == 1
            typ = ('holds a' if a in held else 'holds b,c' if {b, c} <= held else 'holds b (a alone)' if b in held and alone(a)
                   else 'holds c (a,b alone)' if c in held and alone(a) and alone(b) else 'holds none (all alone)')
            dump_types[typ] += 1; dump_sizes[X.count(j)] += 1
    for md in solvers: solvers[md][0].delete()
print(f"witness checks={checked} failures={bad} ({time.time()-t0:.0f}s)")
print("dump-bundle size:", dict(dump_sizes)); print("how the dump holder is safe:", dict(dump_types))
