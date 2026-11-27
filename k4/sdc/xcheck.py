"""Cross-check: the SAT encodings (sdsat, sdsat_r1) enumerate exactly the extendable SD pick vectors found by explicit
order enumeration plus brute-force completion (all n^m allocations, raw EFX0 check pmax.efx0)."""
import sys, random, itertools, json
from p1_brute import efx0 as raw
from sdclib import Enc
from sdc_orders import sd
from sdsat import build
from sdsat_r1 import r1extra
from pysat.solvers import Cadical153
from p1_rand import rand_inst
def brute(sets, vals, m, r1):
    n = len(sets); E = Enc(sets, vals, m)
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, x in zip(sets[i], vals[i]): v[i][g] = x
    good = []
    for asg in itertools.product(range(n), repeat=m):
        B = [[] for _ in range(n)]
        for g, a in enumerate(asg): B[a].append(g)
        if raw(n, v, B): good.append(asg)
    res = set()
    for o in itertools.permutations(range(n)):
        Y = tuple(sd(E, o, r1)[0])
        if Y in res: continue
        if any(all(Y[i] is None or a[Y[i]] == i for i in range(n)) for a in good): res.add(Y)
    return res
def sat(sets, vals, m, r1):
    E, p, o, cl = build(sets, vals, m, extra=r1extra if r1 else None)
    S = Cadical153(bootstrap_with=cl); allp = [l for i in range(E.n) for l in p[i].values()]; res = set()
    while S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        Y = tuple(next((g for g, l in p[i].items() if l in mdl), None) for i in range(E.n)); res.add(Y)
        S.add_clause([-l for l in allp if l in mdl] + [l for l in allp if l not in mdl])
    S.delete(); return res
seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); bad = 0
for t in range(N):
    R, v = rand_inst(rng, n, m, [3, 4])
    vals = [[v[i][g] for g in R[i]] for i in range(n)]
    for r1 in (False, True):
        a, b = brute(R, vals, m, r1), sat(R, vals, m, r1)
        if a != b: bad += 1; print('MISMATCH', r1, json.dumps((R, vals)), sorted(a), sorted(b))
print('instances', N, 'mismatches', bad)
