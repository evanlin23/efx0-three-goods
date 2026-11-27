"""Distinct tops: is there an EFX0 allocation in which every agent holds its top? (SD-C when all tops differ.)"""
import sys, os, random, json, collections
import _paths
from sdclib import Enc
from pysat.solvers import Cadical153
from de4lib import random_profile
def hold_tops(sets, vals, m):
    E = Enc(sets, vals, m); cl = list(E.cl)
    for g in range(m): cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        a = max(E.R[i], key=lambda g: (E.v[i][g], -g)); cl.append([E.x[a][i]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok
seed, N, n, kind = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed); C = collections.Counter()
while C['tested'] < N:
    m = rng.randint(n + 2, 3 * n)
    sizes = [3] if kind == 'k3' else [3, 4]
    sets = [sorted(rng.sample(range(m), rng.choice(sizes))) for _ in range(n)]
    if len(set().union(*map(set, sets))) != m: continue
    vals = random_profile(sets, rng)
    tops = [max(zip(v, s))[1] for s, v in zip(sets, vals)]
    if len(set(tops)) < n: continue
    C['tested'] += 1
    if not hold_tops(sets, vals, m):
        C['FAIL'] += 1
        if C['FAIL'] <= 3: print('FAIL', json.dumps((sets, vals)), flush=True)
print(kind, 'n', n, dict(C))
