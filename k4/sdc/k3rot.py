import sys, random, collections, json
import _paths
import k3algo as K
from sdsat import build
from pysat.solvers import Cadical153
def po_inside(n, m, v, X):
    sets = [sorted(v[i]) for i in range(n)]; vals = [[v[i][g] for g in sets[i]] for i in range(n)]
    E, p, o, cl = build(sets, vals, m)
    for g in range(m): cl.append([E.x[g][X[g]]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok
seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
for t in range(N):
    vt = K.random_hard(n, m, rng)
    P = K.profile_of(vt, n, list(range(m)))
    v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
    X, info = K.fast(n, m, v)
    br = info.get('branch')
    if not br.startswith('rot'): C['norot'] += 1; continue
    ok = po_inside(n, m, v, X); C[(br, ok)] += 1
    if not ok and C['shown'] < 2: C['shown'] += 1; print('NOT-PO', json.dumps(([sorted(x.items()) for x in v], X, info)))
print(dict(C))
