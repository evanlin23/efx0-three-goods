"""k = 3: does EVERY R1-priority order's SD outcome extend (as LB+ without rotation would need), or only some?"""
import sys, random, itertools, collections, json
import _paths
import k3algo as K
from sdclib import Enc
from sdc_orders import sd, completable
seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
for t in range(N):
    vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
    sets = [sorted(P[i]) for i in range(n)]; vals = [[{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5}[g] for g in sets[i]] for i in range(n)]
    E = Enc(sets, vals, m); outs = set(tuple(sd(E, o, True)[0]) for o in itertools.permutations(range(n)))
    ext = [completable(E, list(Y)) for Y in outs]
    C['inst'] += 1; C['all R1 outcomes extend'] += all(ext); C['some extends'] += any(ext)
    if not all(ext) and C['shown'] < 2: C['shown'] += 1; print('NOT-ALL', json.dumps((sets, vals)), sum(ext), len(ext))
print(dict(C))
