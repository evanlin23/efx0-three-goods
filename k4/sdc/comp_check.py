"""Kind (a) of k4/sdc.md §14: direct contests in NO's plain order whose loser j had need(j) <= 0 at time tau.  Is the
compensation intact at the end: j picked z2 (its second available good at tau), z3 is unpicked, and j is not frozen
(so LB4r's need-shrinking upgrade gives j the good z3 and j stops preferring y)?  If not, why: z2 taken by a later agent,
z3 taken, or j frozen.

    python3 k4/sdc/comp_check.py screen|cores:FILES N SEED"""
import sys, os, json, random, gzip, collections
import _paths
from sdclib import Enc
from sdc_need import instances, score
from lemma_n_check import run

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/comp_check.py', *sys.argv[1:])
    if src == 'screen':
        items = instances(src)
    else:
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(s) for s in sets)))
    for name, sets, vals, m in items:
        E = Enc(sets, vals, m); Y, pi, snap, t_of = run(E, False)
        picked = set(g for g in Y if g is not None)
        def frozen_j(j):
            return Y[j] is not None and any(i != j and E.v[i].get(Y[j], 0) > (E.v[i][Y[i]] if Y[i] is not None else 0) for i in range(E.n))
        for x in range(E.n):
            if Y[x] is None: continue
            y = Y[x]; tau = t_of[x]; G = snap[tau]
            for j in range(E.n):
                if j == x or E.v[j].get(y, 0) <= (E.v[j][Y[j]] if Y[j] is not None else 0): continue
                av = sorted((g for g in E.R[j] if g in G), key=lambda h: (-E.v[j][h], h))
                if not av or av[0] != y: continue
                if score(E, j, G, 'need2') > 0: continue
                C['compensable direct contests'] += 1
                z2 = av[1] if len(av) > 1 else None; z3 = av[2] if len(av) > 2 else None
                if Y[j] != z2: C['  z2 not j\'s pick (taken by a later agent)'] += 1; continue
                if z3 is None or z3 in picked: C['  z3 picked by someone'] += 1; continue
                if frozen_j(j): C['  j frozen itself'] += 1; continue
                C['  intact: j can take z3 and stop needing y'] += 1
    for k in sorted(C, key=str): print(k, C[k])
