"""The one-dangerous-agent case of OC1 (k4/sdc.md §29).  Starts needing a chain whose dangerous set D (frozen agents
valuing junk) is a single agent k.  Canonical candidates: chains x_0 = k, x_1, ..., x_t in which each x_i (i >= 1)
wants the good it receives (v(B_{x_{i-1}}) > v(B_{x_i})) and takes no junk, the end x_t holds a pick nobody else wants,
and k takes H_0 (junk or goods of B_{x_t}).  Question: does some canonical chain repair (one-absorber completion)?
and does every one whose H_0 is k's best improving set?

    python3 k4/sdc/oc_d1.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from oc_absorb import extends_A

DF.CHAIN_ONLY = True

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/oc_d1.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 4: continue
        E = Enc(sets, vals, m); seenY = set()
        val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y in seenY: continue
            seenY.add(Y)
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            J = [g for g in range(m) if base[g] < 0]
            wants = lambda i, j: Y[j] is not None and ((Y[i] is None and E.v[i].get(Y[j], 0) > 0) or
                                                       (Y[i] is not None and E.v[i].get(Y[j], 0) > E.v[i][Y[i]]))
            wanted = lambda j: any(wants(i, j) for i in range(n) if i != j)
            D = [j for j in range(n) if wanted(j) and any(E.v[j].get(g, 0) > 0 for g in J)]
            if len(D) != 1 or extends_A(E, base, 1): continue
            k = D[0]; C['starts needing a chain with |D| = 1'] += 1
            B = DF.bundles(E, base)
            canon = []
            for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                for kind, path, H in ds:
                    if path[0] != k or len(path) < 2: continue
                    if any(H.get(i) for i in range(1, len(path))): continue
                    if wanted(path[-1]): continue
                    canon.append((b2, path, H.get(0, ())))
            C['  canonical chains exist'] += bool(canon)
            good = [c for c in canon if extends_A(E, c[0], 1)]
            C['  some canonical chain repairs'] += bool(good)
            if canon:
                bestv = max(val(k, c[2]) for c in canon)
                top = [c for c in canon if val(k, c[2]) == bestv]
                C['  every canonical chain with k\'s best H_0 repairs'] += all(extends_A(E, c[0], 1) for c in top)
                C['  some canonical chain with k\'s best H_0 repairs'] += any(extends_A(E, c[0], 1) for c in top)
            if not good and C['shown'] < 3:
                C['shown'] += 1; print('NO CANONICAL REPAIR', name, json.dumps((sets, vals)), 'picks', Y, 'k', k, flush=True)
    for k_ in sorted(C, key=str): print(k_, C[k_])
    print('time %.0f s' % (time.time() - t0))
