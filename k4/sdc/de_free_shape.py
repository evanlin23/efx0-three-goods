"""Shapes of the repairing chains of de_free.py (k4/sdc.md §29).  For every order's serial-dictatorship start whose
picks do not extend, list the improving chains x_0 -> ... -> x_t after which the bases extend, and classify the
shortest one found: t, |H_0|, how many goods of H_0 come from B_{x_t}, whether a middle agent takes junk, and whether
x_0 is frozen in LB4r's sense (its pick needed by another agent).  Also: is some repairing chain a plain LB4r
rotation shape (no junk for x_1..x_t)?

    python3 k4/sdc/de_free_shape.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time(); DF.CHAIN_ONLY = True
    print('$ python3 k4/sdc/de_free_shape.py', *sys.argv[1:], flush=True)
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
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y in seenY: continue
            seenY.add(Y)
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            if DF.extends(E, base): continue
            C['starts whose picks do not extend'] += 1
            B = DF.bundles(E, base); J = set(g for g in range(m) if base[g] < 0)
            needed = set(g for i in range(n) for g in E.R[i] if Y[i] is not None and E.v[i][g] > E.v[i][Y[i]]) | \
                     set(g for i in range(n) if Y[i] is None for g in E.R[i])
            shapes = []
            for b2, (kind, path, H) in DF.moves(E, base, describe=True).items():
                if not DF.extends(E, b2): continue
                t = len(path) - 1; x0 = path[0]; H0 = H.get(0, ())
                fromEnd = sum(1 for g in H0 if t >= 1 and base[g] == path[-1])
                mid_junk = any(H.get(i) for i in range(1, len(path)))
                shapes.append((t, len(H0), fromEnd, mid_junk, Y[x0] in needed))
            if not shapes:
                C['no repairing chain'] += 1; continue
            C['some repairing chain gives no junk to x_1..x_t'] += any(not s[3] for s in shapes)
            C['some repairing chain starts at an agent whose pick is needed (frozen)'] += any(s[4] for s in shapes)
            best = min(shapes)
            C['shortest: t=%d |H_0|=%d (from B_end %d) middle junk %s x_0 needed %s' % best] += 1
    for k in sorted(C, key=lambda x: -C[x]): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
