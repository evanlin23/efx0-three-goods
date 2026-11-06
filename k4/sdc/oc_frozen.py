"""The obstruction left by Theorem DT+ (k4/sdc.md §6, §29).  DT+: if no frozen agent (its pick wanted by another agent)
values an unpicked good, the picks have a one-absorber completion.  So every start that needs a chain under OC1 has
'dangerous' agents D: frozen agents valuing some junk good.  For every such start: |D|; whether some repairing chain
(one-absorber completion afterwards) passes through every agent of D; through at least one; whether some repairing
chain starts at an agent of D.

    python3 k4/sdc/oc_frozen.py screen|suite|special|cores:FILES N SEED"""
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
    print('$ python3 k4/sdc/oc_frozen.py', *sys.argv[1:], flush=True)
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
            J = [g for g in range(m) if base[g] < 0]
            wanted = lambda j: Y[j] is not None and any(
                (Y[i] is None and E.v[i].get(Y[j], 0) > 0) or (Y[i] is not None and E.v[i].get(Y[j], 0) > E.v[i][Y[i]])
                for i in range(n) if i != j)
            D = [j for j in range(n) if wanted(j) and any(E.v[j].get(g, 0) > 0 for g in J)]
            ok0 = extends_A(E, base, 1)
            C['distinct starts'] += 1
            C['distinct starts with no dangerous agent'] += not D
            if not D and not ok0: C['  DT+ VIOLATED (no dangerous agent, no one-absorber completion)'] += 1
            if ok0: continue
            C['starts needing a chain'] += 1; C['  |D| = %d' % len(D)] += 1
            rep = [path for b2, (kind, path, H) in DF.moves(E, base, describe=True).items() if extends_A(E, b2, 1)]
            C['  some repairing chain passes through all of D'] += any(set(D) <= set(p) for p in rep)
            C['  some repairing chain passes through some agent of D'] += any(set(D) & set(p) for p in rep)
            C['  some repairing chain starts in D'] += any(p[0] in D for p in rep)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
