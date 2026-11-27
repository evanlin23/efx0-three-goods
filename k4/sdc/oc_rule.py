"""Is there a canonical repairing chain for OC1 (k4/sdc.md §29)?  For every order's start without a one-absorber
completion, rank all improving chains by a rule and test only the best one(s) (ties: all of the tied ones must work
for 'all-ties', some for 'some-tie'):
  junk : the most junk goods absorbed by the chain (|H_0 cap J| + sum |H_i|)
  gain : the largest total value gain of the chain agents
  junk-gain : junk, then gain
  short-junk : the shortest chain, then junk
  x0gain : the largest gain of x_0 alone

    python3 k4/sdc/oc_rule.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from oc_absorb import extends_A

DF.CHAIN_ONLY = True
RULES = {
    'junk': lambda f: (f['junk'],),
    'gain': lambda f: (f['gain'],),
    'junk-gain': lambda f: (f['junk'], f['gain']),
    'short-junk': lambda f: (-f['t'], f['junk']),
    'x0gain': lambda f: (f['g0'],),
}

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/oc_rule.py', *sys.argv[1:], flush=True)
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
            if extends_A(E, base, 1): continue
            C['distinct starts needing a chain'] += 1
            B = DF.bundles(E, base); J = set(g for g in range(m) if base[g] < 0)
            feats = []
            for b2, (kind, path, H) in DF.moves(E, base, describe=True).items():
                B2 = DF.bundles(E, b2)
                junk = sum(1 for g in range(m) if base[g] < 0 and b2[g] >= 0)
                gain = sum(val(i, B2[i]) - val(i, B[i]) for i in path)
                feats.append(({'junk': junk, 'gain': gain, 't': len(path) - 1, 'g0': val(path[0], B2[path[0]]) - val(path[0], B[path[0]])}, b2))
            ok = {b2: extends_A(E, b2, 1) for _, b2 in feats}
            for rn, key in RULES.items():
                best = max(key(f) for f, _ in feats)
                tied = [b2 for f, b2 in feats if key(f) == best]
                C[rn + ': some tied chain works'] += any(ok[b] for b in tied)
                C[rn + ': every tied chain works'] += all(ok[b] for b in tied)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
