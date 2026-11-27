"""The fewest frozen agents over all orders (k4/sdc.md §30).  For each instance: f = the least number of frozen agents
(pick wanted by another agent) over all serial-dictatorship outcomes, i.e. over all Pareto-optimal matchings (Lemma
SDPO); and whether some outcome with f frozen agents has a one-absorber completion with no chain.

    python3 k4/sdc/min_frozen.py screen|suite|special|logs|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from oc_absorb import extends_A


def nfrozen(E, Y):
    def wants(i, j):
        if Y[j] is None or i == j: return False
        if Y[i] is None: return E.v[i].get(Y[j], 0) > 0
        return E.v[i].get(Y[j], 0) > E.v[i][Y[i]]
    return [j for j in range(E.n) if any(wants(i, j) for i in range(E.n))]


def load(src, argv):
    if src == 'special': return SPECIAL
    if src.startswith('cores:'):
        N, seed = int(argv[2]), int(argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
        return items
    if src == 'logs':
        import re, glob
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
        return items
    return instances(src)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/min_frozen.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 6: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        outs = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y not in outs: outs[Y] = len(nfrozen(E, Y))
        f = min(outs.values()); C['f = %d' % f] += 1
        ok = False
        for Y, k in outs.items():
            if k != f: continue
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            if extends_A(E, tuple(base), 1): ok = True; break
        C['f = %d: some min-frozen outcome has a one-absorber completion' % f] += ok
        if not ok: print('MIN-FROZEN FAILS', name, json.dumps((sets, vals)), 'f', f, flush=True)
        if f >= 2 and C['shown'] < 3:
            C['shown'] += 1; print('f >= 2', name, json.dumps((sets, vals)), f, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
