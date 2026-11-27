"""Which agent absorbs at the start (k4/sdc.md §29)?  For every order whose picks have a one-absorber completion
(oc_absorb.extends_A with A = 1), test whether no absorber is needed (A = 0), whether the last agent of the order can be
the absorber, and whether the last agent holding a pick nobody needs can.  This is the analogue of LB+'s Theorem A,
whose owner is the last agent that is neither frozen nor upgraded.

    python3 k4/sdc/oc_last.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from oc_absorb import extends_A
from oc_owner import absorbers

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/oc_last.py', *sys.argv[1:], flush=True)
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
        if n > 5: continue
        E = Enc(sets, vals, m)
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            if not extends_A(E, base, 1): continue
            C['orders with a one-absorber completion'] += 1
            ab = absorbers(E, base)
            if None in ab: C['  no absorber needed'] += 1; continue
            C['  an absorber is needed'] += 1
            last = o[-1]
            needed = lambda j: Y[j] is not None and any(Y[i] is None and E.v[i].get(Y[j], 0) > 0 or Y[i] is not None and E.v[i].get(Y[j], 0) > E.v[i][Y[i]] for i in range(n) if i != j)
            free = [j for j in o if not needed(j)]
            C['    the last agent can absorb'] += last in ab
            C['    the last agent with an unneeded pick can absorb'] += bool(free) and free[-1] in ab
            C['    some agent with an unneeded pick can absorb'] += any(j in ab for j in free)
            if last not in ab and (not free or free[-1] not in ab) and C['shown'] < 3:
                C['shown'] += 1; print('NEITHER', name, json.dumps((sets, vals)), 'order', o, 'picks', Y, 'absorbers', sorted(ab), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
