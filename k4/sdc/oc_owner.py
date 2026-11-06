"""Who absorbs after OC1's chain (k4/sdc.md §29).  For every order's start that needs a chain under the one-absorber
completion (oc_absorb.py, A = 1), over all repairing chains x_0 -> ... -> x_t and all agents that can be the single
absorber of a completion of the result (an agent with two or more junk goods; 'none' if no agent needs to), classify
the absorber against the chain: 'x0', 'end' (x_t), 'mid', 'off', 'none'.  Per start: which classes occur.

    python3 k4/sdc/oc_owner.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from oc_absorb import extends_A
from pysat.solvers import Cadical153

DF.CHAIN_ONLY = True


def absorbers(E, base):
    """agents o such that some completion gives every agent other than o at most one junk good; None if A = 0 works"""
    J = [g for g in range(E.m) if base[g] < 0]
    if extends_A(E, base, 0): return {None}
    out = set()
    for o in range(E.n):
        cl = list(E.cl)
        for g in range(E.m):
            cl.append([-E.x[g][E.n]])
            if base[g] >= 0: cl.append([E.x[g][base[g]]])
        for i in range(E.n):
            if i == o: continue
            for g, h in itertools.combinations(J, 2): cl.append([-E.x[g][i], -E.x[h][i]])
        S = Cadical153(bootstrap_with=cl)
        if S.solve(): out.add(o)
        S.delete()
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/oc_owner.py', *sys.argv[1:], flush=True)
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
            if extends_A(E, base, 1): continue
            C['distinct starts needing a chain'] += 1
            cls = set()
            for b2, (kind, path, H) in DF.moves(E, base, describe=True).items():
                if not extends_A(E, b2, 1): continue
                for a in absorbers(E, b2):
                    cls.add('none' if a is None else 'x0' if a == path[0] else 'end' if a == path[-1] else 'mid' if a in path else 'off')
            for x in ('x0', 'end', 'mid', 'off', 'none'): C['some repair with absorber ' + x] += x in cls
            C['some repair with absorber x0 or none'] += bool(cls & {'x0', 'none'})
            if not cls & {'x0', 'none'} and C['shown'] < 3:
                C['shown'] += 1; print('NO x0 ABSORBER', name, json.dumps((sets, vals)), 'picks', Y, sorted(cls), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
