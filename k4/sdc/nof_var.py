"""Variants of NOF after its refutation (k4/sdc.md §16).  Order rules: neediest first by a need score of the available
goods y1 > y2 > y3 > ... ('need2' = y1 - y2 - y3, 'need1' = y1 - y2 (regret), 'needall' = y1 - rest), with or without
R1 priority.  Candidate sets: 'back' (the order, or it with one agent moved to the end: NOF), 'front' (one agent moved
to the front), 'both'.  Reports, per variant, the instances on which no candidate's picks extend.

    python3 k4/sdc/nof_var.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import completable, sd

SPECIAL = [('T3', [[5, 0, 4, 2], [3, 1, 4], [4, 1, 3, 0]], [[1, 38, 36, 6], [12, 22, 30], [28, 20, 12, 38]], 6),
           ('Q2', [[0, 1, 3, 4], [2, 3, 6, 7], [2, 5, 7], [4, 5, 6, 7]], [[2, 3, 10, 6], [2, 8, 3, 4], [2, 4, 3], [4, 8, 2, 3]], 8),
           ('r4253', [[0, 2, 5, 6], [1, 4, 6], [2, 3, 4, 5], [3, 4, 5, 6]], [[2, 4, 10, 7], [2, 4, 3], [4, 5, 8, 2], [2, 6, 10, 7]], 7),
           ('r3943', [[0, 1, 3, 4], [2, 3, 4, 5], [2, 3, 6], [2, 5, 6], [4, 5, 6]], [[6, 4, 1, 8], [6, 8, 5, 4], [3, 4, 2], [4, 2, 3], [4, 2, 3]], 7)]


def score(E, i, left, kind):
    av = sorted((E.v[i][g] for g in E.R[i] if g in left), reverse=True)
    if not av: return -10 ** 9
    if kind == 'need2': return av[0] - sum(av[1:3])
    if kind == 'need1': return av[0] - (av[1] if len(av) > 1 else 0)
    return av[0] - sum(av[1:])


def order(E, kind, r1):
    left = set(range(E.m)); Y = [None] * E.n; done = []
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done]
        lost = [i for i in rest if any(g not in left for g in E.R[i])] if r1 else []
        i = max(lost if lost else rest, key=lambda j: (score(E, j, left, kind), -j))
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i)
    return Y, done


VARIANTS = [(k, r1, c) for k in ('need2', 'need1', 'needall') for r1 in (False, True) for c in ('back', 'front', 'both')]


def test(E, kind, r1, cands):
    Y, pi = order(E, kind, r1)
    if completable(E, Y): return True
    orders = []
    if cands in ('back', 'both'): orders += [[i for i in pi if i != o] + [o] for o in pi]
    if cands in ('front', 'both'): orders += [[o] + [i for i in pi if i != o] for o in pi]
    return any(completable(E, sd(E, o)[0]) for o in orders)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); fails = collections.defaultdict(list); t0 = time.time()
    print('$ python3 k4/sdc/nof_var.py', *sys.argv[1:])
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
        E = Enc(sets, vals, m); C['instances'] += 1
        for var in VARIANTS:
            if not test(E, *var):
                C['%s %s %s: fails' % (var[0], 'R1' if var[1] else 'plain', var[2])] += 1; fails[var].append(name)
    for k in sorted(C): print(k, C[k])
    for var, l in fails.items():
        if len(l) <= 6: print('   ', var, l)
    print('time %.0f s' % (time.time() - t0))
