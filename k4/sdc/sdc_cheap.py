"""An explicit order rule for SD-C ("cheapest freezing first"): at every step, among the agents allowed by R1 priority
(agents that lost a good first), take the agent whose favourite remaining good y would be cheapest to protect if it were
frozen: the least number of its goods below y that must be kept out of a bundle so that the rest is worth at most y.
Ties: larger value of y relative to the rest, then index.  Does the SD outcome of this one order extend?

    python3 k4/sdc/sdc_cheap.py screen|suite|rand N SEED"""
import sys, os, json, glob, random, collections
import _paths
from sdclib import Enc
from sdc_orders import completable


def cost(E, i, left):
    av = sorted((g for g in E.R[i] if g in left), key=lambda g: (-E.v[i][g], g))
    if not av:
        return (0, 0, i)
    y = av[0]; low = sorted((E.v[i][g] for g in av[1:]), reverse=True)
    c = 0
    while sum(low[c:]) > E.v[i][y]:
        c += 1
    return (c, sum(low) - E.v[i][y], i)


def cheap_order(E, r1=True):
    left = set(range(E.m)); Y = [None] * E.n; done = []
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done]
        lost = [i for i in rest if any(g not in left for g in E.R[i])] if r1 else []
        cand = lost if lost else rest
        i = min(cand, key=lambda j: cost(E, j, left))
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i)
    return Y, done


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/sdc_cheap.py', *sys.argv[1:])
    insts = []
    if src == 'screen':
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        for name, I in screen_set():
            insts.append((name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m))
        os.chdir(cwd)
    elif src == 'suite':
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'k4/suite/instances/*.json'))):
            d = json.load(open(f))
            if d.get('vals') and d.get('sets'):
                insts.append((d.get('id'), d['sets'], d['vals'], d.get('m') or 1 + max(max(s) for s in d['sets'])))
    for name, sets, vals, m in insts:
        E = Enc(sets, vals, m)
        for r1 in (True, False):
            Y, order = cheap_order(E, r1)
            ok = completable(E, Y)
            C[('R1' if r1 else 'plain') + ' rule extends'] += ok
            if not ok and C['shown' + str(r1)] < 3:
                C['shown' + str(r1)] += 1; print('FAIL', 'R1' if r1 else 'plain', name, len(sets), m)
        C['instances'] += 1
    print(dict((k, v) for k, v in C.items() if not k.startswith('shown')))
