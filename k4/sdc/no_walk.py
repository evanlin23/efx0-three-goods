"""Owner walk for Conjecture NO: start from o = the last agent of the plain neediest-first run; while NO(o) does not
extend, move to an agent holding (in NO(o)) a good that o prefers to its own pick (o's 'needs').  Does some such
neighbour work at every failing step, and does the walk reach a working owner?  Also a breadth-first search over these
moves from the last agent.

    python3 k4/sdc/no_walk.py screen|suite|cores:FILES N SEED"""
import sys, os, json, random, gzip, collections
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need import instances, rule_order
from sdc_need_owner import order_with_last


def needs_holders(E, Y, o):
    vo = E.v[o][Y[o]] if Y[o] is not None else 0
    return [j for j in range(E.n) if j != o and Y[j] is not None and E.v[o].get(Y[j], 0) > vo]


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/no_walk.py', *sys.argv[1:])
    if src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed)
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        items = []
        for t in range(N):
            sets = rng.choice(cores); vals = random_profile(sets, rng)
            items.append(('r%d' % t, sets, vals, 1 + max(max(s) for s in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        E = Enc(sets, vals, m); C['instances'] += 1
        cache = {}
        def ok(o):
            if o not in cache: cache[o] = completable(E, order_with_last(E, 'need2', False, o)[0])
            return cache[o]
        o = rule_order(E, 'need2', False)[1][-1]; seen = {o}; steps = 0
        while not ok(o):
            Y = order_with_last(E, 'need2', False, o)[0]
            nb = [j for j in needs_holders(E, Y, o) if j not in seen]
            C['failing steps'] += 1; C['failing steps with a working neighbour'] += any(ok(j) for j in nb)
            good = [j for j in nb if ok(j)]
            if good: o = good[0]
            elif nb: o = nb[0]
            else: break
            seen.add(o); steps += 1
        C['walk reaches a working owner'] += ok(o)
        if not ok(o) and C['shown'] < 3: C['shown'] += 1; print('WALK FAILS', name, json.dumps((sets, vals)))
        # breadth-first search over the needs-holder graph from the last agent
        start = rule_order(E, 'need2', False)[1][-1]; frontier = [start]; reach = {start}
        while frontier:
            o2 = frontier.pop(0)
            if ok(o2): break
            for j in needs_holders(E, order_with_last(E, 'need2', False, o2)[0], o2):
                if j not in reach: reach.add(j); frontier.append(j)
        found = any(ok(x) for x in reach)
        C['search over needs-holders reaches a working owner'] += found
        if not found and C['shown2'] < 3: C['shown2'] += 1; print('SEARCH FAILS', name, json.dumps((sets, vals)))
    print(dict(C))
