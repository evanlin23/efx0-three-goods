"""SD-C on multigraph instances (every good valued by at most two agents), at most four goods per agent: does SD-C hold,
and does EVERY order work?

    python3 k4/sdc/sdc_multigraph.py SEED N n"""
import sys, random, itertools, collections, json
import _paths
from sdclib import Enc
from sdc_orders import sd, completable

if __name__ == '__main__':
    seed, N, n = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/sdc_multigraph.py', *sys.argv[1:])
    while C['instances'] < N:
        # random multigraph: each agent gets 3 or 4 slots; goods are edges between two agents or private
        deg = [rng.choice([3, 4]) for _ in range(n)]
        sets = [[] for _ in range(n)]; g = 0
        stubs = [i for i in range(n) for _ in range(deg[i])]; rng.shuffle(stubs)
        while stubs:
            i = stubs.pop()
            js = [t for t, j in enumerate(stubs) if j != i and g not in sets[j]]
            if js and rng.random() < 0.85:
                j = stubs.pop(rng.choice(js)); sets[i].append(g); sets[j].append(g)
            else:
                sets[i].append(g)
            g += 1
        if any(len(s) < 3 for s in sets): continue
        vals = []
        for s in sets:
            while True:
                V = rng.sample(range(1, 30), len(s))
                if max(V) < sum(V) - max(V): break
            vals.append(V)
        E = Enc(sets, vals, g)
        outs = set(tuple(sd(E, o)[0]) for o in itertools.permutations(range(n)))
        ext = [completable(E, list(Y)) for Y in outs]
        C['instances'] += 1; C['SD-C'] += any(ext); C['every SD outcome extends'] += all(ext)
        if not any(ext): print('FAIL', json.dumps((sets, vals)), flush=True)
    print(dict(C))
