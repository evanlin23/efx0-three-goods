"""Linear instances (two agents share at most one good), at most four goods per agent.  SD-C, and the owner-free form
"some SD outcome extends with every unpicked good given to one of its valuers".

    python3 k4/sdc/sdc_linear.py SEED N n"""
import sys, random, itertools, collections, json
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from pysat.solvers import Cadical153


def to_valuers(E, Y):
    cl = list(E.cl)
    for g in range(E.m): cl.append([-E.x[g][E.n]])
    picked = set(g for g in Y if g is not None)
    for i in range(E.n):
        if Y[i] is not None: cl.append([E.x[Y[i]][i]])
    for g in range(E.m):
        if g in picked: continue
        vals = [i for i in range(E.n) if g in E.v[i]]
        if vals:
            cl.append([E.x[g][i] for i in vals])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


if __name__ == '__main__':
    seed, N, n = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/sdc_linear.py', *sys.argv[1:])
    while C['instances'] < N:
        m = rng.randint(n + 2, 3 * n)
        sets = []
        ok = True
        for i in range(n):
            for _ in range(200):
                S = set(rng.sample(range(m), rng.choice([3, 4])))
                if all(len(S & set(T)) <= 1 for T in sets): break
            else:
                ok = False; break
            sets.append(sorted(S))
        if not ok or len(set().union(*map(set, sets))) < m: continue
        vals = []
        for s in sets:
            while True:
                V = rng.sample(range(1, 30), len(s))
                if max(V) < sum(V) - max(V): break
            vals.append(V)
        E = Enc(sets, vals, m)
        outs = set(tuple(sd(E, o)[0]) for o in itertools.permutations(range(n)))
        C['instances'] += 1
        C['SD-C'] += any(completable(E, list(Y)) for Y in outs)
        C['every SD outcome extends'] += all(completable(E, list(Y)) for Y in outs)
        C['some SD outcome extends with unpicked goods to valuers'] += any(to_valuers(E, list(Y)) for Y in outs)
    print(dict(C))
