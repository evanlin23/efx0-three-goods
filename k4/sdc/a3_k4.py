"""Claim A3_4 (k4/sdc.md §12), on plain neediest-first runs pi (k <= 4).  Let o be pi's last agent, J the unpicked
goods.  Call a frozen agent x *hard* if some needer j of x (j prefers Y_x to Y_j) is not compensable: no own unpicked
good h of j has v_j(Y_j) + v_j(h) >= v_j(Y_x).  Call x *exposed* if some set T of x's goods inside J + {Y_o} has
v_x(T) > v_x(Y_x).  Claim: every hard exposed x had all its goods available at its turn (a block leader), and its only
such set T is the set of all its other goods (three goods, so cost 1).

    python3 k4/sdc/a3_k4.py screen|suite|cores:FILES N SEED"""
import sys, os, json, random, gzip, itertools, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order


def analyse(E, C, name, shown, r1=False):
    Y, pi = rule_order(E, 'need2', r1)
    o = pi[-1]; picked = set(g for g in Y if g is not None); J = set(range(E.m)) - picked
    pool = set(J) | ({Y[o]} if Y[o] is not None else set())
    # availability at each turn
    left = set(range(E.m)); avail = {}
    for i in pi:
        avail[i] = set(g for g in E.R[i] if g in left)
        if Y[i] is not None: left.discard(Y[i])
    for x in range(E.n):
        if x == o or Y[x] is None: continue
        needers = [j for j in range(E.n) if j != x and E.v[j].get(Y[x], 0) > (E.v[j][Y[j]] if Y[j] is not None else 0)]
        if not needers: continue
        def compensable(j):
            vy = E.v[j][Y[j]] if Y[j] is not None else 0
            return any(vy + E.v[j][h] >= E.v[j][Y[x]] for h in E.R[j] if h in J)
        hard = any(not compensable(j) for j in needers)
        own = [g for g in E.R[x] if g != Y[x] and g in pool]
        Ts = [T for r in range(1, len(own) + 1) for T in itertools.combinations(own, r) if sum(E.v[x][g] for g in T) > E.v[x][Y[x]]]
        Ts = [T for T in Ts if not any(set(U) < set(T) for U in Ts)]
        if not Ts: continue
        C['exposed frozen'] += 1
        if not hard: C['exposed frozen, all needers compensable'] += 1; continue
        C['hard exposed frozen'] += 1
        fresh = avail[x] == set(E.R[x])
        allothers = (len(Ts) == 1 and set(Ts[0]) == set(E.R[x]) - {Y[x]})
        cost1 = any(all(g in T for T in Ts) for g in own)       # one good meets every danger set
        C['hard exposed: cost 1 (one good meets every danger set)'] += cost1
        C['hard exposed: fresh and cost 1'] += (fresh and cost1)
        C['hard exposed: fresh at its turn'] += fresh
        C['hard exposed: only T = all its other goods'] += allothers
        if not (fresh and cost1) and C['shown'] < 4:
            C['shown'] += 1
            print('A3_4 VIOLATION', name, 'x', x, 'Y', Y, 'pi', pi, 'Ts', Ts, json.dumps(([E.R[i] for i in range(E.n)], [[E.v[i][g] for g in E.R[i]] for i in range(E.n)])))


if __name__ == '__main__':
    R1 = '--r1' in sys.argv; sys.argv = [a for a in sys.argv if a != '--r1']
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/a3_k4.py', *sys.argv[1:])
    if src in ('screen', 'suite'):
        items = instances(src)
    else:
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(s) for s in sets)))
    for name, sets, vals, m in items:
        analyse(Enc(sets, vals, m), C, name, None, R1)
    for k in sorted(C, key=str): print(k, C[k])
