"""K4.SDC.K3 data: on profiles where LB+ (K3ALG's insertion rule) reaches the bad case and rotates, which choice of the
last block's leader gives an R1 order whose SD outcome extends to an EFX0 allocation (no rotation)?  The rest of Phase 1
is continued with R1 priority, ties and later insertions by index.  Reports the role of each working leader: the old
leader k*, an agent of a need chain from k*, the chain's end r, or another agent of the last block.

    python3 k4/sdc/k3_leader.py SEED N n m"""
import sys, random, collections, json
import _paths
import k3algo as K
from sdclib import Enc
from sdc_orders import completable


def phase1(E, prefix, leader):
    """Process prefix in order, then leader at an insertion step, then R1 priority by index."""
    left = set(range(E.m)); Y = [None] * E.n; done = set(); order = []
    def take(i):
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.add(i); order.append(i)
    for i in prefix: take(i)
    take(leader)
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done]
        lost = [i for i in rest if any(g not in left for g in E.R[i])]
        take(min(lost) if lost else min(rest))
    return Y, order


def last_block_start(E, order):
    left = set(range(E.m)); start = 0
    for t, i in enumerate(order):
        if all(g in left for g in E.R[i]): start = t
        av = [g for g in E.R[i] if g in left]
        if av: left.discard(max(av, key=lambda h: (E.v[i][h], -h)))
    return start


if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k3_leader.py', *sys.argv[1:])
    while C['bad case'] < N:
        vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
        v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
        X, info = K.fast(n, m, v)
        if not info['branch'].startswith('rot'): continue
        C['bad case'] += 1
        sets = [sorted(v[i]) for i in range(n)]; vals = [[v[i][g] for g in sets[i]] for i in range(n)]
        E = Enc(sets, vals, m)
        order = info['order']; s = last_block_start(E, order); prefix, B = order[:s], order[s:]
        kstar = order[s]; r = info['r']
        Y0, _ = phase1(E, prefix, kstar)
        C['old leader, R1 by index, extends'] += completable(E, Y0)
        work = []
        for y in [i for i in range(n) if i not in prefix]:
            Y, o2 = phase1(E, prefix, y)
            if completable(E, Y): work.append(y)
        C['some leader works'] += bool(work)
        roles = set()
        for y in work:
            roles.add('k*' if y == kstar else 'r' if y == r else 'B*' if y in B else 'other')
        for ro in roles: C['a working leader is ' + ro] += 1
        if not work and C['shown'] < 3:
            C['shown'] += 1; print('NO LEADER WORKS', json.dumps((sets, vals, order, info.get('r'))))
    print(dict(C))
