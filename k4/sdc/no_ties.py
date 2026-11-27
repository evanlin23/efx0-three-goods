"""Conjecture NO under other tie-breaks: ties in the need score broken by a random fixed priority over agents (several
priorities per instance).  Does NO hold for every priority tried?

    python3 k4/sdc/no_ties.py screen|suite P SEED"""
import sys, random, collections
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need import score, instances


def order_prio(E, o, prio):
    left = set(range(E.m)); Y = [None] * E.n; done = []
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done and (i != o or len(done) == E.n - 1)]
        i = max(rest, key=lambda j: (score(E, j, left, 'need2'), -prio[j]))
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i)
    return Y


if __name__ == '__main__':
    src, P, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/no_ties.py', *sys.argv[1:])
    for name, sets, vals, m in instances(src):
        E = Enc(sets, vals, m); C['instances'] += 1; allok = True
        for p in range(P):
            prio = list(range(E.n)); rng.shuffle(prio)
            ok = any(completable(E, order_prio(E, o, prio)) for o in range(E.n))
            C['instance-priorities'] += 1; C['NO holds'] += ok; allok &= ok
            if not ok and C['shown'] < 4: C['shown'] += 1; print('FAIL', name, prio)
        C['NO holds for every priority tried'] += allok
    print(dict(C))
