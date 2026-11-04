"""Need order with a chosen last agent (owner): for each agent o, put o last and order the others by the need rules of
sdc_need.py (R1 priority or plain).  Does some choice of o give an extendable SD outcome?  (n choices instead of n!.)

    python3 k4/sdc/sdc_need_owner.py screen|suite"""
import sys, os, collections
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need import score, instances


def order_with_last(E, kind, r1, o):
    left = set(range(E.m)); Y = [None] * E.n; done = []
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done and (i != o or len(done) == E.n - 1)]
        lost = [i for i in rest if any(g not in left for g in E.R[i])] if r1 else []
        cand = lost if lost else rest
        i = max(cand, key=lambda j: (score(E, j, left, kind), -j))
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i)
    return Y, done


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); fails = collections.defaultdict(list)
    print('$ python3 k4/sdc/sdc_need_owner.py', *sys.argv[1:])
    for name, sets, vals, m in instances(src):
        E = Enc(sets, vals, m); C['instances'] += 1
        for kind in ('need2', 'needall'):
            for r1 in (False,):
                ok = any(completable(E, order_with_last(E, kind, r1, o)[0]) for o in range(E.n))
                key = kind + (' R1' if r1 else ' plain'); C[key + ': some last agent works'] += ok
                if not ok: fails[key].append(name)
    for k in sorted(C, key=str): print(k, C[k])
    for k, v in fails.items(): print('fails', k, v[:10])
