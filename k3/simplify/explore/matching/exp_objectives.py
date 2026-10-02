"""Experiment 1: which base states complete, and do natural matching objectives pick one? Evidence only.

For every ranking profile (gen_small), enumerate every base state (common.py), and for each objective below the set
of optimal states. "all" = every optimal state completes (absorber + slot filling, some absorber); "some" = at least
one does. Singleton objectives (matchings) are followed by K3S's upgrade loop before completing.

  python3 exp_objectives.py N M [N M ...]
"""
import sys, os, collections, itertools
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from common import Base, states, completes, upgrade_loop, held
from test_k3s import gen_small

U = (0, 3, 2, 1, 4)        # utility of options 0 (nothing), a, b, c, {b, c}
V = (0, 4, 3, 2, 5)        # values 4, 3, 2 and b + c

def sig(opt):  # rank signature (#a, #b, #c)
    return (sum(o == 1 for o in opt), sum(o == 2 for o in opt), sum(o == 3 for o in opt))

def popular(rank, opt):
    tops = {r[0] for r in rank}
    for i, o in enumerate(opt):
        r = rank[i]
        if o == 1: continue
        s = next((g for g in r if g not in tops), None)
        if s is None:
            if o != 0: return False
        elif o == 0 or o == 4 or r[o - 1] != s: return False
    held_tops = {rank[i][0] for i, o in enumerate(opt) if o == 1}
    return held_tops == tops

SING = {
    'rankmax': lambda b: sig(b.opt),
    'card_rankmax': lambda b: (sum(o > 0 for o in b.opt),) + sig(b.opt),
    'maxweight': lambda b: sum(V[o] for o in b.opt),
    'popular': lambda b: popular(b.rank, b.opt),
}
GEN = {
    'sumU': lambda b: sum(U[o] for o in b.opt),
    'sumV': lambda b: sum(V[o] for o in b.opt),
    'minNA': lambda b: -len(b.NA),
    'minOverflow': lambda b: -b.overflow(),
    'sumV_minNA': lambda b: (sum(V[o] for o in b.opt), -len(b.NA)),
    'minNA_sumV': lambda b: (-len(b.NA), sum(V[o] for o in b.opt)),
    'leximin': lambda b: tuple(sorted(U[o] for o in b.opt)),
    'maxPairs_sumU': lambda b: (sum(o == 4 for o in b.opt), sum(U[o] for o in b.opt)),
}

def run(n, m):
    stats = {k: collections.Counter() for k in list(SING) + list(GEN)}
    first = {}
    tot = 0; nocomp = 0
    for _, _, rank in gen_small(n, m):
        tot += 1
        allst = [Base(rank, m, o) for o in states(rank)]
        val = [b for b in allst if b.valid]
        comp = {b.opt: completes(b) is not None for b in val}
        if not any(comp.values()): nocomp += 1
        sing = [b for b in allst if all(o < 4 for o in b.opt)]
        for name, f in SING.items():
            pool = sing if name != 'popular' else [b for b in sing if popular(rank, b.opt)]
            if name != 'popular':
                best = max(f(b) for b in pool); opt = [b for b in pool if f(b) == best]
            else:
                opt = pool
                if not opt: stats[name]['none'] += 1; continue
            res = []
            for b in opt:
                o2 = upgrade_loop(rank, b.opt, m); b2 = Base(rank, m, o2)
                res.append(b2.valid and completes(b2) is not None)
            stats[name]['all' if all(res) else ('some' if any(res) else 'no')] += 1
            if not any(res) and name not in first: first[name] = (rank, [b.opt for b in opt])
            if not all(res) and name + '/all' not in first: first[name + '/all'] = (rank, [b.opt for b in opt], res)
        for name, f in GEN.items():
            best = max(f(b) for b in val); opt = [b for b in val if f(b) == best]
            res = [comp[b.opt] for b in opt]
            stats[name]['all' if all(res) else ('some' if any(res) else 'no')] += 1
            if not any(res) and name not in first: first[name] = (rank, [b.opt for b in opt])
            if not all(res) and name + '/all' not in first: first[name + '/all'] = (rank, [b.opt for b in opt], res)
    print(f"n={n} m={m}: {tot} profiles; no valid base state completes: {nocomp}")
    for k, c in stats.items():
        print(f"  {k:16s} all={c['all']} some-not-all={c['some']} none={c['no']}" + (f" no-popular={c['none']}" if c['none'] else ''))
    for k, v in sorted(first.items()):
        print(f"  first failure {k}: {v}")
    sys.stdout.flush()

if __name__ == '__main__':
    a = list(map(int, sys.argv[1:]))
    for i in range(0, len(a), 2): run(a[i], a[i + 1])
