"""Experiment 2 (fast, bitmask enumeration): for objectives over VALID base states (options nothing, a, b, c, {b, c}),
does every optimal state complete (absorber + slot filling, some absorber)? Evidence only.

  python3 exp_fast.py small N M            every ranking profile with N agents on M goods (gen_small)
  python3 exp_fast.py cores MAXN SAMPLE MINN   core_profiles(MAXN, sample=SAMPLE, minn=MINN)
  python3 exp_fast.py random K SEED MAXN   K random profiles, 2 <= n <= MAXN, m in n..2n+3

Objectives (larger is better; 'pareto' = Pareto-optimal for the utilities below among valid states):
  sumU     sum of utilities, nothing 0 < c 1 < b 2 < a 3 < {b, c} 4
  sumV     sum of values 4, 3, 2 ({b, c} = 5)
  minNA    fewest goods needed alone
  minOv    smallest overflow |junk| - slots
  leximin  leximin of the utilities
  pareto   every Pareto-optimal valid state
  minNA_sumU, sumU_minNA   lexicographic combinations
"""
import sys, os, collections, random, itertools
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from common import Base, completes

UT = (0, 3, 2, 1, 4)
VT = (0, 4, 3, 2, 5)
pc = int.bit_count

def options(r):
    a, b, c = (1 << r[0]), (1 << r[1]), (1 << r[2])
    # (opt, held, need, single)
    return [(0, 0, a | b | c, 0), (1, a, 0, a), (2, b, a, b), (3, c, a | b, c), (4, b | c, 0, 0)]

def valid_states(rank, m):
    n = len(rank); ops = [options(r) for r in rank]; out = []
    opt = [0] * n
    def rec(i, held, need, single):
        if i == n:
            if need & ~single == 0: out.append((tuple(opt), held, need))
            return
        for o, h, nd, s in ops[i]:
            if h & held: continue
            opt[i] = o; rec(i + 1, held | h, need | nd, single | s)
    rec(0, 0, 0, 0)
    return out

def features(rank, m, st):
    opt, held, need = st
    slots = 0
    for i, o in enumerate(opt):
        if o == 0: slots += 2
        elif o < 4 and not (need >> rank[i][o - 1]) & 1: slots += 1
    us = [UT[o] for o in opt]
    return dict(sumU=sum(us), sumV=sum(VT[o] for o in opt), minNA=-pc(need),
                minOv=-(m - pc(held) - slots), leximin=tuple(sorted(us)), us=us)

OBJ = {
    'sumU': lambda f: f['sumU'], 'sumV': lambda f: f['sumV'], 'minNA': lambda f: f['minNA'],
    'minOv': lambda f: f['minOv'], 'leximin': lambda f: f['leximin'],
    'minNA_sumU': lambda f: (f['minNA'], f['sumU']), 'sumU_minNA': lambda f: (f['sumU'], f['minNA']),
    'minOv_sumU': lambda f: (f['minOv'], f['sumU']),
}

def pareto(fs):
    idx = sorted(range(len(fs)), key=lambda k: -fs[k]['sumU']); keep = []
    for k in idx:
        u = fs[k]['us']
        if not any(all(x >= y for x, y in zip(fs[j]['us'], u)) and fs[j]['us'] != u for j in keep):
            keep.append(k)
    return keep

def one(rank, m, stats, first, names):
    sts = valid_states(rank, m); fs = [features(rank, m, s) for s in sts]
    cache = {}
    def comp(k):
        if k not in cache: cache[k] = completes(Base(rank, m, sts[k][0])) is not None
        return cache[k]
    for name in names:
        if name == 'pareto': opt = pareto(fs)
        else:
            f = OBJ[name]; best = max(f(x) for x in fs); opt = [k for k in range(len(fs)) if f(fs[k]) == best]
        res = [comp(k) for k in opt]
        key = 'all' if all(res) else ('some' if any(res) else 'none')
        stats[name][key] += 1
        if key != 'all' and (name, key) not in first:
            first[(name, key)] = (len(rank), m, rank, [(sts[k][0], r) for k, r in zip(opt, res)])

def report(title, tot, stats, first):
    print(title + f": {tot} profiles")
    for k, c in stats.items():
        print(f"  {k:12s} all-optima-complete={c['all']} some-but-not-all={c['some']} none={c['none']}")
    for k, v in sorted(first.items(), key=lambda kv: (kv[1][0], kv[1][1])):
        print(f"  first {k}: n={v[0]} m={v[1]} rank={v[2]} optima(opt, completes)={v[3][:8]}")
    sys.stdout.flush()

if __name__ == '__main__':
    from test_k3s import gen_small
    from lbx import core_profiles
    mode = sys.argv[1]; names = list(OBJ) + ['pareto']
    if len(sys.argv) > 5 and mode != 'cores': names = sys.argv[5].split(',')
    stats = {k: collections.Counter() for k in names}; first = {}; tot = 0
    if mode == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3])
        if len(sys.argv) > 4: names = sys.argv[4].split(','); stats = {k: collections.Counter() for k in names}
        for _, _, rank in gen_small(n, m): one(rank, m, stats, first, names); tot += 1
        report(f"small n={n} m={m}", tot, stats, first)
    elif mode == 'cores':
        N, S, lo = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        if len(sys.argv) > 5: names = sys.argv[5].split(','); stats = {k: collections.Counter() for k in names}
        for n, m, rank in core_profiles(N, sample=S, minn=lo): one(rank, m, stats, first, names); tot += 1
        report(f"cores n in [{lo},{N}] sample={S}", tot, stats, first)
    elif mode == 'random':
        K, seed, N = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); rng = random.Random(seed)
        for _ in range(K):
            n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 3)
            rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
            one(rank, m, stats, first, names); tot += 1
        report(f"random K={K} seed={seed} n<={N}", tot, stats, first)
