"""Junk-rich instance generators at any k (k4/ksens.md).  An instance is (sets, vals) with goods 0..m-1, every good
valued by somebody, distinct values per agent.

  jr   : m in [2n, 3n]; each agent values K-1 or K goods; a few 'hot' goods are the tops of several agents (so many
         agents are frozen), the other goods are low-valued junk whose sum often exceeds the top
  hot1 : one hot good everybody ranks first, the rest junk (one frozen agent per order, many wanters)
  pairs: hot goods valued by pairs of agents, junk shared by pairs (want chains point both ways)
  unif : uniform random sets of size 2..K and uniform values (the generator of k4/sdc/de_free_bigk.py, with m >= 2n)
"""
import random


def finish(sets, vals):
    used = sorted(set(g for s in sets for g in s)); ren = {g: k for k, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals


def distinct(vals_list):
    return len(set(vals_list)) == len(vals_list)


def gen(kind, rng, n, K):
    if kind == 'unif':
        m = rng.randint(2 * n, 3 * n)
        while True:
            sets = [sorted(rng.sample(range(m), rng.randint(2, min(K, m)))) for _ in range(n)]
            if len(set().union(*map(set, sets))) == m: break
        return sets, [rng.sample(range(1, 60), len(s)) for s in sets]
    if kind == 'jr':
        nh = rng.randint(1, max(1, n - 2)); m = rng.randint(2 * n, 3 * n); m = max(m, nh + K)
        hot = list(range(nh)); rest = list(range(nh, m))
        sets, vals = [], []
        for i in range(n):
            k = rng.choice([K - 1, K]) if K > 2 else K
            nhi = rng.choice([1, 1, 1, 2]) if nh > 1 else 1
            S = rng.sample(hot, min(nhi, nh)) + rng.sample(rest, k - min(nhi, nh))
            top = rng.randint(20, 60)
            V = [top - 2 * t for t in range(min(nhi, nh))]
            lo = [rng.randint(1, top - 1) for _ in range(k - len(V))]
            while not distinct(V + lo): lo = [rng.randint(1, top - 1) for _ in range(k - len(V))]
            sets.append(S); vals.append(V + lo)
        return finish(sets, vals)
    if kind == 'hot1':
        m = rng.randint(2 * n, 3 * n)
        sets, vals = [], []
        for i in range(n):
            k = rng.choice([K - 1, K])
            S = [0] + rng.sample(range(1, m), k - 1)
            top = rng.randint(20, 60)
            lo = rng.sample(range(1, top), k - 1)
            sets.append(S); vals.append([top] + lo)
        return finish(sets, vals)
    if kind == 'pairs':
        m = rng.randint(2 * n, 3 * n)
        sets, vals = [], []
        nh = max(1, n // 2)
        for i in range(n):
            k = rng.choice([K - 1, K])
            h = [i % nh, (i + 1) % nh] if nh > 1 else [0]
            S = h + rng.sample(range(nh, m), k - len(h))
            top = rng.randint(20, 60)
            V = [top, top - rng.randint(1, 5)][:len(h)]
            lo = rng.sample(range(1, min(V)), k - len(h))
            sets.append(S); vals.append(V + lo)
        return finish(sets, vals)
    raise ValueError(kind)
