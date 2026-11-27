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
    if kind == 'pw':
        # PW-shaped (k4/ksens.md §1): f frozen agents, each valuing its pick p_j and K-1 goods of a pool (shared with
        # the other frozen agents, plus some private goods), W wanters valuing a random set of the p's above their q;
        # the remaining agents (if any) random.  Values: pool goods above half the pick, perturbed.
        f = rng.randint(2, max(2, n - 2)); W = rng.randint(1, max(1, n - f))
        npool = rng.randint(K - 1, K + 1); pool = list(range(f + W, f + W + npool)); nxt = f + W + npool
        sets, vals = [], []
        for j in range(f):
            own = rng.sample(pool, min(K - 1, npool))
            if rng.random() < 0.3 and own:
                own[rng.randrange(len(own))] = nxt; nxt += 1
            top = rng.randint(18, 24)
            V = [top] + [rng.randint(top // 2 + 1, top - 1) for _ in own]
            if not distinct(V): V = [top] + rng.sample(range(top // 2 + 1, top), len(own))
            sets.append([j] + own); vals.append(V)
        for i in range(W):
            ps = rng.sample(range(f), rng.randint(1, min(f, K - 1)))
            V = rng.sample(range(3, 15), len(ps)) + [rng.randint(1, 2)]
            sets.append(ps + [f + i]); vals.append(V)
        while len(sets) < n:
            k = rng.randint(2, K); S = rng.sample(range(nxt + 2), k)
            sets.append(S); vals.append(rng.sample(range(1, 25), k))
        return finish(sets, vals)
    if kind.startswith('pwfam'):    # a random PW(f, W, r) instance (fam_pw.py) with f + W = n, r = K - 1
        import fam_pw
        f = rng.randint(2, n - 1); W = n - f
        sets, vals, m = fam_pw.make(f, W, K - 1, rng)
        return sets, vals
    raise ValueError(kind)
