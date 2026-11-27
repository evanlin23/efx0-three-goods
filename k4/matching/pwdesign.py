"""Instances of the PW design space at k = 4 (generator reimplemented from k4/ksens/pw4_search.py on claude/k4-ksens,
k4/ksens.md §5): f frozen agents x_j valuing their pick p_j (20) and a 3-subset of a pool D (|D| = d), every pair of
which beats 20; W wanters valuing a random nonempty subset of the p's (at most 3) above their own good; optionally one
extra agent valuing 2-4 random goods.  Here n <= NMAX (default 6) so that every official move can be enumerated."""
import random


def make(rng, FMAX=3, DMAX=5, WMAX=2):
    f = rng.randint(2, FMAX); W = rng.randint(1, WMAX); d = rng.randint(3, DMAX); E = rng.choice([0, 0, 1])
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + d)); nxt = f + W + d
    sets, vals = [], []
    for j in range(f):
        pool = sorted(rng.sample(D, 3))
        sets.append([j] + pool); vals.append([20] + rng.sample(range(11, 20), 3))
    for i in range(W):
        ps = rng.sample(P, rng.randint(1, min(3, f)))
        sets.append(ps + [Q[i]]); vals.append(rng.sample(range(3, 15), len(ps)) + [rng.randint(1, 2)])
    for e in range(E):
        S = rng.sample(range(nxt + 1), rng.randint(2, 4))
        sets.append(S); vals.append(rng.sample(range(1, 25), len(S)))
    used = sorted(set(g for s in sets for g in s)); ren = {g: k for k, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals, len(used)


def instances(seed, T):
    rng = random.Random(seed); out = []
    for t in range(T):
        sets, vals, m = make(rng)
        if max(len(s) for s in sets) <= 4: out.append(('pw%d' % t, sets, vals, m))
    return out
