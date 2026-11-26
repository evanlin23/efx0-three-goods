"""Random generators of three-agent additive instances (v[i][g] nonnegative integers), for kgen/ hunts.

kinds:
  klim:K     each agent values a random set of 2..K goods (values 1..99, distinct per agent); needs m <= 3K
  general    every good relevant to every agent (values 1..99, distinct per agent)
  zeros      every value 0 with probability 1/3, else 1..99 (distinct positive values per agent)
  ident      near-identical: a common vector plus small noise (distinct per agent)
  junk       each agent has 1-2 big goods and many small ones (values 1..9 for the small ones)
  ties       values in 1..4 (ties allowed: not a strict profile)
Every good is relevant to someone (a good nobody values is re-drawn)."""
import random


def _distinct(rng, k, lo, hi):
    return rng.sample(range(lo, hi + 1), k)


def gen(kind, m, rng):
    while True:
        v = [[0] * m for _ in range(3)]
        if kind.startswith('klim'):
            K = int(kind.split(':')[1])
            if m > 3 * K: raise ValueError('klim:%d covers at most %d goods' % (K, 3 * K))
            while True:
                size = [rng.randint(2, min(K, m)) for _ in range(3)]
                if sum(size) >= m: break
            S = [set() for _ in range(3)]
            for g in rng.sample(range(m), m):      # cover every good first
                i = rng.choice([a for a in range(3) if len(S[a]) < size[a]]); S[i].add(g)
            for i in range(3):
                while len(S[i]) < size[i]: S[i].add(rng.randrange(m))
                for g, x in zip(sorted(S[i]), _distinct(rng, len(S[i]), 1, 99)): v[i][g] = x
        elif kind == 'general':
            for i in range(3): v[i] = _distinct(rng, m, 1, 99)
        elif kind == 'zeros':
            for i in range(3):
                S = [g for g in range(m) if rng.random() > 1 / 3]
                for g, x in zip(S, _distinct(rng, len(S), 1, 99)): v[i][g] = x
        elif kind == 'ident':
            base = [rng.randint(5, 60) for _ in range(m)]
            for i in range(3):
                while True:
                    row = [max(1, b * 4 + rng.randint(-6, 6)) for b in base]
                    if len(set(row)) == m: break
                v[i] = row
        elif kind == 'junk':
            for i in range(3):
                big = rng.sample(range(m), rng.randint(1, 2))
                xs = _distinct(rng, m, 1, 40)
                v[i] = [x if g not in big else x + rng.randint(20, 80) for g, x in enumerate(xs)]
                for g in range(m):
                    if g not in big and rng.random() < 0.3: v[i][g] = 0
                pos = [x for x in v[i] if x > 0]
                if len(set(pos)) < len(pos):
                    v[i] = [0] * m
        elif kind == 'ties':
            for i in range(3): v[i] = [rng.choice([0, 1, 1, 2, 3, 4]) for _ in range(m)]
        else:
            raise ValueError(kind)
        if all(any(v[i][g] > 0 for i in range(3)) for g in range(m)) and all(any(r) for r in v):
            return v


def strict(v):
    return all(len(set(x for x in r if x > 0)) == sum(1 for x in r if x > 0) for r in v)
