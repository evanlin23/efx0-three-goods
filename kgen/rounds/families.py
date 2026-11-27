"""Instance families for the ROUND+ stress tests (kgen/rounds.md §2).  Every instance is a list of n rows of m
strictly positive integers (every agent values every good).

named()          the lifted known hard instances (PW5, RD5, kgen n = 4, GM4 family, CGM's barrier instance, tops3)
gen(kind, n, m, rng)   random families: generic, small (ties), ident, near, twotype, threetype, tops, pw, bigsmall,
                       lex (powers of two), corr (common value plus noise), pairs
lift(sets, vals)       zeros -> small positive values (k4/ksens.md §8 convention: x100, missing goods 1, 2, 3, ...)
"""
import random


def lift(sets, vals, m, scale=100, eps='seq', rng=None):
    rows = [[0] * m for _ in sets]
    for i, (s, v) in enumerate(zip(sets, vals)):
        for g, x in zip(s, v): rows[i][g] = scale * x
    for i in range(len(sets)):
        t = 1
        for g in range(m):
            if rows[i][g] == 0:
                rows[i][g] = t if eps == 'seq' else (rng.randint(1, eps) if rng else eps)
                t += 1
    return rows


def lift_rows(rows0, scale=100, eps='seq'):
    m = len(rows0[0])
    sets = [[g for g in range(m) if r[g] > 0] for r in rows0]
    vals = [[r[g] for g in s] for r, s in zip(rows0, sets)]
    return lift(sets, vals, m, scale, eps)


def pw_clean(f, W, r):
    """k4/ksens fam_ladder.clean: PW(f, W, r)"""
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)] + [P + [Q[i]] for i in range(W)]
    vals = [[20] + [19 - t for t in range(r)] for j in range(f)] + [[2 * (f - j) for j in range(f)] + [1] for i in range(W)]
    return sets, vals, f + W + r


RD5 = ([[1, 3, 5, 0, 4], [1, 2, 3], [1, 2, 3, 4], [2, 5, 0, 6]],
       [[57, 44, 33, 26, 24], [12, 11, 6], [9, 8, 6, 1], [53, 47, 36, 4]], 7)
KGEN_N4 = [[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]]
KGEN_N4_TIES = [[0, 155, 1, 0, 0, 155, 0], [0, 75, 2, 74, 0, 74, 77], [0, 0, 0, 2, 133, 0, 134], [1, 4, 0, 2, 0, 0, 0]]
CGM_BARRIER = [[8, 2, 12, 2, 0, 17, 1], [5, 0, 9, 4, 10, 0, 3], [0, 0, 0, 0, 9, 10, 2]]
GM4 = {   # k4/gm4_counterexample.py
    'A': [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 2, 3: 7, 5: 8, 6: 4}, {3: 6, 4: 3, 5: 4, 6: 8}],
    'B': [{0: 4, 2: 2, 5: 8, 6: 5}, {1: 3, 4: 6, 5: 8, 6: 10}, {2: 4, 3: 5, 4: 2, 6: 8}, {3: 5, 4: 4, 5: 8, 6: 2}],
    'C': [{0: 2, 2: 4, 5: 8, 6: 3}, {1: 2, 2: 4, 3: 7, 6: 10}, {1: 1, 4: 6, 5: 4, 6: 8}, {3: 8, 4: 6, 5: 10, 6: 3}],
    'D': [{0: 10, 2: 7, 4: 2, 5: 6}, {0: 8, 3: 4, 4: 1, 6: 6}, {1: 1, 2: 4, 5: 8, 6: 6}, {1: 3, 3: 6, 5: 10, 6: 2}],
    'E': [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}],
    'G': [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 3, 3: 6, 5: 8, 6: 4}, {3: 6, 4: 3, 5: 4, 6: 8}],
}


def dict_rows(ds, m):
    return [[d.get(g, 0) for g in range(m)] for d in ds]


def named():
    out = []
    s, v, m = pw_clean(3, 2, 4); out.append(('PW5-lift', lift(s, v, m)))
    for f, W, r in [(3, 2, 5), (4, 2, 5), (4, 3, 5)]:
        s, v, m = pw_clean(f, W, r); out.append(('PW(%d,%d,%d)-lift' % (f, W, r), lift(s, v, m)))
    s, v, m = RD5; out.append(('RD5-lift', lift(s, v, m)))
    out.append(('kgenN4-lift', lift_rows(KGEN_N4)))
    out.append(('kgenN4ties-lift', lift_rows(KGEN_N4_TIES)))
    out.append(('CGM-barrier-lift', lift_rows(CGM_BARRIER)))
    for k, ds in GM4.items(): out.append(('GM4-%s-lift' % k, lift_rows(dict_rows(ds, 7))))
    for m in (8, 9, 10):
        out.append(('tops3-m%d' % m, [[11 if g == i else 10 for g in range(m)] for i in range(3)]))
    for m in (8, 9, 10, 11):
        out.append(('tops4-m%d' % m, [[11 if g == i else 10 for g in range(m)] for i in range(4)]))
    return out


def gen(kind, n, m, rng):
    R = rng
    if kind == 'generic':
        return [R.sample(range(1, 10000), m) for _ in range(n)]
    if kind == 'small':
        return [[R.randint(1, 5) for _ in range(m)] for _ in range(n)]
    if kind == 'ident':
        r = R.sample(range(1, 1000), m); return [list(r) for _ in range(n)]
    if kind == 'near':
        r = [R.randint(100, 400) for _ in range(m)]
        return [[max(1, x + R.randint(-15, 15)) for x in r] for _ in range(n)]
    if kind == 'twotype':
        a = R.sample(range(1, 1000), m); b = R.sample(range(1, 1000), m)
        k = R.randint(1, n - 1); rows = [list(a)] * k + [list(b)] * (n - k)
        R.shuffle(rows); return [list(x) for x in rows]
    if kind == 'threetype':
        T = [R.sample(range(1, 1000), m) for _ in range(3)]
        return [list(T[R.randrange(3)]) for _ in range(n)]
    if kind == 'tops':
        V = [[R.randint(80, 120) for _ in range(m)] for _ in range(n)]
        for i in range(n): V[i][i] = R.randint(150, 300)
        return V
    if kind == 'pw':    # positive PW-like: frozen agents with a shared pool, wanters wanting their picks
        f = R.randint(2, max(2, n - 1)); W = n - f
        V = [[R.randint(1, 5) for _ in range(m)] for _ in range(n)]
        pool = list(range(n, m))
        for j in range(f):
            V[j][j] = 2000
            for g in pool: V[j][g] = R.randint(1100, 1900)
        for i in range(f, n):
            for j in range(f): V[i][j] = 1000 - 50 * j + R.randint(0, 20)
            V[i][i] = R.randint(300, 600)
        return V
    if kind == 'bigsmall':
        V = []
        for i in range(n):
            big = set(R.sample(range(m), R.randint(1, max(1, m // 3))))
            V.append([R.randint(500, 1000) if g in big else R.randint(1, 60) for g in range(m)])
        return V
    if kind == 'lex':
        V = []
        for i in range(n):
            p = list(range(m)); R.shuffle(p)
            V.append([2 ** p[g] + R.randint(0, 0) for g in range(m)])
        return V
    if kind == 'corr':
        c = [R.randint(50, 500) for _ in range(m)]
        return [[max(1, int(x * R.uniform(0.7, 1.3))) for x in c] for _ in range(n)]
    if kind == 'pairs':   # goods come in near-equal pairs per agent
        V = []
        for i in range(n):
            row = []
            for g in range(0, m, 2):
                x = R.randint(10, 500); row += [x, x + R.randint(-3, 3) or 1]
            V.append([max(1, x) for x in row[:m]])
        return V
    raise ValueError(kind)


KINDS = ['generic', 'small', 'ident', 'near', 'twotype', 'threetype', 'tops', 'pw', 'bigsmall', 'lex', 'corr', 'pairs']
