"""OC1 for n = 2 agents, any k (brute force over all 2^m allocations; chains enumerated explicitly as in
kgen/verify_oc1.py, adapted to two agents).  Per order: picks extend with a one-absorber completion (at most one agent
gets two or more goods outside its base), or one chain t = 0 / t = 1 makes the bases extend so.

    python3 kgen/oc2.py SEED N MMIN MMAX"""
import sys, random, itertools, json, collections, time


def efx0(v, X):
    for i in range(2):
        j = 1 - i; own = sum(v[i][g] for g in X[i])
        if len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own: return False
    return True


def sd(v, order):
    m = len(v[0]); left = set(range(m)); y = [None, None]
    for i in order:
        av = [g for g in left if v[i][g] > 0]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); y[i] = g; left.discard(g)
    return y


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1): yield from itertools.combinations(xs, r)


def states(v, B, J):
    val = lambda i, S: sum(v[i][g] for g in S)
    for x in range(2):            # t = 0
        for H in subsets([g for g in J if v[x][g] > 0]):
            if H:
                nb = list(B); nb[x] = B[x] | frozenset(H); yield 0, nb
    for x0 in range(2):           # t = 1: x1 takes B_x0 + H1, x0 takes H0 from J + B_x1
        x1 = 1 - x0
        if not B[x0]: continue
        for H1 in subsets([g for g in J if v[x1][g] > 0]):
            n1 = B[x0] | frozenset(H1)
            if val(x1, n1) <= val(x1, B[x1]): continue
            pool = [g for g in J if g not in H1 and v[x0][g] > 0] + [g for g in B[x1] if v[x0][g] > 0]
            for H0 in subsets(pool):
                if H0 and val(x0, H0) > val(x0, B[x0]):
                    nb = [None, None]; nb[x0] = frozenset(H0); nb[x1] = n1; yield 1, nb


def one_abs(Xs, B):
    return any(all(B[i] <= X[i] for i in range(2)) and sum(len(X[i] - B[i]) >= 2 for i in range(2)) <= 1 for X in Xs)


def gen(rng, m):
    while True:
        v = []
        for i in range(2):
            kind = rng.random()
            S = [g for g in range(m) if rng.random() < (1.0 if kind < 0.4 else 0.6)]
            r = [0] * m
            for g, x in zip(S, rng.sample(range(1, 99), len(S))): r[g] = x
            v.append(r)
        if all(v[0][g] or v[1][g] for g in range(m)) and any(v[0]) and any(v[1]): return v


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 kgen/oc2.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = gen(rng, m)
        Xs = []
        for asg in itertools.product(range(2), repeat=m):
            X = [frozenset(g for g in range(m) if asg[g] == i) for i in range(2)]
            if efx0(v, X): Xs.append(X)
        for o in [(0, 1), (1, 0)]:
            y = sd(v, o); B = [frozenset([y[i]]) if y[i] is not None else frozenset() for i in range(2)]
            J = [g for g in range(m) if g not in y]
            C['starts'] += 1
            if one_abs(Xs, B): C['picks extend (one absorber)'] += 1; continue
            ok = {0: False, 1: False}
            for tt, nb in states(v, B, J):
                if not ok[tt] and one_abs(Xs, nb): ok[tt] = True
            C['repaired by t=0'] += ok[0]; C['repaired by t=1'] += ok[1]
            if not ok[1]:
                C['FAIL t>=1 form'] += 1
                if C['shown1'] < 3: C['shown1'] += 1; print('FAIL t>=1', json.dumps(v), 'order', o, 'picks', y, 't0 repairs', ok[0], flush=True)
            if not ok[0] and not ok[1]:
                C['FAIL t>=0 form'] += 1; print('FAIL t>=0', json.dumps(v), 'order', o, 'picks', y, flush=True)
    for k in sorted(C):
        if not k.startswith('shown'): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
