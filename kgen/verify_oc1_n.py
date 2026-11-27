"""Independent replay of OC1 at one start for n agents (generalizes kgen/verify_oc1.py): pure Python, every complete
allocation (raw EFX0), every improving chain enumerated explicitly (every path x0..xt, t <= n-1, every choice of the
sets H as subsets of the allowed goods), then: does some EFX0 allocation complete the resulting bases with one
absorber?  Plus k4/sdc's SAT pipeline (hunt_n.sat_status).

    python3 kgen/verify_oc1_n.py '<json v>' 'o0,o1,...'"""
import sys, json, itertools


def efx0(v, X):
    n = len(v)
    for i in range(n):
        own = sum(v[i][g] for g in X[i])
        for j in range(n):
            if j != i and len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own:
                return False
    return True


def sd(v, order):
    m = len(v[0]); left = set(range(m)); y = [None] * len(v)
    for i in order:
        av = [g for g in left if v[i][g] > 0]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); y[i] = g; left.discard(g)
    return y


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1): yield from itertools.combinations(xs, r)


def chain_states(v, B, J):
    n = len(v); val = lambda i, S: sum(v[i][g] for g in S)
    for t in range(n):
        for path in itertools.permutations(range(n), t + 1):
            if any(not B[path[i]] for i in range(t)): continue
            def rec(i, used, newB):
                if i > t:
                    x0, xt = path[0], path[-1]
                    pool = [g for g in J if g not in used and v[x0][g] > 0]
                    if t >= 1: pool += [g for g in B[xt] if v[x0][g] > 0]
                    for H0 in subsets(pool):
                        if not H0: continue
                        nb0 = (B[x0] | frozenset(H0)) if t == 0 else frozenset(H0)
                        if val(x0, nb0) <= val(x0, B[x0]): continue
                        nb = list(newB); nb[x0] = nb0; yield t, nb
                    return
                xi, prev = path[i], path[i - 1]
                for H in subsets([g for g in J if g not in used and v[xi][g] > 0]):
                    nbi = B[prev] | frozenset(H)
                    if val(xi, nbi) <= val(xi, B[xi]): continue
                    nb = list(newB); nb[xi] = nbi
                    yield from rec(i + 1, used | set(H), nb)
            yield from rec(1, frozenset(), list(B))


def one_abs(Xs, B):
    n = len(B)
    for X in Xs:
        if all(B[i] <= X[i] for i in range(n)) and sum(1 for i in range(n) if len(X[i] - B[i]) >= 2) <= 1: return X
    return None


if __name__ == '__main__':
    v = json.loads(sys.argv[1]); order = tuple(map(int, sys.argv[2].split(','))); n, m = len(v), len(v[0])
    Xs = []
    for asg in itertools.product(range(n), repeat=m):
        X = [frozenset(g for g in range(m) if asg[g] == i) for i in range(n)]
        if efx0(v, X): Xs.append(X)
    y = sd(v, order); B = [frozenset([y[i]]) if y[i] is not None else frozenset() for i in range(n)]
    J = [g for g in range(m) if g not in y]
    print('picks', y, 'EFX0 allocations', len(Xs))
    X = one_abs(Xs, B); print('picks: one-absorber completion', [sorted(b) for b in X] if X else None)
    rep = {}; cnt = {}
    for t, nb in chain_states(v, B, J):
        cnt[t] = cnt.get(t, 0) + 1
        if t not in rep:
            X = one_abs(Xs, nb)
            if X: rep[t] = ([sorted(b) for b in nb], [sorted(b) for b in X])
    print('chain states per t', cnt, '| repairs per t', rep if rep else 'none')
    sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
    from hunt_n import sat_status
    orders = list(itertools.permutations(range(n)))
    print('SAT pipeline status for this order (0 picks extend, 1 one chain, None neither):', sat_status(v)[orders.index(order)])
