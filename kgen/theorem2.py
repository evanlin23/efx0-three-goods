"""Theorem 2 (kgen/n3.md §9): the two-agent OC1 completion, every k, zeros and ties included, by an explicit
O(m log m) construction.  Checked here against the raw EFX0 definition and the OC1 shapes (kgen/oc2.py's explicit
chain/completion test) on random instances.

Construction, order (a, b) (a picks first; y_a = a's pick, y_b = b's pick, ties to the smaller index):
  0. Degenerate cases: a values nothing -> X = (empty, M).  b values nothing -> X = (M, empty).  b values only y_a:
     X = ({y_a}, M - y_a) if v_a(y_a) >= v_a(M - y_a), else (M - y_a, {y_a}) (a chain a -> b).
  1. If v_b(y_a) > v_b(y_b): b cuts M by LPT_b (goods by decreasing v_b, ties by index, each to the poorer bundle,
     ties to the first bundle), a takes its favourite bundle (the one with y_a on ties), then a's goods worth 0 to a
     move to b (Lemma M).                                                           -> shape A1 or B
  2. Otherwise y_a is a top of a and y_b a top of b (v_b(y_b) >= v_b(g) for all g).  b cuts N' = M - {y_a, y_b} by
     LPT_b, a takes its favourite part, a's worthless goods of it move to b's part (Lemma M on N'), then each agent
     adds its own pick (the Tops Lemma).                                            -> shape A1

    python3 kgen/theorem2.py SEED N MMAX          random instances (generic, small integers, zeros, sparse)
    python3 kgen/theorem2.py exh VMAX MMAX        every valuation with entries in {0, ..., VMAX} and m <= MMAX"""
import sys, random, itertools, collections, json
from oc2 import efx0, sd, states, one_abs


def lpt(vc, goods):
    B = [set(), set()]; val = [0, 0]
    for g in sorted(goods, key=lambda h: (-vc[h], h)):
        s = 0 if val[0] <= val[1] else 1
        B[s].add(g); val[s] += vc[g]
    return B


def cut_choose(v, goods, cutter, chooser, prefer=None):
    P, Q = lpt(v[cutter], goods)
    vp, vq = sum(v[chooser][g] for g in P), sum(v[chooser][g] for g in Q)
    if vp > vq or (vp == vq and (prefer is None or prefer in P)): take, other = P, Q
    else: take, other = Q, P
    W = {g for g in take if v[chooser][g] == 0}              # Lemma M: the chooser envies nobody
    return take - W, other | W


def theorem2(v, order):
    a, b = order; m = len(v[0]); M = set(range(m)); y = sd(v, order); ya, yb = y[a], y[b]
    X = [None, None]
    if ya is None:
        X[a], X[b] = set(), set(M); return X
    if yb is None and v[b][ya] == 0:
        X[a], X[b] = set(M), set(); return X
    if yb is None:
        if v[a][ya] >= sum(v[a][g] for g in M - {ya}): X[a], X[b] = {ya}, M - {ya}
        else: X[a], X[b] = M - {ya}, {ya}
        return X
    if v[b][ya] > v[b][yb]:
        Xa, Xb = cut_choose(v, M, b, a, prefer=ya); X[a], X[b] = Xa, Xb; return X
    Sa, Sb = cut_choose(v, M - {ya, yb}, b, a)
    X[a], X[b] = Sa | {ya}, Sb | {yb}
    return X


def efx0_def(v, X):
    """EFX0 straight from the definition: v_i(X_i) >= v_i(X_j minus g) for every j != i and every g in X_j"""
    for i in range(2):
        for j in range(2):
            if i != j:
                for g in X[j]:
                    if sum(v[i][h] for h in X[i]) < sum(v[i][h] for h in X[j] if h != g): return False
    return True


def oc1_shape(v, order, X):
    """X is a one-absorber completion of the picks, or of the bases after one chain (t >= 0; kgen/oc2.py's moves)"""
    m = len(v[0]); y = sd(v, order); B = [frozenset([y[i]]) if y[i] is not None else frozenset() for i in range(2)]
    Xs = [[frozenset(X[0]), frozenset(X[1])]]
    if one_abs(Xs, B): return 'picks'
    J = [g for g in range(m) if g not in y]
    for t, nb in states(v, B, J):
        if one_abs(Xs, nb): return 't=%d' % t
    return None


def check(v, C, bad, mode):
    for order in [(0, 1), (1, 0)]:
        X = theorem2(v, order)
        assert sorted(X[0] | X[1]) == list(range(len(v[0]))) and not (X[0] & X[1])
        ok = efx0(v, X); assert ok == efx0_def(v, X)
        sh = oc1_shape(v, order, X) if ok else None
        C['%s: starts' % mode] += 1; C['%s: EFX0' % mode] += ok; C['%s: OC1 shape' % mode] += sh is not None
        if not (ok and sh) and len(bad) < 5: bad.append((v, order, [sorted(x) for x in X], ok))


if __name__ == '__main__':
    print('$ python3 kgen/theorem2.py', *sys.argv[1:], flush=True); C = collections.Counter(); bad = []
    if sys.argv[1] == 'exh':
        V, hi = int(sys.argv[2]), int(sys.argv[3])
        for m in range(1, hi + 1):
            for flat in itertools.product(range(V + 1), repeat=2 * m):
                check([list(flat[:m]), list(flat[m:])], C, bad, 'm=%d' % m)
        for k in sorted(C): print(C[k], k)
        for e in bad: print('FAILS', json.dumps(e))
        sys.exit()
    seed, N, hi = map(int, sys.argv[1:4]); rng = random.Random(seed)
    for t in range(N):
        m = rng.randint(1, hi); mode = ['generic', 'small', 'zeros', 'sparse'][t % 4]
        if mode == 'generic': v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        elif mode == 'small': v = [[rng.randint(1, 4) for _ in range(m)] for _ in range(2)]
        elif mode == 'zeros': v = [[rng.choice([0, 0, 1, 2, 3, 5, 8]) for _ in range(m)] for _ in range(2)]
        else: v = [[rng.randint(1, 50) if rng.random() < 0.3 else 0 for _ in range(m)] for _ in range(2)]
        check(v, C, bad, mode)
    for k in sorted(C): print(C[k], k)
    for e in bad: print('FAILS', json.dumps(e))
