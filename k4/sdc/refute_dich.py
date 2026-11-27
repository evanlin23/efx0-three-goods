"""Independent replay (brute force, no SAT, no shared code) of the failure of the strict dichotomy of k4/sdc.md §29:
'for every order, the picks have a completion in which at most one agent receives two or more junk goods, or after
one improving chain the bases have a completion in which no agent receives two or more junk goods'.
Instance (n = 3, m = 7, found by k4/sdc/oc_climb.py dich): agent 0 values goods 0, 2, 4, 3 at 5, 10, 1, 12; agent 1
values 6, 3, 1 at 10, 12, 11; agent 2 values 1, 2, 0, 5 at 11, 8, 6, 1.  Order (0, 2, 1): picks 3, 6, 1.
The replay also confirms OC1 there: one chain gives bases with a completion with at most one absorber.

    python3 k4/sdc/refute_dich.py"""
import itertools

SETS = [[0, 2, 4, 3], [6, 3, 1], [1, 2, 0, 5]]
VALS = [[5, 10, 1, 12], [10, 12, 11], [11, 8, 6, 1]]
N, M = 3, 7
val = [dict(zip(S, V)) for S, V in zip(SETS, VALS)]
w = lambda i, B: sum(val[i].get(g, 0) for g in B)


def sd(order):
    left = set(range(M)); Y = [None] * N
    for i in order:
        av = [g for g in SETS[i] if g in left]
        if av:
            Y[i] = max(av, key=lambda g: val[i][g]); left.discard(Y[i])
    return Y


def efx0(X):
    for i in range(N):
        for j in range(N):
            if i != j and any(w(i, [g for g in X[j] if g != h]) > w(i, X[i]) for h in X[j]):
                return False
    return True


def completions(B, A):
    """complete EFX0 allocations keeping the bases B, with at most A agents receiving two or more junk goods"""
    J = [g for g in range(M) if not any(g in b for b in B)]
    for a in itertools.product(range(N), repeat=len(J)):
        cnt = [sum(1 for x in a if x == i) for i in range(N)]
        if sum(1 for c in cnt if c >= 2) > A: continue
        X = [list(B[i]) + [g for g, x in zip(J, a) if x == i] for i in range(N)]
        if efx0(X): return X
    return None


def chains(B):
    """every result of one improving chain x_0..x_t (t >= 1): x_0 takes H_0 (junk or goods of B_{x_t}, relevant to x_0)
    worth more than B_{x_0}; x_i takes B_{x_{i-1}} plus junk H_i (relevant to x_i) and gains; rest of B_{x_t} -> junk"""
    J = [g for g in range(M) if not any(g in b for b in B)]
    out = []
    for t in range(1, N):
        for xs in itertools.permutations(range(N), t + 1):
            pool = J + list(B[xs[-1]])
            for a in itertools.product(range(-1, t + 1), repeat=len(pool)):
                H = [[g for g, x in zip(pool, a) if x == i] for i in range(t + 1)]
                if any(g in B[xs[-1]] for i in range(1, t + 1) for g in H[i]): continue   # B_{x_t} goods only to x_0
                if any(val[xs[i]].get(g, 0) == 0 for i in range(t + 1) for g in H[i]): continue
                if not H[0] or w(xs[0], H[0]) <= w(xs[0], B[xs[0]]): continue
                if any(w(xs[i], list(B[xs[i - 1]]) + H[i]) <= w(xs[i], B[xs[i]]) for i in range(1, t + 1)): continue
                nb = [list(b) for b in B]
                nb[xs[0]] = list(H[0])
                for i in range(1, t + 1): nb[xs[i]] = list(B[xs[i - 1]]) + H[i]
                out.append((xs, H, nb))
    return out


if __name__ == '__main__':
    print('$ python3 k4/sdc/refute_dich.py')
    Y = sd((0, 2, 1)); B = [[y] if y is not None else [] for y in Y]
    print('order (0, 2, 1): picks', Y)
    print('one-absorber completion of the picks:', completions(B, 1))
    cs = chains(B); print('improving chains:', len(cs))
    zero = [c for c in cs if completions(c[2], 0) is not None]
    one = [c for c in cs if completions(c[2], 1) is not None]
    print('chains whose result has a completion with no absorber:', len(zero))
    print('chains whose result has a completion with at most one absorber (OC1):', len(one))
    if one: print('  e.g. chain', one[0][0], 'H', one[0][1], 'bases', one[0][2], 'completion', completions(one[0][2], 1))
    print('REFUTED: the strict dichotomy fails here' if completions(B, 1) is None and not zero else 'not refuted')
