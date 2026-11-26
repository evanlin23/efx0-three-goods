"""k = 3 test bed for Conjecture OC1 (k4/sdc.md §29; k4/k3_oc1.md).

Core case of Draft and Exchange (paper/k3-simple): every agent values exactly three goods a > b > c, strictly
balanced (a < b + c); goods valued by nobody ("dead goods") may exist.  Every comparison of subset sums of an
agent's goods is then fixed by its ranking (0 < c < b < a < b+c < a+c < a+b < a+b+c), so the values 4, 3, 2 are
without loss of generality, and everything here is exact for every strictly balanced profile with these rankings.

An instance is (rk, m): rk[i] = (a_i, b_i, c_i), the goods of agent i from best to worst; goods are 0..m-1.
A state is a tuple base[g] in {-1 (junk), 0..n-1}.

  sd(rk, m, order)        serial-dictatorship picks (= Draft and Exchange's draft in that order)
  efx0(rk, X)             raw EFX0 test of a complete allocation X (list of bundles)
  completion(rk, m, base, A=1)  a complete EFX0 allocation keeping every base in which at most A agents receive two or
                          more junk goods (every other agent at most one), or None; exhaustive search
  chains(rk, m, base)     every improving chain (k4/sdc.md §29, as in k4/sdc/de_free.py iter_chains): yields
                          (new_base, description)
"""
import itertools

VAL = (4, 3, 2)


def vals(rk):
    return [{g: VAL[t] for t, g in enumerate(r)} for r in rk]


def sd(rk, m, order):
    taken = set(); Y = [None] * len(rk)
    for i in order:
        for g in rk[i]:
            if g not in taken:
                Y[i] = g; taken.add(g); break
    return Y


def base_of(Y, m):
    b = [-1] * m
    for i, g in enumerate(Y):
        if g is not None: b[g] = i
    return tuple(b)


def bundles(base, n):
    B = [[] for _ in range(n)]
    for g, a in enumerate(base):
        if a >= 0: B[a].append(g)
    return B


def efx0(V, X):
    n = len(X)
    own = [sum(V[i].get(g, 0) for g in X[i]) for i in range(n)]
    for j in range(n):
        if len(X[j]) < 2: continue
        for i in range(n):
            if i == j: continue
            vs = [V[i].get(g, 0) for g in X[j]]
            if sum(vs) - min(vs) > own[i]: return False
    return True


def completion(rk, m, base, A=1, V=None):
    """exhaustive: absorbers are agents receiving >= 2 junk goods, at most A of them (A = 1 in OC1)"""
    n = len(rk); V = V or vals(rk)
    B = bundles(base, n); J = [g for g in range(m) if base[g] < 0]
    if not J:
        return B if efx0(V, B) else None
    # choose the absorber set (size <= A; size 0 included), then injective-or-absorbed assignment
    for k in range(0, A + 1):
        for abs_set in itertools.combinations(range(n), k):
            res = _assign(V, B, J, set(abs_set), n)
            if res is not None: return res
    return None


def _assign(V, B, J, absorbers, n):
    X = [list(b) for b in B]; used = [False] * n
    def rec(t):
        if t == len(J):
            if all(len(X[o]) - len(B[o]) >= 2 for o in absorbers) or True:
                return [list(x) for x in X] if efx0(V, X) else None
        g = J[t]
        for a in range(n):
            if a in absorbers:
                X[a].append(g); r = rec(t + 1); X[a].pop()
                if r is not None: return r
            elif not used[a]:
                used[a] = True; X[a].append(g); r = rec(t + 1); X[a].pop(); used[a] = False
                if r is not None: return r
        return None
    return rec(0)


def chains(rk, m, base, V=None, HMAX=3, BMAX=3):
    """every improving chain x0..xt (t >= 0): x0 takes H0 (t = 0: in addition to its base; t >= 1: in place of it,
    H0 from J and the end's base), x_i takes B_{x_{i-1}} + H_i (H_i from J); every agent on it gains strictly"""
    n = len(rk); V = V or vals(rk)
    B = bundles(base, n); J = [g for g in range(m) if base[g] < 0]
    val = lambda i, S: sum(V[i].get(g, 0) for g in S)
    def subsets(xs, lo=0):
        for r in range(lo, min(HMAX, len(xs)) + 1):
            yield from itertools.combinations(xs, r)
    out = []
    def ext(path, usedH, assign):
        x0 = path[0]; xt = path[-1]
        pool0 = [g for g in J if g not in usedH and V[x0].get(g, 0) > 0]
        if len(path) > 1: pool0 += [g for g in B[xt] if V[x0].get(g, 0) > 0]
        for H0 in subsets(pool0, 1):
            nb0 = (list(B[x0]) if len(path) == 1 else []) + list(H0)
            if len(nb0) > BMAX or val(x0, nb0) <= val(x0, B[x0]): continue
            nb = list(base)
            if len(path) > 1:
                for g in B[xt]: nb[g] = -1
                for i in range(len(path) - 1, 0, -1):
                    for g in B[path[i - 1]]: nb[g] = path[i]
                    for g in assign[i]: nb[g] = path[i]
            for g in H0: nb[g] = x0
            out.append((tuple(nb), (tuple(path), {0: H0, **assign})))
        if len(path) >= n or not B[xt]: return
        for y in range(n):
            if y in path: continue
            free = [g for g in J if g not in usedH and V[y].get(g, 0) > 0]
            for H in subsets(free):
                nby = list(B[xt]) + list(H)
                if len(nby) > BMAX or val(y, nby) <= val(y, B[y]): continue
                ext(path + [y], usedH | set(H), {**assign, len(path): H})
    for x in range(n): ext([x], frozenset(), {})
    return out
