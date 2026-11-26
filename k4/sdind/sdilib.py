"""Brute-force completions for the induction along a serial-dictatorship order (k4/sd_induct.md).

Instances: sets[i] (goods of agent i), vals[i] (values, same order), m goods.  An instance object `Inst` keeps a dense
value matrix V (n x m, zero outside R_i).  Everything here is checked against the raw EFX0 definition
(v_i(X_i) >= v_i(X_j minus g) for all i != j, g in X_j), with no SAT and no shared code with k4/sdc/sdclib.py except
the instance sources.

Main entry points:
  sd(I, order)                       serial dictatorship (ties by good index, as in k4/sdc/sdc_orders.sd)
  completions(I, bases, maxabs)      every assignment of the unallocated goods (junk) to agents whose result is EFX0,
                                     with at most `maxabs` agents receiving two or more junk goods (None: no limit);
                                     numpy-vectorized over all n^|J| assignments
  efx0(I, bundles)                   raw check
  delete(I, agents, goods)           the sub-instance without these agents and goods (relabelled), with the maps
"""
import itertools
import numpy as np


class Inst:
    def __init__(self, sets, vals, m):
        self.sets = [list(s) for s in sets]
        self.vals = [list(v) for v in vals]
        self.n = len(sets)
        self.m = m
        self.V = np.zeros((self.n, m), dtype=np.int64)
        for i, (S, vv) in enumerate(zip(sets, vals)):
            for g, x in zip(S, vv):
                self.V[i, g] = x
        self.R = [set(g for g in S if self.V[i, g] > 0) for i, S in enumerate(sets)]

    def val(self, i, S):
        return int(sum(self.V[i, g] for g in S))

    def key(self):
        return (tuple(map(tuple, self.sets)), tuple(map(tuple, self.vals)), self.m)


def sd(I, order):
    """picks Y[i] (good or None) of serial dictatorship in `order`, and the junk (unpicked goods, sorted)"""
    left = set(range(I.m)); Y = [None] * I.n
    for i in order:
        av = [g for g in I.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (I.V[i, h], -h)); Y[i] = g; left.discard(g)
    return Y, sorted(left)


def efx0(I, B):
    for i in range(I.n):
        own = I.val(i, B[i])
        for j in range(I.n):
            if j == i or not B[j]: continue
            vs = [int(I.V[i, g]) for g in B[j]]
            if sum(vs) - min(vs) > own: return False
    return True


def threatened(I, B, i):
    """the agents j whose bundle threatens i (v_i(B_j minus g) > v_i(B_i) for some g)"""
    own = I.val(i, B[i]); out = []
    for j in range(I.n):
        if j == i or not B[j]: continue
        vs = [int(I.V[i, g]) for g in B[j]]
        if sum(vs) - min(vs) > own: out.append(j)
    return out


def completions(I, bases, maxabs=1, J=None, limit_assign=2_000_000):
    """bases: list of n lists (each agent's base).  J: the junk (default: goods in no base).  Returns (J, A) with A an
    int array (N, |J|) of the EFX0 assignments with at most maxabs absorbers (agents with >= 2 junk goods)."""
    n = I.n
    if J is None:
        used = set(g for b in bases for g in b)
        J = [g for g in range(I.m) if g not in used]
    j = len(J)
    if n ** j > limit_assign:
        raise ValueError('too many assignments: %d^%d' % (n, j))
    BIG = 10 ** 12
    # base values and base minima
    baseval = np.zeros((n, n), dtype=np.int64)       # [viewer i, holder k]
    basemin = np.full((n, n), BIG, dtype=np.int64)
    for k in range(n):
        for g in bases[k]:
            baseval[:, k] += I.V[:, g]
            basemin[:, k] = np.minimum(basemin[:, k], I.V[:, g])
    if j == 0:
        A = np.zeros((1, 0), dtype=np.int64)
    else:
        A = np.array(list(itertools.product(range(n), repeat=j)), dtype=np.int64)
    N = A.shape[0]
    W = I.V[:, J]                                     # (n viewers, j)
    S = np.broadcast_to(baseval, (N, n, n)).copy()
    MN = np.broadcast_to(basemin, (N, n, n)).copy()
    cnt = np.zeros((N, n), dtype=np.int64)
    ar = np.arange(N)
    for t in range(j):
        k = A[:, t]
        # add W[:, t] to column k for every viewer
        S[ar, :, k] += W[:, t][None, :]
        MN[ar, :, k] = np.minimum(MN[ar, :, k], W[:, t][None, :])
        cnt[ar, k] += 1
    own = S[:, np.arange(n), np.arange(n)]            # (N, n)
    nonempty = MN < BIG
    thr = np.where(nonempty, S - MN, 0)               # (N, viewer, holder)
    for i in range(n):
        thr[:, i, i] = 0
    ok = (thr <= own[:, :, None]).all(axis=(1, 2))
    if maxabs is not None:
        ok &= ((cnt >= 2).sum(axis=1) <= maxabs)
    return J, A[ok]


def bundles_of(bases, J, a):
    B = [list(b) for b in bases]
    for g, k in zip(J, a):
        B[k].append(g)
    return B


def delete(I, agents, goods):
    """sub-instance without `agents` and `goods`; returns (I2, amap, gmap) with amap[old agent] = new agent,
    gmap[old good] = new good"""
    agents = set(agents); goods = set(goods)
    keepA = [i for i in range(I.n) if i not in agents]
    keepG = [g for g in range(I.m) if g not in goods]
    gmap = {g: t for t, g in enumerate(keepG)}; amap = {i: t for t, i in enumerate(keepA)}
    sets = []; vals = []
    for i in keepA:
        S = [g for g in I.sets[i] if g in gmap]
        sets.append([gmap[g] for g in S]); vals.append([int(I.V[i, g]) for g in S])
    return Inst(sets, vals, len(keepG)), amap, gmap


def picks_base(I, Y):
    return [[Y[i]] if Y[i] is not None else [] for i in range(I.n)]


def wanted_by(I, Y, bases=None):
    """W[j] = the agents i != j that want j's base (v_i(B_j) > v_i(B_i)) -- for picks: v_i(Y_j) > v_i(Y_i)"""
    if bases is None: bases = picks_base(I, Y)
    W = [[] for _ in range(I.n)]
    for j in range(I.n):
        if not bases[j]: continue
        for i in range(I.n):
            if i != j and I.val(i, bases[j]) > I.val(i, bases[i]): W[j].append(i)
    return W
