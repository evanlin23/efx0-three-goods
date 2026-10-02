#!/usr/bin/env python3
"""Configurations at an f = 1 key, written from the definitions (workstream proof/k4-zmove-f1; k4/zmove_f1.md).
EVIDENCE tooling. Imports nothing from the repository.

Definitions used (k4/c4min.md §1, k4/c4min_reduce.md §1-2, k4/sx.md §1-2):
  a strict profile: agent i values the goods sets[i] with values vals[i] (all nonempty subset sums distinct);
  key (g, x): g the top of x, and the other agents have pairwise disjoint admissible sets A_y ⊆ U_y = R_y - {g};
  admissible A ⊆ U_y: 1 <= |A| <= 2 and every good of U_y - A is worth less than A;
  configuration Q at (g, x): pairwise disjoint pairs Q_y ⊆ M - {g} (y != x) with Q_y ∩ U_y admissible; pool L = rest
  (omega = |L| = m - 1 - 2(n - 1) goods);  H_y = Q_y ∩ U_y;  H_x = {g};  X_o = Q_o ∪ L;
  theta_w(Z) = max_{h in Z} v_w(Z - h);  Z threatens w holding B iff theta_w(Z) > v_w(B);
  robust y: v(Q_y) >= v(U_y - Q_y);  level l_y(S) = #{T ⊆ R_y : v(T) < v(S)};  r' = #robust, Lam' = sum l_y(H_y);
  terminal: free y with g in R_y and v_y(Q_y) < v_y(g);
  valid owner (k4/c4min.md §1 at f = 1): free o and C ⊆ X_o such that X_o - C contains an admissible set of o,
  |C| <= u (u = 1 iff nobody free other than o needs g and o does not need g from X_o - C, else 0), and X_o - C
  threatens nobody (x holding {g}, every other free y holding Q_y);  completable: some valid owner.
  By Lemma 0 of k4/sx.md, def*(g, x) > 0 iff no configuration at (g, x) is completable.

Everything is a bitmask over the goods.
"""
import gzip, itertools, json


def bits(S):
    g = 0
    while S:
        if S & 1: yield g
        S >>= 1; g += 1


def pc(S): return bin(S).count('1')


def mask(it):
    s = 0
    for g in it: s |= 1 << g
    return s


def sh(S): return '{' + ','.join(map(str, bits(S))) + '}'


class Prof:
    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(g for S in sets for g in S)
        self.sets = [list(S) for S in sets]
        self.vals = [list(V) for V in vals]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.R = [mask(S) for S in sets]
        self.ALL = (1 << self.m) - 1
        self.vt = []
        for i in range(self.n):
            t = {}
            gs = self.sets[i]
            for k in range(len(gs) + 1):
                for T in itertools.combinations(gs, k):
                    t[mask(T)] = sum(self.v[i][h] for h in T)
            sums = [t[s] for s in t if s]
            assert len(sums) == len(set(sums)), ('not strict', i)
            self.vt.append(t)
        self.lev = []
        for i in range(self.n):
            vs = sorted(self.vt[i].values())
            self.lev.append({S: vs.index(x) for S, x in self.vt[i].items()})

    def val(self, i, X): return self.vt[i][X & self.R[i]]

    def theta(self, w, Z):
        if not Z: return -1
        if Z & ~self.R[w]: return self.val(w, Z)
        return self.val(w, Z) - min(self.v[w][h] for h in bits(Z))

    def threatens(self, Z, w, B): return self.theta(w, Z) > self.val(w, B)

    def top(self, i): return max(self.sets[i], key=lambda h: self.v[i][h])

    def ordered(self, i, U):
        return sorted(bits(U & self.R[i]), key=lambda h: -self.v[i][h])

    def bigtop_on(self, i, g):
        if len(self.sets[i]) != 4 or self.top(i) != g: return False
        lo = self.ordered(i, self.R[i] & ~(1 << g))
        return self.v[i][g] > self.v[i][lo[0]] + self.v[i][lo[1]]

    def admissible(self, i, A, U):
        """A ⊆ U (U = U_i), 1 <= |A| <= 2, every good of U - A worth less than A"""
        A &= U
        if not A or pc(A) > 2: return False
        va = self.val(i, A)
        return all(self.v[i][h] < va for h in bits(U & ~A))

    def is_f0(self):
        """some pre-allocation with every agent need-free (then f = 0)"""
        n = self.n
        opts = []
        for i in range(n):
            gs = self.sets[i]; c = []
            for k in (1, 2):
                for T in itertools.combinations(gs, k):
                    B = mask(T); vb = self.val(i, B)
                    if all(self.v[i][h] < vb for h in bits(self.R[i] & ~B)): c.append(B)
            opts.append(c)
        order = sorted(range(n), key=lambda i: len(opts[i]))

        def rec(k, used):
            if k == n: return True
            for B in opts[order[k]]:
                if not B & used and rec(k + 1, used | B): return True
            return False
        return rec(0, 0)


class Key:
    """the configurations at an f = 1 key (g, x)"""

    def __init__(self, pr, g, x):
        self.pr = pr; self.g = g; self.x = x
        self.G = 1 << g
        self.free = [y for y in range(pr.n) if y != x]
        self.U = [pr.R[y] & ~self.G for y in range(pr.n)]
        self.Mp = pr.ALL & ~self.G
        self.omega = pr.m - 1 - 2 * (pr.n - 1)
        self.pairs = {}
        for y in self.free:
            c = []
            for a, b in itertools.combinations(list(bits(self.Mp)), 2):
                Qy = (1 << a) | (1 << b)
                if pr.admissible(y, Qy, self.U[y]): c.append(Qy)
            self.pairs[y] = c

    def configs(self):
        """yield dicts y -> Q_y"""
        fr = sorted(self.free, key=lambda y: len(self.pairs[y]))
        cur = {}

        def rec(k, used):
            if k == len(fr):
                yield dict(cur); return
            y = fr[k]
            for Qy in self.pairs[y]:
                if not Qy & used:
                    cur[y] = Qy
                    yield from rec(k + 1, used | Qy)
            cur.pop(y, None)
        yield from rec(0, 0)

    def is_key(self):
        """Lemma K of k4/c4min_reduce.md: g the top of x and disjoint admissible sets for the others"""
        pr = self.pr
        if pr.top(self.x) != self.g: return False
        opts = {}
        for y in self.free:
            c = []
            U = self.U[y]
            for k in (1, 2):
                for T in itertools.combinations(list(bits(U)), k):
                    A = mask(T)
                    if pr.admissible(y, A, U): c.append(A)
            opts[y] = c
        fr = sorted(self.free, key=lambda y: len(opts[y]))

        def rec(k, used):
            if k == len(fr): return True
            for A in opts[fr[k]]:
                if not A & used and rec(k + 1, used | A): return True
            return False
        return rec(0, 0)


class Conf:
    """one configuration Q at a key"""

    def __init__(self, K, Q):
        self.K = K; pr = K.pr; self.pr = pr
        self.Q = Q
        used = 0
        for q in Q.values(): used |= q
        self.L = K.Mp & ~used
        self.H = {y: Q[y] & K.U[y] for y in K.free}
        g = K.g
        self.robust = {y: pr.val(y, Q[y]) >= pr.val(y, K.U[y] & ~Q[y]) for y in K.free}
        self.rp = sum(self.robust.values())
        self.lam = sum(pr.lev[y][self.H[y]] for y in K.free)
        self.term = [y for y in K.free if pr.R[y] >> g & 1 and pr.val(y, Q[y]) < pr.v[y][g]]
        self.X = {o: Q[o] | self.L for o in K.free}
        # threat digraph among free agents, and on x
        self.thr = {o: [y for y in K.free if y != o and pr.threatens(self.X[o], y, Q[y])] for o in K.free}
        self.thx = {o: pr.threatens(self.X[o], K.x, K.G) for o in K.free}
        self.leaves = [o for o in K.free if not self.thr[o]]

    def pot(self): return (self.rp, self.lam)

    def holding(self, w):
        return self.K.G if w == self.K.x else self.Q[w]

    def bundle_safe(self, Z, owner, skip=()):
        """Z threatens nobody but the owner (and the agents in skip)"""
        pr = self.pr
        for w in range(pr.n):
            if w == owner or w in skip: continue
            if pr.threatens(Z, w, self.holding(w)): return False
        return True

    def completable(self):
        """some valid owner (k4/c4min.md §1 at f = 1, with the unfreezing clause)"""
        pr = self.pr; K = self.K; g = K.g
        for o in K.free:
            X = self.X[o]
            others_need = any(y != o for y in self.term)
            for C in [0] + [1 << h for h in bits(X)]:
                Z = X & ~C
                # Z contains an admissible set of o (the admissible part of Q_o unless C hits it)
                if C & self.H[o]:
                    ok = False
                    for k in (1, 2):
                        for T in itertools.combinations(list(bits(Z & K.U[o])), k):
                            if pr.admissible(o, mask(T), K.U[o]): ok = True; break
                        if ok: break
                    if not ok: continue
                if C:
                    if others_need: continue
                    if pr.R[o] >> g & 1 and pr.v[o][g] > pr.val(o, Z): continue
                if self.bundle_safe(Z, o): return (o, C)
        return None


def load(path):
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt') as fh:
        txt = fh.read()
    txt = txt.strip()
    if txt.startswith('['):
        for r in json.loads(txt): yield r
    else:
        for line in txt.splitlines():
            if line.strip(): yield json.loads(line)


def f1_keys(pr):
    """the f = 1 keys (g, x) of the profile (assumes f = 1)"""
    out = []
    for x in range(pr.n):
        g = pr.top(x)
        K = Key(pr, g, x)
        if K.is_key(): out.append(K)
    return out


def zmax(K):
    """all configurations, the Z′-maxima, and completability of the key"""
    best = None; mx = []; comp = False; allc = []
    for Q in K.configs():
        c = Conf(K, Q)
        allc.append(c)
        p = c.pot()
        if best is None or p > best: best = p; mx = [c]
        elif p == best: mx.append(c)
    return allc, mx


def noncompletable(allc):
    return all(c.completable() is None for c in allc)
