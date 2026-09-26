"""The suite's own model of the k = 4 objects (proof/k4-strategy; k4/strategy.md, k4/suite/README.md).

Written from the definitions only, sharing no code with k4/hall.c, k4/hall_check.py, k4/c4x.c, k4/c4x_check.py,
k4/c4min*.{c,py} (PR #41), k4/gap*.{c,py} (PR #53) or k4/red*.{c,py} (PR #51). The runner (k4/suite/run.py) compares it
with those tools where they implement the same object.

Definitions used (k4/c4x.md §1, k4/c4min.md §1 and §3.6 on PR #41, k4/hall.md §1):
- Inst(sets, vals): agent i values the goods sets[i] with the values vals[i]; every other good is worth 0 to i.
- threat(i, X, h): max over g in X of v_i(X \\ g) > h, i.e. v_i(X) - min_{g in X} v_i(g) > h (X nonempty).
- 𝒫: bases B_i ⊆ R_i, |B_i| <= 2, pairwise disjoint; needs N_i = {g in R_i \\ B_i : v_i(g) > v_i(B_i)};
  valid iff every needed good is a one-good base (V1, V2). Frozen: a one-good base that is needed.
  f = fewest frozen agents; omega = f - (2n - m); a key = (frozen agent -> its good) of a min-frozen P.
- removal-only deficit (k4/c4x.md §1): P is removal-only completable iff omega(P) <= 0, or some free o and C ⊆ J with
  X = B_o ∪ (J \\ C) threatening no x != o holding B_x and |C| <= slots of the agents other than o, the frozen status
  recomputed with o's needs taken from X.
- configurations (k4/c4min.md §1): at a key, U_i = R_i \\ 𝒩; each free agent y holds a pair Q_y ⊆ M \\ 𝒩 with
  Q_y ∩ U_y admissible (nonempty unless U_y is, <= 2 goods, every good of U_y outside it worth less than it); pool L.
  A free o is a valid owner if some C ⊆ X = Q_o ∪ L has: X \\ C contains an admissible set of o; |C| <= the number of
  frozen x whose good is needed by no agent other than o and not by o's needs from X \\ C; X \\ C threatens no x != o
  holding H_x ({phi(x)} for frozen x, Q_y for free y).
- potentials (k4/c4min.md §3.6, §4): t = #frozen x with v_x(L ∩ U_x) > v_x(phi(x)); r = #robust (frozen x:
  v_x(U_x) <= v_x(phi(x)); free y: v_y(Q_y) >= v_y(U_y \\ Q_y)); Lam = sum of levels of H_i ∩ R_i over R_i;
  p = sum over frozen x of |L ∩ U_x|; Phi' = (-t, r, Lam, -p).
- EFX0 (raw): v_i(X_i) >= v_i(X_j \\ h) for all i != j, h in X_j. Searched with an own SAT encoding (efx0_search).
"""
import itertools
from functools import lru_cache


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


class Inst:
    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(g for S in sets for g in S)
        self.sets = [list(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.R = [mask(S) for S in sets]
        self.ALL = (1 << self.m) - 1
        self._P = None

    @classmethod
    def from_json(cls, d): return cls(d['sets'], d['vals'], d.get('m'))

    # values
    def val(self, i, S):
        vi = self.v[i]; return sum(vi.get(g, 0) for g in bits(S))

    def threat(self, i, X, h):
        if not X: return False
        vi = self.v[i]; ws = [vi.get(g, 0) for g in bits(X)]
        return sum(ws) - min(ws) > h

    def needs(self, i, B):
        b = self.val(i, B); vi = self.v[i]
        return mask(g for g in bits(self.R[i] & ~B) if vi[g] > b)

    def level(self, i, S):
        s = self.val(i, S); gs = self.sets[i]; vi = self.v[i]
        return sum(1 for k in range(len(gs) + 1) for T in itertools.combinations(gs, k) if sum(vi[g] for g in T) < s)

    def top(self, i): return max(self.sets[i], key=lambda g: self.v[i][g])

    def admissible(self, i, A, U):
        """A ⊆ U, |A| <= 2, A nonempty unless U is empty, every good of U \\ A worth less than A"""
        if A & ~U or pc(A) > 2: return False
        if not A: return not U
        a = self.val(i, A)
        return all(self.v[i][g] < a for g in bits(U & ~A))

    # structure
    def private(self, i):
        others = 0
        for j in range(self.n):
            if j != i: others |= self.R[j]
        return self.R[i] & ~others

    def strict(self):
        for i in range(self.n):
            vs = [self.v[i][g] for g in self.sets[i]]
            sums = [sum(c) for k in range(1, len(vs) + 1) for c in itertools.combinations(vs, k)]
            if len(set(sums)) != len(sums): return False
        return True

    def connected(self):
        seen, stack = {0}, [0]
        while stack:
            i = stack.pop()
            for j in range(self.n):
                if j not in seen and self.R[i] & self.R[j]: seen.add(j); stack.append(j)
        return len(seen) == self.n

    def core_violations(self):
        """the conditions of a k = 4 core (K4.CORE, lean EFX.IsCore4) that fail; [] for a core"""
        bad = []
        if self.n < 2: bad.append('n<2')
        allR = 0
        for i in range(self.n):
            d = pc(self.R[i]); tot = self.val(i, self.R[i]); allR |= self.R[i]
            if not 3 <= d <= 4: bad.append(f'agent {i}: {d} goods')
            if any(2 * self.v[i][g] >= tot for g in self.sets[i]): bad.append(f'agent {i}: not strictly balanced')
            P = self.private(i)
            if pc(P) + 2 > d: bad.append(f'agent {i}: {pc(P)} private goods of {d}')
            if pc(P) == 2 and not self.val(i, P) < self.val(i, self.R[i] & ~P): bad.append(f'agent {i}: p + q >= s + t')
        if allR != self.ALL: bad.append('a good valued by nobody')
        if not self.connected(): bad.append('not connected')
        return bad

    # ---------------------------------------------------------------- the space P
    def preallocs(self):
        """every valid pre-allocation: list of (bases tuple, NA mask)"""
        if self._P is not None: return self._P
        n = self.n
        opts = []
        for i in range(n):
            gs = self.sets[i]
            opts.append([mask(c) for k in range(3) for c in itertools.combinations(gs, k)])
        nd = [{B: self.needs(i, B) for B in opts[i]} for i in range(n)]
        out = []
        def rec(i, used, Bs, NA, singles):
            if i == n:
                if NA & ~singles == 0: out.append((tuple(Bs), NA))
                return
            for B in opts[i]:
                if B & used: continue
                Bs.append(B)
                rec(i + 1, used | B, Bs, NA | nd[i][B], singles | (B if pc(B) == 1 else 0))
                Bs.pop()
        rec(0, 0, [], 0, 0)
        self._P = out
        self.f = min(pc(NA) for _, NA in out)
        self.omega = self.f - (2 * self.n - self.m)
        self.minP = [(Bs, NA) for Bs, NA in out if pc(NA) == self.f]
        keys = []
        for Bs, NA in self.minP:
            k = tuple(next(bits(B)) if pc(B) == 1 and B & NA else None for B in Bs)
            if k not in keys: keys.append(k)
        self.keys = keys
        return out

    def frozen_of(self, Bs, NA): return [i for i, B in enumerate(Bs) if pc(B) == 1 and B & NA]

    def removal_only(self, Bs):
        """(ok, owner, C): the pre-allocation with bases Bs is removal-only completable (k4/c4x.md §1)"""
        n = self.n
        N = [self.needs(i, Bs[i]) for i in range(n)]
        NA = 0
        for x in N: NA |= x
        used = 0
        for B in Bs: used |= B
        J = self.ALL & ~used
        frozen = [pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        S = sum(0 if frozen[i] else 2 - pc(Bs[i]) for i in range(n))
        if pc(J) <= S: return True, None, 0
        Jl = list(bits(J))
        for o in range(n):
            if frozen[o]: continue
            others = 0
            for j in range(n):
                if j != o: others |= N[j]
            for k in range(len(Jl) + 1):
                for Cl in itertools.combinations(Jl, k):
                    C = mask(Cl); X = Bs[o] | (J & ~C)
                    if any(self.threat(x, X, self.val(x, Bs[x])) for x in range(n) if x != o): continue
                    NA2 = others | self.needs(o, X)
                    slots = sum(0 if (pc(Bs[j]) == 1 and Bs[j] & NA2) else 2 - pc(Bs[j]) for j in range(n) if j != o)
                    if k <= slots: return True, o, C
        return False, None, None

    def deficit(self, Bs):
        """def(P) of k4/c4x.md §1: |J| - S if <= 0; otherwise the least |C| - S_o(C) over free owners o and C ⊆ J with
        B_o ∪ (J \\ C) threatening nobody holding its base; None (infinite) if no owner has a safe bundle."""
        n = self.n
        N = [self.needs(i, Bs[i]) for i in range(n)]
        NA = 0
        for x in N: NA |= x
        used = 0
        for B in Bs: used |= B
        J = self.ALL & ~used
        frozen = [pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        S = sum(0 if frozen[i] else 2 - pc(Bs[i]) for i in range(n))
        if pc(J) <= S: return pc(J) - S
        Jl = list(bits(J)); best = None
        for o in range(n):
            if frozen[o]: continue
            others = 0
            for j in range(n):
                if j != o: others |= N[j]
            for k in range(len(Jl) + 1):
                if best is not None and k - (S + 2) >= best: break
                for Cl in itertools.combinations(Jl, k):
                    C = mask(Cl); X = Bs[o] | (J & ~C)
                    if any(self.threat(x, X, self.val(x, Bs[x])) for x in range(n) if x != o): continue
                    NA2 = others | self.needs(o, X)
                    slots = sum(0 if (pc(Bs[j]) == 1 and Bs[j] & NA2) else 2 - pc(Bs[j]) for j in range(n) if j != o)
                    d = k - slots
                    if best is None or d < best: best = d
        return best

    def completable_full(self, Bs):
        """(ok, owner, X): a completion of Bs in the sense of k4/c4x.md §1 (owner o free or none; frozen non-owners get
        no junk, free non-owners at most 2 - |B_j|; the owner the rest; frozen status with o's needs from X_o; (OC4)
        v_j(X_o \\ h) <= v_j(X_j) for j != o), re-checked to be EFX0 by the raw definition (Theorem 1'4)."""
        n = self.n
        N = [self.needs(i, Bs[i]) for i in range(n)]
        used = 0
        for B in Bs: used |= B
        J = list(bits(self.ALL & ~used))
        for o in [None] + list(range(n)):
            NA = 0
            for i in range(n): NA |= N[i] if i != o else 0
            if o is not None and pc(Bs[o]) == 1 and Bs[o] & (NA | N[o]): continue    # the owner is not frozen
            for k in range(len(J) + 1):
                if o is None and k: break
                for Kl in itertools.combinations(J, k):
                    Xo = (Bs[o] | mask(Kl)) if o is not None else 0
                    NAo = NA | (self.needs(o, Xo) if o is not None else 0)
                    cap = {i: (0 if pc(Bs[i]) == 1 and Bs[i] & NAo else 2 - pc(Bs[i])) for i in range(n) if i != o}
                    rest = [g for g in J if g not in Kl]
                    if len(rest) > sum(cap.values()): continue
                    if o is not None and any(self.threat(j, Xo, self.val(j, Bs[j]) + self.val(j, self.R[j])) for j in cap): continue
                    agents = sorted(cap)
                    for pick in itertools.product(agents, repeat=len(rest)):
                        if any(pick.count(i) > cap[i] for i in agents): continue
                        X = list(Bs)
                        if o is not None: X[o] = Xo
                        for g, i in zip(rest, pick): X[i] |= 1 << g
                        if o is not None and any(self.threat(j, Xo, self.val(j, X[j])) for j in cap): continue
                        if o is None and any(pc(B) > 2 for B in X): continue
                        assert self.efx0_check(X), 'completion not EFX0: Theorem 1\'4 violated'
                        return True, o, X
        return False, None, None

    def c4min_deficit(self):
        """C4min in deficit form: some min-frozen P is removal-only completable. Returns (ok, bases, owner)."""
        self.preallocs()
        if self.omega <= 0:
            return True, self.minP[0][0], None
        for Bs, NA in self.minP:
            ok, o, C = self.removal_only(Bs)
            if ok: return True, Bs, o
        return False, None, None

    def pareto_max(self, space=None):
        """the Pareto-maximal pre-allocations of `space` (default: all of 𝒫), by the agents' base values"""
        space = self.preallocs() if space is None else space
        vecs = [tuple(self.val(i, Bs[i]) for i in range(self.n)) for Bs, _ in space]
        out = []
        for k, a in enumerate(vecs):
            if not any(all(b[i] >= a[i] for i in range(self.n)) and b != a for b in vecs): out.append(space[k])
        return out

    # ---------------------------------------------------------------- configurations
    def configs(self, keys=None):
        self.preallocs()
        out = []
        for key in (self.keys if keys is None else keys):
            Nm = mask(g for g in key if g is not None)
            Mp = self.ALL & ~Nm
            free = [i for i in range(self.n) if key[i] is None]
            cand = {}
            for y in free:
                U = self.R[y] & ~Nm
                cand[y] = [mask(c) for c in itertools.combinations(list(bits(Mp)), 2) if self.admissible(y, mask(c) & U, U)]
            def rec(j, used, Q):
                if j == len(free):
                    out.append(Config(self, key, dict(Q))); return
                y = free[j]
                for P in cand[y]:
                    if not P & used:
                        Q[y] = P; rec(j + 1, used | P, Q)
                Q.pop(y, None)
            rec(0, 0, {})
        return out

    # ---------------------------------------------------------------- EFX0 search (own SAT encoding)
    def efx0_check(self, X):
        """raw definition on a complete allocation X (list of masks)"""
        for i in range(self.n):
            vi = self.val(i, X[i])
            for j in range(self.n):
                if j != i and self.threat(i, X[j], vi): return False
        return True

    def efx0_search(self, d2=False, unenvied=(), owner_big=None, max_big_size=None, time_limit=None):
        """an EFX0 allocation (list of masks) or None. d2: at most one bundle of > 2 goods. unenvied: agents nobody
        envies (v_j(X_w) <= v_j(X_j)). owner_big: with d2, the agent allowed a bundle of > 2 goods."""
        from pysat.solvers import Minisat22
        n, m = self.n, self.m
        var = {}
        def V(key):
            if key not in var: var[key] = len(var) + 1
            return var[key]
        cls = []
        for g in range(m):
            cls.append([V(('x', g, i)) for i in range(n)])
            for i, j in itertools.combinations(range(n), 2): cls.append([-V(('x', g, i)), -V(('x', g, j))])
        for i in range(n):
            A = self.sets[i]; vi = self.v[i]
            for j in range(n):
                if j == i: continue
                e = V(('e', j, i))
                for g in range(m):
                    if not (self.R[i] >> g) & 1: cls.append([-V(('x', g, j)), e])
                for sig in itertools.product((0, 1, 2), repeat=len(A)):   # 0: to i, 1: to j, 2: elsewhere
                    own = sum(vi[g] for g, s in zip(A, sig) if s == 0)
                    inj = [vi[g] for g, s in zip(A, sig) if s == 1]
                    t_in = sum(inj) - min(inj) if inj else 0      # X_j ⊆ R_i
                    t_out = sum(inj)                               # X_j has a good outside R_i
                    lits = []
                    for g, s in zip(A, sig):
                        if s == 0: lits.append(-V(('x', g, i)))
                        elif s == 1: lits.append(-V(('x', g, j)))
                        else: lits += [V(('x', g, i)), V(('x', g, j))]
                    if t_in > own: cls.append(lits)
                    elif t_out > own: cls.append(lits + [-e])
        for w in unenvied:
            for j in range(n):
                if j == w: continue
                A = self.sets[j]; vj = self.v[j]
                for sig in itertools.product((0, 1, 2), repeat=len(A)):
                    own = sum(vj[g] for g, s in zip(A, sig) if s == 0)
                    tw = sum(vj[g] for g, s in zip(A, sig) if s == 1)
                    if tw > own:
                        lits = []
                        for g, s in zip(A, sig):
                            if s == 0: lits.append(-V(('x', g, j)))
                            elif s == 1: lits.append(-V(('x', g, w)))
                            else: lits += [V(('x', g, j)), V(('x', g, w))]
                        cls.append(lits)
        if d2 or owner_big is not None:
            for i in range(n):
                b = V(('big', i))
                for T in itertools.combinations(range(m), 3): cls.append([-V(('x', g, i)) for g in T] + [b])
                if owner_big is not None and i != owner_big: cls.append([-b])
            for i, j in itertools.combinations(range(n), 2): cls.append([-V(('big', i)), -V(('big', j))])
        with Minisat22(bootstrap_with=cls) as s:
            if time_limit:
                import threading
                tm = threading.Timer(time_limit, s.interrupt); tm.start()
                res = s.solve_limited(expect_interrupt=True); tm.cancel()
                if res is None: raise TimeoutError('SAT interrupted after %ss' % time_limit)
            else:
                res = s.solve()
            if not res: return None
            model = set(l for l in s.get_model() if l > 0)
        X = [0] * n
        for g in range(m):
            for i in range(n):
                if var[('x', g, i)] in model: X[i] |= 1 << g
        assert self.efx0_check(X), 'SAT model is not EFX0 (encoding bug)'
        for w in unenvied:
            assert all(self.val(j, X[w]) <= self.val(j, X[j]) for j in range(n) if j != w)
        if d2: assert sum(1 for B in X if pc(B) > 2) <= 1
        return X

    def efx0_brute(self, d2=False, unenvied=()):
        """plain enumeration of all n^m allocations (small instances only; the self-test of efx0_search)"""
        n, m = self.n, self.m
        for own in itertools.product(range(n), repeat=m):
            X = [0] * n
            for g, i in enumerate(own): X[i] |= 1 << g
            if d2 and sum(1 for B in X if pc(B) > 2) > 1: continue
            if not self.efx0_check(X): continue
            if any(self.val(j, X[w]) > self.val(j, X[j]) for w in unenvied for j in range(n) if j != w): continue
            return X
        return None


class Config:
    def __init__(self, inst, key, Q):
        self.I, self.key = inst, tuple(key)
        self.Nm = mask(g for g in key if g is not None)
        self.frozen = [i for i in range(inst.n) if key[i] is not None]
        self.free = [i for i in range(inst.n) if key[i] is None]
        self.Q = {y: Q[y] for y in self.free}
        used = 0
        for q in self.Q.values(): used |= q
        self.L = inst.ALL & ~self.Nm & ~used
        self._own = {}

    def __repr__(self):
        return 'Config(key=%s, Q={%s}, L=%s)' % (list(self.key), ', '.join('%d: %s' % (y, sorted(bits(q))) for y, q in self.Q.items()), sorted(bits(self.L)))

    def U(self, i): return self.I.R[i] & ~self.Nm
    def H(self, i): return (1 << self.key[i]) if self.key[i] is not None else self.Q[i]
    def hv(self, i): return self.I.val(i, self.H(i))
    def base(self, i): return self.H(i) if self.key[i] is not None else self.Q[i] & self.U(i)
    def needs(self, i): return self.I.needs(i, self.base(i))

    def owner(self, o):
        """least |C| for which o is a valid owner, or None"""
        if o in self._own: return self._own[o]
        I = self.I; X = self.Q[o] | self.L; Uo = self.U(o)
        nd = {i: self.needs(i) for i in range(I.n)}
        res = None
        Xl = list(bits(X))
        for k in range(len(Xl) + 1):
            for Cl in itertools.combinations(Xl, k):
                Xp = X & ~mask(Cl)
                if not any(I.admissible(o, mask(A), Uo) for r in (1, 2) for A in itertools.combinations(list(bits(Xp & Uo)), r)) \
                        and not (Uo == 0): continue
                if any(I.threat(x, Xp, self.hv(x)) for x in range(I.n) if x != o): continue
                if k:
                    no = I.needs(o, Xp)
                    unf = 0
                    for x in self.frozen:
                        g = 1 << self.key[x]
                        if g & no: continue
                        if any(nd[z] & g for z in range(I.n) if z != o): continue
                        unf += 1
                    if k > unf: continue
                res = k; break
            if res is not None: break
        self._own[o] = res
        return res

    @property
    def owners(self): return [o for o in self.free if self.owner(o) is not None]
    @property
    def completable(self): return any(self.owner(o) is not None for o in self.free)

    # potentials
    @property
    def t(self): return sum(1 for x in self.frozen if self.I.val(x, self.L & self.U(x)) > self.hv(x))
    def robust(self, i):
        if self.key[i] is not None: return self.I.val(i, self.U(i)) <= self.hv(i)
        return self.hv(i) >= self.I.val(i, self.U(i) & ~self.Q[i])
    @property
    def r(self): return sum(1 for i in range(self.I.n) if self.robust(i))
    @property
    def Lam(self): return sum(self.I.level(i, self.H(i) & self.I.R[i]) for i in range(self.I.n))
    @property
    def p(self): return sum(pc(self.L & self.U(x)) for x in self.frozen)
    @property
    def phi(self): return (-self.t, self.r, self.Lam, -self.p)
    @property
    def phi0(self): return (-self.t, self.r, self.Lam)
    @property
    def exposed(self): return [x for x in self.frozen if not self.robust(x)]
    def threatens(self, o, x): return self.I.threat(x, self.Q[o] | self.L, self.hv(x))
