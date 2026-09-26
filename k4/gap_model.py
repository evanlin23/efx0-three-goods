"""A Python model of the configurations of conjecture C4min (compute/k4-gap; k4/gap.md), written from the definitions
of k4/c4min.md sections 1, 3 and 4 (PR #41), k4/c4x.md section 1 (PR #36) and k4/hall.md section 5 (PR #46). It shares
no code with k4/gap.c (the enumerator of the catalog), k4/c4min.c, k4/c4min_lib.py, k4/hall.c or k4/c4x.c; the bench
(k4/gap_bench.py) re-checks every counterexample it reports with this model, and gap_model.selftest() compares the two
implementations configuration by configuration.

Profile(sets, vals): sets[i] = the goods of agent i, vals[i] = its values in the same order (strict, k = 4 core).
  .preallocs()          every valid pre-allocation P (tuple of frozensets B_i): |B_i| <= 2, B_i in R_i, disjoint,
                        (V1) every needed good is a base good, (V2) no good of a pair base is needed
  .f, .omega, .keys     the fewest frozen agents, omega = f - (2n - m), the keys (tuple: phi(i) or None) of min-frozen P
  .in_gap               f >= 1, omega >= 1 and every key has an exposed frozen agent (v_x(U_x) > v_x(phi(x)))
  .configs()            every configuration of every key (Config objects)
  .deficit_ok()         some min-frozen P has removal-only deficit <= 0 (c4x.md section 1)
Config(prof, key, Q): Q = {free agent: frozenset pair}; the pool L is the rest of M' = M \\ N.
  .frozen, .free, .N, .L, .H(i), .hv(i), .U(i), .base(i), .needs(i), .needers(g)
  .threatens(o, x, C=())   x != o strongly envies (Q_o + L) \\ C holding H_x
  .owner(o)                the least |C| for which o is a valid owner (c4min.md section 1), or None; .owners, .completable,
                           .simple (some owner with C empty)
  .t, .r, .Lam, .p, .phi   Phi' = (-t, r, Lambda, -p) (c4min.md section 4); .phi0 = (-t, r, Lambda) (the first form)
  .pool_optimal, .kind(i) ('robust', 'T', 'D', 'R', 'frozen-exposed', 'frozen-robust', or 'other'),
  .exposed, .bigtop(x), .threat_edges, .need_edges, .chain_ends(x), .h7(x, o) ('G', 'G1', 'L' or 'O'),
  .mult(x)                 the number of free owners that threaten x (C empty)
  .pool_closure()          best pool improvements repeated until none applies
  .pool_moves(), .cycle_moves(general=False), .two_agent_moves()   the moves of c4min.md section 4: pool improvements;
                           one step along a cycle of the exchange digraph (best pairs, every order of the receivers; or
                           any admissible pairs); re-partitions of two free agents' pairs and the pool
"""
from itertools import combinations, product

class Profile:
    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(g for S in sets for g in S)
        self.R = [frozenset(S) for S in sets]
        self.sets = [list(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.M = frozenset(range(self.m))
        self._pre = None

    # values
    def val(self, i, S): return sum(self.v[i].get(g, 0) for g in S)
    def needs(self, i, B):
        b = self.val(i, B)
        return frozenset(g for g in self.R[i] - B if self.v[i][g] > b)
    def envies(self, i, X, h):
        X = frozenset(X)
        if not X: return False
        return max(self.val(i, X - {g}) for g in X) > h
    def level(self, i, S):
        s = self.val(i, S)
        return sum(1 for k in range(len(self.R[i]) + 1) for T in combinations(self.sets[i], k) if self.val(i, T) < s)
    def admissible(self, i, A, U):
        A, U = frozenset(A), frozenset(U)
        if not A: return not U
        a = self.val(i, A)
        return all(self.v[i][g] < a for g in U - A)
    def top(self, i): return max(self.R[i], key=lambda g: self.v[i][g])
    def is_bigtop(self, i):
        s = sorted(self.v[i].values(), reverse=True)
        return len(s) == 4 and s[0] > s[1] + s[2]

    # the space P
    def preallocs(self):
        if self._pre is None:
            opts = [[frozenset(B) for k in range(3) for B in combinations(self.sets[i], k)] for i in range(self.n)]
            out = []
            def rec(i, used, Bs):
                if i == self.n:
                    NA = frozenset().union(*(self.needs(j, Bs[j]) for j in range(self.n)))
                    singles = frozenset().union(*(B for B in Bs if len(B) == 1))
                    if NA <= singles: out.append((tuple(Bs), NA))
                    return
                for B in opts[i]:
                    if not (B & used): rec(i + 1, used | B, Bs + [B])
            rec(0, frozenset(), [])
            self._pre = out
            self.f = min(len(NA) for _, NA in out)
            self.minP = [(Bs, NA) for Bs, NA in out if len(NA) == self.f]
            ks = []
            for Bs, NA in self.minP:
                k = tuple(next(iter(B)) if len(B) == 1 and B <= NA else None for B in Bs)
                if k not in ks: ks.append(k)
            self.keys = ks
            self.omega = self.f - (2 * self.n - self.m)
        return self._pre

    def exposed_in_key(self, key):
        N = frozenset(g for g in key if g is not None)
        return [x for x in range(self.n) if key[x] is not None and self.val(x, self.R[x] - N) > self.v[x][key[x]]]

    @property
    def in_gap(self):
        self.preallocs()
        return self.f >= 1 and self.omega >= 1 and all(self.exposed_in_key(k) for k in self.keys)

    def configs(self):
        self.preallocs()
        out = []
        for key in self.keys:
            N = frozenset(g for g in key if g is not None)
            Mp = self.M - N
            free = [i for i in range(self.n) if key[i] is None]
            cand = {y: [frozenset(P) for P in combinations(sorted(Mp), 2) if self.admissible(y, frozenset(P) & (self.R[y] - N), self.R[y] - N)]
                    for y in free}
            def rec(j, used, Q):
                if j == len(free): out.append(Config(self, key, dict(Q))); return
                y = free[j]
                for P in cand[y]:
                    if not (P & used): Q[y] = P; rec(j + 1, used | P, Q)
                Q.pop(y, None)
            rec(0, frozenset(), {})
        return out

    def p_ok(self, Bs):
        """the pre-allocation with bases Bs (a min-frozen P) is removal-only completable (c4x.md section 1)"""
        N = [self.needs(i, Bs[i]) for i in range(self.n)]
        NA = frozenset().union(*N)
        J = self.M - frozenset().union(*Bs)
        for o in range(self.n):
            if len(Bs[o]) == 1 and Bs[o] <= NA: continue
            for k in range(len(J) + 1):
                for C in combinations(sorted(J), k):
                    X = Bs[o] | (J - frozenset(C))
                    if any(self.envies(x, X, self.val(x, Bs[x])) for x in range(self.n) if x != o): continue
                    NAp = self.needs(o, X).union(*(N[j] for j in range(self.n) if j != o))
                    S = sum(0 if (len(Bs[j]) == 1 and Bs[j] <= NAp) else 2 - len(Bs[j]) for j in range(self.n) if j != o)
                    if k <= S: return True
        return False

    def deficit_ok(self):
        """some min-frozen P is removal-only completable (c4x.md section 1)"""
        self.preallocs()
        for Bs, NA in self.minP:
            N = [self.needs(i, Bs[i]) for i in range(self.n)]
            J = self.M - frozenset().union(*Bs)
            for o in range(self.n):
                if len(Bs[o]) == 1 and Bs[o] <= NA: continue
                for k in range(len(J) + 1):
                    for C in combinations(sorted(J), k):
                        X = Bs[o] | (J - frozenset(C))
                        if any(self.envies(x, X, self.val(x, Bs[x])) for x in range(self.n) if x != o): continue
                        NAp = self.needs(o, X).union(*(N[j] for j in range(self.n) if j != o))
                        S = sum(0 if (len(Bs[j]) == 1 and Bs[j] <= NAp) else 2 - len(Bs[j]) for j in range(self.n) if j != o)
                        if k <= S: return True
        return False


class Config:
    def __init__(self, prof, key, Q):
        self.P, self.key = prof, tuple(key)
        self.N = frozenset(g for g in key if g is not None)
        self.frozen = [i for i in range(prof.n) if key[i] is not None]
        self.free = [i for i in range(prof.n) if key[i] is None]
        self.Q = {y: frozenset(Q[y]) for y in self.free}
        used = frozenset().union(*self.Q.values()) if self.Q else frozenset()
        self.L = (prof.M - self.N) - used
        self._own = {}

    def __repr__(self):
        return (f"Config(key={list(self.key)}, Q={{{', '.join(f'{y}: {sorted(self.Q[y])}' for y in self.free)}}}, "
                f"L={sorted(self.L)})")
    # holdings, needs
    def U(self, i): return self.P.R[i] - self.N
    def H(self, i): return frozenset([self.key[i]]) if self.key[i] is not None else self.Q[i]
    def hv(self, i): return self.P.val(i, self.H(i))
    def base(self, i): return self.H(i) if self.key[i] is not None else self.Q[i] & self.U(i)
    def needs(self, i): return self.P.needs(i, self.base(i))
    def needers(self, g): return [i for i in range(self.P.n) if g in self.needs(i)]
    # threats and owners
    def threatens(self, o, x, C=()):
        return self.P.envies(x, (self.Q[o] | self.L) - frozenset(C), self.hv(x))
    def owner(self, o):
        if o in self._own: return self._own[o]
        P, X = self.P, self.Q[o] | self.L
        res = None
        for k in range(len(X) + 1):
            for C in combinations(sorted(X), k):
                Xp = X - frozenset(C)
                A = frozenset(sorted((g for g in Xp & self.U(o)), key=lambda g: -P.v[o][g])[:2])
                if not P.admissible(o, A, self.U(o)): continue
                if any(P.envies(x, Xp, self.hv(x)) for x in range(P.n) if x != o): continue
                if k:
                    NoX = P.needs(o, Xp)
                    unf = sum(1 for x in self.frozen if not [z for z in self.needers(self.key[x]) if z != o] and self.key[x] not in NoX)
                    if k > unf: continue
                res = (k, frozenset(C)); break
            if res: break
        self._own[o] = res
        return res
    @property
    def owners(self): return [o for o in self.free if self.owner(o) is not None]
    @property
    def completable(self): return bool(self.owners)
    @property
    def p_completable(self):
        """the pre-allocation of Lemma 1(a) (bases: phi(x) for frozen x, Q_y restricted to R_y for free y) is
        removal-only completable; in it the owner may withhold junk into any free slot, so this is weaker than
        .completable (which fixes the goods each free agent holds outside R_y)"""
        return self.P.p_ok(tuple(self.H(i) & self.P.R[i] for i in range(self.P.n)))
    @property
    def simple(self): return any(self.owner(o)[0] == 0 for o in self.owners)
    # potentials
    @property
    def t(self): return sum(1 for x in self.frozen if self.P.val(x, self.L & self.U(x)) > self.hv(x))
    def robust(self, i):
        if self.key[i] is not None: return self.P.val(i, self.U(i)) <= self.hv(i)
        return self.hv(i) >= self.P.val(i, self.U(i) - self.Q[i])
    @property
    def r(self): return sum(1 for i in range(self.P.n) if self.robust(i))
    @property
    def Lam(self): return sum(self.P.level(i, self.H(i) & self.P.R[i]) for i in range(self.P.n))
    @property
    def p(self): return sum(len(self.L & self.U(x)) for x in self.frozen)
    @property
    def phi(self): return (-self.t, self.r, self.Lam, -self.p)
    @property
    def phi0(self): return (-self.t, self.r, self.Lam)
    @property
    def pool_optimal(self):
        P = self.P
        for y in self.free:
            best = max(P.val(y, S) for S in combinations(sorted((self.Q[y] | self.L) & self.U(y)), min(2, len((self.Q[y] | self.L) & self.U(y))))) \
                if (self.Q[y] | self.L) & self.U(y) else 0
            if best > self.hv(y): return False
        return True
    # structure
    @property
    def exposed(self): return [x for x in self.frozen if not self.robust(x)]
    def bigtop(self, x): return self.P.is_bigtop(x) and self.key[x] == self.P.top(x)
    def kind(self, i):
        P = self.P
        if self.key[i] is not None: return 'frozen-robust' if self.robust(i) else 'frozen-exposed'
        if self.robust(i): return 'robust'
        U, A = self.U(i), self.Q[i] & self.U(i)
        u = sorted(U, key=lambda g: -P.v[i][g])
        if len(A) == 1 and u and A == {u[0]}: return 'T'
        if len(U) == 4 and A == {u[0], u[3]}: return 'D'
        if len(U) == 4 and len(A) == 2 and u[0] not in A: return 'R'
        return 'other'
    @property
    def threat_edges(self): return [(o, x) for o in self.free for x in range(self.P.n) if x != o and self.threatens(o, x)]
    @property
    def need_edges(self): return [(x, z) for x in self.frozen for z in self.needers(self.key[x])]
    def mult(self, x): return sum(1 for o in self.free if o != x and self.threatens(o, x))
    def chain_ends(self, x):
        seen, stack, ends = {x}, [x], set()
        while stack:
            y = stack.pop()
            for z in self.needers(self.key[y]):
                if z in seen: continue
                seen.add(z)
                if self.key[z] is not None: stack.append(z)
                else: ends.add(z)
        return ends
    def h7(self, x, o):
        P = self.P
        JP = (P.M - self.N) - frozenset().union(*(self.base(y) for y in self.free))
        a = self.key[x]
        rest = P.R[x] - {a}
        Bo = self.base(o)
        if len(JP & P.R[x]) >= 2 and P.val(x, JP & P.R[x]) > self.hv(x): return 'G'   # the plain test (hall.md, #46)
        ends = self.chain_ends(x)
        if o in ends and self.bigtop(x) and rest <= JP | Bo: return 'G1'
        if o not in ends and P.val(x, ((self.Q[o] | self.L) - Bo) & P.R[x]) <= self.hv(x): return 'L'
        return 'O'
    # moves (c4min.md section 4)
    def _new(self, key, Q):
        try: return Config(self.P, key, Q)
        except Exception: return None
    def valid_config(self):
        """the pairs are disjoint pairs of M' with admissible restriction, and the key is a key of the profile"""
        P = self.P
        if self.key not in P.keys: return False
        seen = set()
        for y in self.free:
            Qy = self.Q[y]
            if len(Qy) != 2 or Qy & self.N or Qy & seen or not P.admissible(y, Qy & self.U(y), self.U(y)): return False
            seen |= Qy
        return True
    def pool_moves(self):
        P, out = self.P, []
        for y in self.free:
            for S in combinations(sorted(self.Q[y] | self.L), 2):
                S = frozenset(S)
                if P.val(y, S) > self.hv(y) and P.admissible(y, S & self.U(y), self.U(y)):
                    Q = dict(self.Q); Q[y] = S; out.append(('pool', y, Config(P, self.key, Q)))
        return out
    def exchange_digraph(self):
        E = {i: [] for i in range(self.P.n)}
        for o, x in self.threat_edges: E[o].append(x)
        for x, z in self.need_edges: E[x].append(z)
        return E
    def cycles(self):
        E, n, out = self.exchange_digraph(), self.P.n, []
        def rec(start, path, seen):
            for w in E[path[-1]]:
                if w == start: out.append(list(path))
                elif w > start and w not in seen: rec(start, path + [w], seen | {w})
        for s in range(n): rec(s, [s], {s})
        return out
    def cycle_moves(self, general=False, keep=False):
        """every cycle of the exchange digraph, moved one step (c4min.md section 4): across a need edge x -> z, z takes
        phi(x); across a threat edge o -> y, y takes a best admissible pair of Q_o + L. Receivers can compete for pool
        goods, so the threat receivers choose in every order (each time a best pair among the goods still available,
        every best pair). general=True: each threat receiver takes any admissible pair of Q_o + L (disjoint), not only a
        best one. keep=True (with general): a free threat receiver may also keep goods of its own pair (the rest goes on
        to its successor or the pool), as in #52's K4.HALL.BTCYC. Returns the distinct (cycle, new Config) that are
        configurations of a key of the profile."""
        from itertools import permutations
        P, out, seen = self.P, [], set()
        for cyc in self.cycles():
            k = len(cyc)
            key = list(self.key)
            steps = [('need' if self.key[cyc[j]] is not None else 'threat', cyc[j], cyc[(j + 1) % k]) for j in range(k)]
            for kind, u, w in steps:
                if kind == 'need': key[w] = self.key[u]
            thr = [(u, w) for kind, u, w in steps if kind == 'threat']
            for u, w in thr: key[w] = None
            recv = {w for _, _, w in steps}
            Q0 = {y: self.Q[y] for y in self.free if y not in recv}
            avail0 = (P.M - self.N) - frozenset().union(*Q0.values()) if Q0 else P.M - self.N
            def rec(order, idx, avail, Qc):
                if idx == len(order):
                    c2 = Config(P, key, Qc)
                    sig = (c2.key, tuple(sorted((y, tuple(sorted(q))) for y, q in c2.Q.items())))
                    if sig not in seen and c2.valid_config(): seen.add(sig); out.append((cyc, c2))
                    return
                u, w = order[idx]
                src = (self.Q[u] | self.L | (self.Q[w] if keep and self.key[w] is None else frozenset())) & avail
                Uw = P.R[w] - self.N
                opts = [frozenset(S) for S in combinations(sorted(src), 2) if P.admissible(w, frozenset(S) & Uw, Uw)]
                if not opts: return
                if not general:
                    bv = max(P.val(w, S) for S in opts); opts = [S for S in opts if P.val(w, S) == bv]
                for S in opts:
                    Q2 = dict(Qc); Q2[w] = S; rec(order, idx + 1, avail - S, Q2)
            for order in (permutations(thr) if not general else [thr]):
                rec(list(order), 0, avail0, dict(Q0))
        return out
    def downgrade_swaps(self):
        """#52's downgrade swap (attempts/k4-hall-bt-n4.md), written here from its description: a frozen agent x gives
        phi(x) to a free agent z that needs it (z becomes frozen on it; its old pair is released), and x becomes free
        with an admissible pair of L + Q_z (in pre-allocation terms, a single junk good it values as its base). Returns
        (x, z, new Config) for the results that are configurations of a key of the profile."""
        P, out = self.P, []
        for x in self.frozen:
            for z in self.needers(self.key[x]):
                if self.key[z] is not None: continue
                key = list(self.key); key[z] = self.key[x]; key[x] = None
                Q = {y: q for y, q in self.Q.items() if y != z}
                src = sorted(self.L | self.Q[z])
                Ux = P.R[x] - self.N
                for S in combinations(src, 2):
                    S = frozenset(S)
                    if not P.admissible(x, S & Ux, Ux): continue
                    Q2 = dict(Q); Q2[x] = S
                    c2 = Config(P, key, Q2)
                    if c2.valid_config(): out.append((x, z, c2))
        return out
    def pool_closure(self):
        """repeat, for each free agent in turn, the best pool improvement (its best admissible pair of Q_y + L, if worth
        more than Q_y) until none applies; returns the resulting configuration (self if none applies)"""
        P, c = self.P, self
        changed = True
        while changed:
            changed = False
            for y in c.free:
                src = sorted(c.Q[y] | c.L)
                opts = [frozenset(S) for S in combinations(src, 2) if P.admissible(y, frozenset(S) & c.U(y), c.U(y))]
                S = max(opts, key=lambda S: P.val(y, S))
                if P.val(y, S) > c.hv(y):
                    Q = dict(c.Q); Q[y] = S; c = Config(P, c.key, Q); changed = True
        return c
    def two_agent_moves(self):
        """every re-partition of Q_y + Q_z + L into admissible pairs for two free agents y, z (the rest to the pool);
        contains the pool moves and the pool-assisted two-agent exchanges of c4min.md section 4"""
        P, out = self.P, []
        for y, z in combinations(self.free, 2):
            pool = sorted(self.Q[y] | self.Q[z] | self.L)
            for A in combinations(pool, 2):
                A = frozenset(A)
                if not P.admissible(y, A & self.U(y), self.U(y)): continue
                for B in combinations(sorted(set(pool) - A), 2):
                    B = frozenset(B)
                    if not P.admissible(z, B & self.U(z), self.U(z)): continue
                    if A == self.Q[y] and B == self.Q[z]: continue
                    Q = dict(self.Q); Q[y] = A; Q[z] = B
                    out.append(((y, z), Config(P, self.key, Q)))
        return out

def selftest(records, gapbin_dump):
    """compare this model with gap.c's dump (gapbin_dump(record) -> list of (P-line dict, [C-line dicts])) on the
    profiles of the records: the gap class, f, omega, the keys, and per configuration Phi', pool-optimality, the valid
    owners with their least |C|, the threat edges and the H7 classes. Returns the number of mismatches."""
    bad = 0
    for rec in records:
        prof = Profile(rec['core']['sets'], rec['vals'], rec['core']['m'])
        if not prof.in_gap: bad += 1; print('not in gap', rec['prof']); continue
        head, cl = gapbin_dump(rec)
        if (prof.f, prof.omega) != (head['f'], head['omega']) or sorted(map(tuple, (tuple(-1 if g is None else g for g in k) for k in prof.keys))) != sorted(map(tuple, head['keys'])):
            bad += 1; print('keys differ', rec['prof']); continue
        mine = {}
        for c in prof.configs():
            mine[(tuple(-1 if g is None else g for g in c.key), tuple(tuple(sorted(c.Q[y])) if y in c.Q else None for y in range(prof.n)))] = c
        if len(mine) != len(cl): bad += 1; print('config count differs', rec['prof'], len(mine), len(cl)); continue
        for d in cl:
            k = (tuple(d['key']), tuple(tuple(q) if q is not None else None for q in d['Q']))
            c = mine.get(k)
            if c is None: bad += 1; print('missing config', k); continue
            own = sorted((o, c.owner(o)[0]) for o in c.owners)
            town = sorted((o, len(C)) for o, C in d['own'])
            thr = sorted((o, x, c.h7(x, o) if c.key[x] is not None else None) for o, x in c.threat_edges)
            tthr = sorted((o, x, 'G G1 L O'.split()[h] if h >= 0 else None) for o, x, h in d['thr'])
            if tuple(d['phi']) != c.phi or bool(d['po']) != c.pool_optimal or own != town or thr != tthr or sorted(d['L']) != sorted(c.L):
                bad += 1; print('mismatch', rec['prof'], k, d, c.phi, c.pool_optimal, own, thr)
    return bad
