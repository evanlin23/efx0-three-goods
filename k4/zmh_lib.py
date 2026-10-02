#!/usr/bin/env python3
"""The objects of Theorem ZMOVE (workstream proof/k4-zmove-hall; k4/zmove_hall.md). EVIDENCE tooling.

Written from the definitions only (k4/c4x.md §1: 𝒫, needs, frozen agents, slots, removal-only deficit; k4/hall.md §1:
Lemma H1; k4/sx.md §1–§2 and §6: keys, def*, configurations, Z′-maxima, the move classes (T3), (T3⁺), (T4); ledger
K4.DL2.RC / lean/EFX/MovesC.lean `MoveT3plus`). It imports nothing from the repository; the second implementation used
for cross-checks is main's repo-free k4/rt4_n5_indep.py (k4/zmh_xcheck.py).

Everything is a bitmask over the goods. An instance is a strict profile: agent i values the goods sets[i] with the
values vals[i] and every other good 0.

Main objects:
  Prof(sets, vals, m)              the profile; .states = min-frozen states (tuples of base masks), .D = their deficits
                                   by Lemma H1, .keys = key -> list of states, .dstar = key -> def*
  Prof.zmax(key)                   the Z′-maxima of a key as base vectors (P_Q), with the configurations Q over them
  Prof.moves_from(P, pred)         the min-frozen P′ with pred(P, P′), from the classification move_kind(P, P′)
  Prof.zmove(key)                  Theorem ZMOVE's conclusion at the key: per Z′-maximum, the (T3⁺) moves with at most
                                   one helper from P_Q to a state of deficit <= 0; and the (T4) edges to smaller def*
"""
import itertools


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


def show(P):
    return '(' + ', '.join('{' + ','.join(map(str, bits(B))) + '}' for B in P) + ')'


INF = 10 ** 9


class Prof:
    def __init__(self, sets, vals, m=None):
        self.n = n = len(sets)
        self.m = m if m is not None else 1 + max(g for S in sets for g in S)
        self.sets = [list(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.R = [mask(S) for S in sets]
        self.ALL = (1 << self.m) - 1
        # value tables over the subsets of R_i
        self.vt = []
        for i in range(n):
            t = {}
            gs = self.sets[i]
            for k in range(len(gs) + 1):
                for T in itertools.combinations(gs, k):
                    t[mask(T)] = sum(self.v[i][g] for g in T)
            self.vt.append(t)
            sums = [t[s] for s in t if s]
            assert len(sums) == len(set(sums)), ('not strict', i)
        self._needs = [dict() for _ in range(n)]
        self._enum()

    # ---------------------------------------------------------------- values, needs, threats
    def val(self, i, X): return self.vt[i][X & self.R[i]]

    def needs(self, i, B):
        c = self._needs[i]
        r = c.get(B)
        if r is None:
            b = self.val(i, B)
            r = mask(g for g in bits(self.R[i] & ~B) if self.v[i][g] > b)
            c[B] = r
        return r

    def theta(self, w, Z):
        """θ_w(Z) = max_{h ∈ Z} v_w(Z ∖ h) (Z nonempty)"""
        if Z & ~self.R[w]: return self.val(w, Z)
        return self.val(w, Z) - min(self.v[w][g] for g in bits(Z))

    def threat(self, w, Z, b):
        return bool(Z) and self.theta(w, Z) > b

    def level(self, i, S):
        s = self.val(i, S)
        return sum(1 for T, x in self.vt[i].items() if x < s)

    # ---------------------------------------------------------------- 𝒫 and the min-frozen class
    def info(self, P):
        n = self.n
        N = [self.needs(i, P[i]) for i in range(n)]
        NA = 0
        for x in N: NA |= x
        used = 0
        for B in P: used |= B
        J = self.ALL & ~used
        fz = tuple(pc(P[i]) == 1 and bool(P[i] & NA) for i in range(n))
        return N, NA, J, fz

    def _enum(self):
        n = self.n
        opts = []
        for i in range(n):
            gs = self.sets[i]
            o = [0] + [1 << g for g in gs] + [mask(c) for c in itertools.combinations(gs, 2)]
            opts.append(o)
        valid = []
        cur = [0] * n

        def rec(i, used):
            if i == n:
                P = tuple(cur)
                N, NA, J, fz = self.info(P)
                if J & NA: return
                if any(pc(B) == 2 and B & NA for B in P): return
                valid.append((P, sum(fz)))
                return
            for B in opts[i]:
                if B & used: continue
                cur[i] = B
                rec(i + 1, used | B)
            cur[i] = 0
        rec(0, 0)
        self.f = min(k for _, k in valid)
        self.sigma = 2 * n - self.m
        self.omega = self.f - self.sigma
        self.states = [P for P, k in valid if k == self.f]
        self.stateset = set(self.states)
        self.D = {}
        self.keys = {}
        if self.omega < 1:
            return
        for P in self.states:
            self.D[P] = self.deficit(P)
            self.keys.setdefault(self.key(P), []).append(P)
        self.dstar = {k: min(self.D[P] for P in Ps) for k, Ps in self.keys.items()}

    def key(self, P):
        fz = self.info(P)[3]
        return tuple(P[i] if fz[i] else None for i in range(self.n))

    def u(self, P, inf, o, Z):
        """Lemma H1's u_o(Z): frozen x whose good misses N_o(Z) ∪ ⋃_{i≠o} N_i"""
        N, NA, J, fz = inf
        other = 0
        for i in range(self.n):
            if i != o: other |= N[i]
        # N_o(Z) = goods of R_o ∖ Z worth more than v_o(Z) = N_o(Z ∩ R_o)
        No = self.needs(o, Z & self.R[o])
        bad = No | other
        return sum(1 for x in range(self.n) if fz[x] and not (P[x] & bad))

    def safe(self, P, o, Z, bases=None):
        bases = bases or P
        bv = [self.val(i, bases[i]) for i in range(self.n)]
        return not any(self.threat(w, Z, bv[w]) for w in range(self.n) if w != o)

    def owner_val(self, P, o, inf=None):
        """Val_P(o) = max |Z| + u_o(Z) over safe bundles Z, B_o ⊆ Z ⊆ B_o ∪ J; with an optimal Z"""
        inf = inf or self.info(P)
        N, NA, J, fz = inf
        W = P[o] | J
        bv = [self.val(i, P[i]) for i in range(self.n)]
        nf = sum(fz)
        Jl = list(bits(J))
        best, bestZ = -1, None
        for c in range(len(Jl) + 1):
            if pc(W) - c + nf <= best: break
            for C in itertools.combinations(Jl, c):
                Z = W & ~mask(C)
                if any(self.threat(w, Z, bv[w]) for w in range(self.n) if w != o): continue
                val = pc(Z) + self.u(P, inf, o, Z)
                if val > best: best, bestZ = val, Z
        return best, bestZ

    def deficit(self, P):
        inf = self.info(P)
        N, NA, J, fz = inf
        S = sum(2 - pc(P[i]) for i in range(self.n) if not fz[i])
        if pc(J) - S <= 0: return pc(J) - S
        V = max(self.owner_val(P, o, inf)[0] for o in range(self.n) if not fz[o])
        return self.omega + 2 - V

    # ---------------------------------------------------------------- moves
    def move_kind(self, P, Q):
        """the kinds of the move P → Q between min-frozen states, as a set of names among
        'T3', 'T3+', 'T4'; with the shape (U, Z, W, Y) and for T3⁺ the size |W| and the helper list"""
        n = self.n
        N1, NA1, J1, f1 = self.info(P)
        N2, NA2, J2, f2 = self.info(Q)
        ch = [i for i in range(n) if P[i] != Q[i]]
        U = [i for i in ch if f1[i] and not f2[i]]
        Z = [i for i in ch if f2[i] and not f1[i]]
        W = [i for i in ch if f1[i] and f2[i]]
        Y = [i for i in ch if not f1[i] and not f2[i]]
        k = set()
        if not ch or NA1 != NA2: return k, (ch, U, Z, W, Y)
        if all(f1[i] and f2[i] for i in ch): k.add('T4')
        if len(U) == 1 and len(Z) == 1 and len(Y) <= 1 and all(P[y] & ~Q[y] for y in Y):
            z = Z[0]; x = U[0]
            if pc(Q[z]) == 1 and Q[z] & N1[z] and \
                    sorted(Q[i] for i in W + Z) == sorted(P[i] for i in W + U):
                k.add('T3+')
                if not W and Q[z] == P[x]: k.add('T3')
        return k, (ch, U, Z, W, Y)

    # ---------------------------------------------------------------- configurations and Z′-maxima
    def key_data(self, key):
        n = self.n
        F = [i for i in range(n) if key[i] is not None]
        NN = 0
        for i in F: NN |= key[i]
        U = [self.R[i] & ~NN for i in range(n)]
        return F, NN, U

    def fillers(self, P, key):
        """a filler assignment: the free agents with a one-good base get distinct junk goods outside their R
        (Hall matching); None if impossible. Returns dict agent -> good."""
        n = self.n
        F, NN, U = self.key_data(key)
        N, NA, J, fz = self.info(P)
        # one slot per missing good: an agent with an empty base (possible only when U_y = ∅) needs two fillers
        need = [(y, c) for y in range(n) if key[y] is None for c in range(2 - pc(P[y]))]
        cand = {(y, c): [g for g in bits(J & ~self.R[y])] for (y, c) in need}
        match = {}

        def aug(s, seen):
            for g in cand[s]:
                if g in seen: continue
                seen.add(g)
                if g not in match or aug(match[g], seen):
                    match[g] = s; return True
            return False
        for s in need:
            if not aug(s, set()): return None
        out = {}
        for g, (y, c) in match.items(): out.setdefault(y, []).append(g)
        return out

    def potential(self, P, key):
        n = self.n
        F, NN, U = self.key_data(key)
        r = 0; lam = 0
        for y in range(n):
            if key[y] is not None: continue
            H = P[y]
            if self.val(y, H) >= self.val(y, U[y] & ~H): r += 1
            lam += self.level(y, H)
        return (r, lam)

    def config_states(self, key):
        """the states P_Q of the configurations at the key: states of the key whose free bases are nonempty and
        that admit fillers"""
        F, NN, U = self.key_data(key)
        out = []
        for P in self.keys[key]:
            # an empty free base is admissible only when U_y = ∅ (k4/c4min.md §1: every good of U_y outside it is worth
            # less than it); otherwise N_y(∅) = R_y ⊄ 𝒩 and the state is not of the key anyway
            if any(key[y] is None and not P[y] and U[y] for y in range(self.n)): continue
            if self.fillers(P, key) is None: continue
            out.append(P)
        return out

    def zmax_states(self, key):
        cs = self.config_states(key)
        if not cs: return [], None
        pot = {P: self.potential(P, key) for P in cs}
        best = max(pot.values())
        return [P for P in cs if pot[P] == best], best

    def configs_over(self, P, key):
        """every configuration Q over the state P (free y: pair Q_y ⊇ P[y] with Q_y ∖ P[y] ⊆ J ∖ R_y); yields
        (Qdict, L)"""
        n = self.n
        N, NA, J, fz = self.info(P)
        need = [(y, c) for y in range(n) if key[y] is None for c in range(2 - pc(P[y]))]
        res = []

        def rec(k, used, Qd):
            if k == len(need):
                L = J & ~used
                Q2 = {y: P[y] for y in range(n) if key[y] is None}
                for (y, c), g in Qd.items(): Q2[y] |= 1 << g
                res.append((Q2, L))
                return
            y, c = need[k]
            for g in bits(J & ~self.R[y] & ~used):
                if c == 1 and g < Qd[(y, 0)]: continue        # unordered pair of fillers
                Qd[(y, c)] = g
                rec(k + 1, used | (1 << g), Qd)
                del Qd[(y, c)]
        rec(0, 0, {})
        return res

    # ---------------------------------------------------------------- ZMOVE
    def zmove(self, key, all_moves=False):
        """per Z′-maximum state P_Q: the (T3⁺) moves with at most one helper (|Y| <= 1) to states of deficit <= 0;
        and the (T4) edges of the key to keys with smaller def*"""
        zs, best = self.zmax_states(key)
        good = [Q for Q in self.states if self.D[Q] <= 0]
        res = []
        for P in zs:
            mv = []
            for Q in good:
                k, (ch, U, Z, W, Y) = self.move_kind(P, Q)
                if 'T3+' in k:
                    mv.append((Q, len(W), tuple(Y), 'T3' in k, U[0], Z[0]))
            res.append((P, mv))
        t4 = []
        for P in self.keys[key]:
            for Q in self.states:
                kq = self.key(Q)
                if kq == key or self.dstar[kq] >= self.dstar[key]: continue
                if 'T4' in self.move_kind(P, Q)[0]: t4.append((P, Q))
        return res, t4, best


def load_inputs(path):
    """gzip JSON lines with sets/vals/m, a JSON list, or a single JSON record"""
    import gzip, json
    if path.endswith('.gz'):
        with gzip.open(path, 'rt') as fh:
            for line in fh:
                line = line.strip()
                if line: yield json.loads(line)
        return
    with open(path) as fh:
        txt = fh.read()
    d = json.loads(txt)
    if isinstance(d, dict):
        if 'sets' in d: yield d
        elif 'instances' in d:
            yield from d['instances']
        return
    for r in d: yield r
