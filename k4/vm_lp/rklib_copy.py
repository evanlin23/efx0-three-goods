"""READ-ONLY COPY of k4/rkmax/rklib.py from branch proof/k4-rkmax at commit ebd17e7e41c0c09d98d2c6cd20c1c989bb274903
(workstream proof/k4-rkmax, PR #158), vendored unchanged so that k4/vm_lp/ runs from this repository; do not edit here."""
"""rklib: an independent implementation for Conjecture RKMAX (k4/rkmax.md; k4/sdc.md §31 end).

Written from the definitions, sharing no code with k4/sdc/oc1_mc2_rand.py or k4/oc1cert/:
  - maximum matchings of the agent / relevant-good graph are enumerated directly (not through SD orders);
  - rank_i(M) = 1 + #{g in R_i : v_i(g) > v_i(M_i)} (5 if i is unmatched), sigma(M) = (#rank 1, ..., #rank 4);
  - EFX0 is the raw definition: for all i != j and g in X_j, v_i(X_i) >= v_i(X_j minus g);
  - a one-absorber completion keeps every base, gives every junk good to some agent, and at most one agent receives two
    or more junk goods;
  - the official moves of k4/sdc.md §29: an addition (one agent adds a nonempty set of junk goods it values), a chain
    x_0, ..., x_t (t >= 1; x_0 takes H_0 within J and B_{x_t}, worth more than B_{x_0}; x_i takes B_{x_{i-1}} plus junk
    H_i and strictly gains; the rest of B_{x_t} becomes junk; no empty base is handed on), and a ring c_0, ..., c_{r-1}
    (r >= 2; c_i takes B_{c_{i-1}} plus junk H_i and strictly gains; no empty base is handed on).
    All taken sets lie inside the taker's relevant goods, and the H's are pairwise disjoint.
  - OC1 holds at bases B if B has a one-absorber completion or one official move leads to bases that have one.
"""
import itertools


class Prof:
    """A profile: agents with relevant sets and positive values; goods 0..m-1."""

    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(g for s in sets for g in s)
        self.val = [dict() for _ in range(self.n)]
        for i, (s, x) in enumerate(zip(sets, vals)):
            for g, y in zip(s, x):
                assert y > 0
                self.val[i][g] = y
        self.rel = [frozenset(d) for d in self.val]

    def u(self, i, S):
        d = self.val[i]
        return sum(d.get(g, 0) for g in S)

    # ---------------------------------------------------------------- matchings
    def matchings(self):
        """All matchings as tuples M (M[i] = good or None), by brute force over each agent's options."""
        n = self.n; out = []
        opts = [[None] + sorted(self.rel[i]) for i in range(n)]

        def rec(i, used, cur):
            if i == n:
                out.append(tuple(cur)); return
            for g in opts[i]:
                if g is not None and g in used: continue
                cur.append(g); rec(i + 1, used | ({g} if g is not None else set()), cur); cur.pop()
        rec(0, frozenset(), [])
        return out

    def max_matchings(self):
        ms = self.matchings(); nu = max(sum(g is not None for g in M) for M in ms)
        return nu, [M for M in ms if sum(g is not None for g in M) == nu]

    def rank(self, i, g):
        if g is None: return 5
        d = self.val[i]; return 1 + sum(1 for h in d if d[h] > d[g])

    def ranks(self, M):
        return tuple(self.rank(i, M[i]) for i in range(self.n))

    def sigma(self, M):
        r = self.ranks(M); return tuple(sum(1 for x in r if x == k) for k in (1, 2, 3, 4))

    def pareto_optimal(self, M):
        """No matching weakly better for all agents and strictly for one (strict values; unmatched = worst)."""
        n = self.n
        def better_eq(i, a, b):  # agent i weakly prefers a to b
            if a is None: return b is None
            if b is None: return True
            return self.val[i][a] >= self.val[i][b]
        for M2 in self.matchings():
            if M2 == M: continue
            if all(better_eq(i, M2[i], M[i]) for i in range(n)): return False
        return True

    def sd(self, order):
        taken = set(); M = [None] * self.n
        for i in order:
            av = [g for g in self.rel[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: self.val[i][h]); M[i] = g; taken.add(g)
        return tuple(M)

    # ---------------------------------------------------------------- EFX0
    def efx0(self, X):
        n = self.n
        for i in range(n):
            own = self.u(i, X[i])
            for j in range(n):
                if i == j: continue
                Xj = X[j]
                if not Xj: continue
                tot = self.u(i, Xj)
                if tot <= own: continue
                # worst removal for i: the good of X_j i values least (possibly 0)
                lo = min(self.val[i].get(g, 0) for g in Xj)
                if tot - lo > own: return False
        return True

    def threat(self, i, t, S):
        """The bundle S threatens agent i at value t: v_i(S minus h) > t for some h in S (h may be worthless to i)."""
        S = list(S)
        if len(S) < 2: return False
        vs = [self.val[i].get(g, 0) for g in S]
        return sum(vs) - min(vs) > t

    def junk(self, B):
        held = set(g for b in B for g in b)
        return [g for g in range(self.m) if g not in held]

    def one_absorber(self, B, want=False):
        """Search a one-absorber completion of bases B. Returns the allocation (or True) if found, else None."""
        n = self.n; J = self.junk(B)
        # assignment of each junk good to an agent; at most one agent gets >= 2
        for f in itertools.product(range(n), repeat=len(J)):
            cnt = [0] * n
            for a in f: cnt[a] += 1
            if sum(1 for c in cnt if c >= 2) > 1: continue
            X = [list(b) for b in B]
            for g, a in zip(J, f): X[a].append(g)
            if self.efx0(X): return X
        return None

    # ---------------------------------------------------------------- moves
    def moves(self, B):
        """All bases reachable by one official move (k4/sdc.md §29), as tuples of frozensets."""
        n = self.n; J = frozenset(self.junk(B)); out = set()
        Bf = [frozenset(b) for b in B]

        def subsets(S):
            S = sorted(S)
            for r in range(len(S) + 1):
                for T in itertools.combinations(S, r): yield frozenset(T)

        def emit(newB): out.add(tuple(newB))

        # additions
        for x in range(n):
            for H in subsets(J & self.rel[x]):
                if H:
                    nb = list(Bf); nb[x] = Bf[x] | H; emit(nb)
        # chains: sequences x_0..x_t of distinct agents, t >= 1
        def chain(seq, used, takes):
            # seq = [x_0, ..., x_t]; takes[i] for i >= 1 is the set x_i takes (B_{x_{i-1}} + H_i)
            t = len(seq) - 1
            if t >= 1:
                xt = seq[-1]; x0 = seq[0]
                pool = ((J - used) | Bf[xt]) & self.rel[x0]
                for H0 in subsets(pool):
                    if H0 and self.u(x0, H0) > self.u(x0, Bf[x0]):
                        nb = list(Bf); nb[x0] = H0
                        for i in range(1, t + 1): nb[seq[i]] = takes[i]
                        emit(nb)
            if len(seq) == n: return
            prev = seq[-1]
            if not Bf[prev]: return          # never hand on an empty base
            for y in range(n):
                if y in seq: continue
                for H in subsets((J - used) & self.rel[y]):
                    T = Bf[prev] | H
                    if self.u(y, T) > self.u(y, Bf[y]):
                        chain(seq + [y], used | H, {**takes, len(seq): T})
        for x in range(n): chain([x], frozenset(), {})
        # rings
        for r in range(2, n + 1):
            for cyc in itertools.permutations(range(n), r):
                if cyc[0] != min(cyc): continue
                if any(not Bf[c] for c in cyc): continue

                def ring(i, used, takes):
                    if i == r:
                        nb = list(Bf)
                        for t in range(r): nb[cyc[t]] = takes[t]
                        emit(nb); return
                    w = cyc[i]; pred = cyc[i - 1]
                    for H in subsets((J - used) & self.rel[w]):
                        T = Bf[pred] | H
                        if self.u(w, T) > self.u(w, Bf[w]): ring(i + 1, used | H, {**takes, i: T})
                ring(0, frozenset(), {})
        return out

    def oc1(self, M):
        """'P' if the picks complete (one absorber), 'M' if one official move repairs, 'F' if OC1 fails."""
        B = [frozenset([g]) if g is not None else frozenset() for g in M]
        if self.one_absorber(B) is not None: return 'P'
        for nb in self.moves(B):
            if self.one_absorber(list(nb)) is not None: return 'M'
        return 'F'

    # ---------------------------------------------------------------- roles at picks
    def roles(self, M):
        """Receivers U (pick holders nobody else wants), frozen F, dangerous D (frozen, values junk),
        truly dangerous D_T (frozen, junk threatens it at its pick value), pickless agents."""
        n = self.n; J = set(self.junk([[g] if g is not None else [] for g in M]))
        p = [self.val[i][M[i]] if M[i] is not None else 0 for i in range(n)]
        wants = {(i, j) for i in range(n) for j in range(n)
                 if i != j and M[j] is not None and self.val[i].get(M[j], 0) > p[i]}
        frozen = {j for (_, j) in wants}
        U = [i for i in range(n) if M[i] is not None and i not in frozen]
        D = [i for i in frozen if J & self.rel[i]]
        DT = [i for i in D if self.threat(i, p[i], J)]
        return dict(U=U, F=sorted(frozen), D=sorted(D), DT=sorted(DT), wants=wants,
                    pickless=[i for i in range(n) if M[i] is None], J=sorted(J))


def lexmax(items, key):
    best = max(key(x) for x in items)
    return best, [x for x in items if key(x) == best]
