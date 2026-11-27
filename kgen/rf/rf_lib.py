"""Conjecture RF (receiver first; k4/sdc.md §31 end) at general k: own implementation (workstream proof/kgen-n3).

Definitions, as in k4/sdc.md §29 and §31.
- Instance: n agents, agent i values the goods of sets[i] (at most k of them) at positive values vals[i]; other goods 0.
- SD order: each agent in turn takes its most valued remaining relevant good (or nothing).
- nu: maximum matching size of the agent / relevant-good graph.  A start is maximum-matching if its picks match nu agents.
- Moves (official rule: a chain never hands on an empty base), from bases B and junk J:
  addition  one agent x adds a nonempty H ⊆ J ∩ R_x;
  chain     x0 -> x1 -> ... -> xt (t >= 1, distinct): x_i (i >= 1) gets B_{x_{i-1}} ∪ H_i, x0 gets a nonempty
            H_0 ⊆ J, the end's base B_{xt} is released to junk; every passer x_0..x_{t-1} has a nonempty base;
  ring      the same, but x0 gets B_{xt} ∪ H_0 (H_0 may be empty) -- the chain whose x0 takes the end's base;
  each receiver must strictly gain (v_{x}(new) > v_x(old)); the H's are disjoint subsets of J ∩ R_{x}.
- One-absorber completion of bases B: an EFX0 allocation X ⊇ B (X_i ⊇ B_i) in which at most one agent gets two or more
  goods outside its base.  EFX0 is checked from the raw definition: v_i(X_i) >= v_i(X_j) - min_{h in X_j} v_i(h).
- OC1 at a start: the picks have a one-absorber completion, or one move gives bases that have one.
- Receiver of a start Y: an agent u with a pick such that no other agent values Y_u above its own pick (v_i(Y_u) <= v_i(Y_i)).
- RF (amended form, 2026-11-27 04:22 UTC): at a maximum-matching start where OC1 fails, for every receiver u, every order with
  u first whose picks form a maximum matching satisfies OC1."""
import itertools


class Inst:
    def __init__(self, sets, vals, m=None):
        self.sets = [list(s) for s in sets]; self.n = len(sets)
        self.m = m if m is not None else 1 + max(max(s) for s in sets if s)
        self.v = [[0] * self.m for _ in range(self.n)]
        for i, (s, x) in enumerate(zip(sets, vals)):
            for g, a in zip(s, x): self.v[i][g] = a
        self.R = [frozenset(s) for s in sets]

    def val(self, i, S): return sum(self.v[i][g] for g in S)

    def sd(self, order):
        taken = set(); y = [None] * self.n
        for i in order:
            av = [g for g in self.sets[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: (self.v[i][h], -h)); y[i] = g; taken.add(g)
        return tuple(y)

    def nu(self):
        match = {}
        def aug(i, seen):
            for g in self.sets[i]:
                if g in seen: continue
                seen.add(g)
                if g not in match or aug(match[g], seen): match[g] = i; return True
            return False
        return sum(1 for i in range(self.n) if aug(i, set()))

    def efx0(self, X):
        v = self.v
        for i in range(self.n):
            own = sum(v[i][g] for g in X[i])
            for j in range(self.n):
                if j == i or len(X[j]) < 2: continue
                tot = 0; mn = None
                for g in X[j]:
                    a = v[i][g]; tot += a
                    if mn is None or a < mn: mn = a
                if tot - mn > own: return False
        return True

    def complete1(self, B):
        """a one-absorber EFX0 completion of bases B (list of frozensets), or None"""
        n = self.n; J = [g for g in range(self.m) if not any(g in b for b in B)]
        if not J:
            return B if self.efx0(B) else None
        for a in [None] + list(range(n)):
            others = [i for i in range(n) if i != a]
            # each junk good goes to a (if any) or to a distinct non-absorber
            labels = ([a] if a is not None else []) + others
            for lab in itertools.product(range(len(labels)), repeat=len(J)):
                used = [l for l in lab if labels[l] != a]
                if len(used) != len(set(used)): continue
                if a is not None and sum(1 for l in lab if labels[l] == a) < 2: continue   # counted under a smaller case
                X = [set(b) for b in B]
                for g, l in zip(J, lab): X[labels[l]].add(g)
                if self.efx0(X): return X
        return None

    def moves(self, B):
        """every state one official move reaches (addition, chain, ring)"""
        n = self.n; J = [g for g in range(self.m) if not any(g in b for b in B)]
        def subs(xs):
            xs = list(xs)
            for r in range(len(xs) + 1): yield from itertools.combinations(xs, r)
        for x in range(n):   # additions
            for H in subs([g for g in J if g in self.R[x]]):
                if H and self.val(x, B[x] | set(H)) > self.val(x, B[x]):
                    nb = list(B); nb[x] = B[x] | frozenset(H); yield nb
        for t in range(1, n):
            for path in itertools.permutations(range(n), t + 1):
                if any(not B[path[i]] for i in range(t)): continue
                def rec(i, used, nb):
                    if i > t:
                        x0, xt = path[0], path[-1]
                        free = [g for g in J if g not in used and g in self.R[x0]]
                        for H0 in subs(free):   # chain: x0 takes H0 (nonempty)
                            if H0 and self.val(x0, H0) > self.val(x0, B[x0]):
                                s = list(nb); s[x0] = frozenset(H0); yield s
                        if B[xt]:
                            for H0 in subs(free):   # ring: x0 takes B_{xt} + H0
                                nx = B[xt] | frozenset(H0)
                                if self.val(x0, nx) > self.val(x0, B[x0]):
                                    s = list(nb); s[x0] = nx; yield s
                        return
                    xi, prev = path[i], path[i - 1]
                    for H in subs([g for g in J if g not in used and g in self.R[xi]]):
                        nbi = B[prev] | frozenset(H)
                        if self.val(xi, nbi) > self.val(xi, B[xi]):
                            s = list(nb); s[xi] = nbi
                            yield from rec(i + 1, used | set(H), s)
                yield from rec(1, frozenset(), list(B))

    def oc1(self, picks):
        """'picks complete' / 'one move repairs' / 'OC1 fails'"""
        B = [frozenset([g]) if g is not None else frozenset() for g in picks]
        if self.complete1(B) is not None: return 'picks complete'
        for nb in self.moves(B):
            if self.complete1(nb) is not None: return 'one move repairs'
        return 'OC1 fails'

    def receivers(self, picks):
        return [u for u in range(self.n) if picks[u] is not None and
                all(self.v[i][picks[u]] <= (self.v[i][picks[i]] if picks[i] is not None else 0) for i in range(self.n) if i != u)]

    def rf(self, picks, N=None):
        """at a start: returns (receivers, list of (order, picks, oc1 result) for u-first max-matching orders, non-max count)"""
        N = self.nu() if N is None else N; rec = self.receivers(picks); out = []; nonmax = 0; seen = {}
        for u in rec:
            for rest in itertools.permutations([i for i in range(self.n) if i != u]):
                p = self.sd((u,) + rest)
                if sum(x is not None for x in p) != N: nonmax += 1; continue
                if p not in seen: seen[p] = self.oc1(p)
                out.append(((u,) + rest, p, seen[p]))
        return rec, out, nonmax
