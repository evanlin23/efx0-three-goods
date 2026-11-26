"""Matching form of one-absorber completability (workstream proof/k4-matching, k4/matching.md).

Definitions (k4/sdc.md §29-§31, k4/oc1_hall.md §1-§6 on claude/k4-oc1-hall):
  state      bases B_i (lists of goods), junk J = goods in no base;
  wants      i wants g not in B_i if v_i(g) > v_i(B_i);
  frozen     single-good holders whose good someone wants;
  holders    agents with at most one base good that nobody wants (empty bases included);
  completion keep every base, hand out J;
    shape 'oa' (one absorber): one owner o takes any subset, every other agent at most one junk good;
    shape 'ss' (S*): one owner o (any agent), every holder other than o at most one junk good, the rest nothing.
  d dummy slots: d extra capacity-one receivers that value nothing (equivalently, d junk goods deleted).

The FREE-SLOT DEFICIENCY of a state is the least d for which a completion exists (INF if none exists even with all
junk deleted).  delta = 0 iff the state completes.  Everything here is decided against the raw EFX0 definition:
  efx0(X): for all i != j and g in X_j, v_i(X_i) >= v_i(X_j minus g).
The search prunes with necessary conditions only and checks every candidate allocation with efx0; when no bundle of
a receiver can ever threaten anybody (no 'flag'), existence is decided by bipartite matching (Mendelsohn-Dulmage),
and the witness found is still checked with efx0.  bf_complete is a pruning-free brute force used to test that.

model_def implements Lemma 2* of the Hall session (S* shape, hypotheses (G1), (G2)) in its matching form:
  delta*(B, o) = min over kept-out sets H (subsets of J) satisfying (H1) and 'E(H) coverable' of |H| - nu(Gamma(H)).
"""
import itertools
import _mpaths  # noqa: F401
from oc1_mc2_rand import Inst as CInst   # coordinator's raw class: its official move generator (moves)

INF = 10 ** 9


def subsets(xs, lo=0):
    xs = list(xs)
    for r in range(lo, len(xs) + 1):
        for c in itertools.combinations(xs, r): yield c


def bip_match(left, adj):
    """Maximum bipartite matching; adj[l] = iterable of right vertices.  Returns dict right -> left."""
    match = {}

    def aug(l, seen):
        for r in adj[l]:
            if r in seen: continue
            seen.add(r)
            if r not in match or aug(match[r], seen):
                match[r] = l; return True
        return False
    for l in left: aug(l, set())
    return match


class M:
    def __init__(self, sets, vals, m=None, name=''):
        self.sets = [list(s) for s in sets]; self.vals = [list(x) for x in vals]; self.n = len(sets)
        self.m = m if m is not None else 1 + max(max(s) for s in sets if s)
        self.v = [dict(zip(s, x)) for s, x in zip(self.sets, self.vals)]
        self.R = [set(s) for s in self.sets]; self.name = name; self._ci = None

    # ---- raw primitives -------------------------------------------------------------------------------------------
    def V(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def threat(self, i, S, t):
        """Does bundle S (held by someone else) violate EFX0 for agent i whose own value is t?"""
        if not S: return False
        vs = [self.v[i].get(g, 0) for g in S]
        return sum(vs) - min(vs) > t

    def efx0(self, X):
        for i in range(self.n):
            t = self.V(i, X[i])
            for j in range(self.n):
                if j != i and self.threat(i, X[j], t): return False
        return True

    def sd(self, order):
        taken = set(); Y = [None] * self.n
        for i in order:
            av = [g for g in self.sets[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: (self.v[i][h], -h)); Y[i] = g; taken.add(g)
        return tuple(Y)

    def nu(self):
        return len(bip_match(range(self.n), {i: self.sets[i] for i in range(self.n)}))

    # ---- state structure ------------------------------------------------------------------------------------------
    def junk(self, base):
        used = set(g for b in base for g in b)
        return [g for g in range(self.m) if g not in used]

    def wants(self, i, g, base):
        return g not in base[i] and self.v[i].get(g, 0) > self.V(i, base[i])

    def frozen(self, base):
        return [j for j in range(self.n) if len(base[j]) == 1
                and any(i != j and self.wants(i, base[j][0], base) for i in range(self.n))]

    def holders(self, base):
        fz = set(self.frozen(base))
        return [j for j in range(self.n) if len(base[j]) <= 1 and j not in fz]

    def dangerous(self, base):
        J = set(self.junk(base))
        return [x for x in self.frozen(base) if self.R[x] & J]

    def moves(self, base):
        if self._ci is None: self._ci = CInst(self.sets, self.vals)
        return [list(map(list, st)) for st in self._ci.moves([list(b) for b in base])]

    # ---- completion with d dummy slots (raw, pruned search) ------------------------------------------------------
    def complete(self, base, d=0, shape='oa', owners=None):
        """Some owner o and a completion of the given shape with d dummy slots; returns (o, X) or None."""
        n = self.n; base = [list(b) for b in base]; J = self.junk(base)
        hold = set(self.holders(base)) if shape == 'ss' else None
        bv = [self.V(i, base[i]) for i in range(n)]
        for o in (range(n) if owners is None else owners):
            recv = [u for u in range(n) if u != o and (shape == 'oa' or u in hold)]
            nonr = [q for q in range(n) if q != o and q not in recv]
            # fixed bundles among non-receivers (values fixed)
            if any(self.threat(q, base[r], bv[q]) for q in nonr for r in nonr if r != q): continue
            for A in subsets(J):
                R = [g for g in J if g not in A]
                if len(R) > len(recv) + d: continue
                Xo = base[o] + list(A); to = self.V(o, Xo)
                if any(self.threat(q, Xo, bv[q]) for q in nonr): continue
                if any(self.threat(o, base[q], to) for q in nonr): continue
                opts = {}
                for u in recv:
                    ok = []
                    for z in [None] + R:
                        tu = bv[u] + (self.v[u].get(z, 0) if z is not None else 0)
                        if self.threat(u, Xo, tu) or any(self.threat(u, base[q], tu) for q in nonr): continue
                        ok.append(z)
                    opts[u] = ok
                if any(not opts[u] for u in recv): continue
                # flags: can a receiver's bundle threaten anybody at that agent's least possible value?
                least = {i: bv[i] for i in range(n)}; least[o] = to
                flag = any(self.threat(i, base[u] + ([z] if z is not None else []), least[i])
                           for u in recv for z in opts[u] for i in range(n) if i != u)
                X = self._assign(base, o, Xo, R, recv, opts, d, flag)
                if X is not None: return o, X
        return None

    def _assign(self, base, o, Xo, R, recv, opts, d, flag):
        needy = [u for u in recv if None not in opts[u]]
        if not flag:   # existence by Mendelsohn-Dulmage; then build a witness
            adj = {g: [u for u in recv if g in opts[u]] for g in R}
            if len(bip_match(R, adj)) < len(R) - d: return None
            adjn = {u: [g for g in opts[u] if g is not None] for u in needy}
            if len(bip_match(needy, adjn)) < len(needy): return None
        # DFS over goods (witness search; exhaustive when flags exist), raw efx0 at the leaf
        X0 = [list(b) for b in base]; X0[o] = list(Xo); used = set(); n_d = [0]

        def dfs(k):
            if k == len(R):
                if any(u not in used for u in needy): return None
                return [list(b) for b in X0] if self.efx0(X0) else None
            g = R[k]
            for u in recv:
                if u in used or g not in opts[u]: continue
                used.add(u); X0[u].append(g)
                r = dfs(k + 1)
                X0[u].pop(); used.discard(u)
                if r is not None: return r
            if n_d[0] < d:
                n_d[0] += 1; r = dfs(k + 1); n_d[0] -= 1
                if r is not None: return r
            return None
        X = dfs(0)
        if X is None and not flag:
            raise AssertionError('matching said yes, no raw witness: %s %s' % (self.name, base))
        return X

    def deficiency(self, base, shape='oa', owners=None, dmax=None):
        J = self.junk(base); top = len(J) if dmax is None else min(dmax, len(J))
        for d in range(top + 1):
            if self.complete(base, d, shape, owners) is not None: return d
        return INF if dmax is None or dmax >= len(J) else top + 1   # top + 1 means "> dmax"

    def owner_deficiency(self, base, shape='oa'):
        return {o: self.deficiency(base, shape, [o]) for o in range(self.n)}

    # ---- pruning-free brute force (test of complete) --------------------------------------------------------------
    def bf_complete(self, base, d, shape, o):
        n = self.n; base = [list(b) for b in base]; J = self.junk(base)
        hold = set(self.holders(base)) if shape == 'ss' else None
        recv = [u for u in range(n) if u != o and (shape == 'oa' or u in hold)]
        labels = ['o', 'd'] + recv
        for lab in itertools.product(labels, repeat=len(J)):
            if sum(1 for l in lab if l == 'd') > d: continue
            if any(lab.count(u) > 1 for u in recv): continue
            X = [list(b) for b in base]
            for g, l in zip(J, lab):
                if l == 'o': X[o].append(g)
                elif l != 'd': X[l].append(g)
            if self.efx0(X): return True
        return False

    # ---- Lemma 2* in matching form ---------------------------------------------------------------------------------
    def g1g2(self, base):
        """(G1): no bundle of a non-holder threatens anybody at base values; (G2): no junk good is wanted."""
        bv = [self.V(i, base[i]) for i in range(self.n)]; hold = set(self.holders(base))
        g1 = all(not self.threat(i, base[q], bv[i]) for q in range(self.n) if q not in hold
                 for i in range(self.n) if i != q)
        g2 = all(not self.wants(i, g, base) for g in self.junk(base) for i in range(self.n))
        return g1 and g2

    def gamma(self, base, o, H):
        """Kept-out set H: returns (H1 holds, exposed holders E, adjacency of Gamma(H): good -> holders)."""
        n = self.n; J = self.junk(base); hold = set(self.holders(base))
        N1 = [u for u in sorted(hold) if u != o]; Q = [q for q in range(n) if q != o and q not in hold]
        Wo = list(base[o]) + [g for g in J if g not in H]
        h1 = all(not self.threat(q, Wo, self.V(q, base[q])) for q in Q)
        E = [u for u in N1 if self.threat(u, Wo, self.V(u, base[u]))]
        adj = {h: [u for u in N1 if u not in E or
                   (self.v[u].get(h, 0) > 0 and not self.threat(u, Wo, self.V(u, base[u]) + self.v[u][h]))]
               for h in H}
        return h1, E, adj, N1

    def model_def(self, base, o, konig=False):
        """min over H with (H1) and E(H) coverable of |H| - nu(Gamma(H)) (INF if no such H)."""
        J = self.junk(base); best = INF; arg = None
        for H in subsets(J):
            h1, E, adj, N1 = self.gamma(base, o, H)
            if not h1: continue
            radj = {u: [h for h in H if u in adj[h]] for u in E}
            if len(bip_match(E, radj)) < len(E): continue
            nu = len(bip_match(H, adj)); df = len(H) - nu
            if konig:   # Konig-Ore: deficiency = max over S of |S| - |N(S)|
                ko = max(len(S) - len(set(u for h in S for u in adj[h])) for S in subsets(H))
                assert ko == df, ('Konig-Ore', self.name, base, o, H)
            if df < best: best, arg = df, H
        return best, arg
