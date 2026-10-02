#!/usr/bin/env python3
"""The chain lemmas of k4/f2.md §3, checked and measured (workstream proof/k4-f2). EVIDENCE tooling for written proofs.

Objects (k4/f2.md §3): a *need path* to a frozen x is z = a_{k+1}, a_k, ..., a_1, a_0 = x (k >= 0), distinct agents,
a_1..a_k frozen, z free, each a_{i+1} needing the good of a_i. The *chain swap* along it with helper h (or none): z takes
the good of a_k, each a_i (1 <= i <= k) the good of a_{i-1}, x takes A, h takes B'_h, with A, B'_h ⊆ G = J ∪ B_z ∪ B_h.
Every conclusion is asserted against the exact deficits and owner tables (k4/f2_lib.py: main's model.py and
dl2_classify.py):
  (Lemma NP and Lemma CL of k4/f2.md are called "Lemma P" and "Lemma C" in this file's log rows.)
  P    Lemma NP: every frozen agent has a need path from a free agent, or the agents with a need walk to it are all
       frozen and contain a cycle of the frozen need digraph (so: always, at a T4-optimal P).
  L6+  Lemma 6+: every chain swap with admissible A, B'_h (N(.) ⊆ 𝒩) is min-frozen with NA(P') = NA(P),
       F(P') = F - x + z, and is a (T3+) move (k4/f2_lib.t3plus) when the helper gives up a good.
  L8+  Lemma 8+: Val_{P'}(x) = max over A ⊆ Z ⊆ G minus B'_h, Z safe for the P' bases, of |Z| + #{q ∈ 𝒩 : q ∉ N_x(Z) ∪ 𝒩'},
       𝒩' = N_z({g_k}) ∪ ⋃ N_{a_i}({g_{i-1}}) ∪ N_h(B'_h) ∪ the needs of the unmoved agents; all from P's data.
  C1+  Corollary 9.1+ (the S1 repair through a need path): o a best owner, X optimal, c ∈ J \\ X, X ∪ {c} threatens
       only a frozen x, o the free end of a need path to x, theta_o(X ∪ {c}) <= v_o(g_k): for every admissible
       A ⊆ X ∪ {c}, def(P') <= def(P) - 1 - iota (iota = 1 if nobody but o needs g_k).
  C2+  Corollary 11.1+ (the blocker swap through a need path): X ∪ {c} threatens only a free z, z the free end of a
       need path to a frozen x, theta_z(X ∪ {c}) <= v_z(g_k), A ⊆ (J ∪ B_z) minus (X ∪ {c}) admissible with
       theta_x(X ∪ {c}) <= v_x(A) and no good counted in u_o(X) in N_x(A): def(P') <= def(P) - 1.
  C    Lemma CL: a (T4) move followed by a (T3+) move is a (T3+) move (every composition through every (T4) neighbour);
  N    Proposition N: at a def > 0 state no (T4) move improves, frozen rotations reach a T4-optimal state, equal deficit;
       and its dichotomy (--propn): (i) def*(κ(P*)) < def(P), a (T4) key edge, or (ii) P* at the T3 stage.
  C4+  Corollary 11.2+ (the kappa swap): a best owner o keeps an optimal X; a frozen x whose good g has exactly one
       needer a_1 besides o, g ∉ N_o(X); a need path z, ..., a_1, x avoiding o; x takes a pair A ⊆ (J ∪ B_z) minus X with
       v_x(A) > v_x(g) and theta_x(X) <= v_x(A): def(P') <= def(P) - 1 (g becomes counted at o).
  C8+  certificate: some chain swap along a need path (helper giving up a good, or none) makes x an owner with
       Val_{P'}(x) > Val*(P) (Lemma 8+, exact);
  C11+ certificate: some such chain swap keeps an unmoved best owner o, an optimal X of o misses A ∪ B'_h, and Lemma
       11+'s value max over Y ⊇ X safe in P' of |Y| + (u_o(X) - e*) + kappa exceeds Val*(P) (the bound is asserted);
  C3+  Corollary 8.2+ (the Lemma 7 swap through a need path): x big-top on its top g, a_1 the only needer of g, a need
       path through a_1, L_x ⊆ G, B'_h ⊆ G minus L_x admissible with g ∉ N_h(B'_h), Z ⊇ L_x a safe bundle of x in P':
       def(P') <= omega + 1 - |Z|; certified when |Z| + 1 > Val*(P).
usage: python3 k4/f2_lemmas.py DUMP.jsonl.gz ...            (T3-stage dumps of k4/f2_shapes.py: coverage, all checks)
       python3 k4/f2_lemmas.py --stuck STUCK.jsonl.gz ...    (the T3-stage states among k4/dl13_stuck.py's T1-stuck
                                   records, any f >= 1: the same coverage, case and repairs computed here)
       python3 k4/f2_lemmas.py --caseb DUMP.jsonl.gz ...    (case B at every def > 0 state of the dumps' profiles)
       python3 k4/f2_lemmas.py --propn DUMP.jsonl.gz ...    (Proposition N's dichotomy at the non-T4-optimal states)
       --light: skip the checks of Lemmas 6+, 8+, C and Proposition N (the coverage only)
       python3 k4/f2_lemmas.py --random N [--seed=S] [--nmax=5] [--mmax=12]   (random strict instances, not cores,
                                   biased to f >= 2; every check at every def > 0 state with f >= 1)
       python3 k4/f2_lemmas.py --profiles SOURCE ... [--every=E] [--max=N] [--all]   (the f >= 2 profiles of the sources,
                                   as k4/f2_shapes.py reads them; --all: Lemmas P, 6+, 8+, C at every min-frozen state)"""
import collections, gzip, itertools, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f2_lib import Prof, bits, pc, mask, tup, lst, counted, bigtop, kind, t3plus, INF
import model as M


class Ctx:
    def __init__(self, pr, Bs):
        self.pr, self.Bs, self.I = pr, Bs, pr.I
        self.P = pr.PA[Bs]; self.D = pr.D[Bs]
        self.best = pr.best(Bs); self.V = pr.V(Bs)
        self.omega = pc(self.P.J) - self.P.S
        self.F = [i for i in range(self.I.n) if self.P.frozen[i]]

    def thr(self, w, Z, hold): return self.I.threat(w, Z, self.I.val(w, hold))

    def adm(self, i, pool, kmax=2):
        I, P = self.I, self.P
        return [mask(A) for k in range(1, kmax + 1) for A in itertools.combinations(list(bits(pool & I.R[i])), k)
                if not (I.needs(i, mask(A)) & ~P.NA)]

    # ------------------------------------------------------------ need paths
    def paths_to(self, x):
        """every need path [z, a_k, ..., a_1, x] (lists) to the frozen x"""
        P, I = self.P, self.I
        out = []

        def rec(path):
            head = path[0]
            for i in range(I.n):
                if i in path or not (P.N[i] & self.Bs[head]): continue
                if P.frozen[i]: rec([i] + path)
                else: out.append([i] + path)
        rec([x])
        return out

    def lemmaP(self):
        """every frozen x: a need path from a free agent, or a need cycle among the agents with a need walk to x"""
        P, I = self.P, self.I
        for x in self.F:
            if self.paths_to(x): continue
            S, stack = {x}, [x]
            while stack:
                y = stack.pop()
                for i in range(I.n):
                    if P.N[i] & self.Bs[y] and i not in S: S.add(i); stack.append(i)
            assert all(P.frozen[i] for i in S), ('Lemma P: a free agent reaches x without a path', self.Bs, x)
            assert not self.pr.t4_optimal(self.Bs), ('Lemma P: T4-optimal but no path', self.Bs, x)
            return 1
        return 0

    def swap(self, path, A, h=None, Bh=None):
        b = list(self.Bs)
        for j in range(len(path) - 1): b[path[j]] = self.Bs[path[j + 1]]
        b[path[-1]] = A
        if h is not None: b[h] = Bh
        return tuple(b)

    def hold(self, path, h=None, Bh=None):
        """the P' bases of the moved agents other than x"""
        hd = {path[j]: self.Bs[path[j + 1]] for j in range(len(path) - 1)}
        if h is not None: hd[h] = Bh
        return hd

    def Nprime(self, path, h=None, Bh=None, skip=()):
        """𝒩' of Lemma 8+ (the needs in P' of every agent other than x and the agents in skip)"""
        I, P = self.I, self.P
        hd = self.hold(path, h, Bh); x = path[-1]
        out = 0
        for i in range(I.n):
            if i == x or i in skip: continue
            out |= I.needs(i, hd[i]) if i in hd else P.N[i]
        return out

    # ------------------------------------------------------------ Lemma 6+ and Lemma 8+
    def moves(self, kmax_paths=None):
        """every chain swap allowed by Lemma 6+: (path, A, h, Bh)"""
        I, P, Bs = self.I, self.P, self.Bs
        for x in self.F:
            for path in self.paths_to(x):
                z = path[0]
                for h in [None] + [h for h in P.free if h != z]:
                    G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                    for A in self.adm(x, G):
                        if h is None: yield path, A, None, None; continue
                        for k in range(3):
                            for Bh in itertools.combinations(list(bits((G & ~A) & I.R[h])), k):
                                Bh = mask(Bh)
                                if I.needs(h, Bh) & ~P.NA: continue
                                yield path, A, h, Bh

    def lemma11_value(self, o, X, path, A, h=None, Bh=None):
        """Lemma 11+ at an unmoved free o with a bundle X of P missing A ∪ B'_h: the largest |Y| + (u_o(X) - e*) + kappa
        over the bundles Y ⊇ X of o in P' that are safe in P', all from P's data; -1 if none"""
        I, P, Bs = self.I, self.P, self.Bs
        x, z = path[-1], path[0]
        hd = self.hold(path, h, Bh); hd[x] = A
        G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
        Jn = G & ~A & ~(Bh or 0)                              # J(P')
        NxA = I.needs(x, A); Nh = I.needs(h, Bh) if h is not None else 0
        cnt = [q for q in bits(P.NA) if not ((1 << q) & (I.needs(o, X) | self.Nminus(o)))]   # counted in u_o(X)
        es = sum(1 for q in cnt if (1 << q) & (NxA | Nh))
        Nm = 0
        for i in range(I.n):
            if i == o: continue
            Nm |= I.needs(i, hd[i]) if i in hd else P.N[i]
        rest = list(bits(Jn & ~X)); best = -1
        for k in range(len(rest), -1, -1):
            for K in itertools.combinations(rest, k):
                Y = X | mask(K)
                if any(self.thr(w, Y, hd.get(w, Bs[w])) for w in range(I.n) if w != o): continue
                NY = I.needs(o, Y)
                kappa = sum(1 for q in bits(P.NA) if q not in cnt and not ((1 << q) & (NY | Nm)))
                best = max(best, pc(Y) + len(cnt) - es + kappa)
        return best

    def Nminus(self, o):
        out = 0
        for i in range(self.I.n):
            if i != o: out |= self.P.N[i]
        return out

    def certificates(self):
        """C8+: some chain swap along a need path makes x an owner with Val > V (Lemma 8+); C11+: some chain swap keeps
        an unmoved best owner o with an optimal X (missing A ∪ B'_h) whose Lemma 11+ value exceeds V. Each conclusion
        (def(P') <= omega + 2 - value) is asserted against the exact deficit."""
        pr, Bs = self.pr, self.Bs
        c8 = c11 = False
        for path, A, h, Bh in self.moves():
            if h is not None and not (Bs[h] & ~Bh): continue          # (T3+) helpers give up a good
            b2 = self.swap(path, A, h, Bh); x = path[-1]
            if not c8 and pr.OWN[b2][x][0] > self.V: c8 = (len(path) - 2,)
            if not c11:
                for o in self.best:
                    if o in path or o == h: continue
                    for X in pr.OWN[Bs][o][1]:
                        if X & (A | (Bh or 0)): continue
                        val = self.lemma11_value(o, X, path, A, h, Bh)
                        if val < 0: continue
                        assert pr.D[b2] <= self.omega + 2 - val, ('Lemma 11+', Bs, b2, val)
                        if val > self.V: c11 = (len(path) - 2,); break
                    if c11: break
            if c8 and c11: break
        return c8, c11

    def check_6_8(self):
        pr, I, P, Bs = self.pr, self.I, self.P, self.Bs
        n6 = n8 = 0
        for path, A, h, Bh in self.moves():
            x, z = path[-1], path[0]
            b2 = self.swap(path, A, h, Bh)
            assert b2 in pr.D, ('Lemma 6+: not min-frozen', Bs, b2)
            P2 = pr.PA[b2]
            assert P2.NA == P.NA and [i for i in range(I.n) if P2.frozen[i]] == sorted(set(self.F) - {x} | {z}), \
                ('Lemma 6+: needed or frozen set', Bs, b2)
            gives = h is None or bool(Bs[h] & ~Bh)
            if gives:
                k = kind(P, P2)
                assert k == ('t3' if len(path) == 2 else 't3c'), ('Lemma 6+: not a T3+ move', Bs, b2, k)
            n6 += 1
            # Lemma 8+
            G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
            W = G & ~(Bh or 0)
            hd = self.hold(path, h, Bh)
            Np = self.Nprime(path, h, Bh)
            rest = list(bits(W & ~A)); best = -1
            for k in range(len(rest) + 1):
                for K in itertools.combinations(rest, k):
                    Z = A | mask(K)
                    if any(self.thr(w, Z, hd.get(w, Bs[w])) for w in range(I.n) if w != x): continue
                    u = sum(1 for q in bits(P.NA) if not ((1 << q) & (I.needs(x, Z) | Np)))
                    best = max(best, pc(Z) + u)
            assert best == pr.OWN[b2][x][0], ('Lemma 8+', Bs, b2, best, pr.OWN[b2][x][0])
            n8 += 1
        return n6, n8

    # ------------------------------------------------------------ Lemma C and Proposition N
    def check_closure(self):
        """Lemma C: for every (T4) move P -> P* and every (T3⁺) move P* -> P' (all min-frozen), P -> P' is (T3⁺).
        Proposition N (at a state where no T4 move lowers def): repeated frozen rotations reach a T4-optimal P* with
        def(P*) = def(P). Returns (number of compositions checked, 1 if P was not T4-optimal)."""
        pr, Bs = self.pr, self.Bs
        P = self.P; n = 0
        t4s = [B2 for B2 in pr.mp if B2 != Bs and kind(P, pr.PA[B2]) == 't4']
        for B2 in t4s:
            P2 = pr.PA[B2]
            for B3 in pr.mp:
                if B3 == B2 or t3plus(P2, pr.PA[B3]) is None: continue
                if B3 == Bs: continue
                assert t3plus(P, pr.PA[B3]) is not None, ('Lemma C', Bs, B2, B3)
                n += 1
        rot = 0
        if pr.D[Bs] > 0 and not pr.t4_optimal(Bs) and not any(pr.D[B2] < pr.D[Bs] for B2 in t4s):
            rot = 1
            cur = Bs
            while not pr.t4_optimal(cur):          # a Pareto reassignment along a cycle (Lemma 12)
                Pc = pr.PA[cur]; F = [i for i in range(self.I.n) if Pc.frozen[i]]
                nxt = None
                for B2 in pr.mp:
                    ch = [i for i in range(self.I.n) if cur[i] != B2[i]]
                    if ch and all(i in F for i in ch) and kind(Pc, pr.PA[B2]) == 't4' and \
                            all(self.I.val(i, B2[i]) > self.I.val(i, cur[i]) for i in ch):
                        nxt = B2; break
                assert nxt is not None, ('Proposition N: no rotation at a cyclic state', cur)
                assert pr.D[nxt] <= pr.D[cur], ('Lemma 12', cur, nxt)
                cur = nxt
            assert pr.D[cur] == pr.D[Bs], ('Proposition N: def(P*) != def(P)', Bs, cur)
            assert kind(P, pr.PA[cur]) == 't4', ('Proposition N: P -> P* not (T4)', Bs, cur)
            # the dichotomy of Proposition N (k4/f2.md §3.3): (i) def*(κ(P*)) < def(P), a (T4) key edge to a smaller
            # def*; or (ii) P* is at the T3 stage
            if pr.dstar[pr.key[cur]] < pr.D[Bs]:
                rot = 'i'
            else:
                assert pr.t3_stage(cur), ('Proposition N (ii): P* not at the T3 stage', Bs, cur)
                rot = 'ii'
            self.pstar = cur
        return n, rot

    # ------------------------------------------------------------ the corollaries
    def single_blocks(self, pairs=None):
        """(o, X, c, w): w the only agent other than o threatened by X ∪ {c}, for the (o, X) of pairs (default: the best
        owners and their optimal bundles)"""
        if pairs is None: return self.pr.single_blocks(self.Bs)
        out = []
        for o, X in pairs:
            for c in bits(self.P.J & ~X):
                ws = self.pr.blockers(self.Bs, o, X | (1 << c))
                if len(ws) == 1: out.append((o, X, c, ws[0]))
        return out

    def all_pairs(self):
        """every free o with every bundle X of o that is safe in P"""
        P, Bs = self.P, self.Bs
        Jl = list(bits(P.J)); out = []
        for o in P.free:
            for k in range(len(Jl) + 1):
                for K in itertools.combinations(Jl, k):
                    X = Bs[o] | mask(K)
                    if P.safe(o, X): out.append((o, X))
        return out

    def val(self, o, X): return pc(X) + self.P.u(o, X)

    def C1p(self, sb):
        """Corollary 9.1+; returns the (o, x, c, k) certified"""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        out = []
        for o, X, c, x in sb:
            if not P.frozen[x]: continue
            Y = X | (1 << c)
            for path in self.paths_to(x):
                if path[0] != o: continue
                gk = Bs[path[1]]
                if self.thr(o, Y, gk): continue
                As = self.adm(x, Y)
                assert As, ('Corollary 9.1+: no admissible A', Bs)
                iota = 0 if any(P.N[i] & gk for i in range(I.n) if i != o) else 1
                bound = self.omega + 1 - self.val(o, X) - iota          # = def(P) - 1 - iota at a best owner, X optimal
                for A in As:
                    b2 = self.swap(path, A)
                    assert b2 in pr.D and pr.D[b2] <= bound, ('Corollary 9.1+', Bs, b2)
                out.append((o, x, c, len(path) - 2))
        return out

    def C2p(self, sb):
        """Corollary 11.1+; returns the (o, z, x, c, k) certified"""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        out = []
        for o, X, c, z in sb:
            if P.frozen[z]: continue
            cnt = counted(P, o, X); Y = X | (1 << c)
            for x in self.F:
                for path in self.paths_to(x):
                    if path[0] != z: continue
                    gk = Bs[path[1]]
                    if self.thr(z, Y, gk): continue
                    for A in self.adm(x, (P.J | Bs[z]) & ~Y):
                        if self.thr(x, Y, A): continue
                        if any(Bs[w] & I.needs(x, A) for w in cnt): continue
                        b2 = self.swap(path, A)
                        assert b2 in pr.D and pr.D[b2] <= self.omega + 1 - self.val(o, X), ('Corollary 11.1+', Bs, b2)
                        out.append((o, z, x, c, len(path) - 2))
        return out

    def C4p(self, pairs=None):
        """Corollary 11.2+ (the kappa swap): a free o keeps a safe X (default: best owners, optimal X); a frozen x whose
        good g is needed by exactly one agent a_1 other than o, and g ∉ N_o(X); a need path z, ..., a_1, x with o not on
        it; x takes a pair A ⊆ ((J ∪ B_z) minus X) ∩ R_x with v_x(A) > v_x(g) and theta_x(X) <= v_x(A):
        def(P') <= omega + 1 - |X| - u_o(X). Returns the (o, x, k) certified."""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        out = []
        if pairs is None: pairs = [(o, X) for o in self.best for X in pr.OWN[Bs][o][1]]
        for o, X in pairs:
            NoX = I.needs(o, X)
            for x in self.F:
                g = Bs[x]
                if g & NoX: continue
                others = [i for i in range(I.n) if i != o and P.N[i] & g]
                if len(others) != 1: continue
                a1 = others[0]; vg = I.val(x, g)
                for path in self.paths_to(x):
                    if path[-2] != a1 or o in path: continue
                    z = path[0]
                    pool = ((P.J | Bs[z]) & ~X) & I.R[x]
                    for A in itertools.combinations(list(bits(pool)), 2):
                        A = mask(A)
                        if I.val(x, A) <= vg or self.thr(x, X, A): continue
                        b2 = self.swap(path, A)
                        assert b2 in pr.D and pr.D[b2] <= self.omega + 1 - self.val(o, X), ('Corollary 11.2+', Bs, b2)
                        out.append((o, x, len(path) - 2))
        return out

    def C3p(self):
        """Corollary 8.2+; returns the (x, path, h) certified (first found)"""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        for x in self.F:
            if not bigtop(I, x): continue
            g = Bs[x]
            if max(I.sets[x], key=lambda q: I.v[x][q]) != next(bits(g)): continue
            nd = [i for i in range(I.n) if P.N[i] & g]
            if len(nd) != 1: continue
            L = I.R[x] & ~g
            for path in self.paths_to(x):
                z = path[0]
                for h in [None] + [h for h in P.free if h != z]:
                    G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                    if L & ~G: continue
                    hs = [None]
                    if h is not None:
                        hs = [mask(B) for k in range(3) for B in itertools.combinations(list(bits((G & ~L) & I.R[h])), k)
                              if (Bs[h] & ~mask(B)) and not (I.needs(h, mask(B)) & ~P.NA)
                              and not (I.needs(h, mask(B)) & g)]
                    for Bh in hs:
                        hd = self.hold(path, h, Bh)
                        W = G & ~(Bh or 0)
                        safe = lambda Z: not any(self.thr(w, Z, hd.get(w, Bs[w])) for w in range(I.n) if w != x)
                        if not safe(L): continue
                        rest = list(bits(W & ~L)); bestZ = None
                        for k in range(len(rest), -1, -1):
                            for K in itertools.combinations(rest, k):
                                if safe(L | mask(K)): bestZ = L | mask(K); break
                            if bestZ is not None: break
                        for A in self.adm(x, L):
                            b2 = self.swap(path, A, h, Bh)
                            assert b2 in pr.D and pr.D[b2] <= self.omega + 1 - pc(bestZ), ('Corollary 8.2+', Bs, b2)
                        if pc(bestZ) + 1 <= self.V: continue
                        return [(x, path, h)]
        return []


# ------------------------------------------------------------------ drivers
def coverage(files, stuck=False, light=False):
    """the T3-stage states of f2_shapes.py dumps (or, with stuck=True, the T3-stage states among the T1-stuck records of
    k4/dl13_stuck.py dumps, any f >= 1, whose case and repairs are computed here)"""
    from f2_shapes import State
    cnt = collections.Counter(); ex = {}; cache = {}
    for fn in files:
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Prof({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, fmin=1)
            pr = cache[key]; Bs = tup(r['Bs']); ctx = Ctx(pr, Bs)
            if stuck:
                if not pr.ok or not pr.t3_stage(Bs): continue
                cs, _, thetas, _, _ = State(pr, Bs).case()
                from f2_lib import chain_shape
                r = dict(r, case=cs, thetas=sorted(thetas), src=r.get('src', fn),
                         reps=[{'k': len(W), 'needp': chain_shape(pr.PA[Bs], pr.PA[B2], x, z, W)[2]}
                               for B2, x, z, W, _ in pr.t3_moves(Bs)])
            assert pr.t3_stage(Bs)
            cnt['states'] += 1; cnt['states f=%d' % pr.I.f] += 1
            P = ctx.P
            if not any(P.frozen[x] and any(ctx.I.threat(x, P.W(o), P.bv[x]) for o in P.free) for x in range(ctx.I.n)):
                cnt['SX fails: no frozen agent exposed w.r.t. a free agent'] += 1
            cnt['Lemma P: a frozen agent without a need path (not T4-optimal)'] += ctx.lemmaP()
            if not light:
                n6, n8 = ctx.check_6_8(); cnt['Lemma 6+ chain swaps checked'] += n6; cnt['Lemma 8+ values checked'] += n8
                nc, rot = ctx.check_closure(); cnt['Lemma C compositions checked'] += nc
                cnt['Proposition N: not T4-optimal, rotated to a T4-optimal state of equal deficit'] += 1 if rot else 0
            sb = ctx.single_blocks()
            c1 = ctx.C1p(sb); c2 = ctx.C2p(sb); c3 = ctx.C3p(); c4 = ctx.C4p()
            plain = any(t[-1] == 0 for t in c1 + c2 + c4) or any(len(t[1]) == 2 for t in c3)
            first = ('C1+' if c1 else ('C2+' if c2 else ('C3+' if c3 else ('C4+' if c4 else 'none'))))
            if not c1 and c4: cnt[(r['case'], 'Corollary 11.2+ applies where Corollary 9.1+ does not')] += 1
            if first == 'none':
                c8, c11 = ctx.certificates()
                first = 'C8+' if c8 else ('C11+' if c11 else 'none')
                if first != 'none': plain = (c8 or c11)[0] == 0
            if r['case'] == 'A-S1' and 'ok' not in r['thetas']:
                cnt[('A-S1, every S1 triple theta-fails', 'Corollary 11.2+ (kappa swap) applies' if c4 else
                     'Corollary 11.2+ does not apply')] += 1
            chain_only = not any(rp['k'] == 0 for rp in r['reps'])
            row = (r['case'], 'chain-only' if chain_only else 'plain T3 exists')
            cnt[row + (first,)] += 1
            cnt[row + ('certified by a plain (k = 0) corollary' if plain else 'only by a chain corollary (k >= 1)'
                       if first != 'none' else 'not certified',)] += 1
            if chain_only and r['reps']:
                cnt[('chain-only', 'least |W| of an improving T3+ move = %d' % min(rp['k'] for rp in r['reps']))] += 1
                cnt[('chain-only', 'some improving chain is a path swap (need path)' if any(rp['needp'] for rp in r['reps'])
                     else 'no improving chain is a path swap')] += 1
            if first == 'none':
                cur = ex.get(r['case'])
                cand = (len(r['sets']), r['m'], r['src'], r['sets'], r['vals'], r['Bs'])
                if cur is None or cand[:2] < cur[:2]: ex[r['case']] = cand
    for k in sorted(cnt, key=str): print('  %-100s %d' % (' | '.join(k) if isinstance(k, tuple) else k, cnt[k]))
    for k in sorted(ex):
        print('  smallest uncertified, case %s: n=%d m=%d %s sets=%s vals=%s P=%s' % ((k,) + ex[k]))


def caseb(files):
    """at every def > 0 state of the profiles of the dumps: the single frozen blockers of best owners whose needers are
    all frozen, and whether the owner is the free end of a need path to the blocker (case B-S1c) or not (case B), by
    stage (T3 stage; least deficit of its key but a (T4) move improves; not the least deficit of its key)"""
    from f2_shapes import path_ends_all
    seen = set(); cnt = collections.Counter(); ex = {}
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            key = json.dumps([r['sets'], r['vals']])
            if key in seen: continue
            seen.add(key)
            pr = Prof({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, fmin=2)
            if not pr.ok: continue
            cnt['profiles'] += 1
            for Bs in pr.mp:
                if pr.D[Bs] <= 0: continue
                P = pr.PA[Bs]
                st = 'T3 stage' if pr.t3_stage(Bs) else ('key-minimal, a (T4) move improves'
                                                         if pr.D[Bs] == pr.dstar[pr.key[Bs]] else 'not key-minimal')
                cnt[(st, 'def>0 states')] += 1
                for o, X, c, w in pr.single_blocks(Bs):
                    if not P.frozen[w] or pr.free_needers(Bs, w): continue
                    ends = path_ends_all(pr, Bs, w)
                    tag = 'owner a free end (B-S1c)' if o in ends else ('owner not a free end (B)' if ends
                                                                       else 'no free end (need cycle)')
                    cnt[(st, 'single blocks by a frozen agent with frozen needers only', tag)] += 1
                    if o not in ends:
                        cur = ex.get((st, tag)); cand = (len(r['sets']), r['m'], r['sets'], r['vals'], lst(Bs), o, w)
                        if cur is None or cand[:2] < cur[:2]: ex[(st, tag)] = cand
    for k in sorted(cnt, key=str): print('  %-110s %d' % (' | '.join(k) if isinstance(k, tuple) else k, cnt[k]))
    for k, v in sorted(ex.items()):
        print('  smallest %s: n=%d m=%d sets=%s vals=%s P=%s owner %d blocker %d' % ((' | '.join(k),) + v))


def rand_inst(rng, nmax, mmax):
    """strict, strictly balanced 3- and 4-good agents, every good valued; a few 'hot' goods are many agents' tops"""
    while True:
        n = rng.randint(3, nmax)
        m = rng.randint(min(2 * n - 2, mmax), min(mmax, 3 * n))      # omega = f - (2n - m) >= 1 needs m large
        goods = list(range(m)); hot = rng.sample(goods, rng.randint(2, 3))
        sets, vals = [], []
        for _ in range(n):
            k = rng.choice((3, 4))
            top = rng.choice(hot)
            S = [top] + rng.sample([g for g in goods if g != top], k - 1)
            while True:
                vs = [rng.randint(1, 12) for _ in S]
                vs[0] = max(vs)
                sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(vs, r)]
                if len(set(sums)) == len(sums) and all(2 * v < sum(vs) for v in vs): break
            sets.append(S); vals.append(vs)
        if set(g for S in sets for g in S) == set(goods):
            return {'sets': sets, 'vals': vals, 'm': m}


def propn(files):
    """Proposition N's dichotomy (k4/f2.md §3.3) at every T3-stage state of the dumps that is not T4-optimal: the
    rotation to a T4-optimal P* of equal deficit, then (i) def*(κ(P*)) < def(P), or (ii) P* at the T3 stage, and in
    case (ii) every improving (T3⁺) move from P* composes to one from P (Lemma CL)"""
    cnt = collections.Counter(); cache = {}; ex = None
    for fn in files:
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            if r['t4opt']: continue
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Prof({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, fmin=1)
            pr = cache[key]; Bs = tup(r['Bs']); ctx = Ctx(pr, Bs)
            assert pr.t3_stage(Bs)
            _, rot = ctx.check_closure()
            assert rot in ('i', 'ii'), ('not rotated', Bs)
            cnt['T3-stage states not T4-optimal'] += 1
            cnt['case (%s)' % rot] += 1
            if rot == 'ii':
                for B2, x, z, W, h in pr.t3_moves(ctx.pstar):
                    assert t3plus(ctx.P, pr.PA[B2]) is not None, ('Lemma CL lift', Bs, ctx.pstar, B2)
                    cnt['case (ii): improving (T3+) moves of P* lifted to P'] += 1
            else:
                cand = (len(r['sets']), r['m'], sum(map(sum, r['vals'])), r['sets'], r['vals'], r['Bs'],
                        lst(ctx.pstar), pr.dstar[pr.key[ctx.pstar]])
                if ex is None or cand[:3] < ex[:3]: ex = cand
    for k in sorted(cnt): print('  %-70s %d' % (k, cnt[k]))
    if ex: print('  smallest case (i): n=%d m=%d sets=%s vals=%s P=%s P*=%s def*(key(P*))=%d' % (ex[:2] + ex[3:]))


def check_run(profiles, all_states=False):
    """every check at every def > 0 state (with all_states: Lemmas P, 6+, 8+, C at every min-frozen state)"""
    cnt = collections.Counter()
    for d in profiles:
        pr = Prof(d, fmin=1)
        cnt['instances'] += 1
        if not pr.ok: continue
        cnt['instances f>=1, omega>=1'] += 1; cnt['instances f=%d' % pr.I.f] += 1
        for Bs in pr.mp:
            ctx = Ctx(pr, Bs)
            cnt['Lemma P: frozen agent without a need path (not T4-optimal)'] += ctx.lemmaP()
            if pr.D[Bs] <= 0 and not all_states: continue
            cnt['states checked'] += 1
            n6, n8 = ctx.check_6_8(); cnt['Lemma 6+ chain swaps'] += n6; cnt['Lemma 8+ values'] += n8
            nc, rot = ctx.check_closure(); cnt['Lemma C compositions'] += nc; cnt['Proposition N rotations'] += 1 if rot else 0
            if pr.D[Bs] <= 0: continue
            cnt['def>0 states'] += 1; cnt['def>0 states f=%d' % pr.I.f] += 1
            pairs = ctx.all_pairs()
            sb = ctx.single_blocks(pairs)
            c1 = ctx.C1p(sb); c2 = ctx.C2p(sb); c3 = ctx.C3p(); c4 = ctx.C4p(pairs)
            cnt['(o, X) pairs (every free owner, every safe bundle)'] += len(pairs)
            cnt['C4+ applies'] += bool(c4); cnt['C4+ applies with k >= 1'] += any(t[-1] >= 1 for t in c4)
            cnt['C1+ applies'] += bool(c1); cnt['C1+ applies with k >= 1'] += any(t[-1] >= 1 for t in c1)
            cnt['C2+ applies'] += bool(c2); cnt['C2+ applies with k >= 1'] += any(t[-1] >= 1 for t in c2)
            cnt['C3+ applies'] += bool(c3); cnt['C3+ applies with k >= 1'] += any(len(t[1]) > 2 for t in c3)
    for k in sorted(cnt): print('  %-70s %d' % (k, cnt[k]))


def main(argv):
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    rest = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/f2_lemmas.py ' + ' '.join(argv), flush=True)
    if 'random' in opt:
        rng = random.Random(int(opt.get('seed', 1)))
        check_run((rand_inst(rng, int(opt.get('nmax', 5)), int(opt.get('mmax', 12))) for _ in range(int(rest[0]))))
    elif 'caseb' in opt:
        caseb(rest)
    elif 'propn' in opt:
        propn(rest)
    elif 'profiles' in opt:
        from f2_shapes import collect
        check_run((d for d, _ in collect(rest, opt)), all_states='all' in opt)
    else:
        coverage(rest, stuck='stuck' in opt, light='light' in opt)
    print('# no assertion failed')


if __name__ == '__main__':
    main(sys.argv[1:])
