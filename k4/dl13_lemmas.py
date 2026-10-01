#!/usr/bin/env python3
"""The role-swap lemmas of k4/dl13.md, checked and measured (workstream proof/k4-dl13).

Every conclusion is asserted against the exact deficits (k4/dl2_classify.PA.deficit, i.e. Lemma H1 of k4/hall.md;
with --check also against k4/suite/model.py's direct removal-only deficit):
  L8   Lemma 8 (the unfrozen agent as owner), its equality form: for every role swap with a needer and at most one
       helper allowed by Lemma 6 (k4/dl2.md), Val_{P'}(x) = max over the bundles Z of x in P' of |Z| + ubar(Z) + iota(Z),
       computed from P's data; checked at every swap of every def > 0 state (--swaps) or of the stuck states.
  L10  Lemma 10 (the theta-dichotomy) wherever its hypothesis holds at an S1 shape.
  C1   Corollary 9.1 (owner swap at a best owner o that needs the frozen good: X ∪ {c} threatens only x, and o holding
       g is not threatened by it): def(P') <= def(P) - 1 for every admissible A ⊆ (X ∪ {c}) ∩ R_x.
  C1*  Lemma 9 with any bundle Z ⊆ W_o of x (Z threatens x holding g and nobody outside {o, x}; theta_o(Z) <= v_o(g)),
       o a best owner needing g, X optimal with v_o(X) < v_o(g), |Z| + iota(Z) > |X|.
  C2   Corollary 11.1 (blocker swap): X ∪ {c} threatens only a free needer z != o of g; z holding g and x holding A are
       not threatened by it; A ⊆ (J ∪ B_z) minus (X ∪ {c}) admissible; e* = 0.
  C3   Corollary 8.2 (Lemma 7 swap): x big-top frozen on its top g, no agent other than the needer z needs g, at most
       one helper h; the lower goods L_x lie in x's bundle Z (in P'), which is safe in P'; |Z| + 1 > Val*(P).
A state is *certified* by a construction when its hypotheses hold with the stated gain; the conclusion is asserted.

usage: python3 k4/dl13_lemmas.py STUCK.jsonl.gz ... [--lemma8]   (dumps of k4/dl13_stuck.py; coverage of the
                                                                       T1-stuck states; --lemma8: Lemma 8 at every swap)
       python3 k4/dl13_lemmas.py --stats STUCK.jsonl.gz ...   (the regime statistics of k4/dl13.md §3)
       python3 k4/dl13_lemmas.py --candidates STUCK.jsonl.gz ...   (the failed candidates of k4/dl13.md §5)
       python3 k4/dl13_lemmas.py --swaps catalog FILE [--every=E] [--max=N]   (Lemma 8 at every swap of every def > 0
                                                                               state with f >= 1; C1, C2, C3 asserted)
       python3 k4/dl13_lemmas.py --swaps random N [--seed=S] [--nmax=4] [--mmax=10]  (random strict instances that
                                                                               need not be cores, as k4/dl2_lemma_random.py)"""
import collections, gzip, itertools, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from dl2_classify import best_owners, counted, bigtop
from dl13_stuck import Profile


def tup(L): return tuple(mask(b) for b in L)


class Ctx:
    """one state P (bases Bs) of a profile, with helpers for the lemmas"""

    def __init__(self, pr, Bs):
        self.pr, self.Bs, self.I = pr, Bs, pr.I
        self.P = pr.PA[Bs]; self.D = pr.D[Bs]
        self.best = best_owners(pr.OWN[Bs])
        self.V = pr.OWN[Bs][self.best[0]][0] if self.best else None
        P = self.P
        self.omega = pc(P.J) - P.S

    def thr(self, w, Z, hold):
        return self.I.threat(w, Z, self.I.val(w, hold))

    def blockers(self, o, Z, hold=None):
        """agents other than o threatened by Z, each holding its base (or hold[w] if given)"""
        hold = hold or {}
        return [w for w in range(self.I.n) if w != o and self.thr(w, Z, hold.get(w, self.Bs[w]))]

    def admissible(self, i, pool):
        I, P = self.I, self.P
        out = []
        for k in (1, 2):
            for A in itertools.combinations(list(bits(pool & I.R[i])), k):
                A = mask(A)
                if not (I.needs(i, A) & ~P.NA): out.append(A)
        return out

    def needers(self, x):
        return [i for i in range(self.I.n) if self.P.N[i] & self.Bs[x]]

    def free_needers(self, x):
        return [i for i in self.needers(x) if not self.P.frozen[i]]

    def new(self, x, z, A, h=None, Bh=None):
        b = list(self.Bs); b[z] = self.Bs[x]; b[x] = A
        if h is not None: b[h] = Bh
        return tuple(b)

    # ------------------------------------------------------------- Lemma 8: x as owner after a swap
    def lemma8_value(self, x, z, A, h=None, Bh=None):
        """max over bundles Z of x in P' (A ⊆ Z ⊆ G minus B'_h) that are safe in P' of |Z| + ubar(Z) + iota(Z),
        all computed from P (k4/dl13.md Lemma 8)"""
        I, P, Bs = self.I, self.P, self.Bs
        g = Bs[x]
        G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
        W = G & ~(Bh or 0)
        Nrest = I.needs(z, g) | (I.needs(h, Bh) if h is not None else 0)
        for i in range(I.n):
            if i not in (x, z, h): Nrest |= P.N[i]
        hold = {z: g}
        if h is not None: hold[h] = Bh
        rest = list(bits(W & ~A))
        best = -1
        for k in range(len(rest) + 1):
            for K in itertools.combinations(rest, k):
                Z = A | mask(K)
                if self.blockers(x, Z, hold): continue
                NZ = I.needs(x, Z)
                ub = sum(1 for w in range(I.n) if P.frozen[w] and w != x and not (Bs[w] & (NZ | Nrest)))
                io = 1 if (I.val(x, Z) > I.val(x, g) and not (g & Nrest)) else 0
                best = max(best, pc(Z) + ub + io)
        return best

    def swaps(self):
        """every role swap with a needer and at most one helper giving up a good, as allowed by Lemma 6:
        (x, z, A, h, B'_h)"""
        I, P, Bs = self.I, self.P, self.Bs
        for x in range(I.n):
            if not P.frozen[x]: continue
            for z in self.free_needers(x):
                for h in [None] + [h for h in P.free if h != z]:
                    G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                    for A in self.admissible(x, G):
                        if h is None:
                            yield x, z, A, None, None; continue
                        for k in range(3):
                            for Bh in itertools.combinations(list(bits((G & ~A) & I.R[h])), k):
                                Bh = mask(Bh)
                                if not (Bs[h] & ~Bh): continue          # the helper gives up a good of its base
                                if I.needs(h, Bh) & ~P.NA: continue
                                yield x, z, A, h, Bh

    def check_lemma8(self):
        n = 0
        for x, z, A, h, Bh in self.swaps():
            b2 = self.new(x, z, A, h, Bh)
            assert b2 in self.pr.D, ('Lemma 6 violated', self.Bs, b2)
            P2 = self.pr.PA[b2]
            assert P2.NA == self.P.NA and P2.frozen[z] and not P2.frozen[x], ('Lemma 6 frozen set', self.Bs, b2)
            exact = self.pr.OWN[b2][x][0]
            val = self.lemma8_value(x, z, A, h, Bh)
            assert val == exact, ('Lemma 8 violated', self.Bs, b2, val, exact)
            n += 1
        return n

    # ------------------------------------------------------------- key-optimal, T4-stuck (the RT4 architecture)
    def key(self, Bs=None):
        Bs = self.Bs if Bs is None else Bs
        P = self.pr.PA[Bs]
        return tuple(Bs[i] if P.frozen[i] else None for i in range(self.I.n))

    def key_optimal(self):
        """no (T1) or (T2) move lowers the deficit: def(P) is the least deficit over the min-frozen P' with P's key
        (needed set, frozen agents and their goods; k4/dl2.md §3: (T1) ∪ (T2) are exactly the moves inside a key)"""
        k = self.key()
        return all(self.pr.D[B2] >= self.D for B2 in self.pr.mp if self.key(B2) == k)

    def t4_stuck(self):
        return not self.pr.t4_moves(self.Bs)

    # ------------------------------------------------------------- Proposition T (b), (c), (d)
    def check_propT(self, stuck):
        """(b) every best owner's optimal X misses a junk good, and every such good has a blocker; (c) at a T1-stuck
        state, a single free blocker y of c has no admissible B' != B_y inside (B_y ∪ J) minus (X ∪ {c}) with
        v_y(B') >= v_y(B_y) (or no counted good in N_y(B')) that X ∪ {c} does not threaten; (d) the only needer of a
        needed good, if it is free, keeps needing it at every admissible re-base. Returns the number of checks made."""
        I, P, Bs = self.I, self.P, self.Bs
        n = 0
        for o in self.best:
            for X in self.pr.OWN[Bs][o][1]:
                C = P.J & ~X
                assert C, ('Proposition T(b): C empty', Bs, o)
                cnt = counted(P, o, X)
                for c in bits(C):
                    ws = self.blockers(o, X | (1 << c))
                    assert ws, ('Proposition T(b): unblocked junk good', Bs, o, c); n += 1
                    if not stuck or len(ws) != 1 or P.frozen[ws[0]]: continue
                    y = ws[0]; Y = X | (1 << c)
                    for k in (0, 1, 2):
                        for Bl in itertools.combinations(list(bits(((Bs[y] | P.J) & ~Y) & I.R[y])), k):
                            B2 = mask(Bl)
                            if B2 == Bs[y] or I.needs(y, B2) & ~P.NA: continue
                            if I.val(y, B2) < P.bv[y] and any(Bs[w] & I.needs(y, B2) for w in cnt): continue
                            assert self.thr(y, Y, B2), ('Proposition T(c) violated', Bs, o, c, y, B2); n += 1
        for x in range(I.n):
            if not P.frozen[x]: continue
            nd = self.needers(x)
            if len(nd) != 1 or P.frozen[nd[0]]: continue
            z = nd[0]
            for k in (0, 1, 2):
                for Bl in itertools.combinations(list(bits((Bs[z] | P.J) & I.R[z])), k):
                    B2 = mask(Bl)
                    if I.needs(z, B2) & ~P.NA: continue
                    assert I.needs(z, B2) & Bs[x], ('Proposition T(d) violated', Bs, z, B2); n += 1
        return n

    # ------------------------------------------------------------- the S1 shape, Lemma 10, C1, C1*
    def s1_triples(self):
        """(o, X, c, x): o a best owner, X optimal, c ∈ J \\ X, X ∪ {c} threatens x (frozen, o needs its good) and
        nobody else outside {o}"""
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for o in self.best:
            for X in self.pr.OWN[Bs][o][1]:
                for c in bits(P.J & ~X):
                    ws = self.blockers(o, X | (1 << c))
                    if len(ws) == 1 and P.frozen[ws[0]] and P.N[o] & Bs[ws[0]]:
                        out.append((o, X, c, ws[0]))
        return out

    def lemma10(self, o, Z, g):
        """theta_o(Z) > v_o(g), g ∈ N_o: (a) a set of <= 2 goods of Z ∩ R_o worth more than g, and then another agent
        needs g; or (b) o is big-top with top g and R_o \\ {g} ⊆ Z. Returns 'a' or 'b'."""
        I, P = self.I, self.P
        vg = I.val(o, g); Q = list(bits(Z & I.R[o]))
        if any(I.val(o, mask(q)) > vg for k in (1, 2) for q in itertools.combinations(Q, k)):
            assert any(P.N[i] & g for i in range(I.n) if i != o), ('Lemma 10(a): nobody else needs g', self.Bs, o)
            return 'a'
        a = I.sets[o]
        assert len(a) == 4 and bigtop(I, o) and max(a, key=lambda q: I.v[o][q]) == next(bits(g)) \
            and not (I.R[o] & ~g & ~Z), ('Lemma 10(b) violated', self.Bs, o)
        return 'b'

    def C1(self):
        out = []; kinds = set()
        for o, X, c, x in self.s1_triples():
            g = self.Bs[x]; Z = X | (1 << c)
            if self.thr(o, Z, g):
                kinds.add('theta-' + self.lemma10(o, Z, g)); continue
            kinds.add('ok')
            As = self.admissible(x, Z)
            assert As, ('C1: no admissible A', self.Bs)
            iota = 0 if any(self.P.N[i] & g for i in range(self.I.n) if i not in (o, x)) else 1
            for A in As:
                b2 = self.new(x, o, A)
                assert b2 in self.pr.D and self.pr.D[b2] <= self.D - 1 - iota, ('Corollary 9.1 violated', self.Bs, b2)
            out.append((o, x, c))
        return out, kinds

    def C1star(self):
        """Lemma 9 at a best owner o needing g with any bundle Z of x inside W_o"""
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for o in self.best:
            for x in range(I.n):
                if not P.frozen[x] or not (P.N[o] & Bs[x]): continue
                g = Bs[x]
                Ng = I.needs(o, g)
                iota_ok = not any(P.N[i] & g for i in range(I.n) if i not in (o, x))
                iota = 1 if iota_ok else 0
                W = P.W(o)
                for X in self.pr.OWN[Bs][o][1]:
                    cnt = counted(P, o, X)
                    e = sum(1 for w in cnt if w == x or Bs[w] & Ng)
                    if e: continue        # Corollary 9.2 is stated with e = 0 (the bound is checked below anyway)
                    for k in range(pc(X) + 1 - iota, pc(W) + 1):
                        for Zl in itertools.combinations(list(bits(W)), k):
                            Z = mask(Zl)
                            if not self.thr(x, Z, g) or self.thr(o, Z, g): continue
                            if [w for w in self.blockers(o, Z) if w != x]: continue
                            for A in self.admissible(x, Z):
                                b2 = self.new(x, o, A)
                                bound = self.omega + 2 - pc(Z) - (len(cnt) - e) - iota
                                assert b2 in self.pr.D and self.pr.D[b2] <= bound and self.pr.D[b2] < self.D, \
                                    ('Lemma 9 violated', Bs, b2, bound)
                            out.append((o, x, sorted(bits(Z))))
                            return out
        return out

    # ------------------------------------------------------------- C2: blocker swap
    def C2(self):
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for o in self.best:
            for X in self.pr.OWN[Bs][o][1]:
                cnt = counted(P, o, X)
                for c in bits(P.J & ~X):
                    Y = X | (1 << c)
                    ws = self.blockers(o, Y)
                    if len(ws) != 1: continue
                    z = ws[0]
                    if P.frozen[z]: continue
                    for x in range(I.n):
                        if not P.frozen[x] or not (P.N[z] & Bs[x]): continue
                        g = Bs[x]
                        if self.thr(z, Y, g): continue
                        for A in self.admissible(x, (P.J | Bs[z]) & ~Y):
                            if self.thr(x, Y, A): continue
                            NxA = I.needs(x, A)
                            if any(Bs[w] & NxA for w in cnt): continue
                            b2 = self.new(x, z, A)
                            assert b2 in self.pr.D and self.pr.D[b2] <= self.D - 1, ('Corollary 11.1 violated', Bs, b2)
                            out.append((o, x, z, c))
        return out

    # ------------------------------------------------------------- C2*: Lemma 11 at a best owner (no helper)
    def C2star(self):
        """Lemma 11: a best owner o keeps its base through a swap of x with a needer z != o (no helper); X optimal
        avoiding A; Y ⊇ X a bundle of o in P' safe in P'; bound omega + 2 - |Y| - (u_o(X) - e*) - kappa"""
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for o in self.best:
            for x in range(I.n):
                if not P.frozen[x]: continue
                g = Bs[x]
                for z in self.free_needers(x):
                    if z == o: continue
                    for A in self.admissible(x, P.J | Bs[z]):
                        b2 = self.new(x, z, A)
                        Jn = (P.J | Bs[z]) & ~A
                        hold = {x: A, z: g}
                        Nch = I.needs(x, A) | I.needs(z, g)
                        for X in self.pr.OWN[Bs][o][1]:
                            if X & A: continue
                            cnt = counted(P, o, X)
                            es = sum(1 for w in cnt if w in (x, z) or Bs[w] & Nch)
                            rest = list(bits(Jn & ~X)); best = None
                            for k in range(len(rest), 0, -1):
                                for K in itertools.combinations(rest, k):
                                    Y = X | mask(K)
                                    if self.blockers(o, Y, hold): continue
                                    Nrest = I.needs(o, Y) | Nch
                                    for i in range(I.n):
                                        if i not in (o, x, z): Nrest |= P.N[i]
                                    kappa = 0 if g & Nrest else 1
                                    gain = pc(Y) - pc(X) - es + kappa
                                    if gain > 0: best = (Y, kappa, gain); break
                                if best: break
                            if best is None: continue
                            Y, kappa, gain = best
                            bound = self.omega + 2 - pc(Y) - (len(cnt) - es) - kappa
                            assert self.pr.D[b2] <= bound and self.pr.D[b2] < self.D, ('Lemma 11 violated', Bs, b2)
                            out.append((o, x, z)); return out
        return out

    # ------------------------------------------------------------- Lemma 11 at any owner, any swap (certificate)
    def lemma11_value(self, o, x, z, A, h=None, Bh=None):
        """max over bundles Y of o in P' that are safe in P' of |Y| + (u_o(X) - e*) + kappa with X = Y ∩ W_o (a bundle
        of o in P missing the new bases), all from P's data (k4/dl13.md Lemma 11); the bound is asserted"""
        I, P, Bs = self.I, self.P, self.Bs
        g = Bs[x]
        G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
        Jn = G & ~A & ~(Bh or 0)
        hold = {x: A, z: g}
        if h is not None: hold[h] = Bh
        Nch = I.needs(x, A) | I.needs(z, g) | (I.needs(h, Bh) if h is not None else 0)
        Nrest0 = Nch
        for i in range(I.n):
            if i not in (o, x, z, h): Nrest0 |= P.N[i]
        ch = {x, z} | ({h} if h is not None else set())
        b2 = self.new(x, z, A, h, Bh)
        rest = list(bits(Jn)); best = -1
        for k in range(len(rest) + 1):
            for K in itertools.combinations(rest, k):
                Y = Bs[o] | mask(K)
                if self.blockers(o, Y, hold): continue
                X = Y & P.W(o)
                cnt = counted(P, o, X)
                es = sum(1 for w in cnt if w in ch or Bs[w] & Nch)
                kappa = 0 if g & (I.needs(o, Y) | Nrest0) else 1
                val = pc(Y) + len(cnt) - es + kappa
                assert self.pr.D[b2] <= self.omega + 2 - val, ('Lemma 11 violated', Bs, b2, o)
                best = max(best, val)
        return best

    def certified_by_8_11(self, moves):
        """some improving (T3) move whose deficit drop Lemma 8 (x the owner) or Lemma 11 (an owner that does not
        move) accounts for: 'L8', 'L11', or None"""
        I, Bs = self.I, self.Bs
        out = None
        for B2, x, z, h in moves:
            A = B2[x]; Bh = B2[h] if h is not None else None
            if self.lemma8_value(x, z, A, h, Bh) > self.V: return 'L8'
            for o in self.P.free:
                if o in (x, z, h): continue
                if self.lemma11_value(o, x, z, A, h, Bh) > self.V: out = 'L11'
        return out

    # ------------------------------------------------------------- C3: the Lemma 7 swap of a big-top x
    def C3(self):
        I, P, Bs = self.I, self.P, self.Bs
        out = []
        for x in range(I.n):
            if not P.frozen[x] or not bigtop(I, x): continue
            g = Bs[x]
            if max(I.sets[x], key=lambda q: I.v[x][q]) != next(bits(g)): continue
            L = I.R[x] & ~g
            fz = self.free_needers(x)
            if len(self.needers(x)) != 1 or len(fz) != 1: continue
            z = fz[0]
            for h in [None] + [h for h in P.free if h != z]:
                G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                if L & ~G: continue
                hs = [None]
                if h is not None:
                    hs = []
                    for k in range(3):
                        for Bh in itertools.combinations(list(bits((G & ~L) & I.R[h])), k):
                            Bh = mask(Bh)
                            if (Bs[h] & ~Bh) and not (I.needs(h, Bh) & ~P.NA) and not (I.needs(h, Bh) & g):
                                hs.append(Bh)
                for Bh in hs:
                    hold = {z: g}
                    if h is not None: hold[h] = Bh
                    W = G & ~(Bh or 0)
                    if self.blockers(x, L, hold): continue
                    rest = list(bits(W & ~L)); bestZ = None
                    for k in range(len(rest), -1, -1):
                        for K in itertools.combinations(rest, k):
                            if not self.blockers(x, L | mask(K), hold): bestZ = L | mask(K); break
                        if bestZ is not None: break
                    if pc(bestZ) + 1 <= self.V: continue
                    for A in self.admissible(x, L):
                        b2 = self.new(x, z, A, h, Bh)
                        assert b2 in self.pr.D and self.pr.D[b2] <= self.omega + 1 - pc(bestZ) \
                            and self.pr.D[b2] < self.D, ('Corollary 8.2 violated', Bs, b2)
                    out.append((x, z, h))
                    return out
        return out


def mechanism(pr, Bs, t3):
    """A: a no-helper repair with x a best owner afterwards; B*: one with an unmoved best owner of P; B: one with
    another unmoved owner; H: every repair has a helper"""
    best = set(best_owners(pr.OWN[Bs])); mech = set()
    for m in t3:
        B2 = tup(m['Bs']); x, h = m['x'], m['h']
        for o in best_owners(pr.OWN[B2]):
            t = 'X' if o == x else ('H' if o == h else ('O*' if o in best else 'O'))
            mech.add(('h' if h is not None else '-') + t)
    if '-X' in mech: return 'A'
    if '-O*' in mech: return 'B*'
    if '-O' in mech: return 'B'
    return 'H'


def regime(ctx):
    P, I = ctx.P, ctx.I
    if sum(P.frozen) >= 2:
        return 'f>=2, T4-optimal' if ctx.pr.t4_optimal(ctx.Bs) else 'f>=2, not T4-optimal'
    x = P.frozen.index(True)
    return 'f=1, %s needer%s' % (('1', '') if len(ctx.needers(x)) == 1 else ('>=2', 's'))


def coverage(files, check=False, check8=False):
    cnt = collections.Counter(); ex = {}; n8 = 0
    cache = {}
    for fn in files:
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Profile({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, check)
            pr = cache[key]; Bs = tup(r['Bs']); ctx = Ctx(pr, Bs)
            if check8: n8 += ctx.check_lemma8()
            cnt[('propT checks',)] += ctx.check_propT(True)
            c1, kinds = ctx.C1()
            c1s = ctx.C1star() if not c1 else []
            c2 = ctx.C2()
            c3 = ctx.C3() if not (c1 or c2) else []
            c2s = ctx.C2star() if not (c1 or c1s or c2 or c3) else []
            first = 'C1' if c1 else ('C2' if c2 else ('C3' if c3 else ('C1*' if c1s else ('C2*' if c2s else 'none'))))
            if first == 'none':
                moves = [(tup(m['Bs']), m['x'], m['z'], m['h']) for m in r['t3']]
                l = ctx.certified_by_8_11(moves)
                if l: first = l
            shape = 'S1 ' + '/'.join(sorted(kinds)) if kinds else 'no S1 shape'
            rg = regime(ctx); mech = mechanism(pr, Bs, r['t3'])
            for key2 in [('all', first), (rg, first), (rg, shape, first), ('uncovered', rg, mech) if first == 'none' else None]:
                if key2 is None: continue
                cnt[key2] += 1
            if first == 'none':
                k = (rg, mech)
                cur = ex.get(k)
                cand = (len(r['sets']), r['m'], r['src'], r['sets'], r['vals'], r['Bs'])
                if cur is None or cand[:2] < cur[:2]: ex[k] = cand
            cnt[('states',)] += 1
    return cnt, ex, n8


def stats(files):
    """the regime statistics of k4/dl13.md §3: S1 shapes, theta kinds, big-top frozen agents, where L_x lies"""
    cnt = collections.Counter(); cache = {}
    for fn in files:
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Profile({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
            pr = cache[key]; Bs = tup(r['Bs']); ctx = Ctx(pr, Bs); I, P = ctx.I, ctx.P
            rg = regime(ctx); n3 = 'n=3' if I.n == 3 else 'n>=4'
            cnt[(rg, 'states')] += 1; cnt[(rg, n3, 'states')] += 1
            trip = ctx.s1_triples()
            if trip: cnt[(rg, 'S1 shape')] += 1; cnt[(rg, n3, 'S1 shape')] += 1
            _, kinds = ctx.C1()
            if trip and 'ok' not in kinds:
                cnt[(rg, 'S1 shape, every triple theta-fails')] += 1
                cnt[(rg, 'S1 shape, every triple theta-fails, kinds ' + '/'.join(sorted(kinds)))] += 1
            if 'theta-a' in kinds:
                cnt[(rg, 'some triple theta-a')] += 1
                nn = max(len(ctx.needers(x)) for x in range(I.n) if P.frozen[x])
                cnt[(rg, 'some triple theta-a, most needers of a frozen good = %d' % nn)] += 1
            if rg.startswith('f>=2'):
                single = [ctx.blockers(o, X | (1 << c))[0] for o in ctx.best for X in pr.OWN[Bs][o][1]
                          for c in bits(P.J & ~X) if len(ctx.blockers(o, X | (1 << c))) == 1]
                fz = [w for w in single if P.frozen[w]]
                if fz:
                    cnt[(rg, 'a junk good of a best owner blocked by one frozen agent alone')] += 1
                    if all(not ctx.free_needers(w) for w in fz):
                        cnt[(rg, '... and every such frozen agent has only frozen needers')] += 1
            if rg == 'f=1, 1 needer':
                x = P.frozen.index(True); g = Bs[x]
                bt = bigtop(I, x) and max(I.sets[x], key=lambda q: I.v[x][q]) == next(bits(g))
                cnt[(rg, 'x big-top on its top')] += bt
                if bt:
                    z = ctx.free_needers(x)[0] if ctx.free_needers(x) else None
                    loc = []
                    for q in bits(I.R[x] & ~g):
                        if P.J >> q & 1: loc.append('J')
                        elif z is not None and Bs[z] >> q & 1: loc.append('z')
                        elif any(Bs[o] >> q & 1 for o in ctx.best): loc.append('best owner')
                        else: loc.append('other')
                    cnt[(rg, 'x big-top, L_x in ' + '+'.join(sorted(loc)))] += 1
                    sf = any(ctx.blockers(o, X | (1 << c)) == [x] for o in ctx.best
                             for X in pr.OWN[Bs][o][1] for c in bits(P.J & ~X))
                    cnt[(rg, 'x big-top, some best owner has a junk good blocked by x alone')] += sf
    for k in sorted(cnt): print('  %-70s %d' % (' | '.join(k), cnt[k]))


def candidates(files):
    """the failed candidate statements of k4/dl13.md §5: number of T1-stuck states violating each, and the smallest"""
    best = {}; cnt = collections.Counter(); cache = {}; tot = 0
    for fn in files:
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Profile({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
            pr = cache[key]; Bs = tup(r['Bs']); ctx = Ctx(pr, Bs); I = ctx.I; P = ctx.P
            tot += 1
            trip = ctx.s1_triples()
            c1, kinds = ctx.C1()
            sf = any(len(ctx.blockers(o, X | (1 << c))) == 1 and P.frozen[ctx.blockers(o, X | (1 << c))[0]]
                     for o in ctx.best for X in pr.OWN[Bs][o][1] for c in bits(P.J & ~X))
            ex = any(P.frozen[x] and any(I.threat(x, P.W(o), P.bv[x]) for o in P.free) for x in range(I.n))
            c2 = ctx.C2(); c3 = ctx.C3() if not (c1 or c2) else []
            fails = {'A1 S1 shape': not trip,
                     'A2 S1 shape => Corollary 9.1': bool(trip) and not c1,
                     'A3 some frozen agent exposed': not ex,
                     'A4 single frozen blocker at a best owner': not sf,
                     'A5 f = 1, >= 2 needers => S1 shape': regime(ctx) == 'f=1, >=2 needers' and not trip,
                     'A6 theta-fail => theta-b': 'theta-a' in kinds,
                     'A7 C1, C2 or C3': not (c1 or c2 or c3)}
            kin = ctx.key_optimal(); t4s = ctx.t4_stuck()
            kopt = kin and t4s
            if kopt: cnt['(states where no (T1), (T2) or (T4) move lowers def)'] += 1
            if not ex:      # the states without an exposed frozen agent: their f and which move lowers the deficit
                cnt['(no frozen exposure: f = %d, %s, %s)' % (
                    r['f'], 'a (T1)/(T2) move lowers def' if not kin else 'key-optimal',
                    'a (T4) move lowers def' if not t4s else 'no (T4) move lowers def')] += 1
            for k, v in fails.items():
                if not v: continue
                for k2 in ([k, k + ' | at states where no T1, T2, T4 move lowers def'] if kopt else [k]):
                    cnt[k2] += 1
                    cand = (len(r['sets']), r['m'], r['def'], r['src'], r['sets'], r['vals'], r['Bs'], r['f'])
                    if k2 not in best or cand[:3] < best[k2][:3]: best[k2] = cand
    print('T1-stuck states (records): %d; of them %d with no improving (T1), (T2) or (T4) move (the T3 stage)' % (
        tot, cnt['(states where no (T1), (T2) or (T4) move lowers def)']))
    del cnt['(states where no (T1), (T2) or (T4) move lowers def)']
    names = ['A1 S1 shape', 'A2 S1 shape => Corollary 9.1', 'A3 some frozen agent exposed',
             'A4 single frozen blocker at a best owner', 'A5 f = 1, >= 2 needers => S1 shape',
             'A6 theta-fail => theta-b', 'A7 C1, C2 or C3']
    for k in names:
        for k2 in (k, k + ' | at states where no T1, T2, T4 move lowers def'):
            if cnt[k2]:
                n, m, d, src, sets, vals, Bs, f = best[k2]
                print('  %-45s fails at %5d states; smallest: n=%d m=%d f=%d def=%d %s sets=%s vals=%s P=%s' % (
                    k2, cnt[k2], n, m, f, d, src, sets, vals, Bs))
            else:
                print('  %-45s fails at %5d states' % (k2, 0))
    for k in sorted(c for c in cnt if c.startswith('(no frozen exposure')):
        print('  %-45s %d' % (k, cnt[k]))


def swaps_mode(argv, opt):
    """Lemma 8 at every swap of every def > 0 state with f >= 1; C1, C1*, C2, C3 asserted wherever they apply"""
    items = []
    if argv[0] == 'catalog':
        recs = json.load(gzip.open(argv[1], 'rt'))['records'][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        items = [{'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m']} for r in recs]
    else:
        # random strict instances with 3- or 4-good strictly balanced agents (k4/dl2_lemma_random.py's generator),
        # kept only when f >= 1 and omega >= 1; to make that likely, with probability 1/2 a random good g becomes the
        # top of each agent with probability 0.7 (put in place of a random good of its set if needed; the values are
        # permuted, so balance and strictness are kept; instances with a good valued by nobody are dropped)
        sys.path.insert(0, HERE)
        from dl2_lemma_random import rand_inst
        rng = random.Random(int(opt.get('seed', 1)))
        tries = 0
        while len(items) < int(argv[1]) and tries < 200 * int(argv[1]):
            tries += 1
            I = rand_inst(rng, int(opt.get('nmax', 4)), int(opt.get('mmax', 10)))
            sets = [list(S) for S in I.sets]; vals = [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]
            if rng.random() < 0.5:
                g = rng.randrange(I.m)
                for i in range(I.n):
                    if rng.random() < 0.7:
                        if g not in sets[i]: sets[i][rng.randrange(len(sets[i]))] = g
                        k = sets[i].index(g); t = max(range(len(vals[i])), key=lambda j: vals[i][j])
                        vals[i][k], vals[i][t] = vals[i][t], vals[i][k]      # g becomes i's top
                if set(q for S in sets for q in S) != set(range(I.m)): continue
            J = M.Inst(sets, vals, I.m)
            J.preallocs()
            if J.f >= 1 and J.omega >= 1:
                items.append({'sets': sets, 'vals': vals, 'm': I.m})
        print('# %d instances with f >= 1 and omega >= 1 from %d draws' % (len(items), tries))
    cnt = collections.Counter()
    for d in items:
        pr = Profile(d, check='--check' in sys.argv)
        cnt['profiles'] += 1
        if not pr.ok or pr.I.f == 0: continue
        for Bs in pr.mp:
            if pr.D[Bs] <= 0: continue
            ctx = Ctx(pr, Bs)
            if not ctx.P.free: continue
            cnt['def>0 states f>=1'] += 1
            cnt['swaps checked (Lemma 8)'] += ctx.check_lemma8()
            cnt['Proposition T checks (b), (d)'] += ctx.check_propT(False)
            c1, kinds = ctx.C1()
            for k in kinds: cnt['S1 shape ' + k] += 1
            if c1: cnt['C1 applies'] += 1
            if ctx.C1star(): cnt['C1* applies'] += 1
            if ctx.C2(): cnt['C2 applies'] += 1
            if ctx.C3(): cnt['C3 applies'] += 1
    for k in sorted(cnt): print('%-30s %d' % (k, cnt[k]))
    print('no assertion failed')


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    args = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/dl13_lemmas.py ' + ' '.join(argv), flush=True)
    if '--swaps' in argv:
        swaps_mode(args, opt); return
    if '--stats' in argv:
        stats(args); return
    if '--candidates' in argv:
        candidates(args); return
    cnt, ex, n8 = coverage(args, '--check' in argv, '--lemma8' in argv)
    if '--lemma8' in argv: print('Lemma 8 equality checked at %d swaps (all moves of Lemma 6 at the stuck states)' % n8)
    print('T1-stuck states: %d; Proposition T (b), (c), (d) checked %d times' % (cnt[('states',)], cnt[('propT checks',)]))
    print('\nfirst certifying construction (order C1, C2, C3 (structural), then the certificates C1*, C2*, then Lemma 8 or '
          'Lemma 11 evaluated at the repairs found, L8 / L11):')
    for k in sorted(k for k in cnt if len(k) == 2 and k[0] != 'uncovered'):
        print('  %-28s %-6s %d' % (k[0], k[1], cnt[k]))
    print('\nby S1 shape (theta-ok / theta-a / theta-b of Lemma 10):')
    for k in sorted(k for k in cnt if len(k) == 3 and k[0] != 'uncovered'):
        print('  %-28s %-32s %-6s %d' % (k[0], k[1], k[2], cnt[k]))
    print('\nuncovered, by mechanism of the repairs (A: no helper, x owner; B*: no helper, unmoved best owner; '
          'B: no helper, other unmoved owner; H: helper needed):')
    for k in sorted(k for k in cnt if k[0] == 'uncovered'):
        print('  %-28s %-4s %d' % (k[1], k[2], cnt[k]))
    print('\nsmallest uncovered instance per (regime, mechanism):')
    for k in sorted(ex):
        n, m, src, sets, vals, Bs = ex[k]
        print('  %s %s: n=%d m=%d %s sets=%s vals=%s P=%s' % (k[0], k[1], n, m, src, sets, vals, Bs))
    print('no assertion failed')


if __name__ == '__main__':
    main(sys.argv[1:])
