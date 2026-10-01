#!/usr/bin/env python3
"""Replays the failed candidate statements of proof/k4-dl13 (k4/dl13.md §5; attempts/k4-dl13-*.md) with two
implementations, at their smallest failing T1-stuck states.

A T1-stuck state: a min-frozen P (fewest frozen agents f >= 1, omega >= 1) with def(P) > 0 such that no (T1) move
(one free agent re-bases, the needed set unchanged) gives a min-frozen P' with def(P') < def(P).
  Implementation A: k4/dl13_lemmas.py (Ctx) on k4/dl13_stuck.py (Profile: k4/suite/model.py's 𝒫 and the deficit of
    Lemma H1, k4/dl2_classify.PA).
  Implementation B: main's k4/c4x_check.py (`analyse`: every base map, (V1), (V2) literally, its own removal-only
    deficit `rodef`), with the T1 test, the owner values and the blockers written separately below (frozensets).
Each candidate is checked to FAIL at its state by both implementations, and DL13 (a (T3) move lowering the deficit)
is checked to HOLD there by both.
usage: python3 attempts/k4_dl13_attempts.py"""
import itertools, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite')); sys.path.insert(0, os.path.join(ROOT, 'k4'))
import model as M
import c4x_check as CX
from dl13_stuck import Profile
from dl13_lemmas import Ctx, regime
from model import bits, mask

ok_all = True


def say(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print('%-58s %s  %s' % (name, 'confirmed' if ok else 'NOT REPRODUCED', detail), flush=True)


# ------------------------------------------------------------------ implementation B
class B:
    def __init__(self, sets, vals, m):
        self.sets, self.m, self.n = sets, m, len(sets)
        self.vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        res = CX.analyse(sets, m, self.vl)
        mf = max(r[2]['-frozen'] for r in res)
        self.f = -mf
        self.mp = {tuple(r[0]): r[2]['rodef'] for r in res if r[2]['-frozen'] == mf}

    def v(self, i, S): return sum(self.vl[i].get(g, 0) for g in S)

    def needs(self, i, Bi): return frozenset(g for g in self.vl[i] if g not in Bi and self.vl[i][g] > self.v(i, Bi))

    def NA(self, P): return frozenset().union(*[self.needs(i, P[i]) for i in range(self.n)])

    def frozen(self, P):
        na = self.NA(P)
        return [len(P[i]) == 1 and P[i] <= na for i in range(self.n)]

    def J(self, P): return frozenset(range(self.m)) - frozenset().union(*P)

    def thr(self, i, X, hold):
        return any(self.v(i, X - {h}) > self.v(i, hold) for h in X)

    def t1_stuck(self, P):
        d = self.mp[P]; na = self.NA(P)
        for P2, d2 in self.mp.items():
            ch = [i for i in range(self.n) if P[i] != P2[i]]
            if len(ch) == 1 and self.NA(P2) == na and d2 < d: return False
        return True

    def t3_repairs(self, P):
        """min-frozen P2 with smaller deficit reached by a role swap with a needer (+ <= 1 helper giving up a good)"""
        d = self.mp[P]; na = self.NA(P); fz = self.frozen(P); out = []
        for P2, d2 in self.mp.items():
            if d2 >= d or self.NA(P2) != na: continue
            fz2 = self.frozen(P2)
            ch = [i for i in range(self.n) if P[i] != P2[i]]
            xs = [i for i in ch if fz[i] and not fz2[i]]; zs = [i for i in ch if fz2[i] and not fz[i]]
            ys = [i for i in ch if not fz[i] and not fz2[i]]
            if len(xs) == 1 and len(zs) == 1 and len(ch) == 2 + len(ys) and len(ys) <= 1 \
                    and P2[zs[0]] == P[xs[0]] and P[xs[0]] <= self.needs(zs[0], P[zs[0]]) \
                    and all(P[y] - P2[y] for y in ys):
                out.append(P2)
        return out

    def owner_table(self, P):
        """o -> (best value, [optimal bundles]) by Lemma H1's count, written from the definitions"""
        fz = self.frozen(P); J = sorted(self.J(P)); out = {}
        N = [self.needs(i, P[i]) for i in range(self.n)]
        for o in range(self.n):
            if fz[o]: continue
            best, arg = -1, []
            for k in range(len(J) + 1):
                for K in itertools.combinations(J, k):
                    X = P[o] | frozenset(K)
                    if any(self.thr(w, X, P[w]) for w in range(self.n) if w != o): continue
                    NX = frozenset(g for g in self.vl[o] if g not in X and self.vl[o][g] > self.v(o, X))
                    other = frozenset().union(*[N[j] for j in range(self.n) if j != o]) | NX
                    u = sum(1 for w in range(self.n) if w != o and fz[w] and not (P[w] & other))
                    if len(X) + u > best: best, arg = len(X) + u, [X]
                    elif len(X) + u == best: arg.append(X)
            out[o] = (best, arg)
        return out

    def shapes(self, P):
        """(S1 triples with theta-ok / theta-fail flags, any single frozen blocker, any frozen agent exposed)"""
        fz = self.frozen(P); J = self.J(P); tab = self.owner_table(P)
        V = max(b for b, _ in tab.values())
        s1 = []; sf = False
        for o, (b, Xs) in tab.items():
            if b != V: continue
            for X in Xs:
                for c in J - X:
                    Y = X | {c}
                    ws = [w for w in range(self.n) if w != o and self.thr(w, Y, P[w])]
                    if len(ws) == 1 and fz[ws[0]]:
                        sf = True
                        x = ws[0]
                        if P[x] <= self.needs(o, P[o]):
                            s1.append(('ok' if not self.thr(o, Y, P[x]) else 'fail', o, x))
        exposed = any(fz[x] and any(self.thr(x, P[o] | J, P[x]) for o in range(self.n) if not fz[o]) for x in range(self.n))
        return s1, sf, exposed


def state(sets, vals, m, P0):
    pr = Profile({'sets': sets, 'vals': vals, 'm': m})
    Bs = tuple(mask(b) for b in P0)
    ctx = Ctx(pr, Bs)
    b = B(sets, vals, m)
    PB = tuple(frozenset(x) for x in P0)
    I = M.Inst(sets, vals, m)
    return pr, ctx, b, PB, (I.core_violations() == [] and I.strict())


def common(label, sets, vals, m, P0):
    """both implementations: P0 is min-frozen with def > 0, f >= 1, T1-stuck; DL13 holds there (a (T3) repair)"""
    pr, ctx, b, PB, core = state(sets, vals, m, P0)
    Bs = ctx.Bs
    a_ok = Bs in pr.D and pr.D[Bs] > 0 and pr.I.f >= 1 and not pr.t1_moves(Bs) and bool(pr.t3_moves(Bs))
    b_ok = PB in b.mp and b.mp[PB] > 0 and b.f >= 1 and b.t1_stuck(PB) and bool(b.t3_repairs(PB))
    say(label + ': T1-stuck, DL13 holds', core and a_ok and b_ok and pr.D[Bs] == b.mp[PB],
        'core %s; def %s / %s; f %s / %s; (T3) repairs %d / %d' % (core, pr.D.get(Bs), b.mp.get(PB), pr.I.f, b.f,
                                                               len(pr.t3_moves(Bs)), len(b.t3_repairs(PB))))
    return pr, ctx, b, PB


# 1. m = 6: no S1 shape, no single frozen blocker, the frozen agent not exposed, none of C1, C2, C3
#    (attempts/k4-dl13-s1-shape.md, k4-dl13-frozen-exposed.md, k4-dl13-single-frozen-blocker.md,
#    k4-dl13-structural-cover.md). #53's n = 3 catalogue: core (m = 6, idx 13) of k4_certs_3, profile 4,17,236.
sets = [[0, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]]; vals = [[1, 8, 4, 6], [2, 4, 10, 7], [8, 4, 6, 3]]; m = 6
P0 = [[2], [3, 5], [4]]
pr, ctx, b, PB = common('n = 3, m = 6 (dl13-n3m6)', sets, vals, m, P0)
s1B, sfB, exB = b.shapes(PB)
say('  "every T1-stuck state has an S1 shape" fails', not ctx.s1_triples() and not s1B)
sfA = any(len(ctx.blockers(o, X | (1 << c))) == 1 and ctx.P.frozen[ctx.blockers(o, X | (1 << c))[0]]
          for o in ctx.best for X in pr.OWN[ctx.Bs][o][1] for c in bits(ctx.P.J & ~X))
say('  "some best owner has a single frozen blocker" fails', not sfA and not sfB)
exA = any(ctx.P.frozen[x] and any(ctx.I.threat(x, ctx.P.W(o), ctx.P.bv[x]) for o in ctx.P.free) for x in range(ctx.I.n))
say('  "some frozen agent is exposed" fails', not exA and not exB)
c1, _ = ctx.C1()
say('  "C1, C2 or C3 applies" fails (implementation A only)', not c1 and not ctx.C2() and not ctx.C3())

# 2. m = 7: an S1 shape at which Corollary 9.1 never applies (theta-b of Lemma 10) (attempts/k4-dl13-s1-theta.md).
#    #53's n = 3 catalogue: core (m = 7, idx 5) of k4_certs_3, profile 20,146,100.
sets = [[0, 2, 5, 6], [1, 4, 5, 6], [3, 4, 5, 6]]; vals = [[2, 6, 3, 10], [6, 2, 3, 10], [4, 6, 5, 8]]; m = 7
P0 = [[0, 2], [1, 4], [6]]
pr, ctx, b, PB = common('n = 3, m = 7 (dl13-n3m7-theta)', sets, vals, m, P0)
s1B, _, _ = b.shapes(PB)
c1, kinds = ctx.C1()
say('  "an S1 shape gives Corollary 9.1" fails', bool(ctx.s1_triples()) and not c1 and kinds == {'theta-b'}
    and s1B and all(t[0] == 'fail' for t in s1B), 'kinds %s; implementation B: %s' % (sorted(kinds), s1B))

# 3. n = 4, m = 10, f = 1, two needers, no S1 shape (attempts/k4-dl13-two-needers.md).
#    #53's hunt catalogue hunt_n4_pure_s400k: core (m = 10, idx 18) of k4_certs_4_pure, profile 115,72,285,150.
sets = [[0, 2, 6, 9], [1, 5, 8, 9], [3, 6, 7, 8], [4, 7, 8, 9]]
vals = [[6, 4, 5, 8], [4, 3, 2, 8], [10, 8, 3, 6], [6, 3, 2, 10]]; m = 10
P0 = [[9], [1], [3, 7], [4, 8]]
pr, ctx, b, PB = common('n = 4, m = 10 (dl13-n4m10-needers)', sets, vals, m, P0)
s1B, _, _ = b.shapes(PB)
nB = sum(1 for i in range(b.n) if PB[[i for i in range(b.n) if b.frozen(PB)[i]][0]] <= b.needs(i, PB[i]))
say('  "f = 1 with >= 2 needers has an S1 shape" fails', regime(ctx) == 'f=1, >=2 needers' and not ctx.s1_triples()
    and not s1B and b.f == 1 and nB >= 2, 'needers (B): %d' % nB)

# 4. n = 4, m = 10: an S1 shape whose theta-fail is of kind (a) (attempts/k4-dl13-theta-a.md).
#    #53's gap catalogue gap_n4_pure_s4000: core (m = 10, idx 12) of k4_certs_4_pure, profile 10,88,73,21.
sets = [[0, 2, 8, 9], [1, 5, 8, 9], [3, 6, 8, 9], [4, 7, 8, 9]]
vals = [[2, 4, 3, 8], [4, 8, 3, 10], [4, 3, 6, 8], [2, 6, 7, 10]]; m = 10
P0 = [[0, 2], [9], [3, 6], [4, 7]]
pr, ctx, b, PB = common('n = 4, m = 10 (dl13-n4m10-theta-a)', sets, vals, m, P0)
c1, kinds = ctx.C1()
# implementation B: an S1 triple whose owner o has a pair of its goods in X ∪ {c} worth more than the frozen good
s1B, _, _ = b.shapes(PB)
tab = b.owner_table(PB); V = max(v for v, _ in tab.values()); fz = b.frozen(PB); J = b.J(PB); pairB = False
for o, (val, Xs) in tab.items():
    if val != V: continue
    for X in Xs:
        for c in J - X:
            Y = X | {c}
            ws = [w for w in range(b.n) if w != o and b.thr(w, Y, PB[w])]
            if len(ws) == 1 and fz[ws[0]] and PB[ws[0]] <= b.needs(o, PB[o]) and b.thr(o, Y, PB[ws[0]]):
                g = PB[ws[0]]
                Q = [q for q in Y if q in b.vl[o]]
                if any(b.v(o, set(p)) > b.v(o, g) for k in (1, 2) for p in itertools.combinations(Q, k)): pairB = True
say('  "a theta-fail is always of kind (b)" fails', 'theta-a' in kinds and pairB, 'kinds %s' % sorted(kinds))

print('ALL CONFIRMED' if ok_all else 'SOME NOT REPRODUCED')
