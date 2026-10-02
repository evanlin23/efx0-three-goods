#!/usr/bin/env python3
"""Replays the failed candidate statements of proof/k4-thetab (k4/thetab.md §5; attempts/k4-thetab-*.md) at their
smallest failing states, with two implementations.

  Implementation A: k4/thetab_lib.py on k4/dl13_stuck.py (Profile: k4/suite/model.py's 𝒫 and the deficit of Lemma H1,
    k4/dl2_classify.PA) and k4/dl13_lemmas.py (Ctx), PR #75.
  Implementation B: main's k4/c4x_check.py (`analyse`: every base map, (V1), (V2) literally, its own removal-only
    deficit `rodef`), with the key, the T1 test, the needers and the plain swaps written separately below
    (frozensets). Big-top: v(top) > v(second) + v(third), four goods.
The check that an instance is a strict core uses k4/suite/model.py for both.
For each state both implementations compute: f, def(P), whether P is T1-stuck and key-optimal (the T3 stage at f = 1),
the needers of the frozen good and which are big-top, the plain swaps that lower the deficit (a needer z takes g,
x takes an admissible A ⊆ J ∪ B_z, nobody else moves), and the number of (T3) moves (a role swap with a needer and at
most one helper that gives up a good) that lower it. The candidate's failure is checked with both; the theorems of
k4/thetab.md (W, K, G1) with implementation A only, as noted per case.
usage: python3 attempts/k4_thetab_attempts.py"""
import itertools, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite')); sys.path.insert(0, os.path.join(ROOT, 'k4'))
import model as M
import c4x_check as CX
from thetab_lib import (Profile, Ctx, tup, setting, in_H, gw1_hyp, k_swaps, g_certificates, plain_moves, helper_moves,
                        theorems, swaps, t3_stage,
                        target_class, bigtop, bits, mask)

ok_all = True


def say(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print('%-70s %s  %s' % (name, 'confirmed' if ok else 'NOT REPRODUCED', detail), flush=True)


class B:
    """implementation B: the min-frozen class from k4/c4x_check.analyse, everything else from the definitions"""

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

    def key(self, P):
        fz = self.frozen(P)
        return (self.NA(P), tuple(P[i] if fz[i] else None for i in range(self.n)))

    def t1_stuck(self, P):
        d = self.mp[P]; na = self.NA(P)
        for P2, d2 in self.mp.items():
            ch = [i for i in range(self.n) if P[i] != P2[i]]
            if len(ch) == 1 and self.NA(P2) == na and d2 < d: return False
        return True

    def key_optimal(self, P):
        k = self.key(P)
        return all(d2 >= self.mp[P] for P2, d2 in self.mp.items() if self.key(P2) == k)

    def bigtop(self, i):
        vs = sorted(self.vl[i].values(), reverse=True)
        return len(vs) == 4 and vs[0] > vs[1] + vs[2]

    def needers(self, P):
        x = self.frozen(P).index(True); g = P[x]
        return x, g, [i for i in range(self.n) if g <= self.needs(i, P[i])]

    def plain_swaps(self, P):
        """(z, A, def(P')) for every plain swap with a smaller deficit"""
        x, g, nd = self.needers(P); d = self.mp[P]; out = []
        na = self.NA(P); J = self.J(P)
        for z in nd:
            pool = sorted((J | P[z]) & frozenset(self.vl[x]))
            for k in (1, 2):
                for A in itertools.combinations(pool, k):
                    A = frozenset(A)
                    if not self.needs(x, A) <= na: continue
                    P2 = list(P); P2[z] = g; P2[x] = A; P2 = tuple(P2)
                    assert P2 in self.mp, ('Lemma 6 violated (B)', P2)
                    if self.mp[P2] < d: out.append((z, tuple(sorted(A)), self.mp[P2]))
        return sorted(out)

    def t3_moves(self, P):
        """min-frozen P2 with a smaller deficit by a role swap with a needer and at most one helper giving up a good"""
        d = self.mp[P]; na = self.NA(P); fz = self.frozen(P); out = 0
        for P2, d2 in self.mp.items():
            if d2 >= d or self.NA(P2) != na: continue
            fz2 = self.frozen(P2)
            ch = [i for i in range(self.n) if P[i] != P2[i]]
            xs = [i for i in ch if fz[i] and not fz2[i]]; zs = [i for i in ch if fz2[i] and not fz[i]]
            ys = [i for i in ch if not fz[i] and not fz2[i]]
            if len(xs) == 1 and len(zs) == 1 and len(ch) == 2 + len(ys) and len(ys) <= 1 \
                    and P2[zs[0]] == P[xs[0]] and P[xs[0]] <= self.needs(zs[0], P[zs[0]]) \
                    and all(P[y] - P2[y] for y in ys):
                out += 1
        return out


def both(name, d, P0):
    """the facts of the state P0 by both implementations; returns (A-facts, B-facts) after checking they agree"""
    I = M.Inst(d['sets'], d['vals'], d['m'])
    core = not I.core_violations() and I.strict()
    pr = Profile(d); Bs = tup(P0); ctx = Ctx(pr, Bs)
    x, g, nd, third = setting(ctx)
    plainA = sorted((z, tuple(sorted(bits(A))), pr.D[ctx.new(x, z, A)]) for z in nd for A in swaps(ctx, z)
                    if pr.D[ctx.new(x, z, A)] < ctx.D)
    fa = dict(core=core, f=pr.I.f, d=ctx.D, stuck=not pr.t1_moves(Bs), kopt=ctx.key_optimal(),
              x=x, needers=nd, bt=[bigtop(pr.I, y) for y in nd], plain=plainA, t3=len(pr.t3_moves(Bs)))
    b = B(d['sets'], d['vals'], d['m'])
    PB = tuple(frozenset(S) for S in P0)
    xb, gb, ndb = b.needers(PB)
    fb = dict(core=core, f=b.f, d=b.mp[PB], stuck=b.t1_stuck(PB), kopt=b.key_optimal(PB), x=xb, needers=ndb,
              bt=[b.bigtop(y) for y in ndb], plain=b.plain_swaps(PB), t3=b.t3_moves(PB))
    agree = fa == fb
    say(name + ': the two implementations agree on the state', agree,
        '' if agree else 'A=%s B=%s' % (fa, fb))
    return fa, pr, ctx


def main():
    # X1: in setting (H) a plain swap lowers the deficit at every def > 0 state (Corollary N3 proves it at n = 3)
    d = {'sets': [[0, 2, 4, 8], [1, 3, 7, 8], [4, 5, 6, 7], [5, 6, 7, 8]],
         'vals': [[3, 4, 2, 8], [2, 6, 3, 10], [8, 6, 3, 4], [4, 7, 2, 10]], 'm': 9}
    P0 = [[0, 2], [1, 3], [5, 6], [8]]
    fa, pr, ctx = both('X1 (k4_certs_4_pure m=9 idx=5 38,20,245,105)', d, P0)
    say('X1: strict core, f = 1, def(P) > 0, two big-top needers (setting (H))',
        fa['core'] and fa['f'] == 1 and fa['d'] > 0 and len(fa['needers']) == 2 and all(fa['bt']) and in_H(ctx))
    say('X1: no plain swap lowers the deficit (the candidate fails)', not fa['plain'])
    say('X1: P is not T1-stuck (a (T1) move lowers the deficit)', not fa['stuck'])
    print('  first of W, K, G1, G1h that applies (A):', theorems(pr, ctx))

    # X2: every f = 1 target of k4/dl13.md §6 item 2 is in setting (H) (two needers, both big-top)
    d = {'sets': [[0, 2, 7, 8], [1, 3, 7, 8], [4, 5, 6, 8], [4, 5, 6]],
         'vals': [[6, 3, 2, 10], [3, 6, 5, 7], [4, 5, 2, 8], [3, 4, 2]], 'm': 9}
    P0 = [[0, 7], [8], [4, 6], [5]]
    fa, pr, ctx = both('X2 (k4_certs_4_n4_3 m=9 idx=5 106,48,94,3)', d, P0)
    say('X2: strict core, f = 1, def(P) > 0, at the T3 stage (T1-stuck and key-optimal)',
        fa['core'] and fa['f'] == 1 and fa['d'] > 0 and fa['stuck'] and fa['kopt'])
    say('X2: a target (C1, C2, C3 of k4/dl13.md do not apply; implementation A only)', target_class(ctx) is not None,
        str(target_class(ctx)))
    say('X2: two needers, one of them not big-top (the candidate fails)',
        len(fa['needers']) == 2 and sorted(fa['bt']) == [False, True])
    say('X2: a plain swap lowers the deficit', bool(fa['plain']), str(fa['plain'][:3]))
    say('X2: Corollary G1 certifies a plain swap (implementation A)', theorems(pr, ctx) == 'G1')

    # X3 (Conjecture PS): at every T3-stage state in setting (H) some plain swap lowers the deficit
    d = {'sets': [[0, 4, 5, 6], [0, 1, 2, 3], [0, 1, 2, 3], [7, 5, 1, 4]],
         'vals': [[12, 10, 9, 8], [13, 7, 5, 4], [15, 8, 6, 4], [12, 7, 8, 6]], 'm': 8}
    P0 = [[0], [1], [2, 3], [4, 5]]
    fa, pr, ctx = both('X3 (twin hunt, hunt:1:27942)', d, P0)
    say('X3: strict core, f = 1, def(P) > 0, at the T3 stage (T1-stuck and key-optimal)',
        fa['core'] and fa['f'] == 1 and fa['d'] > 0 and fa['stuck'] and fa['kopt'])
    say('X3: setting (H)', len(fa['needers']) == 2 and all(fa['bt']) and in_H(ctx))
    say('X3: no plain swap lowers the deficit (the candidate fails)', not fa['plain'])
    say('X3: some (T3) move with one helper lowers the deficit', fa['t3'] > 0, '%d moves' % fa['t3'])
    say('X3: a target (no S1 shape; C1, C2, C3 do not apply; implementation A only)', target_class(ctx) == 'noS1')
    cs = g_certificates(ctx, pr, helper_moves(ctx), 1)
    say('X3: Corollary G1 with one helper certifies a swap (implementation A)', theorems(pr, ctx) == 'G1h' and bool(cs))
    b = B(d['sets'], d['vals'], d['m'])
    x, z, A, o, h, Bh, bd = cs[0]
    P2 = [frozenset(S) for S in P0]; P2[z] = frozenset(P0[x]); P2[x] = frozenset(bits(A)); P2[h] = frozenset(bits(Bh))
    P2 = tuple(P2)
    dA = pr.D[ctx.new(x, z, A, h, Bh)]; dB = b.mp[P2]
    say("X3: that swap (z=%d, x takes %s, helper %d takes %s): def(P') by A and B, <= %d" % (
        z, sorted(bits(A)), h, sorted(bits(Bh)), bd), dA == dB and dA <= bd, "def(P') = %d / %d" % (dA, dB))

    # X4: W, K or G1 applies at every T1-stuck state in setting (H) (the T3 stage is T1-stuck plus no (T2) move)
    d = {'sets': [[0, 2, 7, 9], [1, 5, 8, 9], [3, 6, 8, 9], [4, 7, 8, 9]],
         'vals': [[3, 10, 6, 8], [2, 3, 8, 4], [5, 3, 7, 6], [4, 2, 8, 3]], 'm': 10}
    P0 = [[0, 9], [1, 5], [8], [4, 7]]
    fa, pr, ctx = both('X4 (k4_certs_4_pure m=10 idx=13 60,8,93,84)', d, P0)
    say('X4: strict core, f = 1, def(P) > 0, T1-stuck but not key-optimal (a (T2) move lowers the deficit)',
        fa['core'] and fa['f'] == 1 and fa['d'] > 0 and fa['stuck'] and not fa['kopt'])
    say('X4: setting (H)', len(fa['needers']) == 2 and all(fa['bt']) and in_H(ctx))
    say('X4: W, K, G1 (plain swap) do not apply (implementation A)', theorems(pr, ctx) in ('-', 'G1h'),
        theorems(pr, ctx))
    say('X4: a plain swap lowers the deficit', bool(fa['plain']), str(fa['plain'][:3]))

    # Y: the theorems' swaps at dl13-n3m7-theta (k4/dl13.md §5), deficits of P' by both implementations
    d = {'sets': [[0, 2, 5, 6], [1, 4, 5, 6], [3, 4, 5, 6]], 'vals': [[2, 6, 3, 10], [6, 2, 3, 10], [4, 6, 5, 8]],
         'm': 7}
    P0 = [[0, 2], [1, 4], [6]]
    fa, pr, ctx = both('Y (dl13-n3m7-theta)', d, P0)
    from thetab_lib import w1_construction
    zA = w1_construction(ctx); kk = k_swaps(ctx)
    b = B(d['sets'], d['vals'], d['m'])
    x = fa['x']
    for name, (z, A), bound in [('Theorem W', zA, None)] + [('Theorem K', t, 0) for t in kk]:
        P2 = [frozenset(S) for S in P0]; P2[z] = frozenset(P0[x]); P2[x] = frozenset(bits(A)); P2 = tuple(P2)
        dA = pr.D[ctx.new(x, z, A)]; dB = b.mp[P2]
        bd = len(list(bits(A))) - 2 if bound is None else bound
        say('Y: %s swap z=%d A=%s: def(P\') by A and B, <= %d' % (name, z, sorted(bits(A)), bd),
            dA == dB and dA <= bd, 'def(P\') = %d / %d' % (dA, dB))
    print('ALL CONFIRMED' if ok_all else 'SOME CASE NOT REPRODUCED')


if __name__ == '__main__':
    main()
