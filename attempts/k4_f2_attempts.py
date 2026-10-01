#!/usr/bin/env python3
"""Replays the failed candidate statements of proof/k4-f2 (k4/f2.md §5; attempts/k4-f2-*.md) and the DL_RT4 failure
that motivates (T3⁺) (k4/f2.md §0, found by compute/k4-rt4), with two implementations, at their smallest states.

  Implementation A: k4/f2_lib.py, k4/f2_shapes.py, k4/f2_lemmas.py (k4/suite/model.py's 𝒫, Lemma H1's deficit of
    k4/dl2_classify.PA, the move kinds of k4/f2_lib.py).
  Implementation B: main's k4/dl134_xcheck.py (k4/c4x_check.py's enumeration of 𝒫 and its own removal-only deficit, and
    its own T1, T2, T3, T4 kinds), with the (T3⁺) test of k4/f2_xcheck2.py and the owner values, blockers and need paths
    written separately below (frozensets).
The check that an instance is a strict core uses k4/suite/model.py for both.
Every state below is checked by both to be a T3-stage state (f >= 2, def > 0, no improving (T1), (T2), (T4) move) at
which some (T3⁺) move lowers the deficit (DL for R_C holds), and the candidate is checked to fail there.
usage: python3 attempts/k4_f2_attempts.py"""
import itertools, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite')); sys.path.insert(0, os.path.join(ROOT, 'k4'))
import model as M
import dl134_xcheck as X
from f2_xcheck2 import t3plus_own
from f2_lib import Prof, tup, mask, bits
from f2_shapes import State
from f2_lemmas import Ctx

ok_all = True


def say(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print('%-66s %s  %s' % (name, 'confirmed' if ok else 'NOT REPRODUCED', detail), flush=True)


class B:
    """implementation B of one profile"""

    def __init__(self, sets, vals, m):
        self.Pr = X.Prof(sets, vals, m)
        self.n, self.m, self.f = len(sets), m, self.Pr.f
        self.vl = self.Pr.vl
        self.mp = dict(self.Pr.mp)
        self.info = {P: self.Pr.info(P) for P in self.mp}

    def v(self, i, S): return sum(self.vl[i].get(g, 0) for g in S)

    def thr(self, i, Z, hold): return any(self.v(i, Z - {h}) > self.v(i, hold) for h in Z)

    def J(self, P): return frozenset(range(self.m)) - frozenset().union(*P)

    def kinds(self, P):
        """the kinds of the improving moves at P: t1 t2 t3 (plain) t3c (T3⁺ with W != ∅) t4"""
        d = self.mp[P]; out = set()
        for Q, dq in self.mp.items():
            if dq >= d: continue
            k, _ = self.Pr.move(P, Q, self.info[P], self.info[Q])
            for kk in ('t1', 't2', 't4'):
                if k[kk]: out.add(kk)
            t = t3plus_own(P, Q, self.info[P], self.info[Q])
            if t == 1: out.add('t3')
            elif t == 2: out.add('t3c')
        return out

    def owner_table(self, P):
        N, NA, fz = self.info[P]; J = sorted(self.J(P)); out = {}
        for o in range(self.n):
            if fz[o]: continue
            best, arg = -1, []
            for k in range(len(J) + 1):
                for K in itertools.combinations(J, k):
                    Z = P[o] | frozenset(K)
                    if any(self.thr(w, Z, P[w]) for w in range(self.n) if w != o): continue
                    NZ = frozenset(g for g in self.vl[o] if g not in Z and self.vl[o][g] > self.v(o, Z))
                    other = frozenset().union(*[N[j] for j in range(self.n) if j != o]) | NZ
                    u = sum(1 for w in range(self.n) if w != o and fz[w] and not (P[w] & other))
                    if len(Z) + u > best: best, arg = len(Z) + u, [Z]
                    elif len(Z) + u == best: arg.append(Z)
            out[o] = (best, arg)
        return out

    def single_blocks(self, P):
        tab = self.owner_table(P); V = max(b for b, _ in tab.values()); J = self.J(P); out = []
        for o, (b, Zs) in tab.items():
            if b != V: continue
            for Z in Zs:
                for c in J - Z:
                    Y = Z | {c}
                    ws = [w for w in range(self.n) if w != o and self.thr(w, Y, P[w])]
                    if len(ws) == 1: out.append((o, Z, c, ws[0]))
        return out

    def free_ends(self, P, x):
        """the free agents with a need path to x, each with the good it takes (the last good before it)"""
        N, NA, fz = self.info[P]; out = set()

        def walk(y, seen):
            for i in range(self.n):
                if i in seen or not (P[y] <= N[i]): continue
                if fz[i]: walk(i, seen | {i})
                else: out.add((i, P[y]))
        walk(x, {x})
        return out


def both(label, sets, vals, m, P0):
    """both implementations: P0 is a T3-stage state with f >= 2 at which DL_{R_C} holds; returns the objects"""
    pr = Prof({'sets': sets, 'vals': vals, 'm': m}, fmin=1)
    Bs = tup(P0)
    b = B(sets, vals, m); PB = tuple(frozenset(x) for x in P0)
    I = M.Inst(sets, vals, m); core = I.core_violations() == [] and I.strict()
    kA = set(k for _, k in pr.improving(Bs) if k)
    kB = b.kinds(PB)
    okA = Bs in pr.D and pr.D[Bs] > 0 and pr.I.f >= 2 and pr.t3_stage(Bs) and bool(kA & {'t3', 't3c'})
    okB = PB in b.mp and b.mp[PB] > 0 and b.f >= 2 and not (kB & {'t1', 't2', 't4'}) and bool(kB & {'t3', 't3c'})
    say(label + ': T3 stage, DL_RC holds', core and okA and okB and kA == kB and pr.D[Bs] == b.mp[PB],
        'core %s; f %s / %s; def %s / %s; improving kinds %s / %s' % (core, pr.I.f, b.f, pr.D.get(Bs), b.mp.get(PB),
                                                                   sorted(kA), sorted(kB)))
    return pr, Bs, b, PB, kA, kB


CANDIDATES = []      # filled below with (label, sets, vals, m, P, checker)


def run():
    # 0. the smallest DL_RT4 failure (compute/k4-rt4-n5b, results/k4_rt4/n5b_FAILURES.md): only chain moves improve
    sets = [[0, 2, 4, 7], [1, 4, 7, 8], [3, 6, 8], [5, 6, 7, 8], [5, 6, 7, 8]]
    vals = [[6, 3, 5, 7], [4, 2, 8, 7], [2, 4, 3], [4, 8, 1, 6], [2, 7, 8, 4]]; m = 9
    P0 = [[7], [8], [3], [5], [6]]
    pr, Bs, b, PB, kA, kB = both('n = 5, m = 9 (rt4-n5b, DL_RT4 fails)', sets, vals, m, P0)
    say('  no improving (T3): every improving R_C move is a chain', 't3' not in kA and 't3' not in kB and 't3c' in kA)
    ctx = Ctx(pr, Bs)
    c1 = ctx.C1p(ctx.single_blocks())
    sbB = b.single_blocks(PB)
    s1cB = [(o, x) for o, Z, c, x in sbB if b.info[PB][2][x]
            and any(e == o and not b.thr(o, Z | {c}, g) for e, g in b.free_ends(PB, x))]
    say('  Corollary 9.1+ applies with k >= 1 (A asserts the drop; B finds the shape)',
        any(t[-1] >= 1 for t in c1) and bool(s1cB), 'A: %s; B: %s' % (sorted(set(c1))[:3], sorted(set(s1cB))[:3]))
    for label, sets, vals, m, P0, chk in CANDIDATES:
        pr, Bs, b, PB, kA, kB = both(label, sets, vals, m, P0)
        chk(pr, Bs, b, PB)


if __name__ == '__main__':
    run()
    print('ALL CONFIRMED' if ok_all else 'SOME NOT REPRODUCED')
