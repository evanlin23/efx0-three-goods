#!/usr/bin/env python3
"""Replay of the failed candidate statements of workstream proof/k4-sx (attempts/k4-sx-*.md), with two
implementations: k4/suite/model.py through k4/sx_keygraph.py (deficits by Lemma H1), and main's k4/c4x_check.py
through k4/sx_xcheck.py (its own enumeration of 𝒫 and the direct removal-only deficit `rodef`).

1. Lemma A without its theta-b exception (attempts/k4-sx-owner-swap-thetab.md): at a Z′-maximum of a non-completable
   f = 1 key, the owner swap with a theta-b terminal leaf o ends, for every admissible base of x inside X_o, at a state
   whose deficit is not below def*(κ).
2. Lemma B for every leaf (attempts/k4-sx-path-move-r-leaf.md): for an (R) leaf o with s_o in the pool, x's bundle X_o
   threatens o holding its threatener's pair after the plain path move (the move still lowers the deficit there, by
   another owner; what fails is the proof's owner).
3. Lemma A⁺ at every non-completable f >= 2 key (attempts/k4-sx-aplus-f3.md): at an n = 5, f = 3 key of
   compute/k4-rt4-n5c no maximum of (r', Λ') satisfies the hypotheses of Lemma A⁺ (k4/sx.md §6).
4. K4.SX.COVER with the structural hypotheses (H*), (H'*), (H_B'*) (attempts/k4-sx-cover-structural.md): at an
   n = 4, m = 9 key no Z′-maximum is covered that way; with the exact hypotheses Lemma C applies.
usage: python3 attempts/k4_sx_attempts.py"""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4')); sys.path.insert(0, os.path.join(HERE, '..', 'k4', 'suite'))
import c4x_check as CX
from sx_keygraph import KeyProfile
from sx_xcheck import keygraph
from model import bits, pc, mask


def kt(key): return tuple(None if t == '-' else int(t) for t in key.split(','))


def rodef_x(d, bases):
    """the removal-only deficit of the pre-allocation `bases` (lists of goods) by main's k4/c4x_check.rodef"""
    n, m = len(d['sets']), d['m']
    vl = [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])]
    R = [set(S) for S in d['sets']]
    B = [frozenset(b) for b in bases]
    J = frozenset(range(m)) - frozenset().union(*B)
    N = [frozenset(g for g in R[i] - B[i] if vl[i][g] > sum(vl[i][h] for h in B[i])) for i in range(n)]
    NA = frozenset().union(*N)
    fz = [len(B[i]) == 1 and B[i] <= NA for i in range(n)]
    cap = [0 if fz[i] else max(0, 2 - len(B[i])) for i in range(n)]
    return CX.rodef(n, vl, B, J, fz, cap, R, N)


def case1():
    """theta-b owner swap: n = 4, m = 10"""
    d = {'sets': [[0, 2, 6, 9], [1, 5, 8, 9], [3, 6, 7, 9], [4, 7, 8]],
         'vals': [[4, 5, 6, 8], [4, 2, 3, 8], [4, 2, 3, 8], [2, 4, 3]], 'm': 10}
    key, x, o, g = '9,-,-,-', 0, 1, 9
    P = [[9], [1, 8], [3, 6], [4, 7]]            # the Z′-maximum Q_1 = {1, 8}, Q_2 = {3, 6}, Q_3 = {4, 7}, L = {0, 2, 5}
    Xo = {1, 8, 0, 2, 5}
    kp = KeyProfile(d); I = kp.I
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    ds = (kp.dstar[kt(key)], xr[key]['def*'])
    assert ds == (1, 1)
    res = []
    for r in (1, 2):
        for A in itertools.combinations(sorted(Xo & set(d['sets'][x])), r):
            if not I.admissible(x, mask(A), I.R[x] & ~(1 << g)): continue
            P2 = [list(b) for b in P]; P2[o] = [g]; P2[x] = list(A)
            res.append((A, kp.D[tuple(mask(b) for b in P2)], rodef_x(d, P2)))
    good = res and all(a == b and a >= 1 for _, a, b in res)
    print('1. theta-b owner swap (n = 4, m = 10): def* = %s (both); x\'s admissible bases inside X_o and def(P\') '
          '(model, c4x_check): %s  %s' % (ds[0], res, 'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def case2():
    """plain path move to an (R) leaf with s in L: n = 4, m = 8"""
    d = {'sets': [[0, 4, 5, 6], [1, 4, 5, 7], [2, 3, 6, 7], [2, 3, 6, 7]],
         'vals': [[4, 6, 3, 8], [6, 8, 3, 10], [3, 2, 4, 8], [6, 3, 8, 10]], 'm': 8}
    key = '-,7,-,-'                             # x = 1 frozen on 7; Q_0 = {0, 4}, Q_2 = {1, 6}, Q_3 = {2, 3}, L = {5}
    kp = KeyProfile(d); I = kp.I
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    ds = (kp.dstar[kt(key)], xr[key]['def*'])
    # leaf o = 0, kind (R): a = 6, {p, q} = {0, 4}, s = 5 in L; tau = 2 threatens 0 (6 in Q_2); plain move: 0 takes Q_2
    Xo = mask([0, 4, 5]); new_o = mask([1, 6])
    thr = I.threat(0, Xo, I.val(0, new_o))
    thr_x = (max(I.val(0, Xo & ~(1 << h)) for h in (0, 4, 5)), I.val(0, new_o))   # theta_0(X_o), v_0({1, 6})
    good = ds == (1, 1) and thr
    print('2. plain path move to an (R) leaf with s in L (n = 4, m = 8): def* = %s (model, c4x_check); X_o = {0, 4, 5} '
          'threatens o = 0 holding {1, 6}: %s (theta = %d > %d)  %s' % (ds, thr, thr_x[0], thr_x[1],
                                                                        'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def case3():
    """Lemma A+ hypotheses fail at every (r', Λ')-maximum of an n = 5, f = 3 key (compute/k4-rt4-n5c)"""
    d = {'sets': [[0, 2, 6, 10], [1, 4, 9, 11], [3, 5, 9, 11], [6, 7, 8, 10], [7, 8, 10, 11]],
         'vals': [[2, 3, 6, 10], [3, 4, 2, 8], [3, 2, 4, 8], [2, 3, 10, 6], [2, 10, 6, 3]], 'm': 12}
    key = '10,-,11,8,-'
    kp = KeyProfile(d)
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    ds = (kp.dstar[kt(key)], xr[key]['def*'])
    import collections
    import sx_f2
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    sx_f2.analyse_key(kp, kt(key), cnt, ex, 0)
    good = ds == (1, 1) and cnt['Zmax: Lemma A+ applies=False'] == cnt['Zmax'] > 0
    print('3. Lemma A+ at an n = 5, f = 3 key: def* = %s (model, c4x_check); maxima %d, with Lemma A+ %d; '
          'DLK with T3+ edges holds there: %s  %s' % (ds, cnt['Zmax'], cnt['Zmax: Lemma A+ applies=True'],
                                                     xr[key]['DLK_T3+T4'], 'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def case4():
    """K4.SX.COVER with the structural hypotheses (H*), (H'*), (H_B'*): n = 4, m = 9, the unique Z′-maximum of a
    non-completable key satisfies none of A, B (k = 1), B' (k = 1) with (H_B'*), C with (H*), C' with (H'*); with the
    exact hypotheses (H), (H_B') Lemma C applies"""
    d = {'sets': [[0, 2, 4, 5], [1, 3, 4, 8], [3, 6, 7, 8], [5, 6, 7, 8]],
         'vals': [[4, 5, 8, 2], [3, 4, 2, 8], [6, 2, 3, 10], [6, 3, 5, 7]], 'm': 9}
    key = '-,-,-,8'
    import collections
    import sx_zprime
    kp = KeyProfile(d)
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    ds = (kp.dstar[kt(key)], xr[key]['def*'])
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    nb = kp.neighbours()
    sx_zprime.analyse_key(kp, kt(key), cnt, ex, 0, nb)
    struct = cnt["KEYS: some Z-max covered by A, B1, C, C', B1' (structural hypotheses) = False"] == 1
    exact = cnt['KEYS: some Z-max covered with the exact hypotheses = True'] == 1
    good = ds == (1, 1) and struct and exact and cnt['Zmax'] == 1
    print('4. K4.SX.COVER with structural hypotheses (n = 4, m = 9): def* = %s (model, c4x_check); Z′-maxima %d; '
          'covered with (H*): %s; with the exact (H): %s; DLK (T3) holds: %s  %s'
          % (ds, cnt['Zmax'], not struct, exact, xr[key]['DLK_T3'], 'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def main():
    ok = [case1(), case2(), case3(), case4()]
    print('ALL CONFIRMED' if all(ok) else 'SOME NOT CONFIRMED')


if __name__ == '__main__':
    main()
