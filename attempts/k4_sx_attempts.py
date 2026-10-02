#!/usr/bin/env python3
"""Replay of the failed candidate statements of workstream proof/k4-sx (attempts/k4-sx-*.md; ledger row K4.SX.X).

Implementations, and what each computes:
  M  k4/suite/model.py through k4/sx_keygraph.py, k4/sx_zprime.py, k4/sx_f2.py (deficits by Lemma H1; configurations,
     threats, the lemmas' hypotheses);
  X  main's k4/c4x_check.py through k4/sx_xcheck.py (its own enumeration of 𝒫, the direct removal-only deficit `rodef`):
     def* of the key, and the deficits of the images in case 1;
  I  k4/sx_indep.py, the PR #80 referee's checker (no repository code; f = 1): def*, the Z′-maxima, θ-b, the kinds,
     threats and the lemma hypotheses of cases 1, 2 and 4, and, from its primitives (Prof.theta, Prof.deficit), the
     leaves' threats at the f = 2 maxima of case 3;
  R  main's k4/rt4_n5_indep.py (PR #86 auditor's checker, no repository code): def* of the f >= 2 keys of case 3.

1. Lemma A without its theta-b exception (attempts/k4-sx-owner-swap-thetab.md): at a Z′-maximum of a non-completable
   f = 1 key, the owner swap with a theta-b terminal leaf o ends, for every admissible base of x inside X_o, at a state
   whose deficit is not below def*(κ). [M, X, I]
2. Lemma B for every leaf (attempts/k4-sx-path-move-r-leaf.md): for an (R) leaf o with s_o in the pool, x's bundle X_o
   threatens o holding its threatener's pair after the plain path move. [M, X, I]
3. Lemma A⁺ (or B⁺) at every non-completable f >= 2 key (attempts/k4-sx-aplus-f3.md): no maximum of (r', Λ') at the
   key satisfies the hypotheses of Lemma A⁺ or B⁺ (k4/sx.md §6).
   3a. n = 4, m = 8, f = 2 (the smallest found; the PR #80 referee's instance): every leaf at every maximum threatens
       both frozen agents. def* [M, X, R, I]; the leaves' threats [M, I]; A⁺/B⁺ verdict [M].
   3b. n = 4, m = 9, f = 2 (the PR #80 auditor's instance). def* [M, X, R]; A⁺/B⁺ verdict [M].
   3c. n = 5, m = 12, f = 3 (compute/k4-rt4-n5c). def* [M, X]; A⁺/B⁺ verdict [M].
4. K4.SX.COVER with the structural hypotheses (H*), (H'*), (H_B'*) (attempts/k4-sx-cover-structural.md): at an
   n = 4, m = 9 key no Z′-maximum is covered that way; with the exact hypotheses Lemma C applies. [M, X, I]
usage: python3 attempts/k4_sx_attempts.py"""
import collections, itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4')); sys.path.insert(0, os.path.join(HERE, '..', 'k4', 'suite'))
import c4x_check as CX
from sx_keygraph import KeyProfile
from sx_xcheck import keygraph
from model import bits, pc, mask
import sx_indep as SI
import rt4_n5_indep as RI

F = SI.F


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


# ---------------------------------------------------------------- implementation I (k4/sx_indep.py), f = 1 keys
def indep_key(d, g, x):
    """(Prof, Key, def*, the Z′-maxima) of the f = 1 key (g, x) in k4/sx_indep.py's model"""
    pr = SI.Prof(d['sets'], d['vals'], d['m'])
    st = pr.all_states()
    f = min(len(inf[1]) for _, inf in st)
    assert f == 1
    P0, inf0 = next((P, inf) for P, inf in st if len(inf[1]) == 1)
    om = len(inf0[2]) - sum(2 - len(P0[i]) for i in range(pr.n) if i not in inf0[1])
    ds = min(pr.deficit(P) for P, inf in st if inf[1] == F(x) and P[x] == F(g))
    K = SI.Key(pr, g, x, om)
    cfs = [SI.Cfg(K, Q, L) for Q, L in K.configs()]
    best = max(c.pot() for c in cfs)
    return pr, K, ds, [c for c in cfs if c.pot() == best]


def find_cfg(cs, Q, L):
    return next(c for c in cs if {y: set(q) for y, q in c.Q.items()} == {y: set(q) for y, q in Q.items()}
                and set(c.L) == set(L))


# ---------------------------------------------------------------- implementation I's primitives at f >= 2 (case 3a)
def indep_leaves_f2(d, phi):
    """the maxima of (r', Λ') at the key phi = {frozen agent: good}, with k4/sx_indep.py's Prof (values, theta, needs);
    for each maximum the list (leaf o, frozen agents its bundle threatens)"""
    pr = SI.Prof(d['sets'], d['vals'], d['m'])
    Nset = frozenset(phi.values())
    free = [y for y in range(pr.n) if y not in phi]
    U = {y: pr.R[y] - Nset for y in range(pr.n)}

    def adm(y, A):
        if not A or len(A) > 2 or not A <= U[y]: return False
        return all(pr.v[y][h] < pr.val(y, A) for h in U[y] - A)
    Mp = sorted(pr.M - Nset)
    cand = {y: [F(a, b) for a, b in itertools.combinations(Mp, 2) if adm(y, F(a, b) & U[y])] for y in free}
    cfgs = []

    def rec(i, used, cur):
        if i == len(free): cfgs.append((dict(cur), pr.M - Nset - used)); return
        for Q in cand[free[i]]:
            if Q & used: continue
            cur[free[i]] = Q; rec(i + 1, used | Q, cur); del cur[free[i]]
    rec(0, frozenset(), {})

    def pot(Q):
        r = sum(pr.val(y, Q[y]) >= pr.val(y, U[y] - Q[y]) for y in free)
        lam = 0
        for y in free:
            vH = pr.val(y, Q[y] & U[y]); R = sorted(pr.R[y])
            lam += sum(1 for k in range(len(R) + 1) for T in itertools.combinations(R, k) if pr.val(y, T) < vH)
        return r, lam
    best = max(pot(Q) for Q, L in cfgs)
    out = []
    for Q, L in cfgs:
        if pot(Q) != best: continue
        hv = {y: pr.val(y, Q[y] & U[y]) for y in free}
        hv.update({w: pr.v[w][g] for w, g in phi.items()})
        X = {o: Q[o] | L for o in free}
        leaves = [o for o in free if not any(pr.theta(y, X[o]) > hv[y] for y in free if y != o)]
        out.append([(o, sorted(w for w in phi if pr.theta(w, X[o]) > hv[w])) for o in leaves])
    return out


# ---------------------------------------------------------------- the cases
def case1():
    """theta-b owner swap: n = 4, m = 10"""
    d = {'sets': [[0, 2, 6, 9], [1, 5, 8, 9], [3, 6, 7, 9], [4, 7, 8]],
         'vals': [[4, 5, 6, 8], [4, 2, 3, 8], [4, 2, 3, 8], [2, 4, 3]], 'm': 10}
    key, x, o, g = '9,-,-,-', 0, 1, 9
    P = [[9], [1, 8], [3, 6], [4, 7]]            # the Z′-maximum Q_1 = {1, 8}, Q_2 = {3, 6}, Q_3 = {4, 7}, L = {0, 2, 5}
    Xo = {1, 8, 0, 2, 5}
    kp = KeyProfile(d); I = kp.I
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    pr, K, dsI, mx = indep_key(d, g, x)
    ds = (kp.dstar[kt(key)], xr[key]['def*'], dsI)
    c = find_cfg(mx, {1: {1, 8}, 2: {3, 6}, 3: {4, 7}}, {0, 2, 5})       # I: it is a Z′-maximum
    thb = SI.thetab(c, o) and c.thr(c.X[o], x) and not any(c.thr(c.X[o], w) for w in K.free if w != o)
    res = []
    for r in (1, 2):
        for A in itertools.combinations(sorted(Xo & set(d['sets'][x])), r):
            if not I.admissible(x, mask(A), I.R[x] & ~(1 << g)): continue
            P2 = [list(b) for b in P]; P2[o] = [g]; P2[x] = list(A)
            res.append((A, kp.D[tuple(mask(b) for b in P2)], rodef_x(d, P2), pr.deficit(tuple(F(*b) for b in P2))))
    resI = sorted(tuple(sorted(Px & K.U[x])) for Px in SI.pairs_for_x(K, c.X[o]))
    good = ds == (1, 1, 1) and thb and res and all(a == b == e and a >= 1 for _, a, b, e in res) and \
        resI == [A for A, _, _, _ in res]
    print('1. theta-b owner swap (n = 4, m = 10): def* = %s (M, X, I); the configuration is a Z′-maximum with o = 1 a '
          'theta-b leaf threatening x (I): %s; x\'s admissible bases inside X_o and def(P\') (M, X, I): %s  %s'
          % (ds, thb, res, 'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def case2():
    """plain path move to an (R) leaf with s in L: n = 4, m = 8"""
    d = {'sets': [[0, 4, 5, 6], [1, 4, 5, 7], [2, 3, 6, 7], [2, 3, 6, 7]],
         'vals': [[4, 6, 3, 8], [6, 8, 3, 10], [3, 2, 4, 8], [6, 3, 8, 10]], 'm': 8}
    key = '-,7,-,-'                             # x = 1 frozen on 7; Q_0 = {0, 4}, Q_2 = {1, 6}, Q_3 = {2, 3}, L = {5}
    kp = KeyProfile(d); I = kp.I
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    pr, K, dsI, mx = indep_key(d, 7, 1)
    ds = (kp.dstar[kt(key)], xr[key]['def*'], dsI)
    # leaf o = 0, kind (R): a = 6, {p, q} = {0, 4}, s = 5 in L; tau = 2 threatens 0 (6 in Q_2); plain move: 0 takes Q_2
    Xo = mask([0, 4, 5]); new_o = mask([1, 6])
    thr = I.threat(0, Xo, I.val(0, new_o))
    thr_x = (max(I.val(0, Xo & ~(1 << h)) for h in (0, 4, 5)), I.val(0, new_o))   # theta_0(X_o), v_0({1, 6})
    c = find_cfg(mx, {0: {0, 4}, 2: {1, 6}, 3: {2, 3}}, {5})              # I: a Z′-maximum
    kindI = SI.kind(c, 0)
    thrI = pr.theta(0, c.X[0]) > pr.val(0, F(1, 6))
    good = ds == (1, 1, 1) and thr and thrI and kindI == 'R' and 5 in c.L and c.thr(c.X[2], 0)
    print('2. plain path move to an (R) leaf with s in L (n = 4, m = 8): def* = %s (M, X, I); at the Z′-maximum (I) '
          'o = 0 is of kind %s, threatened by 2, with s = 5 in L; X_o = {0, 4, 5} threatens o = 0 holding {1, 6}: '
          '%s (M), %s (I) (theta = %d > %d)  %s' % (ds, kindI, thr, thrI, thr_x[0], thr_x[1],
                                                    'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def f2_case(tag, d, key, phi, rt4=True, indep_leaves=False):
    import sx_f2
    kp = KeyProfile(d)
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    ds = [kp.dstar[kt(key)], xr[key]['def*']]
    if rt4:
        ns = RI.analyse(d['sets'], d['vals'], d['m'])
        kd = collections.defaultdict(list)
        for P in ns['mf']:
            fz = ns['info'](P)[3]
            kd[tuple(min(P[i]) if fz[i] else None for i in range(len(P)))].append(ns['D'][P])
        ds.append(min(kd[kt(key)]))
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    sx_f2.analyse_key(kp, kt(key), cnt, ex, 0)
    leafI = None
    if indep_leaves:
        lv = indep_leaves_f2(d, phi)
        leafI = (len(lv), all(len(ws) == 2 for m_ in lv for _, ws in m_) and all(m_ for m_ in lv))
        ds.append(min(SI.Prof(d['sets'], d['vals'], d['m']).deficit(P) for P, inf in
                      SI.Prof(d['sets'], d['vals'], d['m']).all_states()
                      if inf[1] == frozenset(phi) and all(P[w] == F(gg) for w, gg in phi.items())))
    why = sorted((k[len('no A+/B+: '):], v) for k, v in cnt.items() if k.startswith('no A+/B+: '))
    good = all(v == 1 for v in ds) and cnt['Zmax'] > 0 and \
        cnt['Zmax: Lemma A+ or B+ applies=False'] == cnt['Zmax'] and (leafI is None or (leafI[0] == cnt['Zmax'] and leafI[1]))
    print('3%s. Lemma A+/B+ at an f = %d key (n = %d, m = %d) %s: def* = %s (%s); maxima %d, with A+ or B+ %d (M); '
          'why not (M): %s;%s DLK with T3 / T3+T4 edges (X): %s / %s  %s'
          % (tag, kp.I.f, len(d['sets']), d['m'], key, tuple(ds), ', '.join(['M', 'X'] + (['R'] if rt4 else []) +
                                                                         (['I'] if indep_leaves else [])),
             cnt['Zmax'], cnt['Zmax: Lemma A+ or B+ applies=True'], why,
             (' maxima %d, every leaf threatens both frozen agents (I): %s;' % leafI) if leafI else '',
             xr[key]['DLK_T3'], xr[key]['DLK_T3+T4'], 'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def case3():
    a = f2_case('a', {'sets': [[0, 2, 4, 6], [0, 2, 5, 6], [1, 3, 4, 7], [1, 3, 5, 7]],
                      'vals': [[2, 3, 8, 4]] * 4, 'm': 8}, '4,5,-,-', {0: 4, 1: 5}, indep_leaves=True)
    b = f2_case('b', {'sets': [[0, 2, 4, 8], [1, 3, 6, 7], [2, 3, 4, 5], [5, 6, 7, 8]],
                      'vals': [[2, 4, 3, 8], [3, 8, 4, 2], [4, 8, 3, 2], [2, 3, 6, 10]], 'm': 9}, '-,3,-,8', {1: 3, 3: 8})
    c = f2_case('c', {'sets': [[0, 2, 6, 10], [1, 4, 9, 11], [3, 5, 9, 11], [6, 7, 8, 10], [7, 8, 10, 11]],
                      'vals': [[2, 3, 6, 10], [3, 4, 2, 8], [3, 2, 4, 8], [2, 3, 10, 6], [2, 10, 6, 3]], 'm': 12},
                '10,-,11,8,-', {0: 10, 2: 11, 3: 8}, rt4=False)
    return a and b and c


def case4():
    """K4.SX.COVER with the structural hypotheses (H*), (H'*), (H_B'*): n = 4, m = 9, the unique Z′-maximum of a
    non-completable key satisfies none of A, B (k = 1), B' (k = 1) with (H_B'*), C with (H*), C' with (H'*); with the
    exact hypotheses (H), (H_B') Lemma C applies"""
    d = {'sets': [[0, 2, 4, 5], [1, 3, 4, 8], [3, 6, 7, 8], [5, 6, 7, 8]],
         'vals': [[4, 5, 8, 2], [3, 4, 2, 8], [6, 2, 3, 10], [6, 3, 5, 7]], 'm': 9}
    key = '-,-,-,8'
    import sx_zprime
    kp = KeyProfile(d)
    f, xr = keygraph(d['sets'], d['vals'], d['m'])
    pr, K, dsI, mx = indep_key(d, 8, 3)
    ds = (kp.dstar[kt(key)], xr[key]['def*'], dsI)
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    nb = kp.neighbours()
    sx_zprime.analyse_key(kp, kt(key), cnt, ex, 0, nb)
    struct = cnt["KEYS: some Z-max covered by A, B1, C, C', B1' (structural hypotheses) = False"] == 1
    exact = cnt['KEYS: some Z-max covered with the exact hypotheses = True'] == 1
    # I: the lemmas that apply at the Z′-maximum with the exact hypotheses, and (H*) at every Lemma C instance
    SI.cnt.clear(); del SI.viol[:]
    SI.run_profile(d)
    appliesI = sorted(k[len('Zmax applies '):] for k in SI.cnt if k.startswith('Zmax applies '))
    c = mx[0]; x, g = 3, 8
    hst = []
    for t1 in K.free:
        if not (g in pr.R[t1] and pr.val(t1, c.Q[t1]) < pr.v[t1][g]) or not SI.thetab(c, t1): continue
        if any(c.thr(c.X[t1], w) for w in K.free if w != t1): continue
        for o in K.free:
            if o == t1 or any(c.thr(c.X[o], w) for w in K.free if w != o): continue
            for Px in SI.pairs_for_x(K, c.X[t1]):
                if pr.val(x, Px) < pr.val(x, K.U[x] - Px) or not Px & K.U[t1]: continue
                Y = c.Q[o] | (c.X[t1] - Px)
                hstar = not any((c.Q[t1] - Px) & pr.R[w] for w in range(pr.n) if w not in (x, o, t1))
                hex_ = not any(c.thr(Y, w) for w in K.free if w not in (o, t1))
                if hex_: hst.append(hstar)
    okI = len(mx) == 1 and appliesI == ['C'] and hst and not any(hst) and not any(k.startswith('VIOLATION') for k in SI.cnt)
    good = ds == (1, 1, 1) and struct and exact and cnt['Zmax'] == 1 and okI
    print('4. K4.SX.COVER with structural hypotheses (n = 4, m = 9): def* = %s (M, X, I); Z′-maxima %d (M), %d (I); '
          'covered with (H*): %s (M); with the exact (H): %s (M); lemmas applying with exact hypotheses (I): %s, (H*) at '
          'its Lemma C instances (I): %s; DLK (T3) holds (X): %s  %s'
          % (ds, cnt['Zmax'], len(mx), not struct, exact, appliesI, hst, xr[key]['DLK_T3'],
             'CONFIRMED' if good else 'NOT CONFIRMED'))
    return good


def main():
    ok = [case1(), case2(), case3(), case4()]
    print('ALL CONFIRMED' if all(ok) else 'SOME NOT CONFIRMED')


if __name__ == '__main__':
    main()
