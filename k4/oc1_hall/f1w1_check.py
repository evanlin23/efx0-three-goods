"""Theorem F1-1 (k4/oc1_hall.md §5), run literally: exactly one frozen agent x, exactly one wanter w, n >= 3.  The
proof's case split, each case ending in Lemma 2's construction (ohlib.lemma2_build), checked with the raw EFX0 test:
  (A)  some o != x with v_x((J + {Y_o}) & R_x) <= p_x: owner o, H = {} at the picks;
  (B2) x has an improving pair H_0 in I(w) = (J + {Y_w}) & R_x: swap, owner o outside {x, w}, H = {} (Theorem DT1);
  (B3) otherwise I(w) = L_x (x's three lower goods) and every pair of L_x is worth <= p_x:
       (B3a) no agent i != x has some h in L_x with v_i(L_x - h) > p_i: swap (x takes L_x), owner w, H = {};
       (B3b) else such an i, with its better good g of L_x - h: owner o outside {x, i}, H = {g}, g to i's slot.
Counts each case; any failure is printed.

    python3 k4/oc1_hall/f1w1_check.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, lemma2_build, efx0, threatened
from min_frozen import load


def build(I, base, o, H, phi):
    B = bundles_of(I, base); F = set(frozen_set(I, base))
    N1 = [j for j in range(I.n) if j != o and len(B[j]) <= 1 and j not in F]
    X = lemma2_build(I, base, o, H, phi, N1)
    ok = X is not None and efx0(I, X) and all(set(b) <= set(x) for b, x in zip(B, X))
    # S* shape: only o may receive two or more junk goods; frozen and multi-good holders none
    if ok:
        J = set(g for g in range(I.m) if base[g] < 0)
        for j in range(I.n):
            extra = [g for g in X[j] if g in J]
            if j != o and (len(extra) > 1 or (extra and j not in N1)): ok = False
    return ok, X


def swap(P, base, x, w, H0):
    nb = list(base); Y = P.Y; nb[Y[x]] = w
    if Y[w] is not None and Y[w] not in H0: nb[Y[w]] = -1
    for g in H0: nb[g] = x
    return tuple(nb)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/f1w1_check.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5 or n < 3: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.F) != 1: continue
            x = P.F[0]
            if len(P.W[x]) != 1: continue
            w = P.W[x][0]; base = base_of_picks(I, Y); px = P.pv[x]
            C['starts (f = 1, |W| = 1, n >= 3)'] += 1
            Lx = [g for g in I.R[x] if g != Y[x]]
            # (A)
            A = [o for o in range(n) if o != x and I.val(x, [g for g in P.J + [Y[o]] if g is not None and g in I.R[x]]) <= px]
            if A:
                ok, X = build(I, base, A[0], [], {}); case = 'A'
            else:
                Iw = [g for g in P.J + ([Y[w]] if Y[w] is not None else []) if g in I.R[x]]
                pairs = [H for H in itertools.combinations(Iw, 2) if I.val(x, H) > px]
                if pairs:
                    nb = swap(P, base, x, w, pairs[0]); o = [j for j in range(n) if j not in (x, w)][0]
                    ok, X = build(I, nb, o, [], {}); case = 'B2'
                else:
                    assert sorted(Iw) == sorted(Lx) and len(Lx) == 3 and I.val(x, Lx) > px, (name, Y)
                    helpers = []
                    for i in range(n):
                        if i == x: continue
                        for h in Lx:
                            rest = [g for g in Lx if g != h]
                            if sum(1 for g in rest if g in I.R[i]) == 2 and I.val(i, rest) > P.pv[i]:
                                helpers.append((i, max(rest, key=lambda q: I.key[i][q])))
                        # (a pair inside L_x valued above p_i; with all three valued, some pair is such a pair)
                    if not helpers:
                        nb = swap(P, base, x, w, tuple(Lx)); ok, X = build(I, nb, w, [], {}); case = 'B3a'
                    else:
                        i, g = helpers[0]; o = [j for j in range(n) if j not in (x, i)][0]
                        Xo = [Y[o]] + [q for q in P.J if q != g]
                        phi = {i: g} if threatened(I, i, P.pv[i], Xo) else {}
                        if not phi:
                            # Lemma 2 places g in an unexposed holder; i itself is one
                            phi = {}
                        ok, X = build(I, base, o, [g], phi); case = 'B3b'
            C['case %s' % case] += 1
            if not ok:
                C['case %s FAILS' % case] += 1
                print('FAIL', case, name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'w', w, X, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
