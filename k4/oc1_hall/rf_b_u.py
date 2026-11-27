"""Hypothesis (B5) of Lemma RF-B at n = 4 (k4/oc1_hall.md §24.8): where it comes from.

At every B start of the complete n = 4 export (RF picks Y' of an OC1^max failure Y with receiver u; one receiver d at
Y'; two truly dangerous agents; k the one whose pick d wants), the only agent other than k, d that values two goods of
Z = {Y'_k, Y'_d} + (J' - S) is u.  This script checks:

  (U-a) R_u = {t, Y_k', Y_u, Y_k}, where t = Y'_u (u's top good) = Y_d, k' the other truly dangerous agent; so u
        values no junk good of Y, and its goods in Z are Y_u and Y_k (Y_u = Y'_d when d takes Y_u, and Y_u lies in
        J' - S when d takes a junk good);
  (U-b) v_u(Y_k') >= v_u(Y_u) + v_u(Y_k), which with v_u(t) > v_u(Y_k') gives (B5) for u;
  (U-c) u wants Y_k at Y; k wants Y_k' and k' does not want Y_k; R_k = {Y_k, Y_k'} + S; J' - S = {l} (one good) or
        two goods.

Then the contrapositive (EVIDENCE): u's values are changed to violate only (U-b), keeping u's ranking of single goods
and v_u(t) >= v_u(Y_u) + v_u(Y_k) (so (B5) still holds and the SD picks Y, Y' are unchanged), and the explicit repair at
Y is tested:

  REPAIR-Y  chain "k takes S, u takes Y_k" (official: S improving for k, u wants Y_k), then the completion "u takes
            Y_u back, k' takes the junk goods outside S (one good), d keeps t" (raw EFX0, two checkers).

    python3 k4/oc1_hall/rf_b_u.py
"""
import sys, os, json, gzip, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, efx0, absorb_brute
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def b_start(I, Y, u, o):
    Y2 = picks(I, [u] + [x for x in o if x != u]); P = Picks(I, Y2)
    U2 = [i for i in range(I.n) if i not in P.F]; DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
    if len(U2) != 1 or len(DT) != 2: return None
    d = U2[0]
    wants = lambda i, g: I.v[i].get(g, 0) > P.pv[i]
    k = [x for x in DT if wants(d, Y2[x]) and not wants([y for y in DT if y != x][0], Y2[x])][0]
    kk = [x for x in DT if x != k][0]
    S = [g for g in P.J if g in I.R[k] and g in I.R[kk]]
    return Y2, P, d, k, kk, S


def repair_y(I, Y, u, d, k, kk, S, J):
    """REPAIR-Y at the failing picks Y: is it official, and is the allocation EFX0 (both checkers)?"""
    pv = [I.v[i][Y[i]] for i in range(I.n)]
    official = I.val(k, S) > pv[k] and I.v[u][Y[k]] > pv[u]
    rest = [g for g in J if g not in S]
    X = [[y] for y in Y]; X[k] = list(S); X[u] = [Y[k], Y[u]]; X[kk] = [Y[kk]] + rest
    return official, efx0(I, X) and RawInst(I.sets, I.vals).efx0(X)


if __name__ == '__main__':
    data = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    C = collections.Counter(); done = set()
    print('$ python3 k4/oc1_hall/rf_b_u.py', flush=True)
    for hg in data['hypergraphs']:
        sets = hg['sets']; m = 1 + max(max(s) for s in sets)
        for st in hg['starts']:
            vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]; P0 = Picks(I, Y)
            for o in st['orders']:
                r = b_start(I, Y, u, o)
                if r is None: continue
                Y2, P, d, k, kk, S = r
                key = (json.dumps(vals), Y2)
                if key in done: continue
                done.add(key); C['B starts'] += 1
                t = Y2[u]; vu = I.v[u]
                C['(U-a) R_u = {t, Y_kk, Y_u, Y_k}, t = Y_d: %s' % (I.R[u] == {t, Y[kk], Y[u], Y[k]} and t == Y[d])] += 1
                C['(U-a) Y_k = Y\'_k, Y_kk = Y\'_kk: %s' % (Y[k] == Y2[k] and Y[kk] == Y2[kk])] += 1
                C['(U-b) v_u(Y_kk) >= v_u(Y_u) + v_u(Y_k): %s' % (vu[Y[kk]] >= vu[Y[u]] + vu[Y[k]])] += 1
                C['(U-c) u wants Y_k at Y: %s' % (vu[Y[k]] > vu[Y[u]])] += 1
                C['(U-c) k wants Y_kk, kk does not want Y_k (at Y\'): %s' % (I.v[k][Y2[kk]] > P.pv[k] and not I.v[kk].get(Y2[k], 0) > P.pv[kk])] += 1
                C['(U-c) R_k = {Y_k, Y_kk} + S: %s' % (I.R[k] == {Y2[k], Y2[kk]} | set(S))] += 1
                C['(U-c) |J\' - S| = %d, d takes %s' % (len(P.J) - len(S), 'Y_u' if Y2[d] == Y[u] else 'junk')] += 1
                C['(F-k) v_k(Y_kk) <= v_k(S): %s' % (I.v[k][Y[kk]] <= I.val(k, S))] += 1
                C['(F-d) v_d(t) > v_d(g) for g = Y_u, Y_k, Y_kk: %s' % all(I.v[d][t] > I.v[d].get(g, 0) for g in (Y[u], Y[k], Y[kk]))] += 1
                C['(F-d) R_d = %s' % sorted(('t' if g == t else 'Y_u' if g == Y[u] else 'Y_k' if g == Y[k] else 'Y_kk' if g == Y[kk] else 'S' if g in S else 'J-S') for g in I.R[d])] += 1
                C['(F-kk) R_kk = %s' % sorted(('Y_kk' if g == Y[kk] else 'Y_u' if g == Y[u] else 'Y_k' if g == Y[k] else 't' if g == t else 'S' if g in S else 'J-S') for g in I.R[kk])] += 1
                C['REPAIR-Y at the true Y (expected to fail, Y fails OC1): official %s, EFX0 %s' % repair_y(I, Y, u, d, k, kk, S, P0.J)] += 1
                # the contrapositive: violate only (U-b)
                if not I.R[u] == {t, Y[kk], Y[u], Y[k]}: C['perturbation skipped'] += 1; continue
                two = len([g for g in P0.J if g not in S]) == 2
                a, b = vu[Y[u]], vu[Y[k]]
                nv = [[10 * x for x in row] for row in vals]
                nv[u][sets[u].index(Y[kk])] = 10 * max(a, b) + 1
                nv[u][sets[u].index(t)] = 10 * (a + b) + 5
                I2 = Inst(sets, nv, m)
                if picks(I2, o) != Y or picks(I2, [u] + [x for x in o if x != u]) != Y2: C['perturbation changes the picks'] += 1; continue
                if not two:
                    C['perturbed (U-b) violated, (B5) kept, |J - S| = 1: REPAIR-Y official %s, EFX0 %s' % repair_y(I2, Y, u, d, k, kk, S, P0.J)] += 1
                    continue
                # |J - S| = 2: after the chain (k takes S, u takes Y_k), which one-absorber completions exist?
                base = [-1] * m
                for i in range(I.n): base[Y[i]] = i
                for g in S: base[g] = k
                base[Y[k]] = u; base[Y[u]] = -1
                ab = absorb_brute(I2, tuple(base), witness=True)
                if ab is None: C['perturbed, |J - S| = 2: no completion after the chain k -> u'] += 1; continue
                o_, X = ab
                C['perturbed, |J - S| = 2: chain k -> u then owner %s, X = %s' % ({u: 'u', d: 'd', k: 'k', kk: "k'"}[o_], [('t' if Y[d] in b else '') for b in X] and sorted([{u: 'u', d: 'd', k: 'k', kk: "k'"}[i] + ':' + ','.join(sorted(('Y_u' if g == Y[u] else 'Y_k' if g == Y[k] else 'Y_kk' if g == Y[kk] else 't' if g == t else 'S' if g in S else 'l') for g in X[i])) for i in range(I.n)]))] += 1
    for k_ in sorted(C): print(k_, C[k_])
