"""AACGMM (kgen/aacgmm3.py) with the picks carried: "one pick per bundle" (OPB).

Invariant added to AACGMM's: each of the three bundles contains exactly one SD pick.  Then every final matching places
the picks as a permutation (identity, a swap, or a 3-cycle).  Each of those is a chain pattern of Lemma R: no chain,
t = 1 with the third agent off the chain, or t = 2.  So the output is an OC1(t >= 0) completion as soon as the strict
gains hold and, for the identity, some agent holds at most one good besides its pick.  Moves are AACGMM's, restricted:
  - PR never moves a pick (constrained PR; the minimum still rises strictly, so it terminates, but it may stop before
    the partition is EFX for the valuation: "PR stuck");
  - g_i is i's cheapest non-pick good of X3, and compressions keep the bundle's pick.
Failure types are counted: PR stuck (init / case 1 / case 2 / repair), invariant broken, X3 has no non-pick good,
the potential not rising, and case 2's direct exit not being EFX0.

With FINISH=oc1 in the environment, the final matching prefers a feasible matching that is an OC1 completion.

    [FINISH=oc1] python3 kgen/aacgmm3_opb.py SEED N MMIN MMAX"""
import sys, os, itertools, collections, json
from lemmaT3 import reachable
from oc3lib import picks, ORD
from aacgmm3 import val, feasible, efx0
from aacgmm3_fail import instances


FINISH = os.environ.get('FINISH', 'first')


class Stuck(Exception):
    pass


def is_efx(v, X): return all(feasible(v, X, k) for k in range(len(X)) if True) or False


def part_efx(v, X):
    """the partition is EFX for the single valuation v: no bundle minus a good beats another bundle"""
    low = min(val(v, B) for B in X)
    return all(not B or val(v, B) - min(v[g] for g in B) <= low for B in X)


def cpr(v, X, pins, where):
    X = [set(B) for B in X]
    while True:
        l = min(range(len(X)), key=lambda k: val(v, X[k])); mv = None
        for j in range(len(X)):
            if j == l: continue
            free = [g for g in X[j] if g not in pins]
            if not free: continue
            g = min(free, key=lambda h: (v[h], h))
            if val(v, X[j]) - v[g] > val(v, X[l]): mv = (j, g); break
        if mv is None: break
        j, g = mv; X[j].discard(g); X[l].add(g)
    if not part_efx(v, X): raise Stuck('PR stuck: ' + where)
    return X


def minimal_keep(v, S, target, keep):
    T = set(S)
    for h in sorted(S - keep, key=lambda h: (v[h], h)):
        if val(v, T - {h}) > target: T.discard(h)
    return T


def opb(V, roles, y):
    A, B, C = roles; m = len(V[0]); P = set(y); it = 0
    pin = lambda S: S & P
    def choose(Q, who):
        k = max(range(3), key=lambda q: val(V[who], Q[q])); return [Q[q] for q in range(3) if q != k] + [Q[k]]
    X = choose(cpr(V[A], [{y[A]} | (set(range(m)) - P), {y[B]}, {y[C]}], P, 'init'), B)
    phi, last = None, 'init'
    while True:
        it += 1
        if it > 5000: raise Stuck('no termination')
        assert all(len(pin(Bd)) == 1 for Bd in X)
        fin = []
        for perm in itertools.permutations(range(3)):
            if all(feasible(V[a], X, perm[p]) for p, a in enumerate((A, B, C))):
                out = [None] * 3
                for p, a in enumerate((A, B, C)): out[a] = X[perm[p]]
                fin.append(out)
        if fin:                       # FINISH=oc1: prefer a feasible matching that is an OC1 completion
            if FINISH == 'oc1':
                for out in fin:
                    if reachable(V, y, out): return out, it
            return fin[0], it
        if not (feasible(V[A], X, 0) and feasible(V[A], X, 1)): raise Stuck('invariant: X1, X2 not EFX-feasible for agent 1')
        if not (feasible(V[B], X, 2) or feasible(V[C], X, 2)): raise Stuck('invariant: X3 feasible for neither agent 2 nor 3')
        newphi = min(val(V[A], X[0]), val(V[A], X[1]))
        if phi is not None and newphi <= phi: raise Stuck('potential does not rise after: ' + last)
        phi = newphi
        if val(V[A], X[0]) > val(V[A], X[1]): X = [X[1], X[0], X[2]]
        X1, X2, X3 = X
        free3 = X3 - P
        if not free3: raise Stuck('X3 is a single pick')
        g = {i: min(free3, key=lambda h: (V[i][h], h)) for i in (B, C)}
        case1 = [i for i in (B, C) if val(V[i], X3 - {g[i]}) > val(V[i], X1 | {g[i]})]
        if case1:
            i = case1[0]; S = X1 | {g[i]}; X1p = minimal_keep(V[A], S, val(V[A], X1), pin(X1))
            Xp = [X1p, set(X2), (X3 - {g[i]}) | (S - X1p)]
            if feasible(V[A], Xp, 0) and feasible(V[A], Xp, 1): X, last = Xp, 'case 1 (add and compress)'
            else: X, last = choose(cpr(V[A], Xp, P, 'case 1 repair'), B), 'case 1 + PR'
            continue
        Y = cpr(V[B], [X1 | {g[B]}, X3 - {g[B]}], P, 'case 2 (agent 2 cuts)')
        if val(V[C], Y[0]) > val(V[C], Y[1]): Y = [Y[1], Y[0]]
        Y2, Y3 = Y; Xp = [X2, Y2, Y3]
        env = [k for k in (1, 2) if Xp[k] and val(V[A], Xp[k]) - min(V[A][h] for h in Xp[k]) > val(V[A], X2)]
        if not env:
            out = [None] * 3; out[A], out[B], out[C] = X2, Y2, Y3
            if not efx0(V, out): raise Stuck('case 2 exit not EFX0 (X3 - g_i is not i\'s best proper subset when g_i must avoid the pick)')
            return out, it
        if len(env) == 2: X, last = choose(cpr(V[A], Xp, P, 'case 2 repair (both envied)'), B), 'case 2, both envied, PR'; continue
        k = env[0]; o = 3 - k; Yb = minimal_keep(V[A], Xp[k], val(V[A], X2), pin(Xp[k]))
        Xpp = [X2, Yb, Xp[o] | (Xp[k] - Yb)]
        if feasible(V[A], Xpp, 0) and feasible(V[A], Xpp, 1): X, last = Xpp, 'case 2, one envied, compress'
        else: X, last = choose(cpr(V[A], Xpp, P, 'case 2 repair (one envied)'), B), 'case 2, one envied, PR'


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); C = collections.Counter(); shown = collections.Counter()
    print('$ python3 kgen/aacgmm3_opb.py', *sys.argv[1:], flush=True)
    for kind, raw, V in instances(seed, N, lo, hi):
        for o in ORD:
            y = picks(V, o)
            if any(g is None for g in y): C[kind + ': starts with a pickless agent (skipped)'] += 1; continue
            C[kind + ': starts'] += 1; good = {}
            for roles in ORD:
                try:
                    X, it = opb(V, roles, y); assert efx0(V, X)
                    r = reachable(V, y, X); good[roles] = r
                    C[kind + ': runs ending EFX0'] += 1; C[kind + ': runs ending EFX0 and OC1-reachable'] += r
                    if not r: C[kind + ': runs ending EFX0, not OC1: identity placement'] += all(y[i] in X[i] for i in range(3))
                except Stuck as e:
                    C[kind + ': runs failing: ' + str(e)] += 1
                    if shown[str(e)] < 2:
                        shown[str(e)] += 1; print('FAIL', str(e), kind, json.dumps(raw), 'order', o, 'roles', roles, 'picks', y, flush=True)
                C[kind + ': runs'] += 1
            C[kind + ': starts where roles = order ends OC1-reachable'] += good.get(o, False)
            C[kind + ': starts where some role assignment ends OC1-reachable'] += any(good.values())
    for k in sorted(C): print(C[k], k)
