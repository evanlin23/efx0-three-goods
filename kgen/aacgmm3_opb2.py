"""OPB-AACGMM, second version (kgen/n3.md §14): the repair of §13's failures F1-F4.

Changes to kgen/aacgmm3_opb.py (one pick per bundle, picks never moved):
  * PR is replaced by REB, a rebalancing that targets only agent 1's two bundles X1, X2 and treats X3 as a dump.
    While X1 or X2 is not EFX-feasible for agent 1, let l be the poorer of the two, and (j, g) a violation:
    v1(Xj - g) > v1(Xl).
      - if some violating g is not a pick: move g from Xj to Xl;
      - else (only Xj's pick violates): exchange the non-pick parts of Xj and Xl. This is allowed when j = 3, or when
        Xj's pick is worth more to agent 1 than Xl's. Otherwise REB is blocked.
    Every move raises phi = min(v1(X1), v1(X2)) strictly, so REB terminates.
  * Repairs start from phi(X') instead of PR's three-bundle minimum. So the pinned compression of §13 (F3) cannot
    lower phi.
  * The start: the constrained three-bundle PR of §13 (stopping wherever it stops), agent 2 takes its favourite bundle
    as X3, then REB.
  * "Both envied" in case 2: the constrained three-bundle PR, agent 2 chooses, then REB (the three-bundle minimum is
    v1(X2) > phi before it, and never falls).
  * Invariant 2 (X3 feasible for agent 2 or 3) is checked after every REB. With RECHOOSE=1, when it is lost,
    agent 2 re-takes its favourite bundle as X3 and REB runs again (phi may fall then; this is counted).
  * The finish prefers a feasible matching that is an OC1 completion.
  * With DUMPSWAP=1, a blocked REB swaps the richer bundle's pick with the dump's pick, when the dump's pick is worth
    more to agent 1 than some non-pick good of the richer bundle. phi is unchanged, and a strict move follows.
Failure types: REB blocked; invariant 2 lost; X3 a single pick; case 2 exit not EFX0; no termination.

    [RECHOOSE=1] [DUMPSWAP=1] python3 kgen/aacgmm3_opb2.py SEED N MMIN MMAX"""
import sys, os, itertools, collections, json
from lemmaT3 import reachable
from oc3lib import picks, ORD
from aacgmm3 import val, feasible, efx0
from aacgmm3_fail import instances
from aacgmm3_opb import minimal_keep, Stuck

RECHOOSE = os.environ.get('RECHOOSE', '0') == '1'
DUMPSWAP = os.environ.get('DUMPSWAP', '0') == '1'


def cpr_soft(v, X, pins):
    """constrained PR without the final check: the three-bundle minimum rises strictly with every move"""
    X = [set(B) for B in X]
    while True:
        l = min(range(3), key=lambda k: val(v, X[k])); mv = None
        for j in range(3):
            if j == l: continue
            free = [g for g in X[j] if g not in pins]
            if free:
                g = min(free, key=lambda h: (v[h], h))
                if val(v, X[j]) - v[g] > val(v, X[l]): mv = (j, g); break
        if mv is None: return X
        j, g = mv; X[j].discard(g); X[l].add(g)


def reb(v, X, P, stats):
    X = [set(B) for B in X]
    while True:
        if feasible(v, X, 0) and feasible(v, X, 1): return X
        l = 0 if val(v, X[0]) < val(v, X[1]) else 1; o = 1 - l; target = val(v, X[l])
        mv = None
        for j in (2, o, l):
            if j == l: continue
            free = sorted((g for g in X[j] if g not in P), key=lambda h: (v[h], h))
            if free and val(v, X[j]) - v[free[0]] > target: mv = ('move', j, free[0]); break
        if mv is None:
            for j in (2, o):
                pk = next(iter(X[j] & P))
                if X[j] and val(v, X[j]) - v[pk] > target:
                    pl = next(iter(X[l] & P))
                    if j == 2 or v[pk] > v[pl]: mv = ('swap', j, None); break
            if mv is None and DUMPSWAP:
                pk = next(iter(X[o] & P)); p3 = next(iter(X[2] & P)); Ro = X[o] - P
                if Ro and v[p3] > min(v[h] for h in Ro): mv = ('pick swap with the dump', o, None)
            if mv is None: raise Stuck('REB blocked: only a pick of agent 1\'s richer bundle violates, and it is worth less than the poorer bundle\'s pick')
        kind, j, g = mv; stats[kind] += 1
        if kind == 'move': X[j].discard(g); X[l].add(g)
        elif kind == 'pick swap with the dump':
            pk = next(iter(X[o] & P)); p3 = next(iter(X[2] & P))
            X[o] = (X[o] - {pk}) | {p3}; X[2] = (X[2] - {p3}) | {pk}
        else:
            Rj, Rl = X[j] - P, X[l] - P
            X[j] = (X[j] & P) | Rl; X[l] = (X[l] & P) | Rj


def opb2(V, roles, y, stats):
    A, B, C = roles; m = len(V[0]); P = set(y); it = 0
    def choose(Q, who):
        k = max(range(3), key=lambda q: val(V[who], Q[q])); return [Q[q] for q in range(3) if q != k] + [Q[k]]
    def settle(X):
        X = reb(V[A], X, P, stats)
        if feasible(V[B], X, 2) or feasible(V[C], X, 2): return X
        if not RECHOOSE: raise Stuck('invariant 2 lost after REB (X3 feasible for neither agent 2 nor 3)')
        for _ in range(50):
            stats['rechoose'] += 1; X = reb(V[A], choose(X, B), P, stats)
            if feasible(V[B], X, 2) or feasible(V[C], X, 2): return X
        raise Stuck('invariant 2 lost after REB, re-choosing does not settle')
    X = settle(choose(cpr_soft(V[A], [{y[A]} | (set(range(m)) - P), {y[B]}, {y[C]}], P), B))
    phi = None
    while True:
        it += 1
        if it > 5000: raise Stuck('no termination')
        fin = []
        for perm in itertools.permutations(range(3)):
            if all(feasible(V[a], X, perm[p]) for p, a in enumerate((A, B, C))):
                out = [None] * 3
                for p, a in enumerate((A, B, C)): out[a] = X[perm[p]]
                fin.append(out)
        if fin:
            for out in fin:
                if reachable(V, y, out): return out, it
            return fin[0], it
        newphi = min(val(V[A], X[0]), val(V[A], X[1]))
        if phi is not None and newphi <= phi: stats['potential fell (after a re-choice)'] += 1
        phi = newphi
        if val(V[A], X[0]) > val(V[A], X[1]): X = [X[1], X[0], X[2]]
        X1, X2, X3 = X
        free3 = X3 - P
        if not free3: raise Stuck('X3 is a single pick')
        g = {i: min(free3, key=lambda h: (V[i][h], h)) for i in (B, C)}
        case1 = [i for i in (B, C) if val(V[i], X3 - {g[i]}) > val(V[i], X1 | {g[i]})]
        if case1:
            i = case1[0]; S = X1 | {g[i]}; X1p = minimal_keep(V[A], S, val(V[A], X1), X1 & P)
            X = settle([X1p, set(X2), (X3 - {g[i]}) | (S - X1p)]); continue
        Yb = [X1 | {g[B]}, X3 - {g[B]}]
        Y = cpr_soft2(V[B], Yb, P)
        if val(V[C], Y[0]) > val(V[C], Y[1]): Y = [Y[1], Y[0]]
        Y2, Y3 = Y; Xp = [X2, Y2, Y3]
        env = [k for k in (1, 2) if Xp[k] and val(V[A], Xp[k]) - min(V[A][h] for h in Xp[k]) > val(V[A], X2)]
        if not env:
            out = [None] * 3; out[A], out[B], out[C] = X2, Y2, Y3
            if not efx0(V, out): raise Stuck('case 2 exit not EFX0')
            return out, it
        if len(env) == 2: X = settle(choose(cpr_soft(V[A], Xp, P), B)); continue
        k = env[0]; o = 3 - k; Ybar = minimal_keep(V[A], Xp[k], val(V[A], X2), Xp[k] & P)
        X = settle([X2, Ybar, Xp[o] | (Xp[k] - Ybar)])


def cpr_soft2(v, Y, P):
    """agent 2's two-bundle constrained PR (case 2); its output must be EFX for agent 2, else case 2 is stuck"""
    Y = [set(B) for B in Y]
    while True:
        l = 0 if val(v, Y[0]) < val(v, Y[1]) else 1; o = 1 - l
        free = sorted((g for g in Y[o] if g not in P), key=lambda h: (v[h], h))
        if free and val(v, Y[o]) - v[free[0]] > val(v, Y[l]): Y[o].discard(free[0]); Y[l].add(free[0]); continue
        if Y[o] and val(v, Y[o]) - min(v[h] for h in Y[o]) > val(v, Y[l]): raise Stuck('case 2: agent 2\'s two-bundle PR blocked by a pick')
        return Y


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); C = collections.Counter(); shown = collections.Counter(); stats = collections.Counter()
    print('$ %s%spython3 kgen/aacgmm3_opb2.py' % ('RECHOOSE=1 ' if RECHOOSE else '', 'DUMPSWAP=1 ' if DUMPSWAP else ''), *sys.argv[1:], flush=True)
    for kind, raw, V in instances(seed, N, lo, hi):
        for o in ORD:
            y = picks(V, o)
            if any(g is None for g in y): continue
            C[kind + ': starts'] += 1; good = {}
            for roles in ORD:
                C[kind + ': runs'] += 1
                try:
                    X, it = opb2(V, roles, y, stats); assert efx0(V, X)
                    r = reachable(V, y, X); good[roles] = r
                    C[kind + ': runs ending EFX0'] += 1; C[kind + ': runs ending EFX0 and OC1-reachable'] += r
                    if not r: C[kind + ': runs ending EFX0, not OC1, identity placement'] += all(y[i] in X[i] for i in range(3))
                except Stuck as e:
                    C[kind + ': runs failing: ' + str(e)] += 1
                    if shown[str(e)] < 1:
                        shown[str(e)] += 1; print('FAIL', str(e), kind, json.dumps(raw), 'order', o, 'roles', roles, 'picks', y, flush=True)
            C[kind + ': starts where some role assignment ends OC1-reachable'] += any(good.values())
            C[kind + ': starts where roles = order ends OC1-reachable'] += good.get(o, False)
    for k in sorted(C): print(C[k], k)
    for k in sorted(stats): print(stats[k], 'moves:', k)
