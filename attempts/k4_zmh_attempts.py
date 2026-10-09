#!/usr/bin/env python3
"""Replays the failed candidate statements of workstream proof/k4-zmove-hall (attempts/k4-zmh-*.md), each with two
implementations: A = k4/zmh_lib.py (states, Lemma H1 deficits, Z′-maxima through the states and fillers), B = main's
repo-free k4/rt4_n5_indep.py (raw removal-only deficit) with the configurations enumerated directly (k4/zmh_xcheck.py).

usage: python3 attempts/k4_zmh_attempts.py"""
import collections, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
from zmh_lib import Prof, show, bits
import zmh_xcheck as XB


def bigtop(sets, vals, x, g):
    v = dict(zip(sets[x], vals[x]))
    if len(sets[x]) != 4: return False
    lo = sorted((v[h] for h in sets[x] if h != g), reverse=True)
    return v[g] > lo[0] + lo[1]


def s1c_plus(inst, x, g):
    """S1c+: at a Z′-maximum of the key (g, x) with x big-top and >= 2 terminals, def(P_Q) <= 0"""
    sets, vals, m = inst['sets'], inst['vals'], inst['m']
    print('instance', inst, ' key: agent %d on good %d, x big-top:' % (x, g), bigtop(sets, vals, x, g))
    # A
    pr = Prof(sets, vals, m)
    key = tuple((1 << g) if i == x else None for i in range(pr.n))
    zs, best = pr.zmax_states(key)
    for P in zs:
        T = [y for y in range(pr.n) if key[y] is None and pr.needs(y, P[y]) >> g & 1]
        print('  A: Z′-max', show(P), 'potential', best, 'terminals', T, 'def(P_Q) =', pr.D[P], 'def* =', pr.dstar[key])
    # B
    omega, out, ns, dstar = XB.zmove_indep(sets, vals, m, all_keys=True, want_ns=True)
    info, D = ns['info'], ns['D']
    for k, (ds, pot, per, t4) in out.items():
        if k[x] != frozenset([g]) or any(k[i] is not None for i in range(len(sets)) if i != x): continue
        for PQ in per:
            N = info(PQ)[0]
            T = [y for y in range(len(sets)) if y != x and g in N[y]]
            print('  B: Z′-max', '(' + ', '.join(str(sorted(b)) for b in PQ) + ')', 'potential', pot, 'terminals', T,
                  'def(P_Q) =', D[PQ], 'def* =', ds)


def po_forest(inst, key_goods, state):
    """'ZMOVE at every pool-optimal configuration whose free threats are acyclic': the given state of the key admits
    such a configuration, def* > 0, and no (T3⁺) move with at most one helper from it reaches deficit <= 0"""
    import itertools
    sets, vals, m = inst['sets'], inst['vals'], inst['m']
    n = len(sets)
    print('instance', inst, ' key', key_goods, ' state', state)
    # A
    pr = Prof(sets, vals, m)
    key = tuple(None if g is None else 1 << g for g in key_goods)
    P = tuple(sum(1 << g for g in B) for B in state)
    good = [Q for Q in pr.states if pr.D[Q] <= 0]
    mv = [Q for Q in good if 'T3+' in pr.move_kind(P, Q)[0]]
    zs, best = pr.zmax_states(key)
    zmv = [any('T3+' in pr.move_kind(Z, Q)[0] for Q in good) for Z in zs]
    print('  A: def* =', pr.dstar[key], ' def(state) =', pr.D[P], ' potential', pr.potential(P, key),
          ' moves to def <= 0:', len(mv), ' Z′-maxima', [show(Z) for Z in zs], 'potential', best,
          'each with a move:', zmv)
    # B: rt4_n5_indep's states, deficits and classify; the configuration over the state, its pool-optimality and its
    # threat digraph among the free agents, written out here
    import rt4_n5_indep as RI
    ns = RI.analyse(sets, vals, m)
    D, info, classify = ns['D'], ns['info'], ns['classify']
    PB = tuple(frozenset(B) for B in state)
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]

    def val(i, X): return sum(v[i].get(g, 0) for g in X)

    def thr(w, X, b): return bool(X) and val(w, X) - min(v[w].get(h, 0) for h in X) > b

    def keyB(X): return tuple(X[i] if info(X)[3][i] else None for i in range(n))
    kP = keyB(PB)
    dstar = min(D[X] for X in D if keyB(X) == kP)
    NN = frozenset(g for g in key_goods if g is not None)
    J = info(PB)[2]
    free = [i for i in range(n) if key_goods[i] is None]
    slots = [(y, c) for y in free for c in range(2 - len(PB[y]))]
    found = None
    for fill in itertools.permutations(sorted(J), len(slots)):
        if any(fill[k] in v[slots[k][0]] for k in range(len(slots))): continue
        Q = {y: set(PB[y]) for y in free}
        for k, (y, c) in enumerate(slots): Q[y].add(fill[k])
        L = set(J) - set(fill)
        U = {y: set(sets[y]) - NN for y in free}
        po = all(val(y, S) <= val(y, Q[y]) for y in free
                 for r in (1, 2) for S in itertools.combinations(sorted((Q[y] | L) & U[y]), r))
        if not po: continue
        adj = {o: [w for w in free if w != o and thr(w, Q[o] | L, val(w, Q[w]))] for o in free}
        left = set(free)                      # acyclic: peel the agents without out-edges inside the rest
        while True:
            sink = [o for o in left if not any(w in left for w in adj[o])]
            if not sink: break
            left -= set(sink)
        if left: continue
        found = (Q, L, adj); break
    moves = [X for X in D if D[X] <= 0 and 'T3+' in classify(PB, X)[0]]
    print('  B: def* =', dstar, ' def(state) =', D[PB], ' pool-optimal acyclic configuration:',
          None if found is None else ({y: sorted(q) for y, q in found[0].items()}, sorted(found[1]), found[2]),
          ' moves to def <= 0:', len(moves))


def x_owner(inst):
    """ZX: at some Z′-maximum of every key with def* > 0, a (T3⁺) move with <= 1 helper to def <= 0 after which the
    unfrozen agent x is a best owner. Prints, per key with def* > 0 and per Z′-maximum, the repairing moves and how many
    of them have x as a best owner."""
    import itertools
    sets, vals, m = inst['sets'], inst['vals'], inst['m']
    n = len(sets)
    print('instance', inst)
    pr = Prof(sets, vals, m)
    for key, ds in pr.dstar.items():
        if ds <= 0: continue
        zs, best = pr.zmax_states(key)
        for P in zs:
            mv = [(Q, pr.move_kind(P, Q)[1]) for Q in pr.states if pr.D[Q] <= 0 and 'T3+' in pr.move_kind(P, Q)[0]]
            xo = sum(1 for Q, sh in mv if pr.owner_val(Q, sh[1][0])[0] >= pr.omega + 2)
            Q0, L0 = pr.configs_over(P, key)[0]
            free = [y for y in range(n) if key[y] is None]
            leaves = [o for o in free if not any(pr.threat(w, Q0[o] | L0, pr.val(w, Q0[w])) for w in free if w != o)]
            roles = collections.Counter()
            for Q, (ch, U, Z, W, Y) in mv:
                inf = pr.info(Q)
                own = [o for o in range(n) if not inf[3][o] and pr.owner_val(Q, o, inf)[0] >= pr.omega + 2]
                roles[tuple(sorted(('x' if o == U[0] else 'helper %d' % o if o in Y else 'unmoved %d' % o) +
                                   (' (a leaf of Q)' if o in leaves else '') for o in own)) +
                      (('helper %d' % Y[0],) if Y else ('no helper',))] += 1
            print('  A: key', [None if b is None else list(bits(b)) for b in key], 'def*', ds, 'Z′-max', show(P),
                  'leaves', leaves, 'repairing moves', len(mv), 'with x a best owner', xo)
            for r, c in sorted(roles.items()): print('     best owners', list(r[:-1]), '|', r[-1], ':', c, 'moves')
    import rt4_n5_indep as RI
    omega, out, ns, dstar = XB.zmove_indep(sets, vals, m, want_ns=True)
    D, info, classify = ns['D'], ns['info'], ns['classify']
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]

    def val(i, X): return sum(v[i].get(g, 0) for g in X)

    def xval(X, o):
        """max |Z| + u_o(Z) over the safe bundles of o in X (the inner loop of rt4_n5_indep's deficit, for one o)"""
        N, NA, J, fz = info(X)
        best = -1
        for r in range(len(J) + 1):
            for C in itertools.combinations(sorted(J), r):
                Z = X[o] | (J - frozenset(C))
                if any(Z and val(w, Z) - min(v[w].get(h, 0) for h in Z) > val(w, X[w]) for w in range(n) if w != o):
                    continue
                No = frozenset(g for g in sets[o] if g not in Z and v[o][g] > val(o, Z))
                other = frozenset().union(*[N[i] for i in range(n) if i != o]) | No
                u = sum(1 for i in range(n) if fz[i] and not (X[i] & other))
                best = max(best, len(Z) + u)
        return best
    for k, (ds, pot, per, t4) in out.items():
        for PQ in per:
            mv = [X for X in D if D[X] <= 0 and 'T3+' in classify(PQ, X)[0]]
            xo = sum(1 for X in mv if xval(X, classify(PQ, X)[1][1][0]) >= omega + 2)
            owners = collections.Counter()
            for X in mv:
                fz = info(X)[3]
                owners[tuple(o for o in range(n) if not fz[o] and xval(X, o) >= omega + 2)] += 1
            print('  B: key', [None if b is None else sorted(b) for b in k], 'def*', ds, 'Z′-max',
                  [sorted(b) for b in PQ], 'repairing moves', len(mv), 'with x a best owner', xo,
                  ' best owners (agents) per move:', dict(owners))


if __name__ == '__main__':
    print('== attempts/k4-zmh-s1c-plus.md: S1c+ (big-top x, >= 2 terminals at a Z′-maximum => def(P_Q) <= 0) ==')
    s1c_plus({"sets": [[0, 2, 5, 7], [1, 4, 6, 7], [3, 5, 6, 7]], "vals": [[6, 2, 3, 10], [4, 2, 3, 8], [3, 2, 4, 8]],
              "m": 8}, 0, 7)
    print()
    print('== attempts/k4-zmh-pool-optimal-forest.md: ZMOVE at every pool-optimal configuration with acyclic free '
          'threats ==')
    po_forest({"sets": [[0, 2, 4, 8], [1, 8, 10, 11], [3, 9, 10, 11], [4, 5, 6, 7], [5, 6, 7, 9]],
               "vals": [[4, 3, 8, 2], [8, 3, 6, 10], [2, 8, 3, 4], [8, 2, 3, 4], [3, 2, 4, 8]], "m": 12},
              [4, None, None, None, 9], [[4], [1, 8], [10, 11], [6, 7], [9]])
    print()
    print('== attempts/k4-zmh-x-owner.md: ZX (a repair after which the unfrozen agent x is a best owner) ==')
    x_owner({"sets": [[0, 2, 5, 7], [1, 4, 6, 7], [3, 5, 6, 7]], "vals": [[3, 4, 2, 8], [2, 3, 4, 8], [3, 5, 6, 7]],
             "m": 8})
