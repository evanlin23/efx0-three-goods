#!/usr/bin/env python3
"""c4min_f1_proof: brute-force check of every step of the proof of Theorem F1 (k4/c4min_f1.md §2), on the independent
Python implementation (k4/c4min_cfg.py). Potential Psi = (r, Lambda); f = 1 profiles with omega >= 1 only.

For every configuration without an owner that is valid with C = {} (a superset of the non-completable ones):
  1. if it is not pool-optimal, the pool move (one free agent takes its best pair inside its pair and the pool) raises
     Psi (Lemma 2);
  2. otherwise: every agent needing g has top g and is free (Lemma 1); x is not robust; every robust free agent is
     threatened by nobody, every other free agent by at most one owner (Lemma 3), with the kinds of Lemma 3;
  3. if the threat digraph has a cycle through free agents only, the rotation of Lemma 5 raises Psi;
  4. otherwise every walk from a terminal tau along threat edges reaches x, and the path move of Lemma 7 along it
     raises Psi when x is not big-top. For big-top x the outcome is recorded by case (Lemma 8).
Every choice of cycle, terminal and path is checked, not only one.
usage: python3 k4/c4min_f1_proof.py FILE [--rand=N] [--seed=S] [--ex=K]"""
import collections, itertools, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import v, needs, threatened, fmt_profile
from c4min_cfg import Config
from c4min_f1 import f1_profiles, frozen_of, xtype, r_of, lam_of, t_of
from c4min_cfg import configs


def psi(c):
    return (r_of(c), lam_of(c))


def kind(c, y):
    """Kind of a free agent (Lemma 3): 'rob' (robust), 'T3', 'T4', 'Tg' (4-good valuer of g holding its best good of
    U_y and junk), 'D', 'R'; plus the fourth good s for 'R'."""
    pr = c.pr; val = pr.vals[y]; g = next(iter(c.NA))
    if c.robust(y): return 'rob', None
    H = c.Q[y] & pr.R[y]
    order = sorted(val, key=lambda z: -val[z])
    if g in val:
        assert len(val) == 4, 'a 3-good valuer of g is always robust'
        u = [z for z in order if z != g]
        assert H == {u[0]} and val[u[0]] < val[u[1]] + val[u[2]], 'Lemma 3 (g-valuer)'
        return 'Tg', None
    a, b, cc = order[0], order[1], order[2]
    if len(val) == 3:
        assert H == {a}, 'Lemma 3 (3-good)'
        return 'T3', None
    d = order[3]
    if H == {a}: return 'T4', None
    if H == {a, d}: return 'D', None
    assert a not in H and len(H) == 2, 'Lemma 3 (4-good)'
    s = next(z for z in order if z != a and z not in H)
    return 'R', s


def threat_digraph(c):
    T = collections.defaultdict(list)
    for o in c.free:
        for z in range(c.pr.n):
            if z != o and threatened(c.pr.vals[z], c.Q[o] | c.L, c.H(z)): T[o].append(z)
    return T


def best_pair(pr, i, S, U):
    """i's best pair inside S ∩ U (by value)."""
    cand = [frozenset(p) for p in itertools.combinations(sorted(S & U), 2)]
    return max(cand, key=lambda p: v(pr.vals[i], p)) if cand else None


def rotation(c, cyc, kinds):
    """Lemma 5: c_{j+1} receives Q_{c_j}; at most one (R) receiver with s in L takes {a, s} instead (the other good of
    Q_{c_j} goes to the pool), used only when no receiver becomes robust by the plain rotation."""
    pr = c.pr; k = len(cyc)
    Q = dict(c.Q); L = set(c.L)
    pred = {cyc[(j + 1) % k]: cyc[j] for j in range(k)}
    plain_robust = any(kinds[y][0] in ('T3', 'Tg', 'D') or (kinds[y][0] == 'R' and kinds[y][1] in c.Q[pred[y]]) for y in cyc)
    mod = None
    if not plain_robust:
        mod = next((y for y in cyc if kinds[y][0] == 'R' and kinds[y][1] in c.L), None)
    for y in cyc:
        S = c.Q[pred[y]]
        if y == mod:
            a = max(pr.vals[y], key=lambda z: pr.vals[y][z]); s = kinds[y][1]
            assert a in S
            L |= S - {a}; L.discard(s); S = frozenset({a, s})
        Q[y] = S
    return Config(pr, c.NA, c.phi, Q, frozenset(L))


def path_move(c, path, x, kinds, xty):
    """Lemma 7: path = [tau = q_0, q_1, ..., q_k], q_{i+1} threatened by q_i, x threatened by q_k. q_{i+1} receives
    Q_{q_i}; x receives its best pair P_x inside (Q_{q_k} ∪ L) ∩ U_x (the rest of Q_{q_k} goes to the pool); tau
    receives g and becomes frozen. At most one (R) receiver with s in L \\ P_x takes {a, s} instead, used only when no
    receiver becomes robust by the plain move. Returns (config, case)."""
    pr = c.pr; g = next(iter(c.NA)); tau = path[0]
    Q = dict(c.Q); L = set(c.L)
    Px = best_pair(pr, x, c.Q[path[-1]] | c.L, c.U[x])
    recv = path[1:]
    pred = {path[i + 1]: path[i] for i in range(len(path) - 1)}
    plain_robust = any(kinds[y][0] in ('T3', 'Tg', 'D') or (kinds[y][0] == 'R' and kinds[y][1] in c.Q[pred[y]]) for y in recv)
    mod = None; case = []
    if not plain_robust:
        mod = next((y for y in recv if kinds[y][0] == 'R' and kinds[y][1] in c.L - Px), None)
        if mod is None and any(kinds[y][0] == 'R' and kinds[y][1] in c.L for y in recv): case.append('R-conflict')
    for y in recv:
        S = c.Q[pred[y]]
        if y == mod:
            a = max(pr.vals[y], key=lambda z: pr.vals[y][z]); s = kinds[y][1]
            L |= S - {a}; L.discard(s); S = frozenset({a, s})
        Q[y] = S
    L |= c.Q[path[-1]] - Px; L -= Px
    del Q[tau]; Q[x] = Px
    phi = list(c.phi); phi[x] = None; phi[tau] = frozenset({g})
    c2 = Config(pr, c.NA, tuple(phi), Q, frozenset(L))
    # validity
    used = frozenset().union(*Q.values())
    assert len(used) == 2 * len(Q) and not (used & c.NA) and not (used & c2.L) and len(used) + len(c2.L) + 1 == pr.m
    for i in range(pr.n):
        assert not (needs(pr.vals[i], c2.H(i)) - c.NA), 'path move: needs outside N'
    case.append('tau robust' if kinds[tau][0] == 'rob' else 'tau not robust')
    case.append(f'k={len(recv)}' if len(recv) <= 1 else 'k>=2')
    return c2, ' '.join(case)


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict((a[2:].split('=') + [''])[:2] for a in sys.argv[1:] if a.startswith('--'))
    rand = int(opt.get('rand', 0) or 0); seed = int(opt.get('seed', 1) or 1); nex = int(opt.get('ex', 3) or 3)
    for fn in files:
        C = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
        def note(key, c, x):
            C[key] += 1
            if len(ex[key]) < nex:
                ex[key].append(f'{fmt_profile(c.pr)} frozen {x}:{sorted(c.phi[x])} pairs {dict((i, sorted(q)) for i, q in c.Q.items())} pool {sorted(c.L)}')
        for ci, pr, ks in f1_profiles(fn, rand, seed):
            n = pr.n; C['profiles'] += 1
            for NA, phi in ks:
                for c in configs(pr, NA, phi):
                    x = frozen_of(c)[0]; g = next(iter(NA)); xty = xtype(pr, x, g)
                    C['configurations'] += 1
                    # Lemma 1
                    assert max(pr.vals[x], key=lambda z: pr.vals[x][z]) == g and not c.robust(x)
                    term = [z for z in range(n) if z != x and g in needs(pr.vals[z], c.H(z))]
                    assert term and all(max(pr.vals[z], key=lambda w: pr.vals[z][w]) == g for z in term)
                    if any(c.owner_ok(o, unfreeze=False) for o in c.free): continue
                    C[f'x {xty}: configurations without owner valid with C = {{}}'] += 1
                    k0 = psi(c)
                    # Lemma 2
                    if not c.pool_optimal():
                        y, S = max(((y, frozenset(S)) for y in c.free for S in itertools.combinations(sorted(c.Q[y] | c.L), 2)),
                                   key=lambda t: v(pr.vals[t[0]], t[1]) - v(pr.vals[t[0]], c.Q[t[0]]))
                        Q = dict(c.Q); Q[y] = S
                        c2 = Config(pr, NA, phi, Q, (c.L | c.Q[y]) - S)
                        if psi(c2) > k0: C[f'x {xty}: 1 pool move raises Psi'] += 1
                        else: note(f'x {xty}: 1 POOL MOVE FAILS', c, x)
                        continue
                    # Lemma 3
                    kinds = {y: kind(c, y) for y in c.free}
                    T = threat_digraph(c)
                    indeg = collections.Counter(z for o in T for z in T[o])
                    for y in c.free:
                        if kinds[y][0] == 'rob': assert indeg[y] == 0, 'Lemma 3: robust agent threatened'
                        else: assert indeg[y] <= 1, 'Lemma 3: two owners'
                    for o in c.free: assert T[o], 'no valid owner: every owner threatens someone'
                    # Lemma 5: cycles through free agents
                    cycles = []
                    def dfs(s, u, path, seen):
                        for w in T[u]:
                            if w == x: continue
                            if w == s: cycles.append(list(path))
                            elif w > s and w not in seen:
                                seen.add(w); path.append(w); dfs(s, w, path, seen); path.pop(); seen.discard(w)
                    for s in c.free: dfs(s, s, [s], {s})
                    if cycles:
                        ok = all(psi(rotation(c, cyc, kinds)) > k0 for cyc in cycles)
                        if ok: C[f'x {xty}: 3 every rotation raises Psi'] += 1
                        else: note(f'x {xty}: 3 SOME ROTATION FAILS', c, x)
                        continue
                    # Lemma 7 / 8: every walk from every terminal along threat edges through free agents to x
                    paths = []
                    def walk(u, path):
                        for w in T[u]:
                            if w == x: paths.append(list(path))
                            elif w not in path: path.append(w); walk(w, path); path.pop()
                    for tau in term: walk(tau, [tau])
                    assert paths, 'Lemma 6: no path from a terminal to x'
                    res = collections.Counter()
                    for P in paths:
                        c2, case = path_move(c, P, x, kinds, xty)
                        k2 = psi(c2)
                        res[(case, 'up' if k2 > k0 else 'tie' if k2 == k0 else 'DOWN')] += 1
                        if 'R-conflict' in case:
                            Px = best_pair(pr, x, c.Q[P[-1]] | c.L, c.U[x]); bx = max(c.U[x], key=lambda z: pr.vals[x][z])
                            ss = {kinds[y][1] for y in P[1:] if kinds[y][0] == 'R' and kinds[y][1] in c.L}
                            C[f'x {xty}: 4r R-conflict path, s = b_x {bx in ss}, psi {"up" if k2 > k0 else "tie" if k2 == k0 else "DOWN"}'] += 1
                    kmin = min(len(P) for P in paths)
                    short = [P for P in paths if len(P) == kmin]
                    sres = [psi(path_move(c, P, x, kinds, xty)[0]) > k0 for P in short]
                    C[f'x {xty}: 4s shortest paths (k={kmin - 1 if kmin <= 2 else ">=2"}): {"all raise" if all(sres) else "some raise" if any(sres) else "NONE RAISES"}'] += 1
                    anyup = any(r == 'up' for (_, r) in res)
                    allup = all(r == 'up' for (_, r) in res)
                    C[f'x {xty}: 4 path moves: {"all raise" if allup else "some raise" if anyup else "NONE RAISES"}'] += 1
                    for (case, r), q in res.items():
                        if r != 'up': note(f'x {xty}: 4 path move {r} [{case}]', c, x)
                    if not anyup:
                        # Lemma 8 (big-top x, every path move ties): the tied move c' and who owns it
                        t0v = t_of(c); nterm = len(term)
                        for P in paths:
                            c2, case = path_move(c, P, x, kinds, xty)
                            if psi(c2) != k0: continue
                            tau = P[0]
                            xo = c2.owner_ok(x, unfreeze=False)
                            anyo = any(c2.owner_ok(o, unfreeze=False) for o in c2.free)
                            anyu = any(c2.owner_ok(o) for o in c2.free)
                            tauu = c.owner_ok(tau)
                            C[f'x {xty}: 8 tie: t={t0v} t\'={t_of(c2)} terminals={nterm} | x owns c\' {xo} | c\' owner (C={{}}) {anyo} | c\' completable {anyu} | tau owns c (unfreezing) {tauu}'] += 1
        print(f'FILE {fn} rand={rand} seed={seed} ({time.time() - t0:.0f} s)')
        for k in sorted(C): print(f'  {k}: {C[k]}')
        for k in sorted(ex):
            for e in ex[k]: print(f'  example ({k}): {e}')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
