"""Local check of Conjecture W at one given state, for instances too large for the census (k4/haxell.md §7).

W at a partial EFX0 allocation X with a nonempty pool asks for a composite of at most two moves (give one good to
another agent, a pooled one included; swap the holders of two goods, the pool counting as a holder; rotate the bundles
along a cycle of agents) giving a partial EFX0 allocation with a smaller pool, or with the same pool and larger
welfare.  This script searches, exactly:

  A. *augmenting* composites, which must contain a placement of a pooled good g:
     A1  the placement alone;
     A2  the placement and one more good move or swap, in either order;
     A3  the placement and one rotation, in either order.  Either way the final bundles are the old bundles with g
         added to one of them (B_j = X_j + g), permuted along one cycle.  For a fixed set of bundles, agent i's EFX0
         condition depends only on the bundle b it receives: v_i(b) >= max over the other bundles b' of tau_i(b'),
         tau_i(b') = v_i(b') - min_{h in b'} v_i(h) (0 for at most one good).  So the EFX0 assignments are the perfect
         matchings of a compatibility graph, and A3 asks for a directed cycle (i -> a: i can take B_a) through every
         agent that cannot keep its own bundle.  A depth-first search decides it exactly.
  B. *welfare-raising* composites keeping the pool (only when A finds nothing):
     B1/B2  one or two good moves or swaps;  B3  one rotation (the same cycle search on the unchanged bundles, with
     positive total gain).  Rotation plus a good move (B4) is not searched, so a "no" in B is not exhaustive.

    python3 k4/haxell/ht_wlocal.py chf"""
import sys, itertools, json, time


class Loc:
    def __init__(self, sets, vals, m):
        self.n = len(sets); self.m = m
        self.R = [dict(zip(s, v)) for s, v in zip(sets, vals)]

    def v(self, i, B):
        return sum(self.R[i].get(g, 0) for g in B)

    def tau(self, i, B):
        if len(B) < 2:
            return 0
        return self.v(i, B) - min(self.R[i].get(g, 0) for g in B)

    def bundles(self, own):
        X = [[] for _ in range(self.n)]
        for g, a in enumerate(own):
            if a >= 0:
                X[a].append(g)
        return X

    def efx0(self, own):
        X = self.bundles(own)
        for i in range(self.n):
            mine = self.v(i, X[i])
            for j in range(self.n):
                if j != i and self.tau(i, X[j]) > mine:
                    return False
        return True

    def welfare(self, own):
        return sum(self.R[a].get(g, 0) for g, a in enumerate(own) if a >= 0)

    def simple(self, own):
        n, m = self.n, self.m
        for g in range(m):
            for b in range(n):
                if b != own[g]:
                    t = list(own); t[g] = b; yield tuple(t), ('move', g, b)
        for g, h in itertools.combinations(range(m), 2):
            if own[g] != own[h]:
                t = list(own); t[g], t[h] = own[h], own[g]; yield tuple(t), ('swap', g, h)

    def cycle_cover(self, B, gain=False):
        """B: list of n bundles (agent j's bundle is B[j]).  A directed cycle i_1 -> ... -> i_L -> i_1 (i_t takes
        B[i_{t+1}]) through every agent that cannot keep B[i]; with gain, also strictly positive welfare change.
        Returns the cycle or None."""
        n = self.n
        T = [[self.tau(i, B[a]) for a in range(n)] for i in range(n)]
        V = [[self.v(i, B[a]) for a in range(n)] for i in range(n)]
        def ok(i, a):
            return V[i][a] >= max([T[i][b] for b in range(n) if b != a] or [0])
        C = [[ok(i, a) for a in range(n)] for i in range(n)]
        need = [i for i in range(n) if not C[i][i]]
        starts = need if need else list(range(n))
        best = [None]
        def dfs(path, onpath, g):
            u = path[-1]
            for a in range(n):
                if not C[u][a]:
                    continue
                if a == path[0] and len(path) >= 2:
                    if all(x in onpath for x in need) and (not gain or g + V[u][a] - V[u][u] > 0):
                        best[0] = list(path); return True
                    continue
                if a in onpath:
                    continue
                path.append(a); onpath.add(a)
                if dfs(path, onpath, g + V[u][a] - V[u][u]):
                    return True
                path.pop(); onpath.discard(a)
            return False
        for s in starts:
            if dfs([s], {s}, 0):
                return best[0]
            if need:
                break           # a cycle through every needed agent passes through need[0]
        return None

    def check(self, own):
        n, m = self.n, self.m
        P = [g for g in range(m) if own[g] < 0]
        X = self.bundles(own); w0 = self.welfare(own)
        for g in P:                                                      # A1
            for j in range(n):
                t = list(own); t[g] = j
                if self.efx0(t):
                    return 'A1', ('place', g, j)
        for t1, mv in self.simple(own):                                  # A2: move then place
            for g in P:
                if t1[g] >= 0:
                    continue
                for j in range(n):
                    t = list(t1); t[g] = j
                    if self.efx0(t):
                        return 'A2', (mv, ('place', g, j))
        for g in P:                                                      # A2: place then move
            for j in range(n):
                t0 = list(own); t0[g] = j; t0 = tuple(t0)
                for t, mv in self.simple(t0):
                    if t.count(-1) < len(P) and self.efx0(t):
                        return 'A2', (('place', g, j), mv)
        for g in P:                                                      # A3
            for j in range(n):
                B = [list(b) for b in X]; B[j] = B[j] + [g]
                cyc = self.cycle_cover(B)
                if cyc is not None:
                    return 'A3', ('place', g, 'into the bundle of', j, 'rotate', cyc)
        for t, mv in self.simple(own):                                   # B1
            if t.count(-1) <= len(P) and self.welfare(t) > w0 and self.efx0(t):
                return 'B1', mv
        for t1, mv1 in self.simple(own):                                 # B2
            for t, mv2 in self.simple(t1):
                if t.count(-1) <= len(P) and self.welfare(t) > w0 and self.efx0(t):
                    return 'B2', (mv1, mv2)
        cyc = self.cycle_cover([list(b) for b in X], gain=True)          # B3
        if cyc is not None:
            return 'B3', ('rotate', cyc)
        return None, None


if __name__ == '__main__':
    import ext_instances as X
    print('$ python3 k4/haxell/ht_wlocal.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m, own in X.chf():
        L = Loc(sets, vals, m); t0 = time.time()
        print(name, 'n', L.n, 'm', m, 'state', L.bundles(own), 'pool', [g for g in range(m) if own[g] < 0],
              'EFX0', L.efx0(own), 'welfare', L.welfare(own), flush=True)
        kind, how = L.check(own)
        print('   W step:', kind, how, '(%.1f s)' % (time.time() - t0), flush=True)
        if kind and kind.startswith('A'):
            # replay the step independently of the search and report the new state
            t = list(own)
            if kind == 'A1':
                t[how[1]] = how[2]
            elif kind == 'A2':
                for mv in how:
                    if mv[0] in ('place', 'move'):
                        t[mv[1]] = mv[2]
                    else:
                        t[mv[1]], t[mv[2]] = t[mv[2]], t[mv[1]]
            else:
                _, g, _, j, _, cyc = how
                t[g] = j
                to = {cyc[k]: cyc[(k + 1) % len(cyc)] for k in range(len(cyc))}   # i takes the bundle of to[i]
                inv = {b: a for a, b in to.items()}                                  # bundle of b goes to inv[b]
                t = [inv.get(a, a) if a >= 0 else a for a in t]
            print('   replayed: EFX0 %s, pool %s, welfare %d, bundles %s' % (
                L.efx0(t), [g for g in range(m) if t[g] < 0], L.welfare(t), L.bundles(t)), flush=True)


def apply_step(L, own, kind, how):
    t = list(own)
    if kind in ('A1', 'B1'):
        mvs = [how]
    elif kind in ('A2', 'B2'):
        mvs = list(how)
    else:
        mvs = []
    for mv in mvs:
        if mv[0] in ('place', 'move'):
            t[mv[1]] = mv[2]
        elif mv[0] == 'swap':
            t[mv[1]], t[mv[2]] = t[mv[2]], t[mv[1]]
    if kind == 'A3':
        _, g, _, j, _, cyc = how
        t[g] = j
        to = {cyc[k]: cyc[(k + 1) % len(cyc)] for k in range(len(cyc))}
        inv = {b: a for a, b in to.items()}
        t = [inv.get(a, a) if a >= 0 else a for a in t]
    if kind == 'B3':
        cyc = how[1]
        to = {cyc[k]: cyc[(k + 1) % len(cyc)] for k in range(len(cyc))}
        inv = {b: a for a, b in to.items()}
        t = [inv.get(a, a) if a >= 0 else a for a in t]
    return tuple(t)


def walk(L, own, maxsteps=500, log=print):
    """apply W steps until the allocation is complete; every visited state is checked locally"""
    steps = 0
    while -1 in own:
        kind, how = L.check(own)
        if kind is None:
            log('   STUCK (A exhaustive; B without rotation-plus-move) at', L.bundles(own), 'pool',
                [g for g in range(L.m) if own[g] < 0], 'welfare', L.welfare(own))
            return False, steps
        new = apply_step(L, own, kind, how)
        assert L.efx0(new), (kind, how)
        p0, p1 = own.count(-1), new.count(-1)
        assert p1 < p0 or (p1 == p0 and L.welfare(new) > L.welfare(own)), (kind, how)
        own = new; steps += 1
        if steps > maxsteps:
            return None, steps
    return True, steps
