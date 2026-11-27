"""Reproduces attempts/k4-haxell-wsub-welfare.md from the raw EFX0 definition alone (no shared code).

W^sub with welfare (k4/haxell.md §6): from every partial EFX0 allocation with a nonempty pool, a composite of at most
two moves reaches a partial EFX0 allocation with a smaller pool, or with the same pool and larger welfare.  A move gives
a nonempty set of one holder's goods (an agent's, or pooled goods) to an agent; or swaps the holders of two goods (the
pool counting as a holder); or rotates the bundles along a cycle of two or more agents.

For the instance WS4 (n = 4, m = 7, every agent valuing at most four goods; a k = 4 core with strict, balanced values)
and its state S, this script enumerates every composite of at most two moves and checks:
  - none reaches a partial EFX0 allocation with a smaller pool, or the same pool and larger welfare (W^sub fails);
  - one reaches a partial EFX0 allocation with the same pool and a leximin-larger value vector (W^sub with leximin
    has a step here);
  - with single-good moves only (|set| = 1), a composite of three moves reaches an improving allocation (W_3 has a
    step here).

    python3 attempts/k4_haxell_wsub.py"""
import itertools

# WS4: VAL[i] = {good: value} (goods 0..6); S[g] = holder of good g (-1 = pooled)
VAL = [{4: 9, 5: 47, 6: 39}, {1: 8, 2: 3, 4: 2, 5: 4}, {0: 7, 1: 4, 3: 1, 5: 9}, {0: 38, 4: 7, 6: 32}]
M = 7
S = (3, 2, 1, 1, 1, 0, -1)


def run(VAL, m, S):
    n = len(VAL)
    v = lambda i, B: sum(VAL[i].get(g, 0) for g in B)

    def bundles(o):
        return [[g for g in range(m) if o[g] == j] for j in range(n)]

    def efx0(o):
        X = bundles(o)
        return all(v(i, [g for g in X[j] if g != h]) <= v(i, X[i])
                   for i in range(n) for j in range(n) if j != i for h in X[j])

    def welfare(o):
        return sum(v(i, B) for i, B in enumerate(bundles(o)))

    def leximin(o):
        return sorted(v(i, B) for i, B in enumerate(bundles(o)))

    def moves(o, sets=True):
        for h in list(range(n)) + [-1]:
            G = [g for g in range(m) if o[g] == h]
            for r in range(1, (len(G) if sets else 1) + 1):
                for T in itertools.combinations(G, r):
                    for b in range(n):
                        if b != h:
                            t = list(o)
                            for g in T:
                                t[g] = b
                            yield tuple(t)
        for g, h in itertools.combinations(range(m), 2):
            if o[g] != o[h]:
                t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] == min(cyc):
                    to = {cyc[s]: cyc[(s + 1) % L] for s in range(L)}
                    yield tuple(to.get(a, a) if a >= 0 else a for a in o)

    def reach(o, r, sets):
        seen = {o}; frontier = {o}
        for _ in range(r):
            frontier = {t for x in frontier for t in moves(x, sets)} - seen
            seen |= frontier
        return seen

    assert efx0(S) and -1 in S
    p, w, lx = S.count(-1), welfare(S), leximin(S)
    two = reach(S, 2, True)
    wel = [t for t in two if efx0(t) and (t.count(-1) < p or (t.count(-1) == p and welfare(t) > w))]
    lex = [t for t in two if efx0(t) and (t.count(-1) < p or (t.count(-1) == p and leximin(t) > lx))]
    three = [t for t in reach(S, 3, False) if efx0(t) and (t.count(-1) < p or (t.count(-1) == p and welfare(t) > w))]
    return bundles, welfare, leximin, len(two), wel, lex, three


if __name__ == '__main__':
    bundles, welfare, leximin, n2, wel, lex, three = run(VAL, M, S)
    show = lambda o: '%s pool %s welfare %d leximin %s' % (bundles(o), [g for g in range(M) if o[g] < 0], welfare(o),
                                                           leximin(o))
    print('WS4 state', show(S))
    print('allocations within two moves:', n2)
    print('W^sub (welfare) steps:', len(wel))
    print('W^sub (leximin) steps:', len(lex), *(['e.g. ' + show(lex[0])] if lex else []))
    print('W_3 (welfare, three single-good moves) steps:', len(three), *(['e.g. ' + show(three[0])] if three else []))
    assert not wel and lex and three
    print('reproduced: W^sub with welfare has no step at this state; W^sub with leximin and W_3 have one')
