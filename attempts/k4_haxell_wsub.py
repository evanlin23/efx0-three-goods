"""Reproduces attempts/k4-haxell-wsub-welfare.md and attempts/k4-haxell-lsub-leximin.md from the raw EFX0 definition
alone (no shared code).

The two-move set-move lemma (k4/haxell.md §6): from every partial EFX0 allocation with a nonempty pool, a composite of
at most two moves reaches a partial EFX0 allocation with a smaller pool, or with the same pool and a larger measure
(W^sub: welfare; L^sub: leximin, the increasingly sorted vector of the agents' values, compared lexicographically).
A move gives a nonempty set of one holder's goods (an agent's, or pooled goods) to an agent; or swaps the holders of
two goods (the pool counting as a holder); or rotates the bundles along a cycle of two or more agents.

Two instances, both n = 4, m = 7, k = 4 cores with strict, balanced values, each with a state S:
  WS4: no welfare step within two moves (W^sub fails); leximin has one; three single-good moves give a welfare step.
  LS4: no leximin step within two moves (L^sub fails); welfare has one; three single-good moves give a leximin step.
At both, composites of three set moves give a step for welfare and for leximin.

    python3 attempts/k4_haxell_wsub.py"""
import itertools

# VAL[i] = {good: value} (goods 0..6); S[g] = holder of good g (-1 = pooled)
INST = {
    'WS4': ([{4: 9, 5: 47, 6: 39}, {1: 8, 2: 3, 4: 2, 5: 4}, {0: 7, 1: 4, 3: 1, 5: 9}, {0: 38, 4: 7, 6: 32}], 7,
            (3, 2, 1, 1, 1, 0, -1)),
    'LS4': ([{3: 30, 4: 20, 5: 55, 6: 57}, {1: 31, 3: 12, 4: 5, 5: 39}, {0: 44, 1: 32, 3: 29}, {0: 60, 1: 31, 2: 7, 6: 43}],
            7, (2, -1, 0, 0, 0, 1, 3)),
}


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
    p = S.count(-1)
    def steps(cands, f):
        return [t for t in cands if efx0(t) and (t.count(-1) < p or (t.count(-1) == p and f(t) > f(S)))]
    two, three1, three = reach(S, 2, True), reach(S, 3, False), reach(S, 3, True)
    res = {(r, f.__name__): len(steps(c, f)) for r, c in (('two set moves', two), ('three single moves', three1),
                                                          ('three set moves', three)) for f in (welfare, leximin)}
    return bundles, welfare, leximin, len(two), res, steps(two, leximin) + steps(two, welfare)


if __name__ == '__main__':
    for name, (VAL, M, S) in INST.items():
        bundles, welfare, leximin, n2, res, ex = run(VAL, M, S)
        show = lambda o: '%s pool %s welfare %d leximin %s' % (bundles(o), [g for g in range(M) if o[g] < 0],
                                                               welfare(o), leximin(o))
        print(name, 'state', show(S), '| allocations within two moves:', n2)
        for (r, f), c in res.items():
            print('   steps within %s, %s: %d' % (r, f, c))
        bad = 'welfare' if name == 'WS4' else 'leximin'; good = 'leximin' if name == 'WS4' else 'welfare'
        assert res[('two set moves', bad)] == 0 and res[('two set moves', good)] > 0
        assert all(c > 0 for (r, f), c in res.items() if r.startswith('three'))
        print('   e.g. a %s step within two moves: %s' % (good, show(ex[0])))
    print('reproduced: W^sub fails at WS4, L^sub at LS4; three moves (single or set) give a step at both, either measure')
