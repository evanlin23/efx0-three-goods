"""Reproduces attempts/k4-haxell-conjecture-w.md from the raw EFX0 definition alone (no shared code).

For each instance below and its state S (a partial EFX0 allocation with one good pooled), search every composite of at
most r moves (move one good to an agent; swap the holders of two goods, the pool counting as a holder; trade the two
bundles, which is the only rotation when n = 2) for a partial EFX0 allocation with an empty pool, or with the same
pool and strictly larger welfare.  With SUB, giving a set of goods of one holder to the other agent is also one move.

  W4: k = 4, n = 2, m = 7: no step within 2 moves (Conjecture W fails); a step within 3 moves; a step within 2
      moves when set transfers count as one move.
  W5: k = 5, n = 2, m = 9: no step within 3 moves (the three-move form fails at k = 5); a step within 2 moves with
      set transfers.

    python3 attempts/k4_haxell_w.py"""
import itertools

INST = {
    'W4': ([{0: 40, 1: 10, 2: 11, 3: 12}, {0: 70, 4: 10, 5: 40, 6: 11}], 7, (-1, 0, 0, 0, 1, 1, 1)),
    'W5': ([{0: 50, 1: 10, 2: 11, 3: 12, 4: 13}, {0: 90, 5: 10, 6: 40, 7: 11, 8: 1}], 9, (-1, 0, 0, 0, 0, 1, 1, 1, 1)),
}


def run(R, m, S, r, sub):
    n = 2

    def efx0(o):
        X = [[g for g in range(m) if o[g] == j] for j in range(n)]
        for i in range(n):
            mine = sum(R[i].get(g, 0) for g in X[i])
            for j in range(n):
                if j != i:
                    for h in X[j]:
                        if sum(R[i].get(g, 0) for g in X[j] if g != h) > mine:
                            return False
        return True

    def welfare(o):
        return sum(R[o[g]].get(g, 0) for g in range(m) if o[g] >= 0)

    def moves(o):
        for g in range(m):
            for b in range(n):
                if b != o[g]:
                    t = list(o); t[g] = b; yield tuple(t)
        for g, h in itertools.combinations(range(m), 2):
            if o[g] != o[h]:
                t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
        yield tuple(1 - x if x >= 0 else x for x in o)
        if sub:
            for holder in (-1, 0, 1):
                G = [g for g in range(m) if o[g] == holder]
                for size in range(2, len(G) + 1):
                    for T in itertools.combinations(G, size):
                        for b in range(n):
                            if b != holder:
                                t = list(o)
                                for g in T:
                                    t[g] = b
                                yield tuple(t)

    assert efx0(S)
    p, w = S.count(-1), welfare(S)
    frontier = {S}; seen = {S}
    for d in range(1, r + 1):
        nxt = set()
        for o in frontier:
            for t in moves(o):
                if t in seen:
                    continue
                seen.add(t); nxt.add(t)
                if t.count(-1) <= p and (t.count(-1) < p or welfare(t) > w) and efx0(t):
                    return d, t
        frontier = nxt
    return None, None


if __name__ == '__main__':
    for name, (R, m, S) in INST.items():
        show = lambda o: ([[g for g in range(m) if o[g] == j] for j in range(2)], [g for g in range(m) if o[g] < 0])
        print(name, 'state', show(S))
        for r, sub in ((2, False), (3, False), (2, True)):
            d, t = run(R, m, S, r, sub)
            print('   within %d moves%s: %s' % (r, ' (set transfers count as one move)' if sub else '',
                                              'step after %d: %s' % (d, show(t)) if d else 'NO STEP'))
        if name == 'W4':
            assert run(R, m, S, 2, False)[0] is None and run(R, m, S, 3, False)[0] and run(R, m, S, 2, True)[0]
        else:
            assert run(R, m, S, 3, False)[0] is None and run(R, m, S, 2, True)[0]
    print('reproduced')
