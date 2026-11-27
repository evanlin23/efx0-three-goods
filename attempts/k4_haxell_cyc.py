"""Reproduces attempts/k4-haxell-fixed-radius-measures.md from the raw EFX0 definition alone (no shared code).

CYC_5 (k = 3): agent i values g_i at 10, g_{i+1} at 11 (indices mod 5) and the pooled good p = 5 at 1.  In the state
where every agent holds its own good and p is pooled:
  (a) no composite of at most three local moves (move one good to an agent, swap two holders with the pool as a
      holder, trade two bundles) reaches a partial EFX0 allocation with an empty pool, or with p still pooled and
      strictly larger welfare, or strictly larger leximin vector;
  (b) one rotation of the bundles along the 5-cycle does (welfare 50 -> 55).

    python3 attempts/k4_haxell_cyc.py"""
import itertools
N, M = 5, 6
R = [{i: 10, (i + 1) % N: 11, N: 1} for i in range(N)]


def efx0(o):
    X = [[g for g in range(M) if o[g] == j] for j in range(N)]
    for i in range(N):
        mine = sum(R[i].get(g, 0) for g in X[i])
        for j in range(N):
            if j != i:
                for h in X[j]:
                    if sum(R[i].get(g, 0) for g in X[j] if g != h) > mine:
                        return False
    return True


def values(o):
    return [sum(R[i].get(g, 0) for g in range(M) if o[g] == i) for i in range(N)]


def moves(o):
    for g in range(M):
        for b in range(N):
            if b != o[g]:
                t = list(o); t[g] = b; yield tuple(t)
    for g, h in itertools.combinations(range(M), 2):
        if o[g] != o[h]:
            t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
    for a, b in itertools.combinations(range(N), 2):
        yield tuple(b if x == a else a if x == b else x for x in o)


if __name__ == '__main__':
    s = tuple(range(N)) + (-1,)
    assert efx0(s)
    w0, lex0 = sum(values(s)), sorted(values(s))
    print('state', [[g for g in range(M) if s[g] == j] for j in range(N)], 'pool [5]: welfare', w0)
    frontier = {s}; seen = {s}; better = []
    for d in range(1, 4):
        nxt = set()
        for o in frontier:
            for t in moves(o):
                if t in seen:
                    continue
                seen.add(t); nxt.add(t)
                if efx0(t) and (t.count(-1) < 1 or sum(values(t)) > w0 or sorted(values(t)) > lex0):
                    better.append((d, t))
        frontier = nxt
        print('  composites of at most %d local moves: %d states, improving ones: %d' % (d, len(seen), len(better)))
    assert not better
    rot = tuple((x - 1) % N if x >= 0 else x for x in s)   # agent i takes g_{i+1}: good g goes to agent g - 1
    assert efx0(rot)
    print('  rotation along the cycle: bundles', [[g for g in range(M) if rot[g] == j] for j in range(N)],
          'welfare', sum(values(rot)), 'EFX0', efx0(rot))
    print('reproduced')
