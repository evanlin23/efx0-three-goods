"""Reproduces attempts/k4-haxell-n2-pure-augmentation.md from the raw EFX0 definition alone (no shared code).

Claim A2 (refuted): with two agents and strict values, every partial EFX0 allocation with a nonempty pool has a composite
of at most two moves that reaches a partial EFX0 allocation with a smaller pool.  The moves (k4/haxell.md §6) give a
nonempty set of one holder's goods (an agent's, or pooled goods) to an agent, swap the holders of two goods (the pool
counting as a holder), or trade the two bundles.

Instance N2A: goods 0..4, agent A values (3, 2, 4, 8, 0), agent B values (0, 4, 2, 8, 3); strict values (no two
distinct sets of an agent's valued goods have equal value), every good valued by someone, each agent values four goods.
State: A holds {2, 4}, B holds {0, 1}, good 3 pooled.  The script checks:
  - the state is partial EFX0, and no composite of at most two moves gives a partial EFX0 allocation with a smaller pool;
  - swapping goods 4 and 0 (each worthless to its holder, valued by the other) gives a partial EFX0 allocation in which
    both agents are strictly better off, so W^sub and L^sub have a step there.

    python3 attempts/k4_haxell_n2aug.py"""
import itertools

VA = (3, 2, 4, 8, 0)
VB = (0, 4, 2, 8, 3)
S = (1, 1, 0, -1, 0)          # S[g]: 0 = A, 1 = B, -1 = pooled
M = 5


def value(v, B):
    return sum(v[g] for g in B)


def efx0(o):
    X = [[g for g in range(M) if o[g] == j] for j in (0, 1)]
    V = (VA, VB)
    for i in (0, 1):
        j = 1 - i
        for h in X[j]:
            if value(V[i], [g for g in X[j] if g != h]) > value(V[i], X[i]):
                return False
    return True


def moves(o):
    for h in (0, 1, -1):
        G = [g for g in range(M) if o[g] == h]
        for r in range(1, len(G) + 1):
            for T in itertools.combinations(G, r):
                for b in (0, 1):
                    if b != h:
                        t = list(o)
                        for g in T:
                            t[g] = b
                        yield tuple(t)
    for g, h in itertools.combinations(range(M), 2):
        if o[g] != o[h]:
            t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
    yield tuple(1 - x if x >= 0 else x for x in o)


if __name__ == '__main__':
    assert efx0(S)
    reach = {S} | set(moves(S))
    reach |= {t for x in list(reach) for t in moves(x)}
    shrink = [t for t in reach if t.count(-1) < S.count(-1) and efx0(t)]
    print('allocations within two moves:', len(reach), '| partial EFX0 with a smaller pool:', len(shrink))
    T = list(S); T[4], T[0] = S[0], S[4]; T = tuple(T)
    gain = (value(VA, [g for g in range(M) if T[g] == 0]) - value(VA, [g for g in range(M) if S[g] == 0]),
            value(VB, [g for g in range(M) if T[g] == 1]) - value(VB, [g for g in range(M) if S[g] == 1]))
    print('swap 4 <-> 0: partial EFX0', efx0(T), '| gains of A and B', gain)
    assert not shrink and efx0(T) and min(gain) > 0
    print('reproduced: no pool-shrinking composite of two moves; a swap raises both agents')
