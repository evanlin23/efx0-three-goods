"""Reproduces attempts/k4-haxell-bounded-augmentation.md from the raw EFX0 definition alone (no shared code).

g372 (n = 3, m = 6, k = 4): the partial EFX0 allocation ({1,4,5}, {0}, {3}) with good 2 unallocated
  (a) cannot reach a partial EFX0 allocation with an empty pool by any composite of at most 3 local moves
      (move one good to an agent, swap the holders of two goods, the pool counting as a holder, trade two bundles;
      intermediate states arbitrary; the pool never growing), but can by a composite of 4;
  (b) is not a trap: a sequence of partial EFX0 allocations, each one local move (radius 1) or two (radius 2) from the
      last, leads to a complete EFX0 allocation; the script prints one.

    python3 attempts/k4_haxell_aug.py"""
import itertools
from collections import deque

SETS = [[1, 2, 3, 5], [0, 2, 3, 4], [0, 2, 3, 5]]
VALS = [[4, 35, 16, 10], [21, 18, 14, 9], [39, 34, 18, 9]]
N, M = 3, 6
R = [dict(zip(a, b)) for a, b in zip(SETS, VALS)]
START = (1, 0, -1, 2, 0, 0)          # good g -> holder; -1 = pool


def efx0(own):
    X = [[g for g in range(M) if own[g] == j] for j in range(N)]
    for i in range(N):
        mine = sum(R[i].get(g, 0) for g in X[i])
        for j in range(N):
            if j != i:
                for h in X[j]:
                    if sum(R[i].get(g, 0) for g in X[j] if g != h) > mine:
                        return False
    return True


def moves(own):
    for g in range(M):
        for b in range(N):
            if b != own[g]:
                o = list(own); o[g] = b; yield tuple(o)
    for g, h in itertools.combinations(range(M), 2):
        if own[g] != own[h]:
            o = list(own); o[g], o[h] = own[h], own[g]; yield tuple(o)
    for a, b in itertools.combinations(range(N), 2):
        yield tuple(b if x == a else a if x == b else x for x in own)


def show(own):
    return [[g for g in range(M) if own[g] == j] for j in range(N)], [g for g in range(M) if own[g] < 0]


if __name__ == '__main__':
    assert efx0(START)
    print('state', show(START), 'is partial EFX0')
    p = START.count(-1); frontier = {START}; seen = {START}; found = None
    for d in range(1, 5):
        nxt = set()
        for o in frontier:
            for t in moves(o):
                if t in seen or t.count(-1) > p:
                    continue
                seen.add(t); nxt.add(t)
                if t.count(-1) < p and efx0(t) and found is None:
                    found = (d, t)
        frontier = nxt
        if found:
            break
        print('  no augmentation by a composite of', d, 'local move(s)')
    print('  first augmentation: a composite of', found[0], 'moves, reaching', show(found[1]))
    assert found[0] == 4
    # (b) a path through partial EFX0 allocations with radius-2 steps
    def step2(o):
        out = set()
        for t1 in moves(o):
            if t1.count(-1) <= o.count(-1) and efx0(t1):
                out.add(t1)
            for t2 in moves(t1):
                if t2.count(-1) <= o.count(-1) and efx0(t2):
                    out.add(t2)
        return out
    par = {START: None}; q = deque([START]); goal = None
    while q:
        o = q.popleft()
        if -1 not in o:
            goal = o; break
        for t in step2(o):
            if t not in par:
                par[t] = o; q.append(t)
    assert goal is not None
    path = []
    while goal is not None:
        path.append(goal); goal = par[goal]
    print('  a path of radius-2 steps through partial EFX0 allocations:')
    for o in reversed(path):
        print('    ', show(o))
    print('reproduced')
