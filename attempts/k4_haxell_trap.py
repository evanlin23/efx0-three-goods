"""Reproduces attempts/k4-haxell-single-swap-collapse.md from the raw EFX0 definition alone (no shared code).

1. The n = 2, m = 5 trap: X = ({0,2}, {1,3}), good 4 unallocated, is a partial EFX0 allocation; every single local
   move (move one good, swap two goods, trade two bundles; the pool never growing) leads outside the partial EFX0
   allocations or to the symmetric trap ({0,3}, {1,2}); two simultaneous transfers complete it.
3. A trap at k = 3 (n = 4, m = 7): ({0,3}, {1,2}, {5}, {4}) with good 6 unallocated; escaped by two moves at once.
2. The C127 dead end of the literal tree: from the serial-dictatorship picks of the order (0, 1, 3, 2), two
   victim-free transfers (goods 0 and 1 to agent 2) reach a partial EFX0 allocation with good 3 unallocated in which
   no single-good move (of any good, picks included) keeps EFX0; a composite of two transfers completes it.  (The
   tree's chains and re-bases were checked by k4/haxell/ht_bfs.py; swaps and bundle trades do escape here, so this
   one is a dead end of the catalogue, not a trap of G*.)

    python3 attempts/k4_haxell_trap.py"""
import itertools


def happy(R, own, n):
    X = [[g for g, a in enumerate(own) if a == j] for j in range(n)]
    for i in range(n):
        mine = sum(R[i].get(g, 0) for g in X[i])
        for j in range(n):
            if j != i and X[j]:
                for h in X[j]:
                    if sum(R[i].get(g, 0) for g in X[j] if g != h) > mine:
                        return False
    return True


def moves(own, n):
    m = len(own)
    for g in range(m):
        for b in range(n):
            if b != own[g]:
                o = list(own); o[g] = b; yield tuple(o)
    for g, h in itertools.combinations(range(m), 2):
        if own[g] != own[h]:
            o = list(own); o[g], o[h] = own[h], own[g]; yield tuple(o)
    for a, b in itertools.combinations(range(n), 2):
        yield tuple(b if x == a else a if x == b else x for x in own)


def closure(R, s, n):
    """partial EFX0 states reachable from s by single local moves, the pool never growing"""
    seen = {s}; stack = [s]
    while stack:
        t = stack.pop()
        for u in moves(t, n):
            if u not in seen and u.count(-1) <= t.count(-1) and happy(R, u, n):
                seen.add(u); stack.append(u)
    return seen


def show(own, n):
    return [[g for g, a in enumerate(own) if a == j] for j in range(n)], [g for g, a in enumerate(own) if a < 0]


def check(name, sets, vals, s):
    n = len(sets); R = [dict(zip(a, b)) for a, b in zip(sets, vals)]
    assert happy(R, s, n), 'not partial EFX0'
    cl = closure(R, s, n)
    print(name, 'state', show(s, n), 'partial EFX0: yes')
    print('  states reachable by single EFX0-preserving local moves:', len(cl),
          '; complete among them:', sum(1 for t in cl if -1 not in t))
    assert all(-1 in t for t in cl)
    esc = None
    for t1 in moves(s, n):
        for t2 in moves(t1, n):
            if t2.count(-1) <= s.count(-1) and happy(R, t2, n) and t2 not in cl:
                if any(-1 not in u for u in closure(R, t2, n)):
                    esc = t2; break
        if esc:
            break
    assert esc, 'no radius-2 escape'
    print('  two local moves at once reach', show(esc, n), ', from which single moves complete')


if __name__ == '__main__':
    # 1. n = 2, m = 5 (the screen instance c4x-n2m5-base-needs)
    check('n2m5', [[0, 2, 3, 4], [1, 2, 3, 4]], [[2, 3, 4, 8], [2, 3, 4, 8]], (0, 1, 0, 1, -1))
    # 2. C127 (screen set): SD picks of (0, 1, 3, 2) are 2, 4, 6, 5; then goods 0, 1 to agent 2
    sets = [[0, 2, 3, 5], [1, 4, 6], [2, 3, 5, 6], [4, 5, 6]]
    vals = [[2, 8, 5, 4], [2, 4, 3], [4, 2, 3, 8], [4, 2, 3]]
    R = [dict(zip(a, b)) for a, b in zip(sets, vals)]
    picks = (-1, -1, 0, -1, 1, 2, 3)
    step1 = (2, -1, 0, -1, 1, 2, 3)
    step2 = (2, 2, 0, -1, 1, 2, 3)
    for st in (picks, step1, step2):
        assert happy(R, st, 4)
    print('C127: picks', show(picks, 4), '-> good 0 to agent 2 -> good 1 to agent 2: all partial EFX0')
    single = [t for t in moves(step2, 4) if sum(1 for a, b in zip(t, step2) if a != b) == 1
              and t.count(-1) <= 1 and happy(R, t, 4)]
    print('C127 state', show(step2, 4), ': single-good moves keeping EFX0:', len(single))
    assert not single
    two = [t for t in moves(step2, 4) for t in moves(t, 4) if -1 not in t and happy(R, t, 4)
           and sum(1 for a, b in zip(t, step2) if a != b) == 2]
    print('  complete EFX0 allocations reached by two single-good moves:', sorted(set(show(t, 4)[0].__repr__() for t in two)))
    assert two
    # 2b. the smallest dead end of the tree found from a serial-dictatorship start: D3 (n = 3, m = 6), order (0, 2, 1),
    # picks 1, 3, 2; goods 0 and 4 to agent 1 (both victim-free) reach ({1}, {0,3,4}, {2}) with good 5 pooled
    setsD = [[0, 1, 2, 4], [1, 2, 3, 5], [2, 3, 4, 5]]
    valsD = [[4, 8, 3, 2], [8, 4, 3, 2], [10, 7, 2, 4]]
    RD = [dict(zip(a, b)) for a, b in zip(setsD, valsD)]
    pD, d1, d2 = (-1, 0, 2, 1, -1, -1), (1, 0, 2, 1, -1, -1), (1, 0, 2, 1, 1, -1)
    assert all(happy(RD, x, 3) for x in (pD, d1, d2))
    singleD = [t for t in moves(d2, 3) if sum(1 for a, b in zip(t, d2) if a != b) == 1 and t.count(-1) <= 1
               and happy(RD, t, 3)]
    print('D3: picks', show(pD, 3), '-> good 0 to agent 1 -> good 4 to agent 1: all partial EFX0;',
          'single-good moves keeping EFX0 from', show(d2, 3), ':', len(singleD))
    assert not singleD
    # 3. a trap at k = 3 (g834 of gen:1000:983:4:7:3): n = 4, m = 7, every agent values three goods
    sets3 = [[0, 5, 6], [2, 5, 6], [0, 4, 5], [1, 3, 4]]
    vals3 = [[22, 9, 24], [9, 40, 29], [6, 40, 28], [11, 20, 21]]
    check('k3-g834', sets3, vals3, (0, 1, 1, 0, 3, 2, -1))
    print('all reproduced')
