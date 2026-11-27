"""Hand-built "ladder" designs for a three-move start (k4/ttc.md §14.5).  A complementary agent c holds T, wants the
pool bundle {Pa, Pb} (+ its private junk j), and Pa, Pb can each enter the pool only by a separate earlier move (the
release of a chain end), so c's own move would be the third.  For each design: core checks, the start of the given
order, and the least number of moves (de_free chains and additions, then a one-absorber completion; also free) by
breadth-first search up to depth 3.

    python3 k4/ttc/ladder.py"""
import sys, itertools, collections
import ttclib as T
import core_climb as CC


def name_goods(spec):
    goods = sorted(set(g for a in spec for g in a))
    return {g: i for i, g in enumerate(goods)}


def build(spec):
    lab = name_goods(spec)
    sets = [[lab[g] for g in a] for a in spec]
    vals = [[a[g] for g in a] for a in spec]
    return sets, vals, len(lab), lab


def depth(E, b, kmax=3, free=False):
    ok = (lambda bb: T.DF.extends(E, bb)) if free else (lambda bb: T.extends_A(E, bb, 1))
    if ok(b):
        return 0, None
    layer = {b: ()}; seen = {b}
    for k in range(1, kmax + 1):
        nxt = {}
        for bb, hist in layer.items():
            for b2, p in T.iter_chains_path(E, bb):
                if b2 in seen:
                    continue
                seen.add(b2); nxt[b2] = hist + (p,)
                if ok(b2):
                    return k, hist + (p,)
        layer = nxt
    return None, len(seen)


DESIGNS = {
    # two copies of the n = 4 instance 0's danger structure (a, d with pair u1 u2; b, e with pair w1 w2), a starved
    # receiver r wanting T, Pd, Pe, and c = {T, j, Pa, Pb} needing both Pa and Pb (4 + 7 > 10)
    'ladder6': [
        {'T': 10, 'j': 2, 'Pa': 4, 'Pb': 7},           # c
        {'T': 10, 'Pr': 3, 'Pe': 8, 'Pd': 4},          # r
        {'u1': 3, 'u2': 5, 'Pa': 6, 'Pd': 7},          # a
        {'w1': 3, 'w2': 5, 'Pb': 6, 'Pe': 7},          # b
        {'u1': 3, 'u2': 2, 'Pd': 4},                   # d
        {'w1': 3, 'w2': 2, 'Pe': 4},                   # e
    ],
    # r wants Pa and Pb instead, so a and b are frozen by r (as agent 2 is by the receiver in instance 0)
    'ladder6b': [
        {'T': 10, 'j': 2, 'Pa': 4, 'Pb': 7},           # c
        {'T': 10, 'Pr': 3, 'Pa': 4, 'Pb': 8},          # r
        {'u1': 3, 'u2': 5, 'Pa': 6, 'Pd': 7},          # a
        {'w1': 3, 'w2': 5, 'Pb': 6, 'Pe': 7},          # b
        {'u1': 3, 'u2': 2, 'Pd': 4},                   # d
        {'w1': 3, 'w2': 2, 'Pe': 4},                   # e
    ],
    # e also wants Pd, so d stays frozen after a's move (the want graph must stay acyclic, so d cannot also want Pe)
    'ladder6c': [
        {'T': 10, 'j': 2, 'Pa': 4, 'Pb': 7},           # c
        {'T': 10, 'Pr': 3, 'Pa': 4, 'Pb': 8},          # r
        {'u1': 3, 'u2': 5, 'Pa': 6, 'Pd': 7},          # a
        {'w1': 3, 'w2': 5, 'Pb': 6, 'Pe': 7},          # b
        {'u1': 3, 'u2': 2, 'Pd': 4},                   # d
        {'w1': 4, 'w2': 2, 'Pe': 5, 'Pd': 8},          # e (strict: no equal disjoint sums)
    ],
}
ORDERS = {'ladder6': ['c', 'd', 'e', 'a', 'b', 'r'], 'ladder6b': ['c', 'd', 'e', 'a', 'b', 'r'],
          'ladder6c': ['c', 'd', 'e', 'a', 'b', 'r']}
AG = ['c', 'r', 'a', 'b', 'd', 'e']

if __name__ == '__main__':
    print('$ python3 k4/ttc/ladder.py')
    for nm, spec in DESIGNS.items():
        sets, vals, m, lab = build(spec)
        inv = {i: g for g, i in lab.items()}
        E = T.Enc(sets, vals, m)
        order = [AG.index(x) for x in ORDERS[nm]]
        Y = tuple(T.sd(E, order)[0]); b = T.base_of(E, Y)
        print(nm, 'sets', sets, 'vals', vals, 'm', m)
        print('  goods', {i: inv[i] for i in range(m)})
        print('  is_core4', CC.is_core4(CC.vmatrix(sets, vals, m)), 'nu', CC.nu(sets), 'two private', CC.two_private(sets))
        print('  order', order, 'picks', [inv[y] if y is not None else None for y in Y])
        F = T.frozen_set(E, b)
        print('  frozen', [AG[i] for i in sorted(F)], 'receivers', [AG[i] for i in range(E.n) if i not in F])
        for free in (False, True):
            k, info = depth(E, b, 3, free)
            print('  %s completion: least moves %s %s' % ('free' if free else 'one-absorber', k,
                                                        info if k is not None else '(searched %s states)' % info))
