#!/usr/bin/env python3
"""Proposition HT of k4/hall.md: for every t >= 1 the core H_t of k4/c4.md §7 (branch proof/k4-c4, PR #33; built as in
k4/c4x_ht.py of PR #36, re-typed here) has an EFX0 allocation with at most one bundle of more than two goods, the
completion of an explicit valid pre-allocation without frozen agents.

H_t: goods g_1..g_t, z, u, u', a_{j,i}, b_{j,i}, c_{j,i} (1 <= j <= t, 1 <= i <= 3); agents
  l with R = {g_1, z, u, u'} and values (8, 6, 5, 4);
  x_{j,i} with R = {a_{j,i}, b_{j,i}, c_{j,i}, g_j} and values (8, 6, 4, 3);
  y_j with R = {a_{j,1}, a_{j,2}, a_{j,3}, e_j} and values (8, 6, 4, 3), e_j = g_{j+1} (j < t), e_t = z.
Allocation: l {g_1, z}; x_{j,1} {b_{j,1}, c_{j,1}}; x_{j,2} {a_{j,2}, b_{j,2}}; x_{j,3} {a_{j,3}, b_{j,3}};
y_j (j >= 2) {a_{j,1}} plus one junk good; y_1 {a_{1,1}} plus all remaining goods.
The script checks, for t = 1..T (default 12): the pre-allocation is valid with no frozen agent (value-based needs),
and the allocation is EFX0 by the raw definition (every ordered pair of agents, every removed good), with only y_1's
bundle larger than two goods. usage: python3 k4/hall_ht.py [T]"""
import sys

def build(t):
    goods = [f'g{j}' for j in range(1, t + 1)] + ['z', 'u', "u'"]
    for j in range(1, t + 1):
        for i in range(1, 4): goods += [f'a{j}{i}', f'b{j}{i}', f'c{j}{i}']
    agents = {'l': dict(zip(['g1', 'z', 'u', "u'"], [8, 6, 5, 4]))}
    for j in range(1, t + 1):
        for i in range(1, 4): agents[f'x{j}{i}'] = dict(zip([f'a{j}{i}', f'b{j}{i}', f'c{j}{i}', f'g{j}'], [8, 6, 4, 3]))
        e = f'g{j + 1}' if j < t else 'z'
        agents[f'y{j}'] = dict(zip([f'a{j}1', f'a{j}2', f'a{j}3', e], [8, 6, 4, 3]))
    return goods, agents

def check(t):
    goods, V = build(t)
    B = {'l': {'g1', 'z'}}
    for j in range(1, t + 1):
        B[f'x{j}1'] = {f'b{j}1', f'c{j}1'}; B[f'x{j}2'] = {f'a{j}2', f'b{j}2'}; B[f'x{j}3'] = {f'a{j}3', f'b{j}3'}
        B[f'y{j}'] = {f'a{j}1'}
    used = set().union(*B.values())
    J = [g for g in goods if g not in used]
    v = lambda i, S: sum(V[i].get(g, 0) for g in S)
    # validity: value-based needs, every needed good must be a one-good base; here we expect no needs at all
    NA = {g for i in V for g in V[i] if g not in B[i] and V[i][g] > v(i, B[i])}
    assert not NA, NA
    assert len(J) == 3 * t + 1 and len(J) - t == 2 * t + 1   # slots S = t (the y_j), omega = 2t + 1
    X = {i: set(B[i]) for i in B}
    rest = list(J)
    for j in range(2, t + 1): X[f'y{j}'].add(rest.pop())
    X['y1'] |= set(rest)
    assert sorted(g for S in X.values() for g in S) == sorted(goods)
    assert all(len(S) <= 2 for i, S in X.items() if i != 'y1')
    for i in V:
        for k in V:
            if i == k: continue
            for h in X[k]:
                if v(i, X[i]) < v(i, X[k] - {h}): return False, (i, k, h)
    return True, len(X['y1'])

if __name__ == '__main__':
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for t in range(1, T + 1):
        ok, info = check(t)
        print(f't = {t}: n = {4 * t + 1}, m = {10 * t + 3}: ' + (f'EFX0, large bundle of {info} goods (y_1)' if ok else f'FAILS {info}'))
