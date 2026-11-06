"""Conjecture D of k4/de4.md §10.2 ("in every (V3)-valid state with (H), every F2-clash cycle of the arc graph is resolved
by Lemma 18, Theorem 23 or a level-raising b-swap") is false. Instance (n = 6, m = 9, found by an adversarial search
around GM4-B's clash): agents 0 and 1 hold their lower pairs, agents 2 and 3 are frozen holders of the tops of 1 and 0
whose b is the leftover good 8, agents 4 and 5 hold the b's of 0 and 1. The arc graph has exactly one cycle,
0 -> 2 -> 1 -> 3 -> 0, and its two arcs out of the lower-pair holders both use the leftover good 8 while neither has a
same-giver alternative (agents 2 and 3 take their c from the giver and their b from J); no b-swap applies. The state
is not a counterexample to Claim T': it is completable, and a valid state with a larger level sum exists (agent 5 takes
its b, which is agent 0's d, keeping its top; agent 0 keeps its c; Lemma 20(d)). Ledger K4.DE4V3R.D.

Written from the definitions of k4/de4.md §1, §7, §8, §10 only; it imports nothing from de4lib, claimt or claimd.
Prints 'confirmed' or 'NOT confirmed' for each claim; exit status 0 iff all are confirmed.   python3 k4/de4/refute_d.py
"""
import itertools
import sys

R = [[0, 2, 4, 5], [1, 3, 6, 7], [1, 4, 8], [0, 6, 8], [1, 2, 6], [3, 5, 6]]
VALS = [[29, 14, 13, 6], [22, 10, 9, 8], [18, 12, 16], [25, 7, 19], [22, 25, 24], [25, 17, 11]]
M = 9
Y0 = [{4, 5}, {6, 7}, {1}, {0}, {2}, {3}]
RAISE = [{4}, {6, 7}, {1}, {0}, {2}, {3, 5}]

N = len(R)
v = [dict(zip(R[i], VALS[i])) for i in range(N)]
ranked = [sorted(R[i], key=lambda g: -v[i][g]) for i in range(N)]
ok_all = True


def report(name, ok):
    global ok_all
    ok_all &= ok
    print(('confirmed    ' if ok else 'NOT confirmed') + ' ' + name)


def subsets(xs):
    return [set(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r)]


def val(i, S):
    return sum(v[i].get(g, 0) for g in S)


def top(i):
    return v[i][ranked[i][0]]


def upper(i, S):
    return len(S) >= 2 and S <= set(R[i]) and val(i, S) > top(i) and all(val(i, S - {h}) <= top(i) for h in S)


def lower_pair(i, S):
    r = ranked[i]
    return len(r) == 4 and S == {r[2], r[3]} and v[i][r[1]] < val(i, S) < v[i][r[0]]


def holding(i, S):
    return len(S) == 0 or (len(S) == 1 and S <= set(R[i])) or upper(i, S) or lower_pair(i, S)


def level(i, S):
    if not S:
        return 0
    if len(S) == 1:
        return 4 - ranked[i].index(next(iter(S)))
    if upper(i, S):
        return 6 if val(i, S) >= val(i, set(R[i]) - S) else 5
    return 3


def theta(i, B):
    return max((val(i, B - {h}) for h in B), default=0) if len(B) >= 2 else 0


def wanted_by(i, Y):
    return {g for g in R[i] if g not in Y[i] and v[i][g] > val(i, Y[i])}


def valid(Y):
    alone = {next(iter(S)) for S in Y if len(S) == 1}
    W = set().union(*(wanted_by(i, Y) for i in range(N)))
    return W <= alone and all(theta(i, Y[j]) <= val(i, Y[i]) for i in range(N) for j in range(N) if i != j)


def v3(Y):
    held = set().union(*Y)
    return all(not lower_pair(i, Y[i]) or ranked[i][1] in held for i in range(N))


def phi(Y):
    return sum(level(i, Y[i]) for i in range(N))


def danger_sets(i, Y):
    cand = [g for g in R[i] if g not in Y[i] and g not in wanted_by(i, Y)]
    vy = val(i, Y[i])
    return [D for D in subsets(cand) if D and val(i, D) > vy and all(val(i, D - {h}) <= vy for h in D)]


def efx0(X):
    return all(theta(i, X[j]) <= val(i, X[i]) for i in range(N) for j in range(N) if i != j)


core = all(len(R[i]) in (3, 4) and top(i) < val(i, R[i]) - top(i) for i in range(N))
strict = all(len(set(val(i, S) for S in subsets(R[i]))) == 2 ** len(R[i]) for i in range(N))
report('the profile is a strict R1-core profile', core and strict)
report('the state %s is valid and (V3)-valid' % [sorted(S) for S in Y0],
       valid(Y0) and v3(Y0) and all(holding(i, Y0[i]) for i in range(N)))
J = set(range(M)) - set().union(*Y0)
W = set().union(*(wanted_by(i, Y0) for i in range(N)))
frozen = [len(Y0[i]) == 1 and next(iter(Y0[i])) in W for i in range(N)]
vals0 = [val(i, Y0[i]) for i in range(N)]
selfup = [x for x in range(N) if not frozen[x] for S in subsets([g for g in Y0[x] | J if g in v[x]])
          if holding(x, S) and val(x, S) > vals0[x] and valid([S if i == x else Y0[i] for i in range(N)])]
report('(H): J = %s; everyone holds a good, nobody is threatened by J alone, no free agent has a valid upgrade inside '
       'its holding and J' % sorted(J),
       all(Y0) and all(val(i, J) <= vals0[i] for i in range(N)) and not selfup)
arcs = []
for o in range(N):
    if frozen[o]:
        g = next(iter(Y0[o]))
        arcs += [(o, x, frozenset(Y0[o])) for x in range(N) if g in wanted_by(x, Y0)]
    else:
        for x in range(N):
            if x == o:
                continue
            for D in danger_sets(x, Y0):
                minimal = not any(E < D for i in range(N) for E in danger_sets(i, Y0))
                if D & Y0[o] and D <= Y0[o] | J and minimal:
                    arcs.append((o, x, frozenset(D)))
cyc = []


def rec(start, path):
    for a in arcs:
        if a[0] != path[-1][1]:
            continue
        if a[1] == start:
            cyc.append(path + [a])
        elif a[1] > start and a[1] not in [z[0] for z in path]:
            rec(start, path + [a])


for a in arcs:
    if a[1] > a[0]:
        rec(a[0], [a])
expected = [(0, 2, {4, 8}), (2, 1, {1}), (1, 3, {6, 8}), (3, 0, {0})]
report('the arc graph has exactly one cycle, %s' % [(o, x, sorted(T)) for o, x, T in expected],
       len(cyc) == 1 and [(o, x, set(T)) for o, x, T in cyc[0]] == expected)
f1 = [a for a in cyc[0] if not frozen[a[0]] and len(Y0[a[0]]) == 1]
labels = [set(a[2]) & J for a in cyc[0]]
report('it is an F2-clash cycle (no arc out of a free holder of one good); the label 8 is shared by the arcs out of the '
       'lower-pair holders 0 and 1 and by no other arc', not f1 and labels == [{8}, set(), {8}, set()]
       and lower_pair(0, Y0[0]) and lower_pair(1, Y0[1]))
no_alt = True
for o, x, T in (cyc[0][0], cyc[0][2]):
    r = ranked[x]
    rich = upper(x, Y0[x]) and len(r) == 4 and r[0] not in Y0[x]
    down_b = frozen[x] and Y0[x] == {r[0]} and r[1] in T & Y0[o]
    down_c = frozen[x] and len(r) == 4 and Y0[x] == {r[1]} and r[2] in T & Y0[o]
    no_alt &= not rich and not down_b and not down_c
report('neither of the two arcs has a same-giver alternative (their takers 2 and 3 are frozen holders of their top '
       'whose take from the giver misses their b), so Lemma 18 and Theorem 23 do not apply', no_alt)
bswap = False
for u in (0, 1):
    a, b, c, d = ranked[u]
    w = next(k for k in range(N) if b in Y0[k])
    bswap |= any(o == u and x == w for o, x, T in arcs)                              # (i)
    bswap |= lower_pair(w, Y0[w]) and ranked[w][1] in Y0[u]                           # (ii)
    bswap |= len(Y0[w]) == 2 and upper(w, Y0[w]) and ranked[w][0] in Y0[w]           # (iii)
report('no b-swap of Lemma 20\' applies (the b of each lower-pair holder is the single holding of an agent with no '
       'arc into it)', not bswap)
report('a valid state with a larger level sum exists (%s, level sum %d > %d), so the state is not a maximum'
       % ([sorted(S) for S in RAISE], phi(RAISE), phi(Y0)), valid(RAISE) and phi(RAISE) > phi(Y0))
comp = any(efx0([Y0[i] | {g for g, o in zip(sorted(J), own) if o == i} for i in range(N)])
           for own in itertools.product(range(N), repeat=len(J)))
report('the state is completable (not a counterexample to Claim T\')', comp)
sys.exit(0 if ok_all else 1)
