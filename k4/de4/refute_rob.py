"""Conjecture K4.DE4V3R (the robust candidate: every maximum of the robust order is completable) is FALSE, and with it
Claim T' and Claim T (k4/de4.md §10). Instance (n = 6, m = 11, found by k4/de4/gapsearch.py-style searches around
GM4-B's double clash, family adv_t3): the state [{4, 5}, {6, 7}, {1}, {0}, {2, 9}, {3, 10}] with the one leftover good
8. Agents 0 and 1 hold their lower pairs; agents 3 and 2 are frozen on the tops of 0 and 1, and both have the leftover
good 8 as their b; agents 4 and 5 hold robust pairs containing the b's of 0 and 1. The state is (V3)-valid, of the
largest level sum among (V3)-valid states, no (V3)-valid state of that level sum is value-Pareto-better (a maximum of
the robust order), and it is not completable: giving the leftover good to any agent breaks EFX0. Ledger K4.DE4V3R.

Written from the definitions of k4/de4.md §1, §7, §8, §10 only; it imports nothing from the repository.
Prints 'confirmed' or 'NOT confirmed' for each claim; exit status 0 iff all are confirmed.   python3 k4/de4/refute_rob.py
"""
import itertools
import sys

R = [[0, 2, 4, 5], [1, 3, 6, 7], [1, 2, 4, 8], [0, 3, 7, 8], [0, 2, 8, 9], [1, 3, 4, 10]]
VALS = [[39, 21, 16, 8], [19, 14, 9, 7], [36, 27, 22, 33], [39, 12, 13, 30], [22, 29, 16, 18], [31, 25, 2, 15]]
M = 11
Y0 = [{4, 5}, {6, 7}, {1}, {0}, {2, 9}, {3, 10}]

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
    """minimal sets D of goods of R_i outside Y_i, not wanted by i, with v_i(D) > v_i(Y_i)"""
    cand = [g for g in R[i] if g not in Y[i] and g not in wanted_by(i, Y)]
    vy = val(i, Y[i])
    return [D for D in subsets(cand) if D and val(i, D) > vy and all(val(i, D - {h}) <= vy for h in D)]



def efx0(X):
    return all(theta(i, X[j]) <= val(i, X[i]) for i in range(N) for j in range(N) if i != j)


def upper(i, S):
    return len(S) >= 2 and S <= set(R[i]) and val(i, S) > top(i) and all(val(i, S - {h}) <= top(i) for h in S)


core = all(len(R[i]) in (3, 4) and top(i) < val(i, R[i]) - top(i) for i in range(N))
strict = all(len(set(val(i, S) for S in subsets(R[i]))) == 2 ** len(R[i]) for i in range(N))
report('the profile is a strict R1-core profile (each agent values 3 or 4 goods, top < sum of the others)', core and strict)
opts = [[S for S in subsets(range(M)) if holding(i, S)] for i in range(N)]
states = [list(Y) for Y in itertools.product(*opts) if sum(map(len, Y)) == len(set().union(*Y)) and valid(list(Y))]
v3states = [Y for Y in states if v3(Y)]
P = max(phi(Y) for Y in v3states)
report('the state %s is valid and (V3)-valid, with the largest robust level sum %d among %d (V3)-valid states'
       % ([sorted(S) for S in Y0], P, len(v3states)),
       valid(Y0) and v3(Y0) and phi(Y0) == P and all(holding(i, Y0[i]) for i in range(N)))
vals0 = [val(i, Y0[i]) for i in range(N)]
better = [Y for Y in v3states if phi(Y) == P and all(val(i, Y[i]) >= vals0[i] for i in range(N))
          and any(val(i, Y[i]) > vals0[i] for i in range(N))]
report('no (V3)-valid state of that level sum is value-Pareto-better: it is a maximum of the robust order', not better)
report('not every agent holds an upper set (agents 0 and 1 hold their lower pairs)',
       lower_pair(0, Y0[0]) and lower_pair(1, Y0[1]))
J = set(range(M)) - set().union(*Y0)
comp = [o for o in itertools.product(range(N), repeat=len(J))
        if efx0([Y0[i] | {g for g, w in zip(sorted(J), o) if w == i} for i in range(N)])]
report('it is not completable: no way of giving the leftover goods %s to the agents is EFX0' % sorted(J), not comp)
sys.exit(0 if ok_all else 1)
