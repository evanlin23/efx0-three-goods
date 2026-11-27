"""Conjecture P1 of k4/de4.md §10.3 ("at a (V3)-valid state of the largest level sum with (H), no free holder of its lower
pair has an out-arc in the arc graph") is false. Instance (n = 4, m = 7, found by a hill-climbing search on the values of
an n = 4 core with two 4-good agents): agent 1 holds its lower pair {1, 4}; agent 0, a free holder of its b (good 3),
has its own lower pair {4, 0} as a minimal danger set, made of agent 1's c and the leftover good 0. So agent 1's
lower pair has an out-arc, although the state is a maximum of the robust order (largest level sum 16; no (V3)-valid
Pareto-better state) and satisfies (H). The arc is lateral: agent 0 would move from its b to its lower pair, level 3
to 3, the exception in Lemma 18. The state is completable and the arc graph has no cycle, so Conjecture C3 and the
hypothesis HX of the Lean frame are not refuted; only the decomposition of C3 through P1. Ledger K4.DE4V3R.P1.

Written from the definitions of k4/de4.md §1, §7, §8, §10 only; it imports nothing from de4lib, claimt or claimd.
Prints 'confirmed' or 'NOT confirmed' for each claim; exit status 0 iff all are confirmed.   python3 k4/de4/refute_p1.py
"""
import itertools
import sys

R = [[0, 3, 4, 5], [1, 4, 5, 6], [2, 4, 6], [3, 5, 6]]
VALS = [[6, 11, 9, 18], [4, 14, 32, 16], [11, 19, 10], [6, 7, 4]]
M = 7
Y0 = [{3}, {1, 4}, {2, 6}, {5}]

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


core = all(len(R[i]) in (3, 4) and top(i) < val(i, R[i]) - top(i) for i in range(N))
strict = all(len(set(val(i, S) for S in subsets(R[i]))) == 2 ** len(R[i]) for i in range(N))
report('the profile is a strict R1-core profile', core and strict)
opts = [[S for S in subsets(range(M)) if holding(i, S)] for i in range(N)]
states = [list(Y) for Y in itertools.product(*opts) if sum(map(len, Y)) == len(set().union(*Y)) and valid(list(Y))]
P = max(phi(Y) for Y in states if v3(Y))
report('the state %s is valid, (V3)-valid, of the largest level sum %d' % ([sorted(S) for S in Y0], P),
       valid(Y0) and v3(Y0) and phi(Y0) == P and all(holding(i, Y0[i]) for i in range(N)))
vals0 = [val(i, Y0[i]) for i in range(N)]
better = [Y for Y in states if v3(Y) and phi(Y) == P and all(val(i, Y[i]) >= vals0[i] for i in range(N))
          and any(val(i, Y[i]) > vals0[i] for i in range(N))]
report('no (V3)-valid state of that level sum is value-Pareto-better: it is a maximum', not better)
J = set(range(M)) - set().union(*Y0)
W = set().union(*(wanted_by(i, Y0) for i in range(N)))
frozen = [len(Y0[i]) == 1 and next(iter(Y0[i])) in W for i in range(N)]
H = (all(Y0) and all(val(i, J) <= val(i, Y0[i]) for i in range(N)) and
     not any(not frozen[x] and holding(x, S) and val(x, S) > vals0[x]
             for x in range(N) for S in subsets([g for g in Y0[x] | J if g in v[x]])))
report('(H): everyone holds a good, nobody is threatened by J = %s alone, no free agent upgrades inside its holding and J'
       % sorted(J), H)
report('agent 1 is a free holder of its lower pair', not frozen[1] and lower_pair(1, Y0[1]))
D = {0, 4}
minimal = not any(E < D for i in range(N) for E in danger_sets(i, Y0))
report('agent 0 (a free holder of its b) has the minimal danger set %s inside Y_1 + J, meeting Y_1: an out-arc of the lower '
       'pair; it is agent 0\'s own lower pair' % sorted(D),
       not frozen[0] and Y0[0] == {ranked[0][1]} and D in danger_sets(0, Y0) and D <= Y0[1] | J and D & Y0[1] and minimal
       and lower_pair(0, D))
comp = any(efx0([Y0[i] | {g for g, o in zip(sorted(J), own) if o == i} for i in range(N)])
           for own in itertools.product(range(N), repeat=len(J)))
report('the state is completable', comp)
sys.exit(0 if ok_all else 1)
