"""In the robust order (k4/de4.md §10.1), a single owner does not always finish a (V3)-valid state of the largest level
sum: on A131 (the instance of the DE4 counterexample, attempts/k4-de4.md) the state [{6}, {1, 3}, {2}, {5}] with
leftover goods {0, 4} is (V3)-valid, has the largest level sum (14, over all valid states and over the (V3)-valid ones),
is not all-upper, and no agent can take both leftover goods; DE's finishing rule completes it (agent 1 takes 4, agent 0
takes 0). Ledger K4.DE4V3R.OWN.

Written from the definitions of k4/de4.md §1, §8 and §10 only; it imports nothing from de4lib, claimt or the C programs
(claimt.py found the state). Prints 'confirmed' or 'NOT confirmed' for each claim; exit status 0 iff all are
confirmed.   python3 k4/de4/refute_owner.py
"""
import itertools
import sys

R = [[0, 2, 4, 6], [1, 3, 5, 6], [2, 3, 6], [4, 5, 6]]
VALS = [[3, 8, 2, 4], [3, 2, 8, 4], [4, 2, 3], [2, 4, 3]]
M = 7
Y0 = [{6}, {1, 3}, {2}, {5}]
COMPLETION = [{6, 0}, {1, 3, 4}, {2}, {5}]

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


def robust(i, S):
    return val(i, S) >= val(i, set(R[i]) - S)


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
        return 6 if robust(i, S) else 5
    return 3


def theta(i, B):
    return max((val(i, B - {h}) for h in B), default=0) if len(B) >= 2 else 0


def valid(Y):
    alone = {next(iter(S)) for S in Y if len(S) == 1}
    wanted = {g for i in range(N) for g in R[i] if g not in Y[i] and v[i][g] > val(i, Y[i])}
    return wanted <= alone and all(theta(i, Y[j]) <= val(i, Y[i]) for i in range(N) for j in range(N) if i != j)


def v3(Y):
    held = set().union(*Y)
    return all(not lower_pair(i, Y[i]) or ranked[i][1] in held for i in range(N))


def phi(Y):
    return sum(level(i, Y[i]) for i in range(N))


def efx0(X):
    return all(theta(i, X[j]) <= val(i, X[i]) for i in range(N) for j in range(N) if i != j)


core = all(len(R[i]) in (3, 4) and top(i) < val(i, R[i]) - top(i) for i in range(N))
strict = all(len(set(val(i, S) for S in subsets(R[i]))) == 2 ** len(R[i]) for i in range(N))
report('A131 is a strict R1-core profile (3 or 4 relevant goods, top worth less than the rest, distinct subset sums)',
       core and strict)
opts = [[S for S in subsets(range(M)) if holding(i, S)] for i in range(N)]
states = [list(Y) for Y in itertools.product(*opts) if sum(map(len, Y)) == len(set().union(*Y)) and valid(list(Y))]
P_all = max(map(phi, states))
P_v3 = max(phi(Y) for Y in states if v3(Y))
report('largest level sum: %d over all valid states, %d over (V3)-valid states' % (P_all, P_v3), P_all == P_v3 == 14)
report('the state %s is valid, (V3)-valid, of level sum %d' % ([sorted(S) for S in Y0], phi(Y0)),
       all(holding(i, Y0[i]) for i in range(N)) and valid(Y0) and v3(Y0) and phi(Y0) == 14)
report('it is not all-upper', not all(upper(i, Y0[i]) for i in range(N)))
J = set(range(M)) - set().union(*Y0)
owners = []
for o in range(N):
    X = [set(S) for S in Y0]
    X[o] |= J
    if efx0(X):
        owners.append(o)
report('leftover goods %s; no agent can take all of them (EFX0 fails for every single owner)' % sorted(J), not owners)
report('the completion %s (agent 1 owns 4, agent 0 helps with 0) is EFX0' % [sorted(S) for S in COMPLETION],
       efx0(COMPLETION) and all(Y0[i] <= COMPLETION[i] for i in range(N))
       and set().union(*COMPLETION) == set(range(M)) and sum(map(len, COMPLETION)) == M)
sys.exit(0 if ok_all else 1)
