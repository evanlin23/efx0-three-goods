"""Every tie-break inside the largest robust level sum fails (ledger K4.DE4V3R.LPX, k4/de4.md §10.5): on this instance the
(V3)-valid states of the largest robust level sum are a single state, and it is not completable. So the lower-pair
order (K4.DE4V3R.LP), the total-value order (K4.DE4V3R.S) and the robust order (K4.DE4V3R) all have a non-completable
maximum here, and so does any order that maximizes the robust level sum first. Instance (n = 6, m = 11, found by
k4/de4/topswap.py on the family advt4r of k4/de4/adv_t4.py): GM4-B's double clash again, with both lower-pair holders
big-top (v(b) + v(c) < v(a)) and both frozen agents' b's the tops of the robust pairs of agents 4 and 5. The instance
has an EFX0 allocation (checked below), so TARGET4 is not refuted.

Written from the definitions of k4/de4.md §1, §7, §8, §10 only; it imports nothing from the repository.
Prints 'confirmed' or 'NOT confirmed' for each claim; exit status 0 iff all are confirmed.   python3 k4/de4/refute_lp.py
"""
import itertools
import sys

R = [[0, 2, 4, 5], [1, 3, 6, 7], [1, 3, 4, 8], [0, 2, 6, 8], [1, 2, 9], [0, 3, 10]]
VALS = [[37, 19, 17, 11], [38, 19, 18, 6], [35, 34, 21, 31], [18, 12, 9, 11], [35, 36, 18], [27, 29, 13]]
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
level_top = [Y for Y in v3states if phi(Y) == P]
report('the largest robust level sum among the %d (V3)-valid states is %d, reached only by %s'
       % (len(v3states), P, [sorted(S) for S in Y0]), level_top == [Y0])


def completable(Y):
    J = sorted(set(range(M)) - set().union(*Y))
    return any(efx0([Y[i] | {g for g, w in zip(J, o) if w == i} for i in range(N)])
               for o in itertools.product(range(N), repeat=len(J)))


report('it is not completable: no way of giving the leftover goods %s to the agents is EFX0'
       % sorted(set(range(M)) - set().union(*Y0)), not completable(Y0))
report('so every order that maximizes the robust level sum first has this non-completable maximum (lower pairs: %d)'
       % sum(lower_pair(i, Y0[i]) for i in range(N)), level_top == [Y0] and not completable(Y0))
P_all = max(phi(Y) for Y in states)
report('it also has the largest robust level sum among all valid states (%d), as Lemma R says' % P_all, P_all == P)


def efx0_exists():
    X = [set() for _ in range(N)]

    def rec(g):
        if g == M:
            return efx0(X)
        for i in range(N):
            X[i].add(g)
            if rec(g + 1):
                return True
            X[i].discard(g)
        return False
    return rec(0)


report('the instance has an EFX0 allocation (TARGET4 is not refuted)', efx0_exists())
sys.exit(0 if ok_all else 1)
