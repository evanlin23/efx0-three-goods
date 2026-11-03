"""Conjecture DE4 (k4/de4.md §2) is false: a strict R1-core profile (n = 4, m = 7, core 131 of
results/k4_certs_4_n4_2.json.gz) with a maximum that has no EFX0 completion. The same instance refutes the improvement
form and Conjecture 11'' (the state satisfies (H) and no valid state is better).

Written from the definitions of k4/de4.md §1 only; it imports nothing from de4lib, check or de4.c (it is a third
implementation: de4.c found the instance, de4lib confirms it). Prints 'confirmed' or 'NOT confirmed' for each claim;
exit status 0 iff all are confirmed.   python3 k4/de4/refute_de4.py
"""
import itertools
import sys

N, M = 4, 7
R = [[0, 2, 4, 6], [1, 3, 5, 6], [2, 3, 6], [4, 5, 6]]   # relevant goods of each agent
PROFILES = {   # values in the order of R[i]; de4.c profiles 353961 and 415963 (and their mirror images)
    'A': [[3, 8, 2, 4], [3, 2, 8, 4], [4, 2, 3], [2, 4, 3]],
    'B': [[3, 2, 8, 4], [3, 8, 2, 4], [2, 4, 3], [4, 2, 3]],
}
BAD = {'A': [{0, 4}, {1, 3}, {2}, {5}], 'B': [{0, 2}, {1, 5}, {3}, {4}]}
ok_all = True


def report(name, ok):
    global ok_all
    ok_all &= ok
    print(('confirmed    ' if ok else 'NOT confirmed') + ' ' + name)


def check(name):
    v = [dict(zip(R[i], PROFILES[name][i])) for i in range(N)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    ranked = [sorted(R[i], key=lambda g: -v[i][g]) for i in range(N)]
    top = [v[i][ranked[i][0]] for i in range(N)]

    def subsets(xs):
        return [set(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r)]

    # the setting: an R1-core (3 or 4 relevant goods, strictly balanced), strict (distinct subset sums)
    core = all(len(R[i]) in (3, 4) and top[i] < val(i, R[i]) - top[i] for i in range(N))
    strict = all(len(set(val(i, S) for S in subsets(R[i]))) == 2 ** len(R[i]) for i in range(N))

    def upper(i, S):
        return len(S) >= 2 and val(i, S) > top[i] and all(val(i, S - {h}) <= top[i] for h in S)

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
        return 5 if upper(i, S) else 3

    def theta(i, B):
        return max((val(i, B - {h}) for h in B), default=0)

    def valid(Y):
        alone = {next(iter(S)) for S in Y if len(S) == 1}
        wanted = {g for i in range(N) for g in R[i] if g not in Y[i] and v[i][g] > val(i, Y[i])}
        return wanted <= alone and all(theta(i, Y[j]) <= val(i, Y[i]) for i in range(N) for j in range(N) if i != j)

    def efx0(X):
        return all(theta(i, X[j]) <= val(i, X[i]) for i in range(N) for j in range(N) if i != j)

    def completable(Y):
        J = [g for g in range(M) if not any(g in S for S in Y)]
        for owners in itertools.product(range(N), repeat=len(J)):
            X = [set(S) for S in Y]
            for g, o in zip(J, owners):
                X[o].add(g)
            if efx0(X):
                return True
        return False

    opts = [[S for S in subsets(range(M)) if S <= set(R[i]) and holding(i, S)] for i in range(N)]
    states = [list(Y) for Y in itertools.product(*opts)
              if sum(map(len, Y)) == len(set().union(*Y)) and valid(list(Y))]
    phi = lambda Y: sum(level(i, Y[i]) for i in range(N))

    def better(Z, Y):   # Z better than Y in the order of §1
        if phi(Z) != phi(Y):
            return phi(Z) > phi(Y)
        a, b = [val(i, Z[i]) for i in range(N)], [val(i, Y[i]) for i in range(N)]
        return all(x >= y for x, y in zip(a, b)) and a != b

    Y = BAD[name]
    J = [g for g in range(M) if not any(g in S for S in Y)]
    frozen = [i for i in range(N) if len(Y[i]) == 1 and any(
        next(iter(Y[i])) in R[w] and v[w][next(iter(Y[i]))] > val(w, Y[w]) for w in range(N))]
    free = [i for i in range(N) if i not in frozen]
    no_self_upgrade = all(not (holding(x, S) and len(S) <= 2 and val(x, S) > val(x, Y[x]))
                          for x in free for S in subsets(sorted(Y[x] | set(J))) if S <= set(R[x]))
    H = (all(Y) and all(val(i, set(J)) <= val(i, Y[i]) for i in range(N)) and no_self_upgrade)
    report('profile %s: strict R1-core (3 or 4 relevant goods, strictly balanced, distinct subset sums)' % name,
           core and strict)
    report('profile %s: Y = %s is a valid state (levels %s, leftover %s)' % (name, Y, [level(i, Y[i]) for i in range(N)], J),
           Y in states)
    report('profile %s: no valid state is better than Y (Y is a maximum: Phi = %d, the largest; %d valid states)'
           % (name, phi(Y), len(states)), not any(better(Z, Y) for Z in states) and phi(Y) == max(map(phi, states)))
    report('profile %s: Y has no EFX0 completion' % name, not completable(Y))
    report('profile %s: Y satisfies (H) (every agent holds a good, the leftover goods threaten nobody, no free '
           'self-upgrade), and a free agent holds two goods' % name, H and any(len(Y[i]) >= 2 for i in free))
    mx = [Z for Z in states if not any(better(W, Z) for W in states)]
    report('profile %s: some other maximum is completable (%d maxima)' % (name, len(mx)),
           any(completable(Z) for Z in mx))


for name in PROFILES:
    check(name)
sys.exit(0 if ok_all else 1)
