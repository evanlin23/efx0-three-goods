"""Conjecture DE4 (k4/de4.md §2) is false, and simple tie-breaks do not repair it (attempts/k4-de4.md).

(1) A strict R1-core profile (n = 4, m = 7, core 131 of results/k4_certs_4_n4_2.json.gz) with a maximum that has no
    EFX0 completion. The same state refutes the improvement form and Conjecture 11'' (it satisfies (H) and no valid
    state is better).
(2) Orders with a scale-invariant tie-break after the level sum (fewest lower pairs; fewest goods held; fewest
    holdings of two or more goods), then value-Pareto: on core 127 a maximum of each has no EFX0 completion.
    The tie-break "fewest frozen agents" leaves (1) a maximum.

Written from the definitions of k4/de4.md §1 only; it imports nothing from de4lib, check or de4.c / de4m.c (it is a
third implementation: the C programs found the instances, de4lib confirms them). Prints 'confirmed' or
'NOT confirmed' for each claim; exit status 0 iff all are confirmed.   python3 k4/de4/refute_de4.py
"""
import itertools
import sys

ok_all = True


def report(name, ok):
    global ok_all
    ok_all &= ok
    print(('confirmed    ' if ok else 'NOT confirmed') + ' ' + name)


def subsets(xs):
    return [set(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r)]


class Profile:
    def __init__(self, R, M, vals):
        self.R, self.M, self.N = R, M, len(R)
        self.v = [dict(zip(R[i], vals[i])) for i in range(self.N)]
        self.ranked = [sorted(R[i], key=lambda g: -self.v[i][g]) for i in range(self.N)]
        self.top = [self.v[i][self.ranked[i][0]] for i in range(self.N)]
        opts = [[S for S in subsets(range(M)) if S <= set(R[i]) and self.holding(i, S)] for i in range(self.N)]
        self.states = [list(Y) for Y in itertools.product(*opts)
                       if sum(map(len, Y)) == len(set().union(*Y)) and self.valid(list(Y))]

    def val(self, i, S):
        return sum(self.v[i].get(g, 0) for g in S)

    def core_strict(self):
        core = all(len(self.R[i]) in (3, 4) and self.top[i] < self.val(i, self.R[i]) - self.top[i] for i in range(self.N))
        strict = all(len(set(self.val(i, S) for S in subsets(self.R[i]))) == 2 ** len(self.R[i]) for i in range(self.N))
        return core and strict

    def upper(self, i, S):
        return len(S) >= 2 and self.val(i, S) > self.top[i] and all(self.val(i, S - {h}) <= self.top[i] for h in S)

    def lower_pair(self, i, S):
        r = self.ranked[i]
        return len(r) == 4 and S == {r[2], r[3]} and self.v[i][r[1]] < self.val(i, S) < self.v[i][r[0]]

    def holding(self, i, S):
        return len(S) == 0 or (len(S) == 1 and S <= set(self.R[i])) or self.upper(i, S) or self.lower_pair(i, S)

    def level(self, i, S):
        if not S:
            return 0
        if len(S) == 1:
            return 4 - self.ranked[i].index(next(iter(S)))
        return 5 if self.upper(i, S) else 3

    def theta(self, i, B):
        return max((self.val(i, B - {h}) for h in B), default=0)

    def wanted(self, Y):
        return {g for i in range(self.N) for g in self.R[i] if g not in Y[i] and self.v[i][g] > self.val(i, Y[i])}

    def valid(self, Y):
        alone = {next(iter(S)) for S in Y if len(S) == 1}
        return self.wanted(Y) <= alone and all(self.theta(i, Y[j]) <= self.val(i, Y[i])
                                               for i in range(self.N) for j in range(self.N) if i != j)

    def completable(self, Y):
        J = [g for g in range(self.M) if not any(g in S for S in Y)]
        for owners in itertools.product(range(self.N), repeat=len(J)):
            X = [set(S) for S in Y]
            for g, o in zip(J, owners):
                X[o].add(g)
            if all(self.theta(i, X[j]) <= self.val(i, X[i]) for i in range(self.N) for j in range(self.N) if i != j):
                return True
        return False

    def phi(self, Y):
        return sum(self.level(i, Y[i]) for i in range(self.N))

    def key(self, Y, tb):   # the tie-break key after the level sum (smaller is better)
        if tb == 'none':
            return 0
        if tb == 'fewest lower pairs':
            return sum(1 for i in range(self.N) if self.lower_pair(i, Y[i]))
        if tb == 'fewest goods held':
            return sum(map(len, Y))
        if tb == 'fewest holdings of two or more goods':
            return sum(1 for S in Y if len(S) >= 2)
        if tb == 'fewest frozen agents':
            W = self.wanted(Y)
            return sum(1 for S in Y if len(S) == 1 and S <= W)
        raise ValueError(tb)

    def better(self, Z, Y, tb='none'):   # Z better than Y: (level sum, -key) lexicographic, then value-Pareto
        a, b = (self.phi(Z), -self.key(Z, tb)), (self.phi(Y), -self.key(Y, tb))
        if a != b:
            return a > b
        x, y = [self.val(i, Z[i]) for i in range(self.N)], [self.val(i, Y[i]) for i in range(self.N)]
        return all(p >= q for p, q in zip(x, y)) and x != y

    def maxima(self, tb='none'):
        return [Z for Z in self.states if not any(self.better(W, Z, tb) for W in self.states)]


# (1) Conjecture DE4: core 131, de4.c profiles 353961 (A) and 415963 (B)
R131 = [[0, 2, 4, 6], [1, 3, 5, 6], [2, 3, 6], [4, 5, 6]]
for name, vals, Y in [('A', [[3, 8, 2, 4], [3, 2, 8, 4], [4, 2, 3], [2, 4, 3]], [{0, 4}, {1, 3}, {2}, {5}]),
                      ('B', [[3, 2, 8, 4], [3, 8, 2, 4], [2, 4, 3], [4, 2, 3]], [{0, 2}, {1, 5}, {3}, {4}])]:
    P = Profile(R131, 7, vals)
    J = [g for g in range(7) if not any(g in S for S in Y)]
    frozen = [i for i in range(4) if len(Y[i]) == 1 and Y[i] <= P.wanted(Y)]
    free = [i for i in range(4) if i not in frozen]
    no_self_upgrade = all(not (P.holding(x, S) and len(S) <= 2 and P.val(x, S) > P.val(x, Y[x]))
                          for x in free for S in subsets(sorted(Y[x] | set(J))) if S <= set(P.R[x]))
    H = all(Y) and all(P.val(i, set(J)) <= P.val(i, Y[i]) for i in range(4)) and no_self_upgrade
    report('profile %s: strict R1-core (3 or 4 relevant goods, strictly balanced, distinct subset sums)' % name,
           P.core_strict())
    report('profile %s: Y = %s is a valid state (levels %s, leftover %s)' % (name, Y, [P.level(i, Y[i]) for i in range(4)], J),
           Y in P.states)
    report('profile %s: no valid state is better than Y (Y is a maximum: Phi = %d, the largest; %d valid states)'
           % (name, P.phi(Y), len(P.states)),
           not any(P.better(Z, Y) for Z in P.states) and P.phi(Y) == max(map(P.phi, P.states)))
    report('profile %s: Y has no EFX0 completion' % name, not P.completable(Y))
    report('profile %s: Y satisfies (H) (every agent holds a good, the leftover goods threaten nobody, no free '
           'self-upgrade), and a free agent holds two goods' % name, H and any(len(Y[i]) >= 2 for i in free))
    mx = P.maxima()
    report('profile %s: some other maximum is completable (%d maxima)' % (name, len(mx)), any(P.completable(Z) for Z in mx))
    if name == 'A':
        report('profile A: with the tie-break "fewest frozen agents", Y is still a maximum',
               Y in P.maxima('fewest frozen agents'))

# (2) tie-breaks: core 127, de4m.c profile 596419 (C)
P = Profile([[0, 2, 3, 5], [1, 4, 6], [2, 3, 5, 6], [4, 5, 6]], 7, [[2, 8, 5, 4], [2, 4, 3], [4, 2, 3, 8], [4, 2, 3]])
Y = [{3, 5}, {4}, {2}, {6}]
report('profile C (core 127): strict R1-core', P.core_strict())
report('profile C: every maximum of DE4 itself is completable (%d maxima)' % len(P.maxima()),
       all(P.completable(Z) for Z in P.maxima()))
report('profile C: Y = %s is valid and has no EFX0 completion' % Y, Y in P.states and not P.completable(Y))
for tb in ['fewest lower pairs', 'fewest goods held', 'fewest holdings of two or more goods']:
    report('profile C: with the tie-break "%s", Y is a maximum' % tb, Y in P.maxima(tb))

sys.exit(0 if ok_all else 1)
