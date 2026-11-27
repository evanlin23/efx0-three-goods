"""Replays the refuted state spaces of attempts/k4-de4-ss.md from the definitions, by brute force (no SAT, no code
shared with ss_screen.py, de4lib.py or the C programs). For each variant and its smallest failing instance found: the
instance is a strict R1-core profile, the state Y is valid in the variant, no valid state of the variant is better
(level sum, then value-Pareto), and no assignment of the leftover goods gives an EFX0 allocation.
Prints 'confirmed' or 'NOT confirmed' per claim; exit status 0 iff all are confirmed.  python3 k4/de4/refute_ss.py"""
import itertools
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ok_all = True


def report(name, ok):
    global ok_all
    ok_all &= ok
    print(('confirmed    ' if ok else 'NOT confirmed') + ' ' + name)


def subsets(xs):
    return [set(c) for r in range(len(xs) + 1) for c in itertools.combinations(sorted(xs), r)]


class Space:
    """levels of the multi-good holding types allowed; 'U' (upper sets) always allowed at 5.
    Types of a 4-good agent a > b > c > d: LP = {c, d} with b < c + d < a; CD = {c, d} with c + d < b;
    BC = {b, c}, BD = {b, d} worth less than a. Extra rules: 'v3' (a holder of its lower pair has its b held by some
    agent), 'v3f' (... held alone by an agent; with (V1) this agent is frozen if someone wants b)."""

    def __init__(self, R, M, vals, lev, rules=()):
        self.R, self.M, self.N = R, M, len(R)
        self.v = [dict(zip(R[i], vals[i])) for i in range(self.N)]
        self.ranked = [sorted(R[i], key=lambda g: -self.v[i][g]) for i in range(self.N)]
        self.lev, self.rules = dict(lev), set(rules)
        opts = [[S for S in subsets(R[i]) if self.kind(i, S) is not None] for i in range(self.N)]
        self.states = [list(Y) for Y in itertools.product(*opts)
                       if sum(map(len, Y)) == len(set().union(*Y)) and self.valid(list(Y))]

    def val(self, i, S):
        return sum(self.v[i].get(g, 0) for g in S)

    def kind(self, i, S):
        r, v = self.ranked[i], self.v[i]
        if not S <= set(r):
            return None
        if len(S) <= 1:
            return 'single'
        top, x = v[r[0]], self.val(i, S)
        if x > top and all(x - v[h] <= top for h in S):
            return 'U'
        t = None
        if len(r) == 4:
            a, b, c, d = r
            if S == {c, d}:
                t = 'LP' if v[b] < x < top else ('CD' if x < v[b] else None)
            elif S == {b, c} and x < top:
                t = 'BC'
            elif S == {b, d} and x < top:
                t = 'BD'
        return t if t in self.lev else None

    def level(self, i, S):
        k = self.kind(i, S)
        if k == 'single':
            return 4 - self.ranked[i].index(next(iter(S))) if S else 0
        return 5 if k == 'U' else self.lev[k]

    def theta(self, i, B):
        return max((self.val(i, B - {h}) for h in B), default=0)

    def valid(self, Y):
        alone = {next(iter(S)) for S in Y if len(S) == 1}
        wanted = {g for i in range(self.N) for g in self.R[i] if g not in Y[i] and self.v[i][g] > self.val(i, Y[i])}
        if not wanted <= alone:
            return False
        if not all(self.theta(i, Y[j]) <= self.val(i, Y[i]) for i in range(self.N) for j in range(self.N) if i != j):
            return False
        held = set().union(*Y)
        for i in range(self.N):
            if self.kind(i, Y[i]) == 'LP':
                b = self.ranked[i][1]
                if 'v3' in self.rules and b not in held:
                    return False
                if 'v3f' in self.rules and {b} not in Y:
                    return False
        return True

    def core_strict(self):
        return all(len(self.R[i]) in (3, 4) and 2 * self.v[i][self.ranked[i][0]] < self.val(i, self.R[i])
                   and len({self.val(i, S) for S in subsets(self.R[i])}) == 2 ** len(self.R[i]) for i in range(self.N))

    def phi(self, Y):
        return sum(self.level(i, Y[i]) for i in range(self.N))

    def better(self, Z, Y):
        if self.phi(Z) != self.phi(Y):
            return self.phi(Z) > self.phi(Y)
        a, b = [self.val(i, Z[i]) for i in range(self.N)], [self.val(i, Y[i]) for i in range(self.N)]
        return all(x >= y for x, y in zip(a, b)) and a != b

    def completable(self, Y):
        J = [g for g in range(self.M) if not any(g in S for S in Y)]
        for owners in itertools.product(range(self.N), repeat=len(J)):
            X = [set(S) for S in Y]
            for g, o in zip(J, owners):
                X[o].add(g)
            if all(self.theta(i, X[j]) <= self.val(i, X[i]) for i in range(self.N) for j in range(self.N) if i != j):
                return True
        return False


def suite(name):
    d = json.load(open(os.path.join(ROOT, 'k4', 'suite', 'instances', name + '.json')))
    return d['sets'], d['m'], d['vals']


INST = {
    'A131 (n = 4, m = 7)': ([[0, 2, 4, 6], [1, 3, 5, 6], [2, 3, 6], [4, 5, 6]], 7,
                            [[3, 8, 2, 4], [3, 2, 8, 4], [4, 2, 3], [2, 4, 3]]),
    'D3 (n = 3, m = 6)': ([[0, 1, 2, 4], [1, 2, 3, 5], [2, 3, 4, 5]], 6, [[4, 8, 3, 2], [8, 4, 3, 2], [10, 7, 2, 4]]),
    'GM4-A (n = 4, m = 7)': ([[0, 2, 5, 6], [1, 4, 5, 6], [2, 3, 5, 6], [3, 4, 5, 6]], 7,
                             [[3, 6, 2, 10], [1, 6, 8, 4], [2, 7, 8, 4], [6, 3, 4, 8]]),
    'induct-pot-nash (n = 3, m = 6)': suite('induct-pot-nash'),
    'R4 (n = 4, m = 9)': ([[6, 0, 1, 8], [2, 0, 1, 3], [2, 4, 5, 8], [6, 4, 5, 7]], 9,
                          [[20, 13, 12, 9], [20, 13, 12, 2], [20, 13, 12, 9], [20, 13, 12, 2]]),
}
CASES = [   # (variant, levels, rules, instance, failing maximum, is it the only kind: every maximum fails?)
    ('DE4 + v3f', {'LP': 3}, ['v3f'], 'D3 (n = 3, m = 6)', [{1}, {2}, {3, 5}]),
    ('lower pair at level 2.5', {'LP': 2.5}, [], 'D3 (n = 3, m = 6)', [{1}, {2}, {3, 5}]),
    ('lower pair at level 2.5, + v3', {'LP': 2.5}, ['v3'], 'D3 (n = 3, m = 6)', [{1}, {2}, {3, 5}]),
    ('no lower pair', {}, [], 'D3 (n = 3, m = 6)', [{1}, {2}, {3, 5}]),
    ('{b, c}, {b, d} at level 3.5, no lower pair', {'BC': 3.5, 'BD': 3.5}, [], 'induct-pot-nash (n = 3, m = 6)', [{4}, {5}, {3}]),
    ('lower pair, {b, c}, {b, d} at level 3.5', {'LP': 3, 'BC': 3.5, 'BD': 3.5}, [], 'GM4-A (n = 4, m = 7)', [{0, 2}, {1, 4}, {5}, {6}]),
    ('lower pair + v3, {b, c}, {b, d} at level 3.5', {'LP': 3, 'BC': 3.5, 'BD': 3.5}, ['v3'], 'GM4-A (n = 4, m = 7)', [{0, 2}, {1, 4}, {5}, {6}]),
    ('lower pair at level 3.5', {'LP': 3.5}, [], 'A131 (n = 4, m = 7)', [{0, 4}, {1, 3}, {2}, {5}]),
    ('lower pair, {c, d} below b at level 2.5', {'LP': 3, 'CD': 2.5}, [], 'A131 (n = 4, m = 7)', [{0, 4}, {1, 3}, {2}, {5}]),
    ('DE4 + v3 (Conjecture DE4^v3)', {'LP': 3}, ['v3'], 'R4 (n = 4, m = 9)', [{0, 1}, {2, 3}, {4, 5}, {6, 7}]),
    ('DE4 + v3 + CD at level 2.5', {'LP': 3, 'CD': 2.5}, ['v3'], 'R4 (n = 4, m = 9)', [{0, 1}, {2, 3}, {4, 5}, {6, 7}]),
    ('DE4', {'LP': 3}, [], 'R4 (n = 4, m = 9)', [{0, 1}, {2, 3}, {4, 5}, {6, 7}]),
]
for var, lev, rules, iname, Y in CASES:
    R, M, vals = INST[iname]
    P = Space(R, M, vals, lev, rules)
    mx = [Z for Z in P.states if not any(P.better(W, Z) for W in P.states)]
    good = P.core_strict() and Y in P.states and Y in mx and not P.completable(Y)
    report('%s: on %s the maximum %s has no EFX0 completion (%d maxima, %d completable)'
           % (var, iname, Y, len(mx), sum(P.completable(Z) for Z in mx)), good)
sys.exit(0 if ok_all else 1)
