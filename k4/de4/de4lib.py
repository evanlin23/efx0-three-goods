"""DE4: a Draft-and-Exchange style state space and potential for k = 4 (workstream proof/k4-de4, k4/de4.md).

Written from the definitions of k4/de4.md §1; shares no code with the other k = 4 tools. The C program de4.c is a
second implementation of the same definitions (cross-checked by check.py --xcheck).

Objects (agent i, relevant goods R_i, |R_i| in {3, 4}, ranked a > b > c (> d) by value, ties by good index):
- holdings: empty; a single good of R_i; an *upper set* (minimal set of R_i worth more than a: v(S) > v(a) and every
  proper subset worth <= v(a)); the *lower pair* {c, d} of a 4-good agent when v(b) < v(c) + v(d) < v(a);
- level: empty 0, a 4, b 3, c 2, d 1, lower pair 3, upper set 5;
- wanted goods of i: goods of R_i outside the holding worth strictly more than the holding;
- a state is valid if (V1) every wanted good is the whole holding of some agent and (V2) no holding threatens another
  agent (exact EFX0 threat of the holding as a bundle);
- completion: every leftover good is given to some agent; completable if some completion is EFX0;
- maxima: valid states of largest level sum, then value-Pareto-maximal among those.
"""
import gzip
import itertools
import json
import random

from pysat.solvers import Minisat22
from pysat.card import CardEnc


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


class Inst:
    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(g for S in sets for g in S)
        self.sets = [list(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]

    @classmethod
    def from_json(cls, d):
        return cls(d['sets'], d['vals'], d.get('m'))

    def val(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)

    def theta(self, i, B):
        """max over h in B of v_i(B minus h); 0 for |B| <= 1"""
        if len(B) <= 1:
            return 0
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in B) - min(vi.get(g, 0) for g in B)

    def ranked(self, i):
        return sorted(self.sets[i], key=lambda g: (-self.v[i][g], g))


def efx0(I, X):
    for i in range(I.n):
        vi = I.val(i, X[i])
        for j in range(I.n):
            if i != j and I.theta(i, X[j]) > vi:
                return False
    return True


def bundles(I, own):
    X = [[] for _ in range(I.n)]
    for g, o in enumerate(own):
        X[o].append(g)
    return X


# ---------------------------------------------------------------- types and profiles
def strict_types(k, maxv=16):
    """One integer representative (values descending) per strict balanced additive order type of k goods."""
    reps = {}
    for vals in itertools.combinations(range(maxv, 0, -1), k):
        vals = list(vals)
        if vals[0] >= sum(vals[1:]):
            continue
        sums = {S: sum(vals[t] for t in S) for S in subsets(range(k))}
        if len(set(sums.values())) != len(sums):
            continue
        key = tuple(sums[S] > sums[T] for S in sums if S for T in sums if T and not set(S) & set(T))
        if key not in reps or max(vals) < max(reps[key]):
            reps[key] = vals
    return sorted(reps.values())


TYPES = {3: strict_types(3), 4: strict_types(4)}       # 1 and 12 types (per ranking)


def type_options(S):
    """all strict balanced profiles of one agent with goods S: (types) x (rankings); 6 for 3 goods, 288 for 4"""
    out = []
    for T in TYPES[len(S)]:
        for perm in itertools.permutations(S):
            d = dict(zip(perm, T))
            out.append([d[g] for g in S])
    return out


def random_profile(sets, rng):
    vals = []
    for S in sets:
        T = rng.choice(TYPES[len(S)])
        perm = list(S)
        rng.shuffle(perm)
        d = dict(zip(perm, T))
        vals.append([d[g] for g in S])
    return vals


def load_cores(path):
    return [c['sets'] for c in json.load(gzip.open(path))['cores']]


# ---------------------------------------------------------------- holdings, levels, validity
def is_upper(I, i, A):
    top = I.v[i][I.ranked(i)[0]]
    if len(A) < 2 or I.val(i, A) <= top:
        return False
    return all(I.val(i, [g for g in A if g != h]) <= top for h in A)


def is_lower_pair(I, i, A):
    r = I.ranked(i)
    return (len(r) == 4 and len(A) == 2 and set(A) == {r[2], r[3]}
            and I.v[i][r[1]] < I.val(i, A) < I.v[i][r[0]])


def allowed(I, i, A):
    return len(A) <= 1 or is_upper(I, i, A) or is_lower_pair(I, i, A)


def level(I, i, A):
    if not A:
        return 0
    if len(A) == 1:
        return 4 - I.ranked(i).index(A[0])
    return 5 if is_upper(I, i, A) else 3


def wanted(I, i, A):
    vA = I.val(i, A)
    return [g for g in I.sets[i] if g not in A and I.v[i][g] > vA]


def wanted_goods(I, Y):
    W = set()
    for i in range(I.n):
        W |= set(wanted(I, i, Y[i]))
    return W


def leftover(I, Y):
    held = set(g for A in Y for g in A)
    return [g for g in range(I.m) if g not in held]


def valid(I, Y):
    alone = set(A[0] for A in Y if len(A) == 1)
    if not wanted_goods(I, Y) <= alone:
        return False
    for j in range(I.n):
        if len(Y[j]) < 2:
            continue
        for i in range(I.n):
            if i != j and I.theta(i, Y[j]) > I.val(i, Y[i]):
                return False
    return True


def all_states(I):
    opts = [[A for A in subsets(I.sets[i]) if allowed(I, i, A)] for i in range(I.n)]
    res = []

    def rec(i, used, Y):
        if i == I.n:
            if valid(I, Y):
                res.append(list(Y))
            return
        for A in opts[i]:
            if used.isdisjoint(A):
                Y.append(A)
                rec(i + 1, used | set(A), Y)
                Y.pop()
    rec(0, set(), [])
    return res


def levsum(I, Y):
    return sum(level(I, i, Y[i]) for i in range(I.n))


def values(I, Y):
    return [I.val(i, Y[i]) for i in range(I.n)]


def pareto_max(I, states):
    vecs = [tuple(values(I, Y)) for Y in states]
    order = sorted(range(len(states)), key=lambda k: -sum(vecs[k]))
    keep = []
    for k in order:
        if not any(all(a >= b for a, b in zip(vecs[l], vecs[k])) and vecs[l] != vecs[k] for l in keep):
            keep.append(k)
    return [states[k] for k in keep]


def maxima(I, states, pot=levsum):
    if not states:
        return []
    best = max(pot(I, Y) for Y in states)
    return pareto_max(I, [Y for Y in states if pot(I, Y) == best])


# ---------------------------------------------------------------- completions
class EFXSearch:
    """Exact EFX0 search (SAT). Clauses forbid, for agents i != j, every configuration (X_i ∩ R_i ⊆ A, X_j ⊇ B)
    with threat > v_i(A); the junk case uses an indicator that X_j has a good outside R_i."""

    def __init__(self, I):
        self.I = I
        n, m = I.n, I.m
        self.nv = 0
        self.x = [[self.new() for _ in range(n)] for _ in range(m)]
        self.cl = []
        for g in range(m):
            self.cl.append([self.x[g][i] for i in range(n)])
            for i in range(n):
                for j in range(i + 1, n):
                    self.cl.append([-self.x[g][i], -self.x[g][j]])
        for i in range(n):
            Ri = I.sets[i]
            out = [g for g in range(m) if g not in I.v[i]]
            for j in range(n):
                if i == j:
                    continue
                Jij = self.new()
                for g in out:
                    self.cl.append([-self.x[g][j], Jij])
                for A in subsets(Ri):
                    vA = I.val(i, A)
                    rest = [g for g in Ri if g not in A]
                    for B in subsets(rest):
                        if not B:
                            continue
                        vB = I.val(i, B)
                        base = [self.x[g][i] for g in rest] + [-self.x[g][j] for g in B]
                        if vB - min(I.v[i][g] for g in B) > vA:
                            self.cl.append(base)
                        elif vB > vA:
                            self.cl.append(base + [-Jij])

    def new(self):
        self.nv += 1
        return self.nv

    def solve(self, extra=()):
        with Minisat22(bootstrap_with=self.cl + list(extra)) as s:
            if not s.solve():
                return None
            model = set(l for l in s.get_model() if l > 0)
            return [next(i for i in range(self.I.n) if self.x[g][i] in model) for g in range(self.I.m)]


def completion(I, Y):
    """an EFX0 allocation X with X_i ⊇ Y_i (leftover goods to any agents), or None"""
    S = EFXSearch(I)
    units = [[S.x[g][j]] for j, A in enumerate(Y) for g in A]
    own = S.solve(units)
    return bundles(I, own) if own is not None else None


def de_finish(I, Y):
    """DE's finishing rule: one owner o (free) takes the leftovers except a set H; each other free agent with at most
    one good takes at most one good of H. Returns an EFX0 allocation or None."""
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    free = [i for i in range(I.n) if not set(Y[i]) & W]
    recv_all = [i for i in free if len(Y[i]) <= 1]
    if not J:
        X = [list(A) for A in Y]
        return X if efx0(I, X) else None
    for o in free:
        recv = [i for i in recv_all if i != o]
        for r in range(min(len(recv), len(J)) + 1):
            for H in itertools.combinations(J, r):
                for assign in itertools.permutations(recv, r):
                    X = [list(A) for A in Y]
                    for g, i in zip(H, assign):
                        X[i].append(g)
                    X[o] += [g for g in J if g not in H]
                    if efx0(I, X):
                        return X
    return None


# ---------------------------------------------------------------- moves (k4/de4.md §3)
def upgrades(I, x, pool, Yx, must=None):
    """allowed holdings N ⊆ pool ∩ R_x worth more than Y_x (meeting `must` if given), smallest first"""
    cand = [g for g in pool if g in I.v[x]]
    vY = I.val(x, Yx)
    out = [N for N in subsets(cand) if N and I.val(x, N) > vY and allowed(I, x, N)
           and (must is None or set(N) & set(must))]
    return sorted(out, key=len)


def apply_takes(I, Y, takes):
    Z = [tuple(A) for A in Y]
    for i, N in takes.items():
        Z[i] = tuple(N)
    goods = [g for A in Z for g in A]
    return Z if len(goods) == len(set(goods)) else None


def want_path(I, Y, x):
    """DE's chain from x: while j_t holds a wanted single, j_{t+1} = the first agent wanting it.
    ('ring', agents from the first repeat) or ('path', path)."""
    W = wanted_goods(I, Y)
    path = [x]
    while len(Y[path[-1]]) == 1 and Y[path[-1]][0] in W:
        g = Y[path[-1]][0]
        j = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
        if j in path:
            return 'ring', path[path.index(j):]
        path.append(j)
    return 'path', path


def chain_move(I, Y):
    """Lemma 4 of k4/de4.md: an agent with an allowed upgrade inside J (plus its own holding if free) takes it, and its
    good passes down the first-wanter path (or the want-ring that path closes is traded). First valid result or None."""
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    for x in range(I.n):
        free = not set(Y[x]) & W
        for N in upgrades(I, x, J + (list(Y[x]) if free else []), Y[x]):
            kind, p = want_path(I, Y, x) if not free else ('path', [x])
            if kind == 'ring':
                takes = {p[t + 1]: Y[p[t]] for t in range(len(p) - 1)}
                takes[p[0]] = Y[p[-1]]
            else:
                takes = {x: N}
                for t in range(1, len(p)):
                    takes[p[t]] = Y[p[t - 1]]
            Z = apply_takes(I, Y, takes)
            if Z and valid(I, Z):
                return Z
    return None


def pointer_ring(I, Y, keep_own=False, lazy=True, f1_only=False):
    """DE's pointers: a frozen agent points to the first agent wanting its good; a free agent to a blocker whose upgrade
    uses its holding and leftover goods not used before (and the blocker's own holding if keep_own and the blocker is
    free). lazy: assign along the walk, from every start; else DE's global greedy over the free agents in index order.
    Returns a valid traded state or None."""
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    F = [i for i in range(I.n) if not set(Y[i]) & W]

    def arc(o, used):
        best = None
        for x in range(I.n):
            if x == o:
                continue
            own = list(Y[x]) if keep_own and not set(Y[x]) & W else []
            for N in upgrades(I, x, list(Y[o]) + [g for g in J if g not in used] + own, Y[x], must=Y[o]):
                k = len(set(N) & set(J))
                if best is None or k < best[0]:
                    best = (k, x, N)
        return best

    def walk(start, sigma, take, assign):
        used = set()
        path, pos = [], {}
        j = start
        while j not in pos:
            pos[j] = len(path)
            path.append(j)
            if j not in sigma:
                if not Y[j] or not assign:
                    return None
                if set(Y[j]) & W:
                    g = Y[j][0]
                    sigma[j] = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
                    take[j] = (g,)
                else:
                    b = arc(j, used)
                    if b is None:
                        return None
                    _, x, N = b
                    sigma[j], take[j] = x, N
                    used |= set(N) & set(J)
            j = sigma[j]
        cyc = path[pos[j]:]
        Z = apply_takes(I, Y, {sigma[w]: take[w] for w in cyc})
        return Z if Z is not None and valid(I, Z) else None

    if not lazy and f1_only:
        # DE's pointers proper: distinct leftover goods for the free agents holding at most one good (index order);
        # a free agent holding two or more goods gets its pointer only if the walk reaches it (leftover goods not used)
        sigma, take, used = {}, {}, set()
        for o in F:
            if len(Y[o]) > 1:
                continue
            if not Y[o]:
                return None
            b = arc(o, used)
            if b is None:
                return None
            _, x, N = b
            sigma[o], take[o] = x, N
            used |= set(N) & set(J)
        for j in range(I.n):
            if j not in sigma and len(Y[j]) == 1 and Y[j][0] in W:
                g = Y[j][0]
                sigma[j] = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
                take[j] = (g,)
        start = next((j for j in range(I.n) if len(Y[j]) == 1), None)
        if start is None:       # nobody holds a single good: start at the first free agent
            start = next((j for j in F if Y[j]), None)
            if start is None:
                return None
        path, pos, j = [], {}, start
        while j not in pos:
            pos[j] = len(path)
            path.append(j)
            if j not in sigma:
                b = arc(j, used)
                if b is None:
                    return None
                _, x, N = b
                sigma[j], take[j] = x, N
                used |= set(N) & set(J)
            j = sigma[j]
        Z = apply_takes(I, Y, {sigma[w]: take[w] for w in path[pos[j]:]})
        return Z if Z is not None and valid(I, Z) else None
    if not lazy:
        sigma, take, used = {}, {}, set()
        for o in F:
            if not Y[o]:
                return None
            b = arc(o, used)
            if b is None:
                return None
            _, x, N = b
            sigma[o], take[o] = x, N
            used |= set(N) & set(J)
        for j in range(I.n):
            if j not in sigma and Y[j]:
                g = Y[j][0]
                sigma[j] = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
                take[j] = (g,)
        start = next((j for j in range(I.n) if Y[j]), None)
        return None if start is None else walk(start, sigma, take, False)
    for start in range(I.n):
        if Y[start]:
            Z = walk(start, {}, {}, True)
            if Z is not None:
                return Z
    return None
