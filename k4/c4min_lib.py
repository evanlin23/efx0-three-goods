"""c4min_lib: valid pre-allocations of a strict k = 4 core profile, written from the definitions of k4/c4x.md §1
(PR #36) and k4/lb4.md §1, for the analysis in k4/c4min.md. Independent of k4/c4x.c (no code shared).

A profile is a list of dicts {good: value} (strict: all nonempty subset sums of each agent distinct; balanced).
A pre-allocation is a tuple of bases (frozensets), B_i ⊆ R_i, |B_i| <= 2, pairwise disjoint.
  needs(i, B)  = {g in R_i \\ B : v_i(g) > v_i(B)}   (value-based, the smallest allowed)
  valid        : every needed good is a one-good base  ((V1) and (V2) together)
  frozen       : |B_i| = 1 and B_i ⊆ NA
  cap(i)       : 0 if frozen, else 2 - |B_i|
  omega        : |J| - S = |F| - (2n - m)
  deficit      : k4/c4x.md §1 (removal-only, owner's needs from its bundle)
  completable  : exact test (Lean's SoundCompletion with ownerNeeds)."""
import gzip, itertools, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

INF = 1 << 20


def load_cores(path):
    data = json.load(gzip.open(path, 'rt'))
    cores = data['cores'] if isinstance(data, dict) else data
    return [(c['n'], c['m'], [list(S) for S in (c['sets'] if 'sets' in c else c['edges'])]) for c in cores]


_DOM = {}
def domains(sets, m):
    """Strict balanced types per agent (integer representatives), as every k = 4 tool uses (k4/check4.py)."""
    key = (tuple(map(tuple, sets)), m)
    if key not in _DOM:
        from check4 import core_domains
        _DOM[key] = core_domains(sets, m, False)
    return _DOM[key]


def v(val, S):
    return sum(val.get(g, 0) for g in S)


def needs(val, B):
    b = v(val, B)
    return frozenset(g for g in val if g not in B and val[g] > b)


def threatened(val, X, B):
    """Agent with values val holding B strongly envies bundle X: max_h v(X \\ h) > v(B)."""
    if len(X) == 0: return False
    tot = v(val, X)
    mn = min(val.get(h, 0) for h in X)
    return tot - mn > v(val, B)


class Profile:
    def __init__(self, vals, m):
        self.vals = vals; self.n = len(vals); self.m = m
        self.R = [frozenset(x) for x in vals]
        self.opts = []
        for i, val in enumerate(vals):
            gs = sorted(val)
            o = [frozenset()] + [frozenset([g]) for g in gs] + [frozenset(p) for p in itertools.combinations(gs, 2)]
            self.opts.append([(B, needs(val, B)) for B in o])

    def valid(self):
        """All valid pre-allocations, as tuples of bases."""
        out = []
        n = self.n
        def rec(i, used, sing, two, NA, cur):
            if i == n:
                if NA <= sing: out.append(tuple(cur))
                return
            for B, N in self.opts[i]:
                if B & used: continue
                NA2 = NA | N
                sing2 = sing | B if len(B) == 1 else sing
                two2 = two | B if len(B) == 2 else two
                if NA2 & two2: continue
                cur.append(B); rec(i + 1, used | B, sing2, two2, NA2, cur); cur.pop()
        rec(0, frozenset(), frozenset(), frozenset(), frozenset(), [])
        return out

    def info(self, P):
        n = self.n
        N = [needs(self.vals[i], P[i]) for i in range(n)]
        NA = frozenset().union(*N)
        used = frozenset().union(*P)
        J = frozenset(range(self.m)) - used
        F = [len(P[i]) == 1 and P[i] <= NA for i in range(n)]
        cap = [0 if F[i] else 2 - len(P[i]) for i in range(n)]
        return N, NA, J, F, cap

    def nfrozen(self, P):
        return sum(self.info(P)[3])

    def owner_split(self, P, o, Xo, N):
        """Slots of the agents other than o, frozen status with the owner's needs from its bundle Xo."""
        val = self.vals[o]; x = v(val, Xo)
        No = frozenset(g for g in val if g not in Xo and val[g] > x)
        NA = No.union(*[N[j] for j in range(self.n) if j != o])
        caps = {}
        for j in range(self.n):
            if j == o: continue
            fz = len(P[j]) == 1 and P[j] <= NA
            caps[j] = 0 if fz else 2 - len(P[j])
        return caps

    def deficit(self, P, want_witness=False):
        """k4/c4x.md §1: |J| - S if <= 0; else min over free owners o and C ⊆ J with B_o ∪ (J \\ C) threatening
        nobody holding its base alone, of |C| - S_o(C). INF if no such (o, C)."""
        N, NA, J, F, cap = self.info(P)
        S = sum(cap)
        if len(J) <= S: return (len(J) - S, None) if want_witness else len(J) - S
        best, wit = INF, None
        Jl = sorted(J)
        for o in range(self.n):
            if F[o]: continue
            for r in range(len(Jl) + 1):
                for C in itertools.combinations(Jl, r):
                    C = frozenset(C)
                    Xo = P[o] | (J - C)
                    if any(threatened(self.vals[x], Xo, P[x]) for x in range(self.n) if x != o): continue
                    caps = self.owner_split(P, o, Xo, N)
                    d = len(C) - sum(caps.values())
                    if d < best: best, wit = d, (o, C)
        return (best, wit) if want_witness else best

    def completable(self, P):
        """Exact test: owner o (free) or none; the owner keeps K ⊆ J; the rest fits the others' slots (frozen status
        from the owner's needs from X_o); every agent threatened by X_o with its base gets a protecting set of the rest
        within its slots, pairwise disjoint."""
        N, NA, J, F, cap = self.info(P)
        if len(J) <= sum(cap): return (None, J)
        Jl = sorted(J)
        for o in range(self.n):
            if F[o]: continue
            for r in range(len(Jl) + 1):
                for K in itertools.combinations(Jl, r):
                    K = frozenset(K); Xo = P[o] | K; rest = J - K
                    caps = self.owner_split(P, o, Xo, N)
                    if len(rest) > sum(caps.values()): continue
                    thr = [x for x in range(self.n) if x != o and threatened(self.vals[x], Xo, P[x])]
                    if any(caps[x] == 0 for x in thr): continue
                    if self._protect(thr, 0, rest, Xo, P, caps): return (o, K)
        return False

    def _protect(self, thr, k, rest, Xo, P, caps):
        if k == len(thr): return True
        x = thr[k]; val = self.vals[x]
        avail = sorted(rest & self.R[x])
        for r in range(1, min(caps[x], len(avail)) + 1):
            for C in itertools.combinations(avail, r):
                if not threatened(val, Xo, P[x] | frozenset(C)) and self._protect(thr, k + 1, rest - frozenset(C), Xo, P, caps):
                    return True
        return False


def profiles(sets, m, rng=None, count=None):
    """All strict profiles (itertools.product over the domains), or `count` random ones."""
    D = domains(sets, m)
    if count is None:
        for combo in itertools.product(*D): yield [dict(x) for x in combo]
    else:
        for _ in range(count): yield [dict(rng.choice(Dk)) for Dk in D]


def fmt_profile(pr):
    return ' '.join('[' + ','.join(f'{g}:{val[g]}' for g in sorted(val)) + ']' for val in pr.vals)


def fmt_P(P, J=None):
    s = ' | '.join('{' + ','.join(map(str, sorted(B))) + '}' for B in P)
    if J is not None: s += '  J {' + ','.join(map(str, sorted(J))) + '}'
    return s
