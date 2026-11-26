"""Independent raw-EFX0 library for the D1 sub-lemmas (k4/d1.md, workstream proof/k4-d1).

Written from the definitions in k4/oc1_hall.md §21 and k4/sdc.md §2, without importing k4/oc1_hall/ohlib.py or SAT.

Instances: sets[i] = the goods agent i values (at most four), vals[i] their (positive) values; every other good is
worth 0 to i.  Ties between goods are broken by good index, as in k4/sdc: i ranks g above h iff
(v_i(g), -g) > (v_i(h), -h).  Serial dictatorship uses this strict ranking.

EFX0 (raw): for all agents i != j and every good g in X_j, v_i(X_i) >= v_i(X_j - g).
"""
import itertools


class Inst:
    def __init__(self, sets, vals, m=None, name=''):
        self.name = name
        self.sets = [list(s) for s in sets]
        self.vals = [list(v) for v in vals]
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(max(s) for s in sets if s)
        self.R = [set(s) for s in sets]
        self.v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]

    def val(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)

    def rank(self, i, g):
        return (self.v[i].get(g, 0), -g)


def sd_picks(I, order):
    left = set(range(I.m)); Y = [None] * I.n
    for i in order:
        av = [g for g in I.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: I.rank(i, h)); Y[i] = g; left.discard(g)
    return tuple(Y)


def threat(I, i, t, S):
    """bundle S threatens agent i holding value t: some h in S with v_i(S - h) > t"""
    if len(S) < 2: return False
    vs = [I.v[i].get(g, 0) for g in S]
    return sum(vs) - min(vs) > t


def efx0(I, X):
    own = [I.val(i, X[i]) for i in range(I.n)]
    for j in range(I.n):
        if len(X[j]) < 2: continue
        for i in range(I.n):
            if i != j and threat(I, i, own[i], X[j]): return False
    return True


def junk_of(I, B):
    held = set(g for b in B for g in b)
    return [g for g in range(I.m) if g not in held]


def wants(I, B, i, g):
    return g not in B[i] and I.v[i].get(g, 0) > I.val(i, B[i])


def frozen(I, B):
    """single-good holders whose good some other agent wants"""
    return [j for j in range(I.n) if len(B[j]) == 1
            and any(wants(I, B, i, B[j][0]) for i in range(I.n) if i != j)]


def one_absorber(I, B, owners=None, witness=False):
    """complete EFX0 allocation keeping the bases B: one agent o takes any number of the remaining goods, every other
    agent at most one (frozen agents included).  Returns the list of working absorbers (or (o, X) with witness)."""
    J = junk_of(I, B); n = I.n; out = []
    for o in (range(n) if owners is None else owners):
        others = [i for i in range(n) if i != o]
        found = _assign(I, B, o, others, J, witness)
        if found is not None:
            if witness: return (o, found)
            out.append(o)
    return None if witness else out


def _assign(I, B, o, holders, J, witness):
    """search: each agent of `holders` gets at most one good of J (distinct); the rest goes to o; EFX0?"""
    X = [list(b) for b in B]
    hs = list(holders)
    res = [None]

    def rec(idx, left):
        if idx == len(hs):
            X[o] = list(B[o]) + sorted(left)
            if efx0(I, X):
                res[0] = [list(x) for x in X]; return True
            X[o] = list(B[o]); return False
        h = hs[idx]
        if rec(idx + 1, left): return True
        for g in sorted(left):
            X[h].append(g)
            if rec(idx + 1, left - {g}): return True
            X[h].pop()
        return False

    ok = rec(0, frozenset(J))
    return res[0] if ok else None


def sstar(I, B, o, witness=False):
    """S* completion with owner o: holders = unfrozen agents other than o with at most one good, each takes at most one
    junk good; frozen agents and multi-good holders take nothing; o takes the rest.  Raw EFX0."""
    F = set(frozen(I, B))
    holders = [j for j in range(I.n) if j != o and len(B[j]) <= 1 and j not in F]
    r = _assign(I, B, o, holders, junk_of(I, B), witness)
    if witness: return r
    return r is not None


def bases_of_picks(I, Y):
    return [[y] if y is not None else [] for y in Y]


class Start:
    """serial-dictatorship picks and their structure"""
    def __init__(self, I, Y):
        self.I = I; self.Y = Y; n = I.n
        self.B = bases_of_picks(I, Y)
        self.J = junk_of(I, self.B)
        self.p = [I.val(i, self.B[i]) for i in range(n)]
        self.W = [[i for i in range(n) if i != j and Y[j] is not None and I.v[i].get(Y[j], 0) > self.p[i]]
                  for j in range(n)]
        self.F = [j for j in range(n) if self.W[j]]
        self.D = [x for x in self.F if any(g in I.R[x] for g in self.J)]


def canonical_chains(S, k):
    """k = x_0, x_1, ..., x_t (t >= 1), distinct, each x_i wanting Y_{x_{i-1}} at the picks, head x_t unfrozen"""
    out = []
    def ext(path):
        last = path[-1]
        if len(path) >= 2 and last not in S.F: out.append(tuple(path))
        if last in S.F:
            for y in S.W[last]:
                if y not in path: ext(path + [y])
    ext([k]); return out


def pool(S, path):
    z = path[-1]
    return sorted(S.J + ([S.Y[z]] if S.Y[z] is not None else []))


def minimal_improving(S, k, Pi):
    I = S.I
    Pk = [g for g in Pi if g in I.R[k]]
    imp = [frozenset(H) for r in range(1, len(Pk) + 1) for H in itertools.combinations(Pk, r) if I.val(k, H) > S.p[k]]
    return [H for H in imp if not any(K < H for K in imp)]


def apply_chain(S, path, H0):
    """bases after the chain: x_i takes Y_{x_{i-1}} alone, k takes H0, Y_{x_t} is released"""
    B = [list(b) for b in S.B]
    Y = S.Y
    for i in range(len(path) - 1, 0, -1):
        B[path[i]] = [Y[path[i - 1]]]
    B[path[0]] = sorted(H0)
    return B


def obstacles(S, path, H0, B2=None):
    """HEAD and CROWD of k4/oc1_hall.md §21 at the state after (path, H0), owner k = path[0]"""
    I = S.I; k = path[0]; z = path[-1]
    if B2 is None: B2 = apply_chain(S, path, H0)
    F2 = set(frozen(I, B2)); Pi = pool(S, path)
    pv2 = [I.val(i, B2[i]) for i in range(I.n)]
    head = z in F2 and threat(I, z, pv2[z], Pi)
    crowded = []
    for u in range(I.n):
        if u == k or u in F2 or len(B2[u]) > 1: continue
        Hu = [g for g in H0 if g in I.R[u]]
        if len(Hu) >= 2 and I.val(u, Hu) > pv2[u]: crowded.append(u)
    return head, crowded, F2
