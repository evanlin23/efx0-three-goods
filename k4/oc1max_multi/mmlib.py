"""Shared code for workstream proof/k4-oc1max-multi (k4/oc1max_multi.md): OC1 at perfect starts with two or more
dangerous agents.  Written from the definitions, independent of k4/oc1_hall/ohlib.py and k4/sdc (no SAT).

Definitions (k4/sdc.md §29-§31, k4/oc1_hall.md):
  * an instance: sets[i] = the goods agent i values, vals[i] the values (additive); ties broken by good index, an
    agent ranks g above h iff (v(g), -g) > (v(h), -h) (the convention of k4/sdc and ohlib);
  * the picks of an order: serial dictatorship; J = the unpicked goods (junk);
  * a *perfect start*: every agent with a relevant good holds a pick (null agents allowed);
  * i *wants* g (held by another agent) if v_i(g) > v_i(B_i); F = frozen agents (single-good holders whose good
    someone wants); D = dangerous agents (frozen agents valuing a junk good);
  * raw EFX0: for all i != j and every g in X_j, v_i(X_i) >= v_i(X_j - g) (goods of value 0 included);
  * a *one-absorber completion* of bases B: a complete EFX0 allocation that keeps every base and gives at most one
    agent (the absorber) two or more junk goods;
  * an *S* completion with owner o*: the holders (agents other than o with at most one base good that nobody wants)
    take at most one junk good each, every other agent other than o takes none, o takes the rest;
  * *moves* (k4/sdc.md §29, official rule): additions (an agent adds junk it values), improving chains
    x_0..x_t (t >= 1; x_0 takes H_0 from J + B_{x_t}; x_i takes B_{x_{i-1}} + H_i, H_i junk; a chain never hands on
    an empty base; every agent on it strictly gains), and rings.
"""
import itertools, collections, json, os


class Inst:
    def __init__(self, sets, vals, m=None, name=''):
        self.name = name
        self.sets = [list(s) for s in sets]; self.vals = [list(x) for x in vals]
        self.n = len(sets)
        self.m = m if m is not None else 1 + max((max(s) for s in sets if s), default=-1)
        self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
        self.R = [frozenset(s) for s in sets]

    def V(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)

    def rk(self, i, g):
        return (self.v[i][g], -g)

    def sd(self, order):
        taken = set(); Y = [None] * self.n
        for i in order:
            av = [g for g in self.R[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: self.rk(i, h)); Y[i] = g; taken.add(g)
        return tuple(Y)

    def efx0(self, X):
        own = [self.V(i, X[i]) for i in range(self.n)]
        for j in range(self.n):
            if len(X[j]) < 2: continue
            for i in range(self.n):
                if i == j: continue
                vs = [self.v[i].get(g, 0) for g in X[j]]
                if sum(vs) - min(vs) > own[i]: return False
        return True

    def threat(self, i, t, S):
        """the bundle S threatens agent i holding value t: some h in S with v_i(S - h) > t"""
        if len(S) < 2: return False
        vs = [self.v[i].get(g, 0) for g in S]
        return sum(vs) - min(vs) > t

    def to_json(self):
        return {'name': self.name, 'sets': self.sets, 'vals': self.vals, 'm': self.m}


# ------------------------------------------------------------------------------------------------ states
def base_from_picks(Y):
    return tuple((y,) if y is not None else () for y in Y)


def junk(I, base):
    used = set(g for b in base for g in b)
    return [g for g in range(I.m) if g not in used]


def frozen(I, base):
    """single-good holders whose good some other agent wants"""
    n = I.n; val = [I.V(i, base[i]) for i in range(n)]
    return [j for j in range(n) if len(base[j]) == 1 and
            any(i != j and I.v[i].get(base[j][0], 0) > val[i] for i in range(n))]


def wanters(I, base, j):
    val = [I.V(i, base[i]) for i in range(I.n)]
    return [i for i in range(I.n) if i != j and base[j] and len(base[j]) == 1 and I.v[i].get(base[j][0], 0) > val[i]]


def dangerous(I, base):
    J = set(junk(I, base))
    return [x for x in frozen(I, base) if any(g in J for g in I.R[x])]


# ------------------------------------------------------------------------------------------------ completions
def oa_absorbers(I, base, want_witness=False, owners=None):
    """one-absorber completions of the bases, by enumeration from the definition.  Returns the set of agents a such
    that some one-absorber completion gives every junk good not given to a to a distinct other agent (at most one
    each) and the rest to a (a may receive 0 or 1 too: then the completion has no absorber).  With want_witness,
    a dict a -> allocation."""
    n = I.n; J = junk(I, base); out = {}
    for a in (owners if owners is not None else range(n)):
        others = [i for i in range(n) if i != a]
        found = None
        for r in range(min(len(J), len(others)) + 1):
            for K in itertools.combinations(J, r):
                rest = [g for g in J if g not in K]
                for who in itertools.permutations(others, r):
                    X = [list(b) for b in base]
                    for g, i in zip(K, who): X[i].append(g)
                    X[a] += rest
                    if I.efx0(X): found = X; break
                if found: break
            if found: break
        if found: out[a] = found
    return out if want_witness else set(out)


def holders(I, base, o):
    F = set(frozen(I, base))
    return [i for i in range(I.n) if i != o and len(base[i]) <= 1 and i not in F]


def sstar(I, base, o, witness=False):
    """S* completion with owner o (holders: unfrozen agents with at most one base good)"""
    J = junk(I, base); hs = holders(I, base, o)
    for r in range(min(len(J), len(hs)) + 1):
        for K in itertools.combinations(J, r):
            rest = [g for g in J if g not in K]
            for who in itertools.permutations(hs, r):
                X = [list(b) for b in base]
                for g, i in zip(K, who): X[i].append(g)
                X[o] += rest
                if I.efx0(X): return X if witness else True
    return None if witness else False


def sstar_owners(I, base, owners=None):
    return set(o for o in (owners if owners is not None else range(I.n)) if sstar(I, base, o))


# ------------------------------------------------------------------------------------------------ moves
def _subsets(xs, minr=0):
    for r in range(minr, len(xs) + 1):
        yield from itertools.combinations(xs, r)


def moves(I, base, max_len=None):
    """every official move from the bases, with descriptions.  Returns dict newbase -> list of descriptions;
    a description is (kind, path, Hs): kind 'add' (path (x,), Hs {0: H}), 'chain' (path x_0..x_t, Hs[i] = H_i;
    H_0 may contain goods of B_{x_t}), 'ring' (cycle c_0..c_{r-1}; c_i takes B_{c_{i-1}} + Hs[i])."""
    n = I.n; J = junk(I, base); res = collections.defaultdict(list)
    key = lambda nb: tuple(tuple(sorted(b)) for b in nb)
    val = [I.V(i, base[i]) for i in range(n)]
    for x in range(n):
        for H in _subsets([g for g in J if g in I.R[x]], 1):
            nb = [list(b) for b in base]; nb[x] = list(base[x]) + list(H)
            res[key(nb)].append(('add', (x,), {0: H}))
    L = max_len if max_len is not None else n

    def ext(path, used, Hs):
        xt = path[-1]
        if len(path) >= 2:
            x0 = path[0]
            pool = [g for g in J if g not in used and g in I.R[x0]] + [g for g in base[xt] if g in I.R[x0]]
            for H0 in _subsets(pool, 1):
                if I.V(x0, H0) > val[x0]:
                    nb = [list(b) for b in base]; nb[x0] = list(H0)
                    for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]]) + list(Hs[i])
                    res[key(nb)].append(('chain', tuple(path), {0: H0, **Hs}))
        if len(path) >= L or not base[xt]: return
        for y in range(n):
            if y in path: continue
            for H in _subsets([g for g in J if g not in used and g in I.R[y]]):
                if I.V(y, list(base[xt]) + list(H)) > val[y]:
                    ext(path + [y], used | set(H), {**Hs, len(path): H})
    for x in range(n): ext([x], frozenset(), {})
    for r in range(2, n + 1):
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc): continue

            def ring(i, used, Hs):
                if i == r:
                    nb = [list(b) for b in base]
                    for t in range(r): nb[cyc[t]] = list(base[cyc[t - 1]]) + list(Hs[t])
                    res[key(nb)].append(('ring', tuple(cyc), dict(Hs))); return
                w, pred = cyc[i], cyc[i - 1]
                if not base[pred]: return
                for H in _subsets([g for g in J if g not in used and g in I.R[w]]):
                    if I.V(w, list(base[pred]) + list(H)) > val[w]: ring(i + 1, used | set(H), {**Hs, i: H})
            ring(0, frozenset(), {})
    return res


def is_ed(I, base, desc, D):
    """Hall's ED chain: x_0 dangerous; middle agents take exactly their predecessor's base (and want it); the head may
    add junk; t = 0 additions by a dangerous agent count too"""
    kind, path, Hs = desc
    if path[0] not in D: return False
    if kind == 'add': return True
    if kind != 'chain': return False
    t = len(path) - 1
    for i in range(1, t):
        if Hs.get(i): return False
    return True


def is_canonical(I, base, desc, D):
    """canonical chain (k4/oc1_hall.md §21): ED, the head takes no junk either, every x_i (i >= 1) wants
    B_{x_{i-1}} alone, and the head is unfrozen at the base"""
    kind, path, Hs = desc
    if kind != 'chain' or path[0] not in D: return False
    t = len(path) - 1
    if any(Hs.get(i) for i in range(1, t + 1)): return False
    val = [I.V(i, base[i]) for i in range(I.n)]
    for i in range(1, t + 1):
        if not (len(base[path[i - 1]]) == 1 and I.v[path[i]].get(base[path[i - 1]][0], 0) > val[path[i]]): return False
    return path[-1] not in frozen(I, base)


# ------------------------------------------------------------------------------------------------ matchings, RED
def nu(I):
    """maximum matching size of the agent / relevant-good graph (augmenting paths)"""
    match = {}
    def aug(i, seen):
        for g in I.sets[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = i; return True
        return False
    return sum(1 for i in range(I.n) if aug(i, set()))


def red(I, Y):
    """Lemma RED (k4/sdc.md §31).  Y maximum-matching picks.  U = pickless agents with relevant goods, S = agents
    reachable from U by Y-alternating paths.  Returns (I', Y', keep) where I' keeps the agents T (the rest) and U
    (as null agents), and the goods of T plus the junk; keep[i'] = the original agent.  Goods keep their numbers."""
    n = I.n
    holder = {g: i for i, g in enumerate(Y) if g is not None}
    U = [i for i in range(n) if Y[i] is None and I.sets[i]]
    S = set(); frontier = list(U); seen = set(U)
    while frontier:
        a = frontier.pop()
        for g in I.sets[a]:
            b = holder.get(g)
            if b is not None and b not in seen:
                seen.add(b); S.add(b); frontier.append(b)
    T = [i for i in range(n) if i not in S and i not in U]
    removed = set(Y[s] for s in S)
    keep = T + U
    sets, vals = [], []
    for i in keep:
        if i in U: sets.append([]); vals.append([])
        else:
            gs = [g for g in I.sets[i] if g not in removed]
            sets.append(gs); vals.append([I.v[i][g] for g in gs])
    I2 = Inst(sets, vals, I.m, I.name + '/red')
    Y2 = tuple(Y[i] if i in T else None for i in keep)
    return I2, Y2, keep, sorted(S), U


def is_perfect(I, Y):
    return all(Y[i] is not None or not I.sets[i] for i in range(I.n))


# ------------------------------------------------------------------------------------------------ descriptions
def describe(I, Y):
    base = base_from_picks(Y); J = set(junk(I, base)); F = set(frozen(I, base))
    out = []
    for i in range(I.n):
        r = sorted(I.R[i], key=lambda g: I.rk(i, g), reverse=True)
        s = ' > '.join('%d(%d)%s' % (g, I.v[i][g], '*' if g == Y[i] else ('j' if g in J else '')) for g in r)
        out.append('  agent %d: %s   pick %s  wanted by %s%s' % (i, s or '(null)', Y[i], wanters(I, base, i),
                                                                 '  FROZEN' if i in F else ''))
    return '\n'.join(out)
