"""Bounded charity in terms of relevant goods (kgen/charity.md): shared library.

Instance: n agents, m goods 0..m-1, v[i] = {good: value > 0} (the relevant goods R_i; every other good is worth 0).
A *partial allocation* is a list X of n disjoint sets of goods; the pool P is the rest.

Definitions (raw, used by every check in this folder):
  EFX0:          for all i != j and every h in X_j:  v_i(X_i) >= v_i(X_j minus h)   (h may be worthless to i).
  strong charity: v_i(P) <= v_i(X_i) for every agent i           (CKMS: nobody envies the pool as a set).
  weak charity:   v_i(g) <= v_i(X_i) for every agent i and g in P (nobody envies a single unallocated good).

Contents:
  - raw checkers (efx0, pool_ok), independent of any encoding;
  - random instance generators (k-relevant);
  - SAT: least number of unallocated goods (strong or weak charity), with an independent brute force for tiny cases;
  - CKMS: the update rules U0, U1, U2 of Chaudhury-Kavitha-Mehlhorn-Sgouritsa (arXiv 1907.04596v3, Algorithm 2) for
    additive valuations in EFX0 form, with envy-cycle elimination, the minimal-envied-subset oracle (their Algorithm 3)
    and U2 applied along a *shortest* rainbow cycle of the source digraph (see kgen/charity.md, Lemma CH5).
"""
import itertools, random, collections

# ----------------------------------------------------------------------------------------------- instances

class Inst:
    def __init__(self, n, m, v):
        self.n, self.m = n, m
        self.v = [dict((int(g), int(x)) for g, x in vi.items() if x > 0) for vi in v]
        self.R = [set(vi) for vi in self.v]
        self.V = [set(i for i in range(n) if g in self.R[i]) for g in range(m)]   # valuers of each good

    def val(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)

    def k(self):
        return max(len(r) for r in self.R)

    def to_json(self):
        return {'n': self.n, 'm': self.m, 'v': [{str(g): x for g, x in sorted(vi.items())} for vi in self.v]}

    @staticmethod
    def from_json(d):
        return Inst(d['n'], d['m'], [{int(g): x for g, x in vi.items()} for vi in d['v']])


def from_sets(sets, vals, m=None):
    if m is None:
        m = 1 + max(max(s) for s in sets if s)
    return Inst(len(sets), m, [dict(zip(s, vv)) for s, vv in zip(sets, vals)])


def rand_inst(rng, n, m, kmin, kmax, vmax=100, cover=True):
    """Each agent values between kmin and kmax goods (uniform), integer values in 1..vmax.  cover: every good valued."""
    if cover:
        m = min(m, n * kmax)
    while True:
        v = []
        for i in range(n):
            d = rng.randint(kmin, min(kmax, m))
            S = rng.sample(range(m), d)
            v.append({g: rng.randint(1, vmax) for g in S})
        I = Inst(n, m, v)
        if not cover or all(I.V[g] for g in range(m)):
            return I


def rand_hot(rng, n, m, k, hot, vmax=100):
    """Contested instances: a few 'hot' goods valued by many agents (unbounded good degree), the rest sparse."""
    m = min(m, hot + n * (k - 1))
    while True:
        v = []
        for i in range(n):
            d = rng.randint(2, min(k, m))
            nh = min(d, rng.randint(1, max(1, d - 1)))
            S = set(rng.sample(range(hot), min(nh, hot)))
            while len(S) < d:
                S.add(rng.randrange(m))
            v.append({g: rng.randint(1, vmax) for g in S})
        I = Inst(n, m, v)
        if all(I.V[g] for g in range(m)):
            return I

# ----------------------------------------------------------------------------------------------- raw checks

def efx0(I, X):
    for i in range(I.n):
        own = I.val(i, X[i])
        for j in range(I.n):
            if j == i or len(X[j]) < 2:
                continue
            tot = I.val(i, X[j])
            mn = min(I.v[i].get(h, 0) for h in X[j])
            if tot - mn > own:
                return False
    return True


def strongly_envies(I, i, B, own):
    if len(B) == 0:
        return False
    tot = I.val(i, B)
    mn = min(I.v[i].get(h, 0) for h in B)
    return tot - mn > own


def pool_of(I, X):
    used = set().union(*X) if X else set()
    return set(range(I.m)) - used


def pool_ok(I, X, P=None, strong=True):
    if P is None:
        P = pool_of(I, X)
    for i in range(I.n):
        own = I.val(i, X[i])
        if strong:
            if I.val(i, P) > own:
                return False
        else:
            if any(I.v[i].get(g, 0) > own for g in P):
                return False
    return True


def disjoint_ok(I, X):
    seen = set()
    for B in X:
        if seen & B:
            return False
        seen |= B
    return seen <= set(range(I.m))

# ----------------------------------------------------------------------------------------------- brute force

def brute_min_charity(I, strong=True):
    """Least |P| over all partial EFX0 allocations with charity; enumerates (n+1)^m assignments (tiny cases only)."""
    best, arg = None, None
    for asg in itertools.product(range(I.n + 1), repeat=I.m):
        p = sum(1 for a in asg if a == I.n)
        if best is not None and p >= best:
            continue
        X = [set() for _ in range(I.n)]
        for g, a in enumerate(asg):
            if a < I.n:
                X[a].add(g)
        if efx0(I, X) and pool_ok(I, X, strong=strong):
            best, arg = p, X
            if p == 0:
                break
    return best, arg

# ----------------------------------------------------------------------------------------------- SAT

def _subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


class Enc:
    """x[g][a]: good g goes to a (a = n: the pool).  y[i][S]: X_i cap R_i = S exactly.
    EFX0 clause: if X_i cap R_i = S, T subset R_i minus S is a minimal set worth more than S to i, then X_j cannot
    contain T plus any further good h.  Charity clause (strong): the pool cannot contain such a T; (weak): only |T| = 1."""

    def __init__(self, I, strong=True, charity=True):
        self.I = I
        n, m = I.n, I.m
        self.top = 0
        self.x = [[self.new() for a in range(n + 1)] for g in range(m)]
        self.cl = []
        for g in range(m):
            self.cl.append([self.x[g][a] for a in range(n + 1)])
            for a in range(n + 1):
                for b in range(a + 1, n + 1):
                    self.cl.append([-self.x[g][a], -self.x[g][b]])
        self.y = []
        for i in range(n):
            Ri = sorted(I.R[i]); d = {}
            for S in _subsets(Ri):
                y = self.new(); d[S] = y
                for g in Ri:
                    self.cl.append([-y, self.x[g][i] if g in S else -self.x[g][i]])
                self.cl.append([y] + [-self.x[g][i] for g in S] + [self.x[g][i] for g in Ri if g not in S])
            self.y.append(d)
        for i in range(n):
            vi = I.v[i]; Ri = sorted(I.R[i])
            for S, y in self.y[i].items():
                vs = sum(vi[g] for g in S)
                rest = [g for g in Ri if g not in S]
                Ts = [T for T in _subsets(rest) if T and sum(vi[g] for g in T) > vs]
                Ts = [T for T in Ts if not any(set(U) < set(T) for U in Ts)]
                for j in range(n):
                    if j == i:
                        continue
                    for T in Ts:
                        for h in range(m):
                            if h in T:
                                continue
                            self.cl.append([-y] + [-self.x[g][j] for g in T] + [-self.x[h][j]])
                if charity:
                    for T in Ts:
                        if strong or len(T) == 1:
                            self.cl.append([-y] + [-self.x[g][n] for g in T])

    def new(self):
        self.top += 1
        return self.top

    def decode(self, model):
        pos = set(l for l in model if l > 0)
        X = [set() for _ in range(self.I.n)]
        for g in range(self.I.m):
            for a in range(self.I.n):
                if self.x[g][a] in pos:
                    X[a].add(g)
        return X


def sat_min_charity(I, strong=True, upto=None):
    """Least |P| (strong or weak charity) by SAT with a cardinality bound; returns (least, X)."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    E = Enc(I, strong=strong)
    if upto is None:
        upto = I.m
    for b in range(0, upto + 1):
        cl = list(E.cl); top = E.top
        pool = [E.x[g][I.n] for g in range(I.m)]
        if b < I.m:
            card = CardEnc.atmost(lits=pool, bound=b, top_id=top, encoding=EncType.seqcounter)
            cl += card.clauses
        s = Cadical153(bootstrap_with=cl)
        ok = s.solve()
        X = E.decode(s.get_model()) if ok else None
        s.delete()
        if ok:
            assert efx0(I, X) and pool_ok(I, X, strong=strong), 'SAT witness fails the raw check'
            return b, X
    return None, None

# ----------------------------------------------------------------------------------------------- CKMS

def envy_graph(I, X):
    own = [I.val(i, X[i]) for i in range(I.n)]
    return [[j for j in range(I.n) if j != i and I.val(i, X[j]) > own[i]] for i in range(I.n)]


def sources(I, X, G=None):
    if G is None:
        G = envy_graph(I, X)
    indeg = [0] * I.n
    for i in range(I.n):
        for j in G[i]:
            indeg[j] += 1
    return [i for i in range(I.n) if indeg[i] == 0]


def find_cycle(G):
    n = len(G); color = [0] * n; par = [-1] * n
    for s in range(n):
        if color[s]:
            continue
        stack = [(s, iter(G[s]))]; color[s] = 1
        while stack:
            u, it = stack[-1]
            for w in it:
                if color[w] == 0:
                    color[w] = 1; par[w] = u; stack.append((w, iter(G[w]))); break
                if color[w] == 1:
                    cyc = [u]
                    while cyc[-1] != w:
                        cyc.append(par[cyc[-1]])
                    return cyc[::-1]          # w -> ... -> u, and u envies w
            else:
                color[u] = 2; stack.pop()
    return None


def decycle(I, X):
    """Lemma 2 of CKMS: rotate bundles along envy cycles until the envy graph is acyclic."""
    while True:
        cyc = find_cycle(envy_graph(I, X))
        if cyc is None:
            return X
        # cyc = c0 -> c1 -> ... -> c_{L-1} -> c0 ; each agent takes the bundle of the agent it envies
        new = [set(B) for B in X]
        L = len(cyc)
        for t in range(L):
            new[cyc[t]] = set(X[cyc[(t + 1) % L]])
        X = new


def min_envied(I, X, S, order=None):
    """CKMS Algorithm 3: an inclusion-wise minimal envied subset Z of S and an agent envying it (S must be envied)."""
    own = [I.val(i, X[i]) for i in range(I.n)]
    Z = set(S)
    ags = list(range(I.n)) if order is None else order
    for i in ags:
        for g in sorted(Z):
            if g in Z and I.val(i, Z - {g}) > own[i]:
                Z.discard(g)
    who = [i for i in ags if I.val(i, Z) > own[i]]
    assert who, 'min_envied called on a set nobody envies'
    return Z, who[0]


def reach(G, s):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for w in G[u]:
            if w not in seen:
                seen.add(w); st.append(w)
    return seen


def path(G, s, t):
    par = {s: None}; q = collections.deque([s])
    while q:
        u = q.popleft()
        if u == t:
            break
        for w in G[u]:
            if w not in par:
                par[w] = u; q.append(w)
    p = [t]
    while p[-1] != s:
        p.append(par[p[-1]])
    return p[::-1]


def u0_moves(I, X, P):
    res = []
    for g in sorted(P):
        for i in range(I.n):
            Y = [set(B) for B in X]; Y[i].add(g)
            if efx0(I, Y):
                res.append((g, i))
    return res


def champion_table(I, X, P, S, order=None):
    """For every source s and pool good g: (t, Z) = most envious agent of X_s + g with its minimal envied subset."""
    tab = {}
    for s in S:
        for g in P:
            B = X[s] | {g}
            own = [I.val(i, X[i]) for i in range(I.n)]
            if not any(I.val(i, B) > own[i] for i in range(I.n)):
                continue
            tab[(s, g)] = min_envied(I, X, B, order)
    return tab


def shortest_rainbow(I, X, P, G, S, tab, maxlen=None):
    """Shortest cycle s_0 -g_0-> s_1 -g_1-> ... -> s_0 with distinct sources and distinct goods, where the edge
    s_i -g_i-> s_{i+1} means: the champion t of X_{s_i} + g_i is reachable from s_{i+1}.  Returns [(s_i, g_i)]."""
    C = {s: reach(G, s) for s in S}
    goods = sorted(P)
    if maxlen is None:
        maxlen = min(len(S), len(goods))

    def dfs(s0, verts, cols, L):
        u = verts[-1]
        for g in goods:
            if g in cols or (u, g) not in tab:
                continue
            t = tab[(u, g)][1]
            if len(cols) + 1 == L:
                if t in C[s0]:
                    return list(zip(verts, cols + [g]))
            else:
                for s2 in S:
                    if s2 in verts or t not in C[s2]:
                        continue
                    r = dfs(s0, verts + [s2], cols + [g], L)
                    if r is not None:
                        return r
        return None

    for L in range(1, maxlen + 1):
        for s0 in S:
            r = dfs(s0, [s0], [], L)
            if r is not None:
                return r
    return None


def apply_u2(I, X, P, G, cyc, tab):
    """CKMS rule U2 along cyc = [(s_0, g_0), ..., (s_{l-1}, g_{l-1})]: t_{i+1} = champion of X_{s_i} + g_i takes
    Z_i; the path s_{i+1} -> ... -> t_{i+1} shifts bundles back by one; (X_{s_i} + g_i) minus Z_i joins the pool."""
    l = len(cyc)
    newX = [set(B) for B in X]; newP = set(P)
    touched = set()
    for i in range(l):
        s, g = cyc[i]
        pth = path(G, cyc[(i + 1) % l][0], tab[(s, g)][1])
        assert not (touched & set(pth)), 'CH5: paths of a shortest rainbow cycle are disjoint'
        touched |= set(pth)
    for i in range(l):
        s, g = cyc[i]
        Z, t = tab[(s, g)]
        s2 = cyc[(i + 1) % l][0]           # t is reachable from s2
        pth = path(G, s2, t)
        for a, b in zip(pth, pth[1:]):
            newX[a] = set(X[b])
        newX[t] = set(Z)
        newP.discard(g)
        newP |= (X[s] | {g}) - Z
    # every source s_i lost its bundle; it was refilled by the path shift (or s_i = t_i got Z)
    return newX, newP


def ckms(I, X=None, rng=None, log=None, check=True, maxsteps=100000):
    """Run CKMS from X (default: empty allocation) until no rule applies.  Returns (X, P, counts)."""
    if X is None:
        X = [set() for _ in range(I.n)]
    X = [set(B) for B in X]
    P = pool_of(I, X)
    cnt = collections.Counter()
    for step in range(maxsteps):
        X = decycle(I, X)
        if check:
            assert efx0(I, X) and disjoint_ok(I, X) and pool_of(I, X) == P
        # U0
        mv = u0_moves(I, X, P)
        if mv:
            g, i = rng.choice(mv) if rng else mv[0]
            X[i].add(g); P.discard(g); cnt['U0'] += 1
            continue
        # U1
        own = [I.val(i, X[i]) for i in range(I.n)]
        if any(I.val(i, P) > own[i] for i in range(I.n)):
            order = list(range(I.n))
            if rng:
                rng.shuffle(order)
            Z, i = min_envied(I, X, P, order)
            P = (P - Z) | X[i]; X[i] = set(Z); cnt['U1'] += 1
            continue
        # U2
        G = envy_graph(I, X); S = sources(I, X, G)
        order = list(range(I.n))
        if rng:
            rng.shuffle(order)
        tab = champion_table(I, X, P, S, order)
        cyc = shortest_rainbow(I, X, P, G, S, tab)
        if cyc is not None:
            w0 = sum(own)
            X, P = apply_u2(I, X, P, G, cyc, tab)
            if check:
                assert efx0(I, X), 'U2 output is not EFX0'
                assert all(I.val(i, X[i]) >= own[i] for i in range(I.n))
                assert sum(I.val(i, X[i]) for i in range(I.n)) > w0
            cnt['U2'] += 1; cnt['U2 len %d' % len(cyc)] += 1
            continue
        return X, P, cnt
    raise RuntimeError('ckms: step limit')


def stuck_report(I, X, P):
    """Structure of a stuck state (Lemmas CH1-CH4 of kgen/charity.md); returns a dict and asserts the lemmas."""
    G = envy_graph(I, X); S = sources(I, X, G)
    rep = {'pool': len(P), 'sources': len(S)}
    if not P:
        return rep
    tab = champion_table(I, X, P, S)
    C = {s: reach(G, s) for s in S}
    for s in S:
        assert len(X[s]) >= 2, 'CH2: a source of a stuck state with nonempty pool holds >= 2 goods'
    for (s, g), (Z, t) in tab.items():
        assert g in Z and t in I.V[g], 'CH1: the champion values g'
        assert Z - {g} and (Z - {g}) <= X[s] and all(h in I.R[t] for h in Z), 'CH1: champion values goods of X_s'
        assert t != s and t not in C[s], 'CH3: champion not reachable from s'
        assert I.R[t] & X[t], 'CH3: champion values its own bundle'
    for s in S:
        for g in P:
            assert (s, g) in tab, 'U0 inapplicable means X_s + g is envied'
    assert len(P) < len(S), 'CKMS Thm 8: |P| < #sources'
    for g in P:
        cover = sum(len([s for s in S if s != c and I.R[c] & X[s]]) for c in I.V[g] if I.R[c] & X[c])
        assert len(S) <= cover, 'CH4 count'
    rep['min valuers of a pool good'] = min(len(I.V[g]) for g in P)
    return rep
