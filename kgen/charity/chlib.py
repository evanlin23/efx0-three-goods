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
    """Contested instances: goods 0..hot-1 are 'hot' (each agent values between 1 and d-1 of them, so they have many
    valuers); every other good is given to an agent with spare capacity, then spare capacity is filled at random.
    m is capped at what the capacities can cover."""
    d = [rng.randint(2, k) for _ in range(n)]
    nh = [min(hot, rng.randint(1, di - 1)) for di in d]
    cap = [di - h for di, h in zip(d, nh)]
    m = max(hot, min(m, hot + sum(cap)))
    S = [set(rng.sample(range(hot), h)) for h in nh]
    rest = list(range(hot, m)); rng.shuffle(rest)
    for g in rest:
        i = rng.choice([i for i in range(n) if cap[i] > 0]); S[i].add(g); cap[i] -= 1
    for i in range(n):
        free = [g for g in range(hot, m) if g not in S[i]]
        rng.shuffle(free)
        S[i] |= set(free[:cap[i]])
    return Inst(n, m, [{g: rng.randint(1, vmax) for g in Si} for Si in S])


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


def min_envied_all(I, X, B, cap=16):
    """Every pair (Z, t): Z an inclusion-wise minimal envied subset of B (someone envies Z, nobody envies Z minus h for
    any h in Z) and t an agent envying Z.  Only goods valued by some agent can lie in a minimal Z."""
    own = [I.val(i, X[i]) for i in range(I.n)]
    rel = sorted(g for g in B if I.V[g])
    assert len(rel) <= cap, 'min_envied_all: bundle too large'
    env = lambda Z: [i for i in range(I.n) if I.val(i, Z) > own[i]]
    out = []
    for r in range(1, len(rel) + 1):
        for Z in itertools.combinations(rel, r):
            E = env(Z)
            if E and all(not env([h for h in Z if h != x]) for x in Z):
                out += [(set(Z), t) for t in E]
    return out


def champion_table(I, X, P, S, order=None, mode='ckms'):
    """For every source s and pool good g with X_s + g envied: the champion options, a list of (Z, t).
    mode 'ckms': the single pair of CKMS's Algorithm 3 with the given agent order; mode 'all': every minimal envied
    subset with every agent envying it (min_envied_all)."""
    tab = {}
    own = [I.val(i, X[i]) for i in range(I.n)]
    for s in S:
        for g in P:
            B = X[s] | {g}
            if not any(I.val(i, B) > own[i] for i in range(I.n)):
                continue
            tab[(s, g)] = [min_envied(I, X, B, order)] if mode == 'ckms' else min_envied_all(I, X, B)
    return tab


def shortest_rainbow(I, X, P, G, S, tab, maxlen=None):
    """Shortest cycle s_0 -g_0-> s_1 -g_1-> ... -> s_0 with distinct sources and distinct goods, where the edge
    s_i -g_i-> s_{i+1} means: a champion option (Z_i, t) of X_{s_i} + g_i has t reachable from s_{i+1}.
    Returns [(s_i, g_i, Z_i, t_{i+1})]."""
    C = {s: reach(G, s) for s in S}
    goods = sorted(P)
    if maxlen is None:
        maxlen = min(len(S), len(goods))

    def dfs(s0, seq, L):
        u = seq[-1][0] if seq and len(seq[-1]) == 1 else None
        verts = [e[0] for e in seq]
        cols = [e[1] for e in seq if len(e) > 1]
        u = verts[-1]
        for g in goods:
            if g in cols or (u, g) not in tab:
                continue
            for Z, t in tab[(u, g)]:
                done = seq[:-1] + [(u, g, Z, t)]
                if len(cols) + 1 == L:
                    if t in C[s0]:
                        return done
                else:
                    for s2 in S:
                        if s2 in verts or t not in C[s2]:
                            continue
                        r = dfs(s0, done + [(s2,)], L)
                        if r is not None:
                            return r
        return None

    for L in range(1, maxlen + 1):
        for s0 in S:
            r = dfs(s0, [(s0,)], L)
            if r is not None:
                return r
    return None


def apply_u2(I, X, P, G, cyc):
    """CKMS rule U2 along cyc = [(s_i, g_i, Z_i, t_{i+1})]: t_{i+1} takes Z_i; the path s_{i+1} -> ... -> t_{i+1}
    shifts bundles back by one; (X_{s_i} + g_i) minus Z_i joins the pool."""
    l = len(cyc)
    newX = [set(B) for B in X]; newP = set(P)
    touched = set()
    for i in range(l):
        pth = path(G, cyc[(i + 1) % l][0], cyc[i][3])
        assert not (touched & set(pth)), 'CH5: paths of a shortest rainbow cycle are disjoint'
        touched |= set(pth)
    for i in range(l):
        s, g, Z, t = cyc[i]
        pth = path(G, cyc[(i + 1) % l][0], t)
        for a, b in zip(pth, pth[1:]):
            newX[a] = set(X[b])
        newX[t] = set(Z)
        newP.discard(g)
        newP |= (X[s] | {g}) - Z
    return newX, newP


def ckms(I, X=None, rng=None, mode='ckms', check=True, maxsteps=100000):
    """Run CKMS from X (default: empty allocation) until no rule applies.  Returns (X, P, counts, tab), tab the champion
    table of the stopping state (mode as in champion_table)."""
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
        tab = champion_table(I, X, P, S, order, mode)
        cyc = shortest_rainbow(I, X, P, G, S, tab)
        if cyc is not None:
            w0 = sum(own)
            X, P = apply_u2(I, X, P, G, cyc)
            if check:
                assert efx0(I, X), 'U2 output is not EFX0'
                assert all(I.val(i, X[i]) >= own[i] for i in range(I.n))
                assert sum(I.val(i, X[i]) for i in range(I.n)) > w0
            cnt['U2'] += 1; cnt['U2 len %d' % len(cyc)] += 1
            continue
        return X, P, cnt, tab
    raise RuntimeError('ckms: step limit')


def stuck_report(I, X, P, tab):
    """Structure of a stopping state with champion table tab (Lemmas CH1-CH4 of kgen/charity.md); asserts them."""
    G = envy_graph(I, X); S = sources(I, X, G)
    rep = {'pool': len(P), 'sources': len(S)}
    if not P:
        return rep
    C = {s: reach(G, s) for s in S}
    for s in S:
        assert len(X[s]) >= 2, 'CH2: a source of a stuck state with nonempty pool holds >= 2 goods'
    for (s, g), opts in tab.items():
      for Z, t in opts:
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


def improve(I, X):
    """A partial EFX0 allocation Y with v_i(Y_i) >= v_i(X_i) for all i and (some agent strictly better, or fewer goods
    unallocated), or None.  None means X is Pareto-maximal among partial EFX0 allocations and allocates the most goods
    for its value vector (the hypothesis of K4.SDC.P1).  No charity condition is imposed on Y."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    E = Enc(I, charity=False)
    u = [I.val(i, X[i]) for i in range(I.n)]
    A = sum(len(B) for B in X)
    cl = list(E.cl); top = E.top
    zs = []
    for i in range(I.n):
        for S, y in E.y[i].items():
            if I.val(i, S) < u[i]:
                cl.append([-y])
        top += 1; z = top; zs.append(z)
        cl.append([-z] + [y for S, y in E.y[i].items() if I.val(i, S) > u[i]])
    top += 1; w = top
    if A < I.m:
        pool = [E.x[g][I.n] for g in range(I.m)]
        card = CardEnc.atmost(lits=pool, bound=I.m - A - 1, top_id=top, encoding=EncType.seqcounter)
        top = max(top, card.nv)
        for c in card.clauses:
            cl.append(c + [-w])
        cl.append(zs + [w])
    else:
        cl.append(zs)
    s = Cadical153(bootstrap_with=cl)
    ok = s.solve()
    Y = E.decode(s.get_model()) if ok else None
    s.delete()
    if Y is not None:
        assert efx0(I, Y)
    return Y


def pareto_climb(I, X):
    """Improve until Pareto-maximal (with the most goods for its value vector)."""
    steps = 0
    while True:
        Y = improve(I, X)
        if Y is None:
            return X, steps
        X = Y; steps += 1


def pm_with_pool(I, minpool, maxiter=100000, log=None):
    """Exact for one instance: a partial EFX0 allocation X with |P| >= minpool that is Pareto-maximal among partial
    EFX0 allocations and allocates the most goods for its value vector, or None if there is none.
    CEGAR: propose X (|P| >= minpool, not dominated by any Pareto maximum found so far); if improve(X) finds Y, climb
    Y to a Pareto maximum Y*; if Y* has |P| >= minpool return it, else forbid everything Y* dominates.
    Pareto maxima of different value vectors are counted in the returned statistics."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    E = Enc(I, charity=False)
    top = [E.top]

    def new():
        top[0] += 1; return top[0]
    s = Cadical153(bootstrap_with=E.cl)
    pool = [E.x[g][I.n] for g in range(I.m)]
    c = CardEnc.atleast(lits=pool, bound=minpool, top_id=top[0], encoding=EncType.seqcounter)
    top[0] = max(top[0], c.nv)
    for cl in c.clauses:
        s.add_clause(cl)
    maxima = set()
    for it in range(maxiter):
        if not s.solve():
            s.delete(); return None, {'iterations': it, 'maxima': len(maxima)}
        X = E.decode(s.get_model())
        Y = improve(I, X)
        if Y is None:
            s.delete(); return X, {'iterations': it, 'maxima': len(maxima)}
        Y, _ = pareto_climb(I, Y)
        if len(pool_of(I, Y)) >= minpool:
            s.delete(); return Y, {'iterations': it, 'maxima': len(maxima)}
        u = [I.val(i, Y[i]) for i in range(I.n)]; py = len(pool_of(I, Y))
        maxima.add(tuple(u))
        w = new()
        A = [y for i in range(I.n) for S, y in E.y[i].items() if I.val(i, S) > u[i]]
        s.add_clause(A + [w])
        for i in range(I.n):
            for S, y in E.y[i].items():
                if I.val(i, S) < u[i]:
                    s.add_clause([-w, -y])
        if py < I.m:
            c = CardEnc.atmost(lits=pool, bound=py, top_id=top[0], encoding=EncType.seqcounter)
            top[0] = max(top[0], c.nv)
            for cl in c.clauses:
                s.add_clause(cl + [-w])
    raise RuntimeError('pm_with_pool: iteration limit')


def welfare_max(I, minpool=None, maxpool=None):
    """Largest total value over partial EFX0 allocations (no charity condition), and the fewest unallocated goods
    among the allocations with that total.  'Total >= W' is encoded by reachable partial sums over the one-hot
    variables y[i][S] (sound and complete for integer values).  Returns (W*, least pool, allocation).
    minpool / maxpool: if given, return instead the largest total among allocations leaving at least minpool / at most
    maxpool goods out (and the pool size of the witness)."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    E = Enc(I, charity=False)
    tot = sum(max(I.val(i, S) for S in E.y[i]) for i in range(I.n))
    base = list(E.cl); top0 = E.top
    pool = [E.x[g][I.n] for g in range(I.m)]

    def solve(W, poolbound=None, atleast=None):
        cl = list(base); top = [top0]

        def new():
            top[0] += 1; return top[0]
        r = {(0, 0): None}                       # None = true
        prev = {0: None}
        for i in range(I.n):
            cur = {}
            for w in range(0, W + 1):
                opts = []
                for S, y in E.y[i].items():
                    w0 = max(0, w - I.val(i, S))
                    if w0 in prev:
                        opts.append((y, prev[w0]))
                if not opts:
                    continue
                v = new(); ts = []
                for y, pv in opts:
                    t = new(); ts.append(t)
                    cl.append([-t, y])
                    if pv is not None:
                        cl.append([-t, pv])
                cl.append([-v] + ts)
                cur[w] = v
            prev = cur
        if W not in prev:
            return None
        cl.append([prev[W]])
        if poolbound is not None:
            c = CardEnc.atmost(lits=pool, bound=poolbound, top_id=top[0], encoding=EncType.seqcounter)
            cl += c.clauses; top[0] = max(top[0], c.nv)
        if atleast is not None:
            c = CardEnc.atleast(lits=pool, bound=atleast, top_id=top[0], encoding=EncType.seqcounter)
            cl += c.clauses; top[0] = max(top[0], c.nv)
        s = Cadical153(bootstrap_with=cl)
        ok = s.solve(); X = E.decode(s.get_model()) if ok else None
        s.delete()
        return X
    lo, hi, best = 0, tot, None                  # largest W with solve(W) satisfiable
    while lo <= hi:
        mid = (lo + hi) // 2
        X = solve(mid, poolbound=maxpool, atleast=minpool)
        if X is not None:
            best = X; lo = sum(I.val(i, X[i]) for i in range(I.n)) + 1
        else:
            hi = mid - 1
    if best is None:
        return None, None, None
    W = sum(I.val(i, best[i]) for i in range(I.n))
    assert efx0(I, best)
    if minpool is not None or maxpool is not None:
        return W, len(pool_of(I, best)), best
    for b in range(0, len(pool_of(I, best)) + 1):
        X = solve(W, poolbound=b)
        if X is not None:
            assert efx0(I, X) and sum(I.val(i, X[i]) for i in range(I.n)) >= W
            return W, len(pool_of(I, X)), X
    return W, len(pool_of(I, best)), best


def leximin_max(I):
    """Leximin maximum over partial EFX0 allocations: maximise the smallest value, then the second smallest, ...;
    then the fewest unallocated goods.  Level r fixes thresholds t_1 <= ... <= t_r: for each j <= r, at least
    n - j + 1 agents have value >= t_j (cardinality over per-agent indicators).  Returns (sorted vector, pool, X)."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    E = Enc(I, charity=False)
    pool = [E.x[g][I.n] for g in range(I.m)]
    levels = sorted(set(I.val(i, S) for i in range(I.n) for S in E.y[i]))

    def feasible(ts, poolbound=None):
        cl = list(E.cl); top = E.top
        for j, t in enumerate(ts):
            ind = []
            for i in range(I.n):
                top += 1; z = top; ind.append(z)
                cl.append([-z] + [y for S, y in E.y[i].items() if I.val(i, S) >= t])
            c = CardEnc.atleast(lits=ind, bound=I.n - j, top_id=top, encoding=EncType.seqcounter)
            cl += c.clauses; top = max(top, c.nv)
        if poolbound is not None:
            c = CardEnc.atmost(lits=pool, bound=poolbound, top_id=top, encoding=EncType.seqcounter)
            cl += c.clauses; top = max(top, c.nv)
        s = Cadical153(bootstrap_with=cl); ok = s.solve()
        X = E.decode(s.get_model()) if ok else None
        s.delete()
        return X
    ts = []
    for r in range(I.n):
        lo, hi = 0, len(levels) - 1                       # largest level index feasible
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if feasible(ts + [levels[mid]]) is not None:
                lo = mid
            else:
                hi = mid - 1
        ts.append(levels[lo])
    X = feasible(ts)
    for b in range(0, I.m + 1):
        Y = feasible(ts, poolbound=b)
        if Y is not None:
            assert efx0(I, Y)
            return tuple(sorted(I.val(i, Y[i]) for i in range(I.n))), len(pool_of(I, Y)), Y
