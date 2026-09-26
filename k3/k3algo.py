"""Algorithm K3ALG (proofs/k3_algorithm.md): a polynomial-time algorithm that computes an EFX0 allocation of every
additive instance in which every agent positively values at most three goods.

Two implementations of the same algorithm, written from proofs/k3_algorithm.md and the Lean definitions it names:
- `mirror(n, m, v)`: a literal transcription of the Lean definitions (`EFX.K3.reduce`, `EFX.K3.profileOf`,
  `EFX.LB.r1Order`, `EFX.LB.lbPlus` and everything they call), on Python lists, with the same list orders and
  tie-breaks. Slow (it recomputes the pick function, NA and the slots whenever the Lean definitions do), but every
  choice is the Lean one. Used to cross-check `fast` and the Lean `#eval` of `EFX.K3.algo`.
- `fast(n, m, v)`: the same algorithm with worklists, counters and hash maps (O((n + m) log n) after reading the
  input, see proofs/k3_algorithm.md section 5). It returns the same allocation as `mirror` (checked on random
  instances: `--cross`). It assumes every agent has at most three relevant goods.
Both return (X, info): X[g] is the agent that receives good g, info records which branch LB+ took.

`raw_efx0(n, m, v, X)` checks the raw EFX0 definition: for all agents i != j and every good g in X_j,
v_i(X_i) >= v_i(X_j minus g). `raw_efx0_naive` is the same check written as three nested loops (small instances).

Instances: n agents, m goods, v[i] a dict {good: positive integer value} (goods not in v[i] are worth 0 to i).

Usage:
  k3algo.py --cross N [--seed S]            N random instances: mirror == fast, both raw EFX0 (both checks)
  k3algo.py --certs FILE... [--jobs=J] [--realizations=R] [--sample=K] [--seed=S] [--mirror-every=E]
                                            every ranking profile (or K random ones) of every core in certificate
                                            files: fast, raw EFX0 under R balanced realizations (default 3, which
                                            must give the same allocation), mirror on every E-th profile
  k3algo.py --time n1 n2 ... [--reps R]     timing of fast on random instances (see timing.py for the logged runs)
"""
import sys, random, heapq, itertools, time, json, gzip, collections

# ----------------------------------------------------------------------------------------------------------------
# Raw EFX0 check
# ----------------------------------------------------------------------------------------------------------------

def val(v, i, S):
    return sum(v[i].get(g, 0) for g in S)

def raw_efx0_naive(n, m, v, X):
    """The raw definition, literally: for all i != j and g in X_j, v_i(X_i) >= v_i(X_j minus g)."""
    bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
    for i in range(n):
        own = val(v, i, bundles[i])
        for j in range(n):
            if j == i: continue
            for g in bundles[j]:
                if val(v, i, [h for h in bundles[j] if h != g]) > own:
                    return False
    return True

def raw_efx0(n, m, v, X):
    """The raw definition, evaluated without enumerating bundles i values at 0: for i != j, the largest
    v_i(X_j minus g) over g in X_j is v_i(X_j) minus the smallest value i gives a good of X_j (0 if X_j has a good
    outside i's relevant set); bundles without a good relevant to i give 0."""
    assert len(X) == m and all(0 <= X[g] < n for g in range(m))
    size = [0] * n
    for g in range(m): size[X[g]] += 1
    for i in range(n):
        own = sum(x for g, x in v[i].items() if X[g] == i)
        byb = collections.defaultdict(list)
        for g, x in v[i].items():
            if X[g] != i: byb[X[g]].append(x)
        for j, xs in byb.items():
            tot = sum(xs)
            worst = tot - (min(xs) if len(xs) == size[j] else 0)
            if worst > own: return False
    return True

# ----------------------------------------------------------------------------------------------------------------
# Literal transcription of the Lean definitions
# ----------------------------------------------------------------------------------------------------------------

def _erase(l, x):
    """List.erase: remove the first occurrence."""
    l = list(l)
    if x in l: l.remove(x)
    return l

def favorite(f, S):
    """EFX.favorite: the first good of S with the largest f; None iff S is empty."""
    best = None
    for g in reversed(S):
        if best is None or f(best) <= f(g): best = g
    return best

def r1_step(v, goods, i):
    """EFX.K3.r1Step: None if R1 does not apply to i; ('empty',) to peel i with nothing (i values no remaining good);
    ('good', p) to peel i with its favourite p (v_i(goods minus p) <= v_i(p))."""
    f = lambda g: v[i].get(g, 0)
    p = favorite(f, goods)
    if p is None or f(p) == 0: return ('empty',)
    if sum(f(g) for g in _erase(goods, p)) <= f(p): return ('good', p)
    return None

def sort3(f, g0, rel):
    """EFX.K3.sort3: three goods sorted by f, largest first, ties by list order; (g0, g0, g0) if rel has not
    exactly three goods."""
    if len(rel) != 3: return (g0, g0, g0)
    x, y, z = rel
    fx, fy, fz = f(x), f(y), f(z)
    if fy <= fx:
        if fz <= fy: return (x, y, z)
        if fz <= fx: return (x, z, y)
        return (z, x, y)
    if fz <= fx: return (y, x, z)
    if fz <= fy: return (y, z, x)
    return (z, y, x)

def profile_of(v, n, goods):
    """EFX.K3.profileOf: agent i's three relevant goods among `goods`, sorted (default: the first good)."""
    g0 = goods[0]
    prof = []
    for i in range(n):
        rel = [g for g in goods if v[i].get(g, 0) > 0]
        prof.append(sort3(lambda g: v[i].get(g, 0), g0, rel))
    return prof

class LB:
    """EFX.LB's definitions for a profile P (list of (a, b, c) triples)."""
    def __init__(self, P): self.P = P
    def a(self, i): return self.P[i][0]
    def b(self, i): return self.P[i][1]
    def c(self, i): return self.P[i][2]
    def rank(self, i, g):
        return 0 if g == self.a(i) else 1 if g == self.b(i) else 2 if g == self.c(i) else 3
    def fav(self, pool, i):
        for g in self.P[i]:
            if g in pool: return g
        return None
    @staticmethod
    def remove_pick(pool, p): return list(pool) if p is None else _erase(pool, p)
    def full(self, pool, i): return all(g in pool for g in self.P[i])
    def r1_order(self, fuel, rem, pool):
        out, rem, pool = [], list(rem), list(pool)
        while fuel > 0:
            fuel -= 1
            i = next((j for j in rem if not self.full(pool, j)), None)
            if i is not None: rem = _erase(rem, i)
            elif rem: i = rem[0]; rem = rem[1:]
            else: break
            out.append(i); pool = self.remove_pick(pool, self.fav(pool, i))
        return out
    def phase1(self, order, goods):
        """The function k -> pick, as `phase1 P order goods` (tabulated; same values)."""
        Y, pool = {}, list(goods)
        for i in order:
            if i in Y: continue           # phase1 returns the first occurrence of k in order
            Y[i] = self.fav(pool, i); pool = self.remove_pick(pool, Y[i])
        return lambda k: Y.get(k)
    def blk_aux(self, order, goods):
        B, pool, cnt = {}, list(goods), 0
        for i in order:
            cnt = cnt + 1 if self.full(pool, i) else cnt
            if i not in B: B[i] = cnt
            pool = self.remove_pick(pool, self.fav(pool, i))
        return lambda k: B.get(k, 0)
    def pick_rank(self, Y, i): return 3 if Y(i) is None else self.rank(i, Y(i))
    def prefers(self, Y, i, g): return self.rank(i, g) < self.pick_rank(Y, i)
    def naB(self, agents, up, Y, g): return any(i not in up and self.prefers(Y, i, g) for i in agents)
    def can_up(self, agents, up, Y, J, k):
        return k not in up and self.pick_rank(Y, k) == 1 and self.c(k) in J and not self.naB(agents, up, Y, self.b(k))
    def upgrades(self, agents, Y, fuel, up, J):
        up, J = list(up), list(J)
        for _ in range(fuel):
            k = next((k for k in agents if self.can_up(agents, up, Y, J, k)), None)
            if k is None: break
            up = [k] + up; J = _erase(J, self.c(k))
        return up, J
    @staticmethod
    def picker(agents, Y, g): return next((k for k in agents if Y(k) == g), None)
    def up_of(self, up, g): return next((k for k in up if self.c(k) == g), None)
    def junk0(self, agents, Y, goods): return [g for g in goods if self.picker(agents, Y, g) is None]
    def lb_up(self, agents, goods, Y): return self.upgrades(agents, Y, len(agents), [], self.junk0(agents, Y, goods))[0]
    def frozenB(self, agents, up, Y, k): return Y(k) is not None and self.naB(agents, up, Y, Y(k))
    def cap(self, agents, up, Y, k):
        if self.frozenB(agents, up, Y, k) or k in up: return 0
        return 2 if Y(k) is None else 1
    def junk_list(self, agents, up, Y, goods):
        return [g for g in goods if self.picker(agents, Y, g) is None and self.up_of(up, g) is None]
    def slot_sum(self, agents, up, Y): return sum(self.cap(agents, up, Y, k) for k in agents)
    @staticmethod
    def slots_except(s, o): return lambda k: 0 if o == k else s(k)
    @staticmethod
    def fill(s, ks, rest, g):
        for k in ks:
            if g in rest[:s(k)]: return k
            rest = rest[s(k):]
        return None
    def complete(self, agents, up, Y, goods, o, H, d):
        J = self.junk_list(agents, up, Y, goods)
        L = list(H) + [j for j in J if j not in H]
        s = self.slots_except(lambda k: self.cap(agents, up, Y, k), o)
        def X(g):
            k = self.picker(agents, Y, g)
            if k is not None: return k
            u = self.up_of(up, g)
            if u is not None: return u
            f = self.fill(s, agents, L, g)
            if f is not None: return f
            return o if o is not None else d
        return X
    @staticmethod
    def last_out(up, order):
        for i in reversed(order):
            if i not in up: return i
        return None
    def in_base(self, up, Y, w, g): return Y(w) == g or (w in up and self.c(w) == g)
    def exposed(self, agents, up, Y, goods, w, x):
        J = self.junk_list(agents, up, Y, goods)
        return (x != w and x not in up and Y(x) == self.a(x)
                and (self.b(x) in J or self.in_base(up, Y, w, self.b(x)))
                and (self.c(x) in J or self.in_base(up, Y, w, self.c(x))))
    def exposed_l(self, agents, up, Y, goods, w):
        return [x for x in agents if self.exposed(agents, up, Y, goods, w, x)]
    def pick_one(self, J, x): return self.b(x) if self.b(x) in J else self.c(x)
    def meet(self, J, E):
        for x in E:
            for y in E:
                if x == y: continue
                for g in (self.b(x), self.c(x)):
                    if g in J and (g == self.b(y) or g == self.c(y)): return (x, y, g)
        return None
    def hit_set(self, J, E):
        mt = self.meet(J, E)
        if mt is not None:
            x, y, g = mt
            return [g] + [self.pick_one(J, z) for z in E if z != x and z != y]
        return [self.pick_one(J, z) for z in E]
    def kstar(self, agents, up, Y, goods, blk, r):
        return next((x for x in self.exposed_l(agents, up, Y, goods, r) if blk(x) == blk(r)), None)
    @staticmethod
    def after(order, x):
        for t, i in enumerate(order):
            if i == x: return order[t + 1:]
        return []
    def is_next(self, agents, up, Y, cur, j):
        return (self.frozenB(agents, up, Y, cur) and j not in up and Y(cur) is not None
                and self.prefers(Y, j, Y(cur)))
    def chain_from(self, agents, up, Y, cur, rest):
        out = []
        for j in rest:
            if self.is_next(agents, up, Y, cur, j): out.append(j); cur = j
        return out
    @staticmethod
    def rot_y(Y, cur, l):
        def Z(x):
            c = cur
            for j in l:
                if x == j: return Y(c)
                c = j
            return Y(x)
        return Z
    def rot_picks(self, Y, k, ch):
        Z = self.rot_y(Y, k, ch)
        return lambda x: self.b(k) if x == k else Z(x)
    def lb_plus(self, agents, goods, order, d):
        """EFX.LB.lbPlus; returns (X, tag)."""
        Y = self.phase1(order, goods)
        up = self.lb_up(agents, goods, Y)
        J = self.junk_list(agents, up, Y, goods)
        if len(J) <= self.slot_sum(agents, up, Y):
            return self.complete(agents, up, Y, goods, None, [], d), 'noowner'
        r = self.last_out(up, order)
        if r is None: return self.complete(agents, up, Y, goods, None, [], d), 'unreachable'
        H = self.hit_set(J, self.exposed_l(agents, up, Y, goods, r))
        s = self.slots_except(lambda k: self.cap(agents, up, Y, k), r)
        if len(H) <= sum(s(k) for k in agents):
            return self.complete(agents, up, Y, goods, r, H, d), 'owner_r'
        k = self.kstar(agents, up, Y, goods, self.blk_aux(order, goods), r)
        if k is None: return self.complete(agents, up, Y, goods, r, H, d), 'unreachable'
        Y2 = self.rot_picks(Y, k, self.chain_from(agents, up, Y, k, self.after(order, k)))
        up2 = [k] + up
        J2 = self.junk_list(agents, up2, Y2, goods)
        if len(J2) <= self.slot_sum(agents, up2, Y2):
            return self.complete(agents, up2, Y2, goods, None, [], d), 'rot_noowner'
        H2 = self.hit_set(J2, self.exposed_l(agents, up2, Y2, goods, k))
        return self.complete(agents, up2, Y2, goods, k, H2, d), 'rot_owner_k'

def mirror(n, m, v):
    """EFX.K3.algo, transcribed: the peeling loop `reduce`, then LB+ on what is left."""
    assert n >= 1
    agents, goods, d = list(range(n)), list(range(m)), 0
    peeled = {}       # good -> agent (peeled with that good)
    info = {'peeled': 0, 'branch': None, 'core_n': 0, 'core_m': 0}
    while True:
        if len(agents) <= 1:
            X = lambda g: agents[0] if agents else d
            info['branch'] = 'one_agent'; break
        if not goods:
            X = lambda g: d; info['branch'] = 'no_goods'; break
        step = next(((i, st) for i in agents for st in [r1_step(v, goods, i)] if st is not None), None)
        if step is None:
            P = profile_of(v, n, goods)
            lb = LB(P)
            order = lb.r1_order(len(agents), agents, goods)
            X, tag = lb.lb_plus(agents, goods, order, d)
            info['branch'] = tag; info['core_n'] = len(agents); info['core_m'] = len(goods); break
        i, st = step
        info['peeled'] += 1
        agents = _erase(agents, i)
        if st[0] == 'good': peeled[st[1]] = i; goods = _erase(goods, st[1])
    return [peeled[g] if g in peeled else X(g) for g in range(m)], info

# ----------------------------------------------------------------------------------------------------------------
# Efficient implementation (same output as mirror; assumes at most three relevant goods per agent)
# ----------------------------------------------------------------------------------------------------------------

def fast(n, m, v, naive_owner_test=False):
    """naive_owner_test=True replaces the exact owner test by |E_r| <= S - cap(r) (one junk good per exposed pair, no
    shared good): a WRONG variant, kept for attempts/k3-owner-test-no-shared-good.md."""
    assert n >= 1
    rel = [sorted(v[i]) for i in range(n)]          # relevant goods of i, by index
    assert all(len(r) <= 3 for r in rel), "fast assumes at most three relevant goods per agent"
    valuers = [[] for _ in range(m)]
    for i in range(n):
        for g in rel[i]: valuers[g].append(i)
    alive_g = [True] * m
    alive_a = [True] * n
    n_alive, m_alive = n, m
    info = {'peeled': 0, 'branch': None, 'core_n': 0, 'core_m': 0}

    def step(i):
        rr = [g for g in rel[i] if alive_g[g]]
        if not rr: return ('empty',)
        f = v[i]
        p = rr[0]
        for g in rr[1:]:
            if f[g] > f[p]: p = g                    # first good of largest value (index order)
        if sum(f[g] for g in rr) - f[p] <= f[p]: return ('good', p)
        return None

    # 1. Peeling (rules R1 and R1 with P = empty): always the first applicable agent in index order. Under the
    # hypothesis, once R1 applies to an agent it keeps applying (proofs/k3_algorithm.md, Lemma 5.1), so a heap of
    # the agents it applies to, refreshed at the valuers of each removed good, finds that agent.
    peeled = {}
    heap = [i for i in range(n) if step(i) is not None]
    heapq.heapify(heap)
    while n_alive >= 2 and m_alive >= 1:
        while heap and (not alive_a[heap[0]] or step(heap[0]) is None): heapq.heappop(heap)
        if not heap: break
        i = heapq.heappop(heap); st = step(i)
        alive_a[i] = False; n_alive -= 1; info['peeled'] += 1
        if st[0] == 'good':
            p = st[1]; peeled[p] = i; alive_g[p] = False; m_alive -= 1
            for j in valuers[p]:
                if alive_a[j] and step(j) is not None: heapq.heappush(heap, j)
    X = [None] * m
    for g, i in peeled.items(): X[g] = i
    agents = [i for i in range(n) if alive_a[i]]
    goods = [g for g in range(m) if alive_g[g]]
    if len(agents) <= 1:
        for g in goods: X[g] = agents[0] if agents else 0
        info['branch'] = 'one_agent'; return X, info
    if not goods:
        info['branch'] = 'no_goods'; return X, info
    info['core_n'], info['core_m'] = len(agents), len(goods)

    # 2. Rankings (sort3 of the three remaining relevant goods, largest value first, ties by index)
    a, b, c = {}, {}, {}
    for i in agents:
        rr = [g for g in rel[i] if alive_g[g]]
        assert len(rr) == 3
        a[i], b[i], c[i] = sort3(lambda g: v[i][g], None, rr)
    rank = {i: {a[i]: 0, b[i]: 1, c[i]: 2} for i in agents}
    holders = collections.defaultdict(list)          # good -> agents ranking it
    for i in agents:
        for g in (a[i], b[i], c[i]): holders[g].append(i)

    # 3. Phase 1 in r1Order: the first unprocessed agent (index order) that is not full, else the first one
    in_pool = {g: True for g in goods}
    done = {i: False for i in agents}
    nonfull = []                                      # heap of agents that may be non-full
    ptr = 0                                           # first unprocessed agent in index order
    order, Y, blk, lead = [], {}, {}, {}
    nblk = 0
    for _ in range(len(agents)):
        while nonfull and done[nonfull[0]]: heapq.heappop(nonfull)
        if nonfull: i = heapq.heappop(nonfull); is_full = False
        else:
            while done[agents[ptr]]: ptr += 1
            i = agents[ptr]; is_full = all(in_pool.get(g, False) for g in (a[i], b[i], c[i]))
        if is_full: nblk += 1
        done[i] = True; order.append(i); blk[i] = nblk; lead[i] = is_full
        y = next((g for g in (a[i], b[i], c[i]) if in_pool.get(g, False)), None)
        Y[i] = y
        if y is not None:
            in_pool[y] = False
            for j in holders[y]:
                if not done[j]: heapq.heappush(nonfull, j)
    return _lbplus_fast(agents, goods, order, a, b, c, rank, holders, Y, blk, X, info, naive_owner_test)

def _lbplus_fast(agents, goods, order, a, b, c, rank, holders, Y, blk, X, info, naive_owner_test=False):
    d = 0
    pickrank = lambda Yf, i: 3 if Yf[i] is None else rank[i][Yf[i]]
    def needs(Yf, i):
        return [g for g in (a[i], b[i], c[i])][:pickrank(Yf, i)]
    def na_counts(Yf, upset):
        cnt = collections.Counter()
        for i in agents:
            if i not in upset:
                for g in needs(Yf, i): cnt[g] += 1
        return cnt
    def picker_map(Yf):
        pm = {}
        for k in agents:                              # the first agent (index order) with that pick
            if Yf[k] is not None and Yf[k] not in pm: pm[Yf[k]] = k
        return pm

    # upgrades: repeatedly the first agent (index order) with pick b, c junk and b not in NA
    pm = picker_map(Y)
    J = {g for g in goods if g not in pm}
    upset, uplist = set(), []
    cnt = na_counts(Y, upset)
    cand = [k for k in agents if pickrank(Y, k) == 1]
    heapq.heapify(cand)
    ok = lambda k: k not in upset and pickrank(Y, k) == 1 and c[k] in J and cnt[b[k]] == 0
    while True:
        while cand and not ok(cand[0]): heapq.heappop(cand)
        if not cand: break
        k = heapq.heappop(cand)
        upset.add(k); uplist.insert(0, k); J.discard(c[k])
        cnt[a[k]] -= 1                                # k's only need was a_k
        if cnt[a[k]] == 0:
            for j in holders[a[k]]:
                if b[j] == a[k] and ok(j): heapq.heappush(cand, j)

    def state(Yf, upl):
        ups = set(upl)
        cn = na_counts(Yf, ups)
        pmf = picker_map(Yf)
        upof = {}
        for u in upl:
            if c[u] not in upof: upof[c[u]] = u
        Jl = [g for g in goods if g not in pmf and g not in upof]
        frozen = {k: Yf[k] is not None and cn[Yf[k]] > 0 for k in agents}
        cap = {k: 0 if (frozen[k] or k in ups) else (2 if Yf[k] is None else 1) for k in agents}
        return ups, pmf, upof, Jl, frozen, cap

    def exposed(Yf, ups, Jset, w, pmf):
        base = {Yf[w]} if Yf[w] is not None else set()
        if w in ups: base.add(c[w])
        return [x for x in agents if x != w and x not in ups and Yf[x] == a[x]
                and (b[x] in Jset or b[x] in base) and (c[x] in Jset or c[x] in base)]

    def hit_set(Jset, E):
        # meet: the first x of E (then the first y of E, y != x, then the first g of [b x, c x]) with g junk and
        # g in {b y, c y}
        pos = {x: t for t, x in enumerate(E)}
        occ = collections.defaultdict(list)           # junk good -> E-positions of agents whose {b, c} contain it
        for t, y in enumerate(E):
            for g in {b[y], c[y]}:
                if g in Jset: occ[g].append(t)
        mt = None
        for t, x in enumerate(E):
            best = None
            for g in (b[x], c[x]):
                if g in Jset:
                    ys = [u for u in occ[g][:2] if u != t]
                    if ys and (best is None or ys[0] < best): best = ys[0]
            if best is not None:
                y = E[best]
                g = next(g for g in (b[x], c[x]) if g in Jset and g in (b[y], c[y]))
                mt = (x, y, g); break
        pick_one = lambda z: b[z] if b[z] in Jset else c[z]
        if mt is not None:
            x, y, g = mt
            return [g] + [pick_one(z) for z in E if z != x and z != y]
        return [pick_one(z) for z in E]

    def complete(Yf, upl, st, o, H):
        ups, pmf, upof, Jl, frozen, cap = st
        L = list(H) + [j for j in Jl if j not in set(H)]
        first = {}
        for t, g in enumerate(L):
            if g not in first: first[g] = t
        owner_at, pos = [], 0
        for k in agents:
            s = 0 if o == k else cap[k]
            owner_at.extend([k] * s); pos += s
        for g in goods:
            if g in pmf: X[g] = pmf[g]
            elif g in upof: X[g] = upof[g]
            elif g in first and first[g] < len(owner_at): X[g] = owner_at[first[g]]
            else: X[g] = o if o is not None else d
        return X

    st = state(Y, uplist)
    ups, pmf, upof, Jl, frozen, cap = st
    S = sum(cap.values())
    if len(Jl) <= S:
        info['branch'] = 'noowner'; return complete(Y, uplist, st, None, []), info
    r = next((i for i in reversed(order) if i not in ups), None)
    Jset = set(Jl)
    E = exposed(Y, ups, Jset, r, pmf)
    H = hit_set(Jset, E)
    # Theorem A's counting (proofs/k3_algorithm.md section 4): S - cap(r) >= |E_r| - 1, which makes the owner test
    # exact without a minimum hitting set; asserted on every run as a check of the implementation
    assert S - cap[r] >= len(E) - 1, "Theorem A's counting violated"
    info.update(r=r, E=list(E), H=list(H), free_slots=S - cap[r], junk=list(Jl), order=list(order), picks=dict(Y),
                upgraded=list(uplist))
    if (len(E) if naive_owner_test else len(H)) <= S - cap[r]:
        info['branch'] = 'owner_r'; return complete(Y, uplist, st, r, H), info
    k = next((x for x in exposed(Y, ups, Jset, r, pmf) if blk[x] == blk[r]), None)
    if k is None:
        info['branch'] = 'unreachable'; return complete(Y, uplist, st, r, H), info
    # need chain from k over the agents after k in the order
    cur, ch = k, []
    for j in order[order.index(k) + 1:]:
        if frozen[cur] and j not in ups and Y[cur] is not None and rank[j].get(Y[cur], 3) < pickrank(Y, j):
            ch.append(j); cur = j
    Y2 = dict(Y)
    prev = k
    for j in ch: Y2[j] = Y[prev]; prev = j
    Y2[k] = b[k]
    up2 = [k] + uplist
    st2 = state(Y2, up2)
    ups2, pmf2, upof2, Jl2, frozen2, cap2 = st2
    if len(Jl2) <= sum(cap2.values()):
        info['branch'] = 'rot_noowner'; return complete(Y2, up2, st2, None, []), info
    J2set = set(Jl2)
    H2 = hit_set(J2set, exposed(Y2, ups2, J2set, k, pmf2))
    info['branch'] = 'rot_owner_k'; return complete(Y2, up2, st2, k, H2), info

# ----------------------------------------------------------------------------------------------------------------
# Random instances
# ----------------------------------------------------------------------------------------------------------------

def random_core(n, m, rng, vmax=100):
    """A random instance in which every agent values exactly three goods and is balanced (a < b + c); goods valued
    by nobody may occur. Goods are drawn from range(m)."""
    v = []
    for _ in range(n):
        S = rng.sample(range(m), 3)
        while True:
            x = sorted((rng.randint(1, vmax) for _ in range(3)), reverse=True)
            if x[0] < x[1] + x[2]: break
        v.append(dict(zip(S, x)))
    return v

def random_instance(n, m, rng, vmax=100):
    """A random instance with at most three relevant goods per agent: each agent draws 0-3 goods (mostly 3) and
    arbitrary positive values (so top-heavy agents and ties occur)."""
    v = []
    for _ in range(n):
        k = min(m, rng.choice([0, 1, 2, 3, 3, 3, 3, 3]))
        S = rng.sample(range(m), k)
        v.append({g: rng.randint(1, vmax) for g in S})
    return v

def random_hard(n, m, rng):
    """Random balanced three-good instances whose values come from few levels (many ties), which exercise LB+'s
    rotation more often."""
    v = []
    for _ in range(n):
        S = rng.sample(range(m), 3)
        x = rng.choice([(3, 2, 2), (4, 3, 2), (2, 2, 2), (5, 4, 2), (3, 3, 2)])
        v.append(dict(zip(S, x)))
    return v

def cross(N, seed):
    rng = random.Random(seed)
    tally = collections.Counter()
    for t in range(N):
        kind = t % 3
        n = rng.randint(1, 9)
        if kind == 0: m = rng.randint(max(1, n // 2), 2 * n + 2); v = random_core(n, m, rng) if m >= 3 else random_instance(n, m, rng)
        elif kind == 1: m = rng.randint(1, 2 * n + 3); v = random_instance(n, m, rng)
        else: m = rng.randint(3, 2 * n + 1); v = random_hard(n, m, rng)
        X1, i1 = mirror(n, m, v)
        X2, i2 = fast(n, m, v)
        if X1 != X2 or any(i1[k] != i2[k] for k in ('peeled', 'branch', 'core_n', 'core_m')):
            print("MISMATCH", n, m, v, X1, X2, i1, i2); sys.exit(1)
        if not raw_efx0(n, m, v, X1) or not raw_efx0_naive(n, m, v, X1):
            print("NOT EFX0", n, m, v, X1, i1); sys.exit(1)
        tally[i1['branch']] += 1
    print(f"cross: {N} random instances (seed {seed}): mirror == fast on every one; every output raw EFX0 (both checks)")
    print("branches:", dict(sorted(tally.items())))

# ----------------------------------------------------------------------------------------------------------------
# Certified cores: every ranking profile
# ----------------------------------------------------------------------------------------------------------------

PERMS = list(itertools.permutations(range(3)))
REAL = [(4, 3, 2), (10, 9, 2), (10, 6, 5)]   # balanced realizations of a > b > c (as in tools/check_certs.py, x2)

def _cert_worker(args):
    rec, mirror_every, nreal, sample, seed = args
    n, m, sets = rec['n'], rec['m'], rec['sets']
    tally = collections.Counter(); fails = 0; runs = 0; big = collections.Counter(); mirrored = 0; nprof = 0
    if sample:
        rng = random.Random(seed * 1000003 + hash(tuple(map(tuple, sets))) % 1000003)
        profiles = [tuple(rng.randrange(6) for _ in range(n)) for _ in range(sample)]
    else:
        profiles = itertools.product(range(6), repeat=n)
    for t, prof in enumerate(profiles):
        nprof += 1
        orders = [[sets[i][p] for p in PERMS[prof[i]]] for i in range(n)]
        X0 = None
        for real in REAL[:nreal]:
            v = [dict(zip(orders[i], real)) for i in range(n)]
            X, info = fast(n, m, v)
            runs += 1
            if not raw_efx0(n, m, v, X): fails += 1
            if X0 is None: X0 = X; tally[info['branch']] += 1
            elif X != X0: fails += 1                 # the algorithm is ordinal on cores
        if mirror_every and t % mirror_every == 0:
            v = [dict(zip(orders[i], REAL[0])) for i in range(n)]
            if mirror(n, m, v)[0] != X0: fails += 1
            mirrored += 1
        cnt = collections.Counter(X0)
        big[sum(1 for s in cnt.values() if s > 2)] += 1
    return n, m, runs, fails, tally, big, mirrored, nprof

def certs(paths, jobs, mirror_every, nreal, sample, seed):
    import multiprocessing
    recs = [rec for path in paths for rec in json.load(gzip.open(path))]
    t0 = time.time()
    tot = collections.Counter(); fails = runs = mirrored = nprof = 0; big = collections.Counter(); per = collections.Counter()
    with multiprocessing.Pool(jobs) as pool:
        for n, m, r, f, tally, bg, mi, np_ in pool.imap_unordered(
                _cert_worker, [(rec, mirror_every, nreal, sample, seed) for rec in recs], chunksize=4):
            runs += r; fails += f; tot.update(tally); big.update(bg); per[(n, m)] += 1; mirrored += mi; nprof += np_
    what = f"{sample} random ranking profiles per core (seed {seed})" if sample else "every ranking profile"
    print(f"certs {' '.join(paths)}: {len(recs)} cores {dict(sorted(per.items()))}; {what}: {nprof} profiles x "
          f"{nreal} realizations = {runs} runs; failures (raw EFX0, ordinality, mirror) {fails}; "
          f"mirror compared on {mirrored} profiles; {time.time() - t0:.0f} s")
    print("branches:", dict(sorted(tot.items())))
    print("bundles of > 2 goods per output:", dict(sorted(big.items())))
    return fails

if __name__ == '__main__':
    args = sys.argv[1:]
    opt = {a.split('=')[0]: (a.split('=')[1] if '=' in a else True) for a in args if a.startswith('--')}
    pos = [a for a in args if not a.startswith('--')]
    if '--cross' in args:
        cross(int(pos[0]), int(opt.get('--seed', 1)))
    elif '--certs' in args:
        sys.exit(1 if certs(pos, int(opt.get('--jobs', 4)), int(opt.get('--mirror-every', 0)),
                            int(opt.get('--realizations', 3)), int(opt.get('--sample', 0)), int(opt.get('--seed', 1))) else 0)
    else:
        print(__doc__)
