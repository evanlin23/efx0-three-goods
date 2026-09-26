"""Tracer for LB4-style constructions on one explicit profile (integer values), written independently of k4/lb4.c
for the exploration of k4/c4.md.
State: bases, kinds ('pick' for Phase 1 picks, 'upg' for upgraded agents, 'rot' for rotated agents; the last two have
value-based needs, no slot and must satisfy (V2)), needs, validity, frozen agents, slots, omega.
owner_test(st, o): exact test over every C subset of J and every assignment of C to the slots (brute force), with the
owner's needs from its base (w1=False) or from its bundle (w1=True); extra=e adds e dummy slots (deficit measurement).
rotate(st, chain, O): the rotation of k4/lb4.md §2; chains_from(st, k): every need chain from a frozen agent k.
upgrades(st, mode): lb4.c's upgrade loop (1 need-shrinking, 2 envy-free only).
pi_moves / pi_search: upgrades and rotations in which the rotated agent gains (attempts/k4-c4-pareto-moves.md).
owner_last(I, o, tau, O): Phase 1 without o, then o takes O (attempts/k4-c4-owner-last.md).
"""
import itertools, json, os, sys, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

class Inst:
    def __init__(self, sets, vals):
        self.sets = [list(S) for S in sets]
        self.n = len(sets)
        self.m = 1 + max(max(S) for S in sets)
        if isinstance(vals[0], dict):
            self.v = [dict(V) for V in vals]
        else:
            self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.R = [frozenset(S) for S in sets]
        self.ord = [sorted(S, key=lambda g: -self.v[i][g]) for i, S in enumerate(sets)]
        self.rank = [{g: r for r, g in enumerate(self.ord[i])} for i in range(self.n)]
    def val(self, i, S):
        return sum(self.v[i].get(g, 0) for g in S)

def phase1(I, tau):
    """tau: list of choices (index among unprocessed agents in index order) at each insertion step; missing = 0."""
    G = set(range(I.m)); done = [False] * I.n; Y = [None] * I.n; pos = [0] * I.n; blk = [0] * I.n
    b = -1; ins = 0; nopts = []
    for step in range(I.n):
        best = None
        for i in range(I.n):
            if done[i]: continue
            left = len(I.R[i] & G)
            if left < len(I.R[i]):
                fr = next((r for r, g in enumerate(I.ord[i]) if g in G), len(I.R[i]))
                key = (fr, left, i)
                if best is None or key < best[0]: best = (key, i)
        if best is None:
            cand = [i for i in range(I.n) if not done[i]]
            c = tau[ins] if ins < len(tau) else 0
            nopts.append(len(cand))
            c = min(c, len(cand) - 1)
            ins += 1; b += 1
            i = cand[c]
        else:
            i = best[1]
        y = next((g for g in I.ord[i] if g in G), None)
        Y[i] = y
        if y is not None: G.discard(y)
        done[i] = True; pos[i] = step; blk[i] = b
    return Y, pos, blk, frozenset(G), nopts

class State:
    def __init__(self, I, base, kind, J, pos, blk, Y):
        self.I = I; self.base = list(base); self.kind = list(kind); self.J = frozenset(J)
        self.pos = pos; self.blk = blk; self.Y = list(Y)
    def copy(self):
        return State(self.I, self.base, self.kind, self.J, self.pos, self.blk, self.Y)
    def needs(self, i, bundle=None):
        I = self.I
        if bundle is not None:   # value-based needs w.r.t. a bundle (owner's needs from its bundle)
            return frozenset(g for g in I.R[i] - bundle if I.v[i][g] > I.val(i, bundle))
        if self.kind[i] == 'pick':
            y = self.Y[i]
            if y is None: return I.R[i]
            return frozenset(I.ord[i][:I.rank[i][y]])
        B = self.base[i]
        return frozenset(g for g in I.R[i] - B if I.v[i][g] > I.val(i, B))
    def NA(self, owner=None, obundle=None):
        s = set()
        for i in range(self.I.n):
            s |= self.needs(i, obundle if i == owner and obundle is not None else None)
        return frozenset(s)
    def valid(self):
        NA = self.NA()
        if self.J & NA: return False
        for i in range(self.I.n):
            if self.kind[i] in ('rot','upg') and self.base[i] & NA: return False
            if len(self.base[i]) >= 2 and self.base[i] & NA: return False
        if sum(len(B) >= 3 for B in self.base) >= 2: return False
        return True
    def frozen(self, NA=None):
        NA = self.NA() if NA is None else NA
        return [len(self.base[i]) == 1 and self.kind[i] == 'pick' and bool(self.base[i] & NA) for i in range(self.I.n)]
    def caps(self, NA=None, rot_slot=False):
        fr = self.frozen(NA)
        out = []
        for i in range(self.I.n):
            if fr[i]: out.append(0)
            elif self.kind[i] in ('rot','upg') and not rot_slot: out.append(0)
            elif self.kind[i] == 'upg': out.append(0)
            else: out.append(max(0, 2 - len(self.base[i])))
        return out
    def omega(self):
        return len(self.J) - sum(self.caps())

def threatened(I, x, L, H):
    """exists h in L: v_x(L - h) > v_x(H)"""
    Q = L & I.R[x]
    if not Q: return False
    vH = I.val(x, H)
    if L - I.R[x]:
        return I.val(x, Q) > vH
    return I.val(x, Q) - min(I.v[x][g] for g in Q) > vH

def owner_test(st, o, w1=True, rot_slot=False, want_all=False, extra=0):
    """Exact: some C subset of J, assigned to slots of agents other than o (cap from NA with owner's needs from its
    bundle if w1), such that no agent j != o is threatened by L = B_o + (J - C) with its own bundle.
    Returns a completion (list of bundles) or None."""
    I = st.I; J = sorted(st.J); n = I.n
    sols = []
    for r in range(len(J), -1, -1):
        for C in itertools.combinations(J, r):
            C = frozenset(C)
            L = st.base[o] | (st.J - C)
            NA = st.NA(owner=o, obundle=L if w1 else None)
            caps = st.caps(NA, rot_slot)
            caps[o] = 0
            if sum(caps) + extra < len(C): continue
            # agents without room must be unthreatened
            bad = False
            thr = []
            for x in range(n):
                if x == o: continue
                if caps[x] == 0:
                    if threatened(I, x, L, st.base[x]): bad = True; break
                elif threatened(I, x, L, st.base[x]):
                    thr.append(x)
            if bad: continue
            # assign C to slots: brute force over assignments (small)
            slots = [x for x in range(n) if x != o for _ in range(caps[x])] + [-1] * extra
            Cl = sorted(C)
            found = None
            for perm in itertools.permutations(slots, len(Cl)):
                X = [set(st.base[x]) for x in range(n)]
                for g, x in zip(Cl, perm):
                    if x >= 0: X[x].add(g)
                if all(not threatened(I, x, L, frozenset(X[x])) for x in thr):
                    X[o] = set(L); found = X; break
            if found is not None:
                if not want_all: return found
                sols.append((C, found))
    return sols if want_all else None

def owner_test_none(st):
    caps = st.caps()
    if len(st.J) > sum(caps): return None
    X = [set(B) for B in st.base]
    J = sorted(st.J)
    slots = [x for x in range(st.I.n) for _ in range(caps[x])]
    for g, x in zip(J, slots): X[x].add(g)
    return X

def efx0(I, X):
    for i in range(I.n):
        mine = I.val(i, X[i])
        for j in range(I.n):
            if j != i and X[j]:
                if mine < I.val(i, X[j]) - min(I.v[i].get(g, 0) for g in X[j]): return False
    return True

def initial_state(I, tau):
    Y, pos, blk, J, nopts = phase1(I, tau)
    base = [frozenset([y]) if y is not None else frozenset() for y in Y]
    return State(I, base, ['pick'] * I.n, J, pos, blk, Y), nopts

def chains_from(st, k):
    """need chains k = x0 -> x1 -> ... -> xt, x1..x_{t-1} frozen, xt not frozen, Y_{x_{i-1}} in N_{x_i}"""
    fr = st.frozen()
    out = []
    def ext(ch):
        x = ch[-1]
        if len(ch) > 1 and not fr[x]:
            out.append(list(ch)); return
        y = st.Y[x]
        if y is None or st.kind[x] != 'pick': return
        for j in range(st.I.n):
            if j in ch: continue
            if y in st.needs(j):
                ext(ch + [j])
    ext([k])
    return out

def rotate(st, ch, O):
    I = st.I; k, t = ch[0], ch[-1]
    ns = st.copy()
    J = set(ns.J) | set(ns.base[t])
    newY = list(ns.Y)
    for i in range(len(ch) - 1, 0, -1):
        newY[ch[i]] = st.Y[ch[i - 1]]
    for i in range(1, len(ch)):
        x = ch[i]; ns.Y[x] = newY[x]; ns.base[x] = frozenset([newY[x]]); ns.kind[x] = 'pick'
    J -= set(O)
    ns.base[k] = frozenset(O); ns.kind[k] = 'rot'; ns.Y[k] = None
    ns.J = frozenset(J)
    return ns

def rot_options(st, ch):
    I = st.I; k, t = ch[0], ch[-1]
    W = (st.J | st.base[t]) & I.R[k]
    W = sorted(W)
    for r in (2, 3, 1, 4):
        for O in itertools.combinations(W, r):
            yield frozenset(O)

def free_owners(st):
    fr = st.frozen()
    return [o for o in range(st.I.n) if not fr[o]]

def try_owners(st, owners=None, w1=True, rot_slot=False):
    """returns (owner, X) or None; owner -1 means no owner"""
    if not st.valid(): return None
    big = [i for i in range(st.I.n) if len(st.base[i]) >= 3]
    if big:
        X = owner_test(st, big[0], w1, rot_slot)
        return (big[0], X) if X else None
    if st.omega() <= 0:
        X = owner_test_none(st)
        if X: return (-1, X)
    for o in (owners if owners is not None else free_owners(st)):
        X = owner_test(st, o, w1, rot_slot)
        if X: return (o, X)
    return None

def search(st, depth, path=(), out=None, w1=True, all_paths=True, rot_slot=False):
    """all rotation paths (up to depth) after which some owner works; st assumed to fail already"""
    if out is None: out = []
    if depth == 0: return out
    fr = st.frozen()
    for k in sorted(range(st.I.n), key=lambda i: -st.pos[i]):
        if not fr[k]: continue
        for ch in chains_from(st, k):
            for O in rot_options(st, ch):
                ns = rotate(st, ch, O)
                if not ns.valid(): continue
                res = try_owners(ns, w1=w1, rot_slot=rot_slot)
                p = path + ((tuple(ch), tuple(sorted(O))),)
                if res:
                    out.append((p, res[0], res[1]))
                    if not all_paths: return out
                else:
                    search(ns, depth - 1, p, out, w1, all_paths, rot_slot)
                    if out and not all_paths: return out
    return out

def show(st):
    return f"Y={st.Y} base={[sorted(b) for b in st.base]} kind={st.kind} J={sorted(st.J)} frozen={st.frozen()} caps={st.caps()} omega={st.omega()}"

def tclass(I, i):
    """threat class of a 4-good agent's top vs pairs of lower goods, and b vs c+d"""
    o = I.ord[i]; v = I.v[i]
    if len(o) == 3: return '3g'
    a, b, c, d = (v[g] for g in o)
    s = 'A>bc' if a > b + c else ('A>bd' if a > b + d else ('A>cd' if a > c + d else 'flat'))
    s += (',b>cd' if b > c + d else ',b<cd')
    return s

def pretty(st):
    I = st.I; fr = st.frozen(); NA = st.NA(); caps = st.caps()
    lines = []
    for p in range(I.n):
        i = [j for j in range(I.n) if st.pos[j] == p][0]
        o = I.ord[i]
        rk = '>'.join(f"{g}{'*' if g in st.J else ''}" for g in o)
        lines.append(f"  pos{p} blk{st.blk[i]} agent{i} [{rk}] {tclass(I,i)} vals={[I.v[i][g] for g in o]} base={sorted(st.base[i])}({st.kind[i]}) N={sorted(st.needs(i))} {'FROZEN' if fr[i] else 'free cap'+str(caps[i])}")
    lines.append(f"  J={sorted(st.J)} omega={st.omega()}")
    return '\n'.join(lines)

def phase1_sub(I, agents, tau, G0=None):
    """Phase 1 restricted to the given agents (others absent), goods G0 (default all)."""
    G = set(range(I.m)) if G0 is None else set(G0)
    done = {i: False for i in agents}; Y = [None] * I.n; pos = [-1] * I.n; blk = [-1] * I.n
    b = -1; ins = 0; nopts = []
    for step in range(len(agents)):
        best = None
        for i in agents:
            if done[i]: continue
            left = len(I.R[i] & G)
            if left < len(I.R[i]):
                fr = next((r for r, g in enumerate(I.ord[i]) if g in G), len(I.R[i]))
                key = (fr, left, i)
                if best is None or key < best[0]: best = (key, i)
        if best is None:
            cand = [i for i in agents if not done[i]]
            c = tau[ins] if ins < len(tau) else 0
            nopts.append(len(cand)); c = min(c, len(cand) - 1); ins += 1; b += 1
            i = cand[c]
        else:
            i = best[1]
        y = next((g for g in I.ord[i] if g in G), None)
        Y[i] = y
        if y is not None: G.discard(y)
        done[i] = True; pos[i] = step; blk[i] = b
    return Y, pos, blk, frozenset(G), nopts

def owner_last(I, o, tau, O=None):
    agents = [i for i in range(I.n) if i != o]
    Y, pos, blk, G, nopts = phase1_sub(I, agents, tau)
    pos[o] = I.n; blk[o] = max(blk) + 1
    base = [frozenset([y]) if y is not None else frozenset() for y in Y]
    Ob = (G & I.R[o]) if O is None else frozenset(O)
    base[o] = Ob
    kind = ['pick'] * I.n; kind[o] = 'rot'
    st = State(I, base, kind, G - Ob, pos, blk, Y)
    return st

def exposed(st, o, X_o_goods):
    """agents x != o threatened by the bundle X_o_goods when holding their base alone"""
    return [x for x in range(st.I.n) if x != o and threatened(st.I, x, frozenset(X_o_goods), st.base[x])]

def rho(st, x, o):
    """min number of junk goods of R_x that must leave X_o = B_o + J so that x (holding its base) is safe"""
    I = st.I; L = st.base[o] | st.J
    cand = sorted(st.J & I.R[x])
    for r in range(len(cand) + 1):
        for T in itertools.combinations(cand, r):
            if not threatened(I, x, L - frozenset(T), st.base[x]): return r
    return 99

def base_val(st, i):
    return st.I.val(i, st.base[i])

def search_pi(st, depth, path=(), w1=True, strict_k=True):
    """rotation paths where the rotated agent k strictly gains (v_k(O) > v_k(old base)); returns first success"""
    if depth == 0: return None
    fr = st.frozen()
    for k in sorted(range(st.I.n), key=lambda i: -st.pos[i]):
        if not fr[k]: continue
        for ch in chains_from(st, k):
            for O in rot_options(st, ch):
                if strict_k and st.I.val(k, O) <= base_val(st, k): continue
                ns = rotate(st, ch, O)
                if not ns.valid(): continue
                p = path + ((tuple(ch), tuple(sorted(O))),)
                res = try_owners(ns, w1=w1)
                if res: return (p, res)
                sub = search_pi(ns, depth - 1, p, w1, strict_k)
                if sub: return sub
    return None

def pi_moves(st, allow_upg=True, allow_rot=True):
    """Pareto-improving moves: upgrades (a free pick agent adds a junk good of its own) and rotations in which the
    rotated agent strictly gains. Yields (desc, new_state)."""
    I = st.I; fr = st.frozen()
    if allow_upg:
        for k in range(I.n):
            if st.kind[k] != 'pick' or fr[k] or st.Y[k] is None: continue
            for g in sorted(st.J & I.R[k]):
                ns = st.copy(); ns.base[k] = st.base[k] | {g}; ns.kind[k] = 'rot'; ns.J = st.J - {g}
                if ns.valid(): yield (('U', k, g), ns)
    if allow_rot:
        for k in sorted(range(I.n), key=lambda i: -st.pos[i]):
            if not fr[k]: continue
            for ch in chains_from(st, k):
                for O in rot_options(st, ch):
                    if I.val(k, O) <= base_val(st, k): continue
                    ns = rotate(st, ch, O)
                    if ns.valid(): yield (('R', tuple(ch), tuple(sorted(O))), ns)

def pi_search(st, depth, path=(), seen=None, **kw):
    if seen is None: seen = set()
    res = try_owners(st)
    if res: return (path, res)
    if depth == 0: return None
    key = (tuple(st.base), tuple(st.kind))
    if key in seen: return None
    seen.add(key)
    for desc, ns in pi_moves(st, **kw):
        r = pi_search(ns, depth - 1, path + (desc,), seen, **kw)
        if r: return r
    return None

def upgrades(st, mode):
    """lb4.c's upgrade loop: mode 1 need-shrinking, 2 envy-free only; smallest index first, best good first"""
    I = st.I
    if mode == 0: return st
    st = st.copy()
    again = True
    while again:
        again = False
        NA = st.NA()
        for k in range(I.n):
            if st.kind[k] != 'pick' or st.Y[k] is None or st.Y[k] in NA: continue
            Nk = st.needs(k)
            if not Nk: continue
            for g in I.ord[k]:
                if g not in st.J: continue
                B = st.base[k] | {g}
                nn = frozenset(x for x in Nk if I.v[k][x] > I.val(k, B))
                if mode == 2 and I.val(k, B) < I.val(k, I.R[k] - B): continue
                if nn != Nk:
                    st.base[k] = B; st.kind[k] = 'upg'; st.J = st.J - {g}; again = True; break
            if again: break
    return st
