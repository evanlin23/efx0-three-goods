"""Raw primitives for the base case "OC1 with phantom constraints" (workstream proof/k4-base-phantom).

Written from the definitions only (PROMPT.md section 1, k4/sdc.md section 29, k4/matching.md section 6,
k4/oc1max_multi.md sections 14-17); it imports nothing from k4/matching, k4/oc1max_multi or k4/sdc.

Goods are bits of an int mask.  An allocation (or state) is a list of masks, one per agent of the full instance I.

* threat(i, S, t): some good h of S has v_i(S - h) > t.  Equivalently v_i(S) - mu_i(S) > t with mu_i(S) the least
  value i gives a good of S (0 if S holds a good i does not value); never for |S| <= 1.
* EFX0(X): no bundle threatens another agent at that agent's own value.
* A *state* (alive, goods, B): the present agents and goods of the current reduced instance, and the bases B (every
  deleted agent k holds its fixed set T_k; it is a *phantom* with threshold tau_k = v_k(T_k)).  J = goods minus the
  present agents' bases.
* wants(i, g): v_i(g) > v_i(B_i).  frozen: a single-good holder whose good another present agent wants.
  dangerous: frozen and valuing a junk good.
* A settlement (k, P, T) (k4/matching.md section 6): k dangerous, P = (k = x0, x1, .., xt) a canonical chain (each x_l,
  l >= 1, wants x_{l-1}'s single good), T inside (J + B_{xt}) and R_k, improving for k.  A round: at most RMAX
  settlements with vertex-disjoint chains and disjoint T's, all applied at once.  Admissible: (L*) at the round's end
  (no T_a threatens another agent present at the round's start, at its value after the round, the other settled
  agents at v(T_b)), (P2) no T_a threatens an earlier phantom at its threshold, and the reduced state is a perfect SD
  outcome of the reduced instance.
* lifted completion: the one-absorber completion of a state over the present agents (one present owner takes any set
  of junk, every other present agent at most one junk good, phantoms nothing), raw EFX0 in I.
* official move (k4/sdc.md section 29): a chain x0..xt (t >= 1) of distinct present agents with disjoint H0 inside
  (J + B_{xt}) and R_{x0}, H_l inside J and R_{x_l}; v_{x0}(H0) > v_{x0}(B_{x0}) and
  v_{x_l}(B_{x_{l-1}} + H_l) > v_{x_l}(B_{x_l}); the rest of B_{xt} becomes junk.  (H0 containing B_{xt} is a ring.)
"""
import itertools

RMAX = 2


def bits(mask):
    out = []
    while mask:
        b = mask & -mask
        out.append(b.bit_length() - 1)
        mask ^= b
    return out


def pc(mask):
    return bin(mask).count('1')


class Inst:
    def __init__(self, sets, vals):
        self.n = len(sets)
        self.m = 1 + max(max(s) for s in sets if s)
        self.val = [[0] * self.m for _ in range(self.n)]
        for i, (s, x) in enumerate(zip(sets, vals)):
            for g, a in zip(s, x):
                assert a > 0
                self.val[i][g] = a
        self.R = [sum(1 << g for g in range(self.m) if self.val[i][g] > 0) for i in range(self.n)]
        self.Rl = [[g for g in range(self.m) if self.val[i][g] > 0] for i in range(self.n)]
        # strict values per agent (3 starts of the data, log459, have a tie; SD then breaks ties by the smaller good)
        self.strict = all(len(set(self.val[i][g] for g in self.Rl[i])) == len(self.Rl[i]) for i in range(self.n))
        self.ALL = (1 << self.m) - 1

    def V(self, i, S):
        v = self.val[i]
        return sum(v[g] for g in self.Rl[i] if S >> g & 1)

    def th(self, i, S):
        """max over h in S of v_i(S - h) (0 for |S| <= 1)."""
        if S & (S - 1) == 0:
            return 0
        v = self.val[i]
        rel = [v[g] for g in self.Rl[i] if S >> g & 1]
        if not rel:
            return 0
        s = sum(rel)
        if S & ~self.R[i]:
            return s
        return s - min(rel)

    def threat(self, i, S, t):
        return self.th(i, S) > t

    def efx0(self, X, agents=None):
        ags = range(self.n) if agents is None else agents
        for i in ags:
            vi = self.V(i, X[i])
            Ri = self.R[i]
            for j in ags:
                if j != i and X[j] & Ri and self.th(i, X[j]) > vi:
                    return False
        return True

    def efx0_violations(self, X):
        out = []
        for i in range(self.n):
            vi = self.V(i, X[i])
            for j in range(self.n):
                if j != i and self.th(i, X[j]) > vi:
                    out.append((i, j))
        return out

    # serial dictatorship -------------------------------------------------------------------------------------------
    def sd(self, order, goods):
        taken = 0
        Y = {}
        for i in order:
            av = [g for g in self.Rl[i] if goods >> g & 1 and not taken >> g & 1]
            if av:
                g = max(av, key=lambda h: (self.val[i][h], -h))
                Y[i] = g
                taken |= 1 << g
        return Y

    def is_sd(self, alive, goods, B):
        """B restricted to `alive` is a perfect SD outcome (every present agent holds exactly one good, which SD of some
        order of the present agents over `goods` gives it).  Characterization (strict values): every agent holds a good
        it values, values no unpicked present good above it, and the wants digraph on the picks is acyclic."""
        picks = 0
        for i in alive:
            b = B[i]
            if b == 0 or b & (b - 1) or not b & self.R[i] or not b & goods:
                return False
            picks |= b
        J = goods & ~picks
        y = {i: B[i].bit_length() - 1 for i in alive}
        for i in alive:
            p = self.val[i][y[i]]
            if any(self.val[i][g] > p for g in self.Rl[i] if J >> g & 1):
                return False
        # acyclic wants digraph
        succ = {i: [j for j in alive if j != i and self.val[i][y[j]] > self.val[i][y[i]]] for i in alive}
        state = {}

        def cyc(u):
            state[u] = 1
            for w in succ[u]:
                if state.get(w) == 1:
                    return True
                if w not in state and cyc(w):
                    return True
            state[u] = 2
            return False
        return not any(u not in state and cyc(u) for u in alive)

    def is_sd_brute(self, alive, goods, B):
        tgt = {i: B[i].bit_length() - 1 for i in alive if B[i]}
        if any(B[i] & (B[i] - 1) for i in alive):
            return False
        for o in itertools.permutations(alive):
            Y = self.sd(o, goods)
            if Y == tgt and len(Y) == len(alive):
                return True
        return False


# states -------------------------------------------------------------------------------------------------------------
class State:
    """alive: tuple of present agents; goods: mask of present goods; B: tuple of masks (all agents; phantoms hold T)."""
    __slots__ = ('alive', 'goods', 'B', 'dead')

    def __init__(self, alive, goods, B, dead=()):
        self.alive = tuple(alive)
        self.goods = goods
        self.B = tuple(B)
        self.dead = tuple(dead)

    def key(self):
        return (self.alive, self.goods, self.B)

    def junk(self):
        u = 0
        for i in self.alive:
            u |= self.B[i]
        return self.goods & ~u


def wants(I, B, i, g):
    return I.val[i][g] > I.V(i, B[i])


def frozen(I, S, k):
    b = S.B[k]
    if b == 0 or b & (b - 1):
        return False
    g = b.bit_length() - 1
    return any(i != k and wants(I, S.B, i, g) for i in S.alive)


def dangerous(I, S):
    J = S.junk()
    return [k for k in S.alive if frozen(I, S, k) and I.R[k] & J]


def canonical_chains(I, S, k):
    out = []

    def ext(P):
        last = S.B[P[-1]]
        if last == 0 or last & (last - 1):
            return
        g = last.bit_length() - 1
        for w in S.alive:
            if w not in P and wants(I, S.B, w, g):
                out.append(P + (w,))
                ext(P + (w,))
    ext((k,))
    return out


def submasks(mask, maxsize=99, minsize=1):
    bl = bits(mask)
    for r in range(minsize, min(len(bl), maxsize) + 1):
        for c in itertools.combinations(bl, r):
            yield sum(1 << g for g in c)


def settlements(I, S, tmax=3):
    J = S.junk()
    out = []
    for k in dangerous(I, S):
        vk = I.V(k, S.B[k])
        for P in canonical_chains(I, S, k):
            pool = (J | S.B[P[-1]]) & I.R[k]
            for T in submasks(pool, tmax):
                if I.V(k, T) > vk:
                    out.append((k, P, T))
    return out


def apply_settlements(S, combo):
    nb = list(S.B)
    for k, P, T in combo:
        nb[k] = T
        for a in range(1, len(P)):
            nb[P[a]] = S.B[P[a - 1]]
    return nb


def rounds(I, S, rmax=RMAX, lstar=True, p2=True, tmax=3, need_sd=True):
    """Every admissible round at S: yields (combo, new State)."""
    sets = settlements(I, S, tmax)
    for r in range(1, rmax + 1):
        for combo in itertools.combinations(sets, r):
            ags = [x for _, P, _ in combo for x in P]
            if len(ags) != len(set(ags)):
                continue
            Tu = 0
            ok = True
            for _, _, T in combo:
                if Tu & T:
                    ok = False
                    break
                Tu |= T
            if not ok:
                continue
            nb = apply_settlements(S, combo)
            if lstar:
                if any(I.th(i, T) > I.V(i, nb[i]) for k, _, T in combo for i in S.alive if i != k):
                    continue
            if p2:
                if any(I.th(f, T) > I.V(f, S.B[f]) for _, _, T in combo for f in S.dead):
                    continue
            K = set(k for k, _, _ in combo)
            alive2 = tuple(a for a in S.alive if a not in K)
            goods2 = S.goods & ~Tu
            if need_sd and alive2 and not I.is_sd(alive2, goods2, nb):
                continue
            yield combo, State(alive2, goods2, nb, S.dead + tuple(sorted(K)))


# completions --------------------------------------------------------------------------------------------------------
def one_absorber(I, B, recv, J, owners=None, want_all=False):
    """One-absorber completions of base B: one owner o in `owners` (default recv) takes any subset of J, every other
    agent of `recv` at most one good of J, all other agents nothing.  Returns the first EFX0 allocation (or all of
    them with want_all)."""
    Jl = bits(J)
    own = recv if owners is None else owners
    found = []
    for o in own:
        others = [u for u in recv if u != o]
        # kept-out set H assigned injectively to `others`
        for r in range(0, min(len(Jl), len(others)) + 1):
            for H in itertools.combinations(Jl, r):
                Hm = sum(1 << g for g in H)
                Xo = B[o] | (J & ~Hm)
                # necessary: Xo threatens no agent outside recv at its base, no receiver beyond its best gain
                bad = False
                for i in range(I.n):
                    if i == o:
                        continue
                    t = I.V(i, B[i])
                    if i in others and H:
                        t += max(I.val[i][g] for g in H)
                    if I.th(i, Xo) > t:
                        bad = True
                        break
                if bad:
                    continue
                for recvs in itertools.permutations(others, r):
                    X = list(B)
                    X[o] = Xo
                    for g, u in zip(H, recvs):
                        X[u] = X[u] | (1 << g)
                    if I.efx0(X):
                        if not want_all:
                            return X
                        found.append(X)
    return found if want_all else None


def lifted_completion(I, S, deadrecv=False, want_all=False):
    recv = list(range(I.n)) if deadrecv else list(S.alive)
    return one_absorber(I, list(S.B), recv, S.junk(), want_all=want_all)


def extensions(I, S, want_all=False, limit=None):
    """Every EFX0 allocation of I in which each phantom keeps its T and the present goods go to present agents in any
    way (no base kept).  Backtracking over goods; a threat to a phantom is permanent, a threat to a present agent is
    pruned when even all unassigned goods could not lift it."""
    gl = bits(S.goods)
    al = list(S.alive)
    X = list(S.B)
    for a in al:
        X[a] = 0
    rem = [0] * (len(gl) + 1)
    for t in range(len(gl) - 1, -1, -1):
        rem[t] = rem[t + 1] | (1 << gl[t])
    out = []

    def ok(t):
        R = rem[t]
        for i in range(I.n):
            vi = I.V(i, X[i]) + (I.V(i, R) if i in al else 0)
            for j in range(I.n):
                if j != i and X[j] & I.R[i] and I.th(i, X[j]) > vi:
                    return False
        return True

    def rec(t):
        if t == len(gl):
            if I.efx0(X):
                out.append(list(X))
                return not want_all or (limit is not None and len(out) >= limit)
            return False
        g = 1 << gl[t]
        for a in al:
            X[a] |= g
            if ok(t + 1) and rec(t + 1):
                return True
            X[a] &= ~g
        return False
    rec(0)
    return out if want_all else (out[0] if out else None)


# official moves -----------------------------------------------------------------------------------------------------
def official_moves(I, S, maxlen=None, mid_junk=True):
    """Every official move of the present instance at S (k4/sdc.md section 29, chains of length >= 2): yields
    (P, H0, Hs, new B).  With mid_junk=False the agents after x0 take no junk."""
    J = S.junk()
    al = S.alive
    L = len(al) if maxlen is None else min(maxlen, len(al))
    for t1 in range(2, L + 1):
        for P in itertools.permutations(al, t1):
            x0 = P[0]
            v0 = I.V(x0, S.B[x0])
            pool0 = (J | S.B[P[-1]]) & I.R[x0]
            for H0 in submasks(pool0):
                if I.V(x0, H0) <= v0:
                    continue
                rest = J & ~H0
                # junk for middle agents
                yield from _mid(I, S, P, H0, rest, 1, [S.B[a] for a in range(0)], mid_junk, [])


def _mid(I, S, P, H0, rest, l, _unused, mid_junk, Hs):
    if l == len(P):
        nb = list(S.B)
        nb[P[0]] = H0
        for a in range(1, len(P)):
            nb[P[a]] = S.B[P[a - 1]] | Hs[a - 1]
        yield P, H0, tuple(Hs), nb
        return
    x = P[l]
    base = S.B[P[l - 1]]
    vx = I.V(x, S.B[x])
    opts = [0]
    if mid_junk:
        opts += list(submasks(rest & I.R[x]))
    for H in opts:
        if I.V(x, base | H) > vx:
            yield from _mid(I, S, P, H0, rest & ~H, l + 1, None, mid_junk, Hs + [H])


def state_after_move(S, nb):
    return State(S.alive, S.goods, nb, S.dead)


# loading ------------------------------------------------------------------------------------------------------------
def load_rows(path):
    import gzip
    import json
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt') as f:
        if path.endswith('.jsonl') or path.endswith('.jsonl.gz'):
            for line in f:
                if line.strip():
                    r = json.loads(line)
                    yield dict(sets=r['sets'], vals=r['vals'], picks=r['picks'], name=r.get('name', ''),
                               src=path.split('/')[-1])
        else:
            d = json.load(f)
            for h in d['hypergraphs']:
                for s in h['starts']:
                    yield dict(sets=h['sets'], vals=s['vals'], picks=s['picks'],
                               name='%s#%s' % (h.get('list'), h.get('idx')), src=path.split('/')[-1])


def start_state(I, picks):
    B = [1 << g for g in picks]
    return State(tuple(range(I.n)), I.ALL, B, ())


def row_key(r):
    return (tuple(map(tuple, r['sets'])), tuple(map(tuple, r['vals'])), tuple(r['picks']))
