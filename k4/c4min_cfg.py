"""c4min_cfg: configurations at the fewest frozen agents (k4/c4min.md §1), from the definitions; Python, independent of
k4/c4min.c. Used by the analyses of §4."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import Profile, v, needs, threatened

FOREIGN = -1


def keys(pr):
    """(f, [(NA, phi)]) for the min-frozen valid pre-allocations; phi: tuple, frozen good (frozenset) or None."""
    Ps = pr.valid()
    inf = {P: pr.info(P) for P in Ps}
    f = min(sum(inf[P][3]) for P in Ps)
    ks = set()
    for P in Ps:
        N, NA, J, F, cap = inf[P]
        if sum(F) == f: ks.add((NA, tuple(P[i] if F[i] else None for i in range(pr.n))))
    return f, sorted(ks, key=lambda k: (sorted(k[0]), [sorted(x) if x else [] for x in k[1]]))


class Config:
    def __init__(self, pr, NA, phi, pairs, pool):
        self.pr, self.NA, self.phi, self.Q, self.L = pr, NA, phi, pairs, pool
        self.U = [pr.R[i] - NA for i in range(pr.n)]
        self.free = [i for i in range(pr.n) if phi[i] is None]

    def H(self, x):
        return self.phi[x] if self.phi[x] is not None else self.Q[x] & self.pr.R[x]

    def admissible_in(self, o, S):
        """some B ⊆ S ∩ U_o, |B| <= 2, with needs inside NA"""
        Su = sorted(S & self.U[o])
        if not self.U[o]: return True
        for r in (1, 2):
            for B in itertools.combinations(Su, r):
                if not (needs(self.pr.vals[o], frozenset(B)) & self.U[o]): return True
        return False

    def owner_ok(self, o, unfreeze=True):
        pr = self.pr; X = self.Q[o] | self.L
        NAo = frozenset().union(*[needs(pr.vals[j], self.H(j)) for j in range(pr.n) if j != o])
        cand = [x for x in range(pr.n) if self.phi[x] is not None and not (self.phi[x] & NAo)] if unfreeze else []
        Xl = sorted(X)
        for r in range(len(cand) + 1):
            for C in itertools.combinations(Xl, r):
                C = frozenset(C); Y = X - C
                if not self.admissible_in(o, Y): continue
                if C:
                    No = needs(pr.vals[o], Y & pr.R[o])
                    if sum(1 for x in cand if not (self.phi[x] & No)) < len(C): continue
                if any(threatened(pr.vals[x], Y, self.H(x)) for x in range(pr.n) if x != o): continue
                return True
        return False

    def owners(self, unfreeze=True):
        return [o for o in self.free if self.owner_ok(o, unfreeze)]

    def threats(self):
        """(o, x): x threatened by Q_o ∪ L (no removal)"""
        pr = self.pr
        return [(o, x) for o in self.free for x in range(pr.n) if x != o and threatened(pr.vals[x], self.Q[o] | self.L, self.H(x))]

    # features
    def robust(self, i):
        val = self.pr.vals[i]
        if self.phi[i] is not None:
            return not threatened(val, self.U[i] | {FOREIGN}, self.phi[i])
        return v(val, self.Q[i]) >= v(val, self.U[i] - self.Q[i])

    def pool_threat(self, x):
        return threatened(self.pr.vals[x], self.L | {FOREIGN}, self.phi[x])

    def level(self, i):
        val = self.pr.vals[i]; x = v(val, self.H(i)); gs = list(val)
        return sum(1 for r in range(len(gs) + 1) for T in itertools.combinations(gs, r) if sum(val[g] for g in T) < x)

    def phi_key(self):
        t = sum(self.pool_threat(x) for x in range(self.pr.n) if self.phi[x] is not None)
        r = sum(self.robust(i) for i in range(self.pr.n))
        return (-t, r, sum(self.level(i) for i in range(self.pr.n)))

    def pool_optimal(self):
        pr = self.pr
        for y in self.free:
            vy = v(pr.vals[y], self.Q[y])
            for S in itertools.combinations(sorted(self.Q[y] | self.L), 2):
                if v(pr.vals[y], S) > vy: return False
        return True


def configs(pr, NA, phi):
    n, m = pr.n, pr.m
    Mp = sorted(frozenset(range(m)) - NA)
    free = [i for i in range(n) if phi[i] is None]
    opts = {}
    for i in free:
        U = pr.R[i] - NA
        opts[i] = [frozenset(p) for p in itertools.combinations(Mp, 2) if not (needs(pr.vals[i], frozenset(p) & U) & U)]
    def rec(k, used, cur):
        if k == len(free):
            yield Config(pr, NA, phi, dict(cur), frozenset(Mp) - used); return
        i = free[k]
        for S in opts[i]:
            if S & used: continue
            cur[i] = S
            yield from rec(k + 1, used | S, cur)
            del cur[i]
    yield from rec(0, frozenset(), {})


def exchange_digraph(c):
    """threat edges o -> x (free owner o, x threatened by Q_o ∪ L) and need edges x -> z (frozen x, z needs phi(x))."""
    pr = c.pr; E = {i: [] for i in range(pr.n)}
    for o, x in c.threats(): E[o].append((x, 'T'))
    for x in range(pr.n):
        if c.phi[x] is None: continue
        for z in range(pr.n):
            if z != x and c.phi[x] <= needs(pr.vals[z], c.H(z)): E[x].append((z, 'N'))
    return E


def simple_cycles(E, n, maxlen=None):
    res = []
    def dfs(start, v0, path, seen):
        for w, typ in E[v0]:
            if w == start: res.append(list(path) + [(v0, w, typ)])
            elif w > start and w not in seen and (maxlen is None or len(path) + 1 < maxlen):
                seen.add(w); path.append((v0, w, typ)); dfs(start, w, path, seen); path.pop(); seen.discard(w)
    for s in range(n): dfs(s, s, [], {s})
    return res


def cycle_move(c, cyc, best_pair=True):
    """Apply the exchange along a cycle [(u, w, type)]: w receives Q_u (type T; with best_pair, w takes its best admissible
    pair inside Q_u ∪ L, the rest of Q_u going to the pool) or phi(u) (type N, w becomes/stays frozen). Returns a Config or
    None if the result is not a configuration at the same needed set."""
    pr = c.pr; n = pr.n
    phi = list(c.phi); Q = dict(c.Q); L = set(c.L)
    recv = {}
    for u, w, typ in cyc: recv[w] = (u, typ)
    # everyone on the cycle gives away its holding
    for u, w, typ in cyc:
        if typ == 'N': phi[w] = c.phi[u]; Q.pop(w, None)
    for u, w, typ in cyc:
        if typ == 'T':
            phi[w] = None
            S = c.Q[u]
            if best_pair:
                cand = [frozenset(p) for p in itertools.combinations(sorted(S | L), 2) if frozenset(p) & S]
                U = pr.R[w] - c.NA
                ok = [p for p in cand if not (needs(pr.vals[w], p & U) & U)]
                if not ok: return None
                p = max(ok, key=lambda p: (v(pr.vals[w], p), -len(p - S)))
                L |= S - p; L -= p; Q[w] = p
            else:
                Q[w] = S
    # frozen agents that received a pair: their old good went along a need edge (they are on the cycle)
    for i in range(n):
        if phi[i] is not None: Q.pop(i, None)
    c2 = Config(pr, c.NA, tuple(phi), Q, frozenset(L))
    # validity: frozen goods = NA, pairs disjoint from each other and from NA and the pool, admissible, needs inside NA
    held = [phi[i] for i in range(n) if phi[i] is not None]
    if frozenset().union(*held) != c.NA or len(held) != len(c.NA): return None
    used = frozenset().union(*Q.values()) if Q else frozenset()
    if len(used) != 2 * len(Q) or used & c.NA or used & frozenset(L): return None
    if len(used) + len(L) + len(c.NA) != pr.m: return None
    for i in range(n):
        if needs(pr.vals[i], c2.H(i)) - c.NA: return None
    return c2
