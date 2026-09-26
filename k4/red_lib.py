"""red_lib: configurations with one frozen agent (f = 1), seen as all-pairs allocations of the reduced instance
I' = I - x - g (k4/c4min_reduce.md). Written from the definitions of k4/c4min.md §1 and k4/c4x.md §1; shares no code
with k4/c4min.c or k4/c4min_lib.py (only the type generator of k4/check4.py).

A profile is a list of dicts {good: value}, strict and balanced. Goods are bits of an int mask.
  admissible(i, A, U):  A ⊆ U, 1 <= |A| <= 2, every good of U \\ A worth less (to i) than A
  fewest frozen f:      0 iff every agent has an admissible set for U = R_i, pairwise disjoint;
                        1 iff not 0 and some key (g, x) exists: g = top of x, and the agents y != x have pairwise
                        disjoint admissible sets for U_y = R_y \\ {g} avoiding g (then someone needs g)
  configuration at (g, x): pairs Q_y ⊆ M \\ {g} (y != x), disjoint, Q_y ∩ U_y admissible; pool L = rest (omega goods)
  valid owner o (free): some C ⊆ X = Q_o ∪ L such that X \\ C contains an admissible set of o, |C| <= u (u = 1 if x
                        unfreezes: no free y != o needs g, i.e. v_y(g) > v_y(Q_y), and g is not in o's needs from
                        X \\ C; else u = 0), and no agent other than o strongly envies X \\ C holding its holding
                        ({g} for x, Q_y for free y)."""
import gzip, itertools, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def bits(S):
    while S:
        b = S & -S
        yield b.bit_length() - 1
        S ^= b


def pc(S):
    return bin(S).count('1')


def load_cores(path):
    data = json.load(gzip.open(path, 'rt'))
    return [(c['n'], c['m'], [list(S) for S in c['sets']]) for c in data['cores']]


_DOM = {}
def domains(sets, m):
    key = (tuple(map(tuple, sets)), m)
    if key not in _DOM:
        from check4 import core_domains
        _DOM[key] = core_domains(sets, m, False)
    return _DOM[key]


class Prof:
    def __init__(self, vals, m):
        self.vals = [dict(v) for v in vals]
        self.n = len(vals); self.m = m
        self.R = [sum(1 << g for g in v) for v in vals]
        self.top = [max(v, key=v.get) for v in vals]

    def v(self, i, S):
        val = self.vals[i]
        return sum(val.get(g, 0) for g in bits(S))

    def threat(self, i, X, H):
        """agent i holding H strongly envies X: max_h v_i(X \\ h) > v_i(H)."""
        if not X: return False
        val = self.vals[i]
        tot = 0; mn = None
        for g in bits(X):
            w = val.get(g, 0); tot += w
            mn = w if mn is None or w < mn else mn
        return tot - mn > self.v(i, H)

    def admissible(self, i, A, U):
        if A & ~U or not A or pc(A) > 2: return False
        a = self.v(i, A)
        return all(self.vals[i][g] < a for g in bits(U & ~A))

    def adm_sets(self, i, U):
        gs = list(bits(U)); out = []
        for k in (1, 2):
            for c in itertools.combinations(gs, k):
                A = sum(1 << g for g in c)
                if self.admissible(i, A, U): out.append(A)
        return out


def disjoint_system(P, agents, Us, avoid=0):
    """Is there a choice of pairwise disjoint admissible sets A_y ⊆ U_y (y in agents), avoiding the goods 'avoid'?"""
    opts = [[A for A in P.adm_sets(y, Us[y]) if not A & avoid] for y in agents]
    order = sorted(range(len(agents)), key=lambda k: len(opts[k]))
    def rec(k, used):
        if k == len(order): return True
        for A in opts[order[k]]:
            if not A & used and rec(k + 1, used | A): return True
        return False
    return rec(0, 0)


def fewest_frozen_le1(P):
    """(f, keys): f = 0, or f = 1 with its keys [(g, x)], or f = None when f >= 2."""
    N = range(P.n)
    if disjoint_system(P, list(N), P.R): return 0, []
    keys = []
    for x in N:
        g = P.top[x]
        agents = [y for y in N if y != x]
        Us = {y: P.R[y] & ~(1 << g) for y in agents}
        if disjoint_system(P, agents, Us, avoid=1 << g): keys.append((g, x))
    return (1, keys) if keys else (None, [])


class Key:
    """A key (g, x) of a profile with f = 1, and its configurations (APAs of the reduced instance I')."""
    def __init__(self, P, g, x):
        self.P, self.g, self.x = P, g, x
        self.free = [y for y in range(P.n) if y != x]
        self.Mp = ((1 << P.m) - 1) & ~(1 << g)
        self.U = {y: P.R[y] & ~(1 << g) for y in self.free}
        self.Ux = P.R[x] & ~(1 << g)
        self.omega = P.m - 2 * P.n + 1
        self.pairs = {}
        for y in self.free:
            ps = []
            for c in itertools.combinations(list(bits(self.Mp)), 2):
                Q = (1 << c[0]) | (1 << c[1])
                if P.admissible(y, Q & self.U[y], self.U[y]): ps.append(Q)
            self.pairs[y] = ps

    def configs(self):
        free = self.free
        def rec(k, used, cur):
            if k == len(free):
                yield dict(cur), self.Mp & ~used
                return
            y = free[k]
            for Q in self.pairs[y]:
                if Q & used: continue
                cur[y] = Q
                yield from rec(k + 1, used | Q, cur)
            cur.pop(y, None)
        yield from rec(0, 0, {})

    # ---- features ----
    def robust(self, y, Q):
        P = self.P
        return P.v(y, Q & self.U[y]) >= P.v(y, self.U[y] & ~Q)

    def level(self, y, Q):
        """level of Q ∩ U_y among the subsets of U_y"""
        P = self.P; U = list(bits(self.U[y])); w = P.v(y, Q & self.U[y])
        return sum(1 for k in range(len(U) + 1) for c in itertools.combinations(U, k)
                   if sum(P.vals[y][h] for h in c) < w)

    def needs_g(self, y, H):
        P = self.P
        return (self.P.R[y] >> self.g) & 1 and P.vals[y][self.g] > P.v(y, H)

    # ---- owner tests ----
    def owner_status(self, Q, L, o):
        """returns (free_valid, x_threatened_C0, completable). free_valid: X = Q_o ∪ L threatens no free agent;
        x_threatened_C0: X threatens x; completable: exact test with unfreezing."""
        P = self.P; X = Q[o] | L; x = self.x
        free_valid = not any(P.threat(y, X, Q[y]) for y in self.free if y != o)
        xthr = P.threat(x, X, 1 << self.g)
        if free_valid and not xthr: return free_valid, xthr, True
        # unfreezing: no other free agent needs g
        if any(self.needs_g(y, Q[y]) for y in self.free if y != o): return free_valid, xthr, False
        for c in bits(X):
            Y = X & ~(1 << c)
            if not any(P.admissible(o, A, self.U[o]) for A in self._subsets(Y & self.U[o])): continue
            if self.needs_g(o, Y): continue
            if P.threat(x, Y, 1 << self.g): continue
            if any(P.threat(y, Y, Q[y]) for y in self.free if y != o): continue
            return free_valid, xthr, True
        return free_valid, xthr, False

    @staticmethod
    def _subsets(S):
        gs = list(bits(S))
        for k in (1, 2):
            for c in itertools.combinations(gs, k):
                yield sum(1 << g for g in c)


def profiles(sets, m, rand=None, rng=None):
    doms = domains(sets, m)
    if rand is None:
        for combo in itertools.product(*doms): yield list(combo)
    else:
        for _ in range(rand): yield [rng.choice(D) for D in doms]
