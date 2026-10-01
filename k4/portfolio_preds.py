"""The predicate registry of the k = 4 deficit-descent portfolio (compute/k4-portfolio). EVIDENCE tooling.

Objects (k4/dl2.md §3, k4/dlrt4.c's header, k4/dl13.md §2.3 Remark). For one strict profile with fewest frozen agents
f >= 1 and omega >= 1, the *min-frozen class* is the set of valid pre-allocations P with exactly f frozen agents;
def(P) is the removal-only deficit (+inf when no free agent can own); a *state* is a min-frozen P with def(P) > 0.
For agent i with base B_i: N_i(B_i) = the goods of R_i outside B_i worth more than B_i; NA = the union of the N_i;
i is *frozen* iff B_i is one good inside NA. By (V1) and (V2) every needed good is a one-good base, so
NA(P) = the union of the frozen agents' bases and |NA(P)| = f; in particular NA(Q) = NA(P) iff the frozen goods are the
same set.

A move P -> Q between min-frozen P, Q is described by (`Move`):
  ch  the agents whose base differs;
  U   the agents frozen in P and free in Q, Z the agents free in P and frozen in Q (over all agents; when NA(Q) = NA(P)
      an unchanged agent keeps its status, so U, Z lie inside ch), W the agents of ch frozen in both, Y the agents of
      ch free in both;
  keep  NA(Q) = NA(P);
  give  every y in Y gives up a good of its base (B_y(P) is not inside B_y(Q));
  need  every z in Z needs its new good in P (B_z(Q) inside N_z(B_z(P)));
  chain the bases of W + Z in Q are exactly the bases of W + U in P (as a set of one-good bases). When keep holds,
        chain holds automatically (both sides are NA minus the goods of the unchanged frozen agents), so it is a
        consistency check, not a restriction.
Since P and Q both have exactly f frozen agents, |U| = |Z| for every move; so "|U| = |Z|" (NAbal) adds nothing to
"NA kept" (NAall) and "|U| <= 1 and |Z| <= 1" is "|U| <= 1". Both are registered as asked and must agree.

The moves of k4/dl2.md §3 and k4/dlrt4.c, in these terms (each equivalent to the cited definition, see the comments):
  T1   |ch| = 1, keep
  T2   |ch| >= 2, keep, U = Z = W = {} (every changed agent free in P and in Q)
  T3   keep, |U| = |Z| = 1, W = {}, |Y| <= 1, give, need (then z takes x's good: chain with W empty)
  T4   keep, ch nonempty, U = Z = Y = {} (the frozen agents of ch permute their goods)
  T3+  (the frozen-chain role swap, ledger K4.DL2.RC) keep, |U| = |Z| = 1, |Y| <= 1, give, need, chain
Single-step forms DL_R: every state P has a min-frozen Q with def(Q) < def(P) and R(P, Q) ("a repair").
Key-graph forms (k4/dl13.md §2.3 Remark): key(P) = (NA, the frozen agents with their bases) -- by the remark above,
just the map frozen agent -> its good; def*(K) = the least def over the min-frozen P of key K. DL on the key graph with
edges E: every key K with def*(K) > 0 has a key K' != K with def*(K') < def*(K) such that some state P of K has an
E-move to some min-frozen Q of key K' (the move itself need not lower the deficit).

The registry: SINGLE and KEYG, ordered from the strongest statement (smallest relation) to the weakest, each entry
(name, doc, test(move) -> bool). Shapes of repairs are "U|W|Z|Y" with "~" appended when NA changes; the *smallest*
repair of a state (key) is the least by (|ch|, |U| + |W|, |Y|, shape string)."""
import collections

Move = collections.namedtuple('Move', 'nch nU nZ nW nY keep give need chain')


def popc(x): return bin(x).count('1')


class ProfData:
    """one profile: sets, vals (lists aligned with sets), m, the min-frozen class as (bases, def) with bases a tuple of
    good bitmasks (one per agent) and def an int (INF for +inf)"""
    INF = float('inf')

    def __init__(self, sets, vals, m, cls):
        self.sets, self.vals, self.m, self.n = sets, vals, m, len(sets)
        self.vm = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.P = [tuple(B) for B, _ in cls]
        self.d = [d for _, d in cls]
        n = self.n
        self.N, self.NA, self.F = [], [], []
        for B in self.P:
            Ni = []
            for i in range(n):
                b = sum(x for g, x in self.vm[i].items() if B[i] >> g & 1)
                Ni.append(sum(1 << g for g, x in self.vm[i].items() if not B[i] >> g & 1 and x > b))
            NA = 0
            for x in Ni: NA |= x
            F = sum(1 << i for i in range(n) if popc(B[i]) == 1 and B[i] & NA)
            self.N.append(Ni); self.NA.append(NA); self.F.append(F)
        fs = set(popc(F) for F in self.F)
        assert len(fs) <= 1, 'not one frozen count in the class'
        self.f = fs.pop() if fs else None
        for p, B in enumerate(self.P):                     # NA = the frozen goods (V1, V2)
            fg = 0
            for i in range(n):
                if self.F[p] >> i & 1: fg |= B[i]
            assert fg == self.NA[p], ('NA is not the set of frozen goods', B)
        self._mv = {}
        self.key = [(self.NA[p], tuple(B[i] if self.F[p] >> i & 1 else -1 for i in range(n))) for p, B in enumerate(self.P)]

    def move(self, p, q):
        k = (p, q)
        if k in self._mv: return self._mv[k]
        A, B = self.P[p], self.P[q]
        Fp, Fq = self.F[p], self.F[q]
        ch = 0
        for i in range(self.n):
            if A[i] != B[i]: ch |= 1 << i
        U, Z = Fp & ~Fq, Fq & ~Fp
        W, Y = ch & Fp & Fq, ch & ~Fp & ~Fq
        give = all(A[i] & ~B[i] for i in range(self.n) if Y >> i & 1)
        need = all(not (B[i] & ~self.N[p][i]) for i in range(self.n) if Z >> i & 1)
        chain = sorted(B[i] for i in range(self.n) if (W | Z) >> i & 1) == sorted(A[i] for i in range(self.n) if (W | U) >> i & 1)
        mv = Move(popc(ch), popc(U), popc(Z), popc(W), popc(Y), self.NA[p] == self.NA[q], give, need, chain)
        self._mv[k] = mv
        return mv


def shape(mv): return '%d|%d|%d|%d%s' % (mv.nU, mv.nW, mv.nZ, mv.nY, '' if mv.keep else '~')


def size_key(mv): return (mv.nch, mv.nU + mv.nW, mv.nY, shape(mv))


# ---- the moves ----
def T1(m): return m.nch == 1 and m.keep
def T2(m): return m.nch >= 2 and m.keep and m.nU == 0 and m.nZ == 0 and m.nW == 0
def T3(m): return m.keep and m.nU == 1 and m.nZ == 1 and m.nW == 0 and m.nY <= 1 and m.give and m.need
def T4(m): return m.keep and m.nch >= 1 and m.nU == 0 and m.nZ == 0 and m.nY == 0


def T3p(m, wmax=99, ymax=1, need=True, give=True):
    return (m.keep and m.nU == 1 and m.nZ == 1 and m.nW <= wmax and m.nY <= ymax and (m.give or not give)
            and (m.need or not need) and m.chain)


def RT4(m): return T1(m) or T2(m) or T3(m) or T4(m)
def RC(m): return T1(m) or T2(m) or T3p(m) or T4(m)


SINGLE = [
    ('RT4', 'T1 + T2 + T3 + T4 (control: refuted at n = 5)', RT4),
    ('RC_W1', 'RC with |W| <= 1 in T3+', lambda m: T1(m) or T2(m) or T3p(m, wmax=1) or T4(m)),
    ('RC', 'T1 + T2 + T3+ + T4 (K4.DL2.RC)', RC),
    ('RC_noneed', 'RC without "z needs its new good"', lambda m: T1(m) or T2(m) or T3p(m, need=False) or T4(m)),
    ('RC_Yfree', 'RC with the helper (at most one) unrestricted (need not give up a good)',
     lambda m: T1(m) or T2(m) or T3p(m, give=False) or T4(m)),
    ('RC_Yany', 'RC with any number of helpers, each giving up a good', lambda m: T1(m) or T2(m) or T3p(m, ymax=99) or T4(m)),
    ('RC_U0', 'NA kept and U empty (T1, T2, T4 and their unions: frozen goods permuted while free agents re-partition) + T3+',
     lambda m: (m.keep and m.nU == 0) or T3p(m)),
    ('NA1', 'NA kept, |U| <= 1, |Z| <= 1 (W, Y arbitrary)', lambda m: m.keep and m.nU <= 1 and m.nZ <= 1),
    ('NAbal', 'NA kept, |U| = |Z| (= NAall, see the docstring)', lambda m: m.keep and m.nU == m.nZ),
    ('NAall', 'NA kept', lambda m: m.keep),
    ('U1Z1', '|U| <= 1 and |Z| <= 1, NA free', lambda m: m.nU <= 1 and m.nZ <= 1),
    ('D2', '|ch| <= 2 (DL2; control: refuted at n = 3)', lambda m: m.nch <= 2),
    ('D3', '|ch| <= 3', lambda m: m.nch <= 3),
    ('D4', '|ch| <= 4', lambda m: m.nch <= 4),
    ('FR3', '|U| + |Z| + |W| <= 3, free agents unrestricted, NA free', lambda m: m.nU + m.nZ + m.nW <= 3),
]

KEYG = [
    ('K1', 'T3 + T4 edges (control: refuted at n = 5, K4.DL13.KEY)', lambda m: T3(m) or T4(m)),
    ('K3', 'T3+ with |W| <= 1, + T4', lambda m: T3p(m, wmax=1) or T4(m)),
    ('K2', 'T3+ + T4 edges (K4.DL2.RC key-graph form)', lambda m: T3p(m) or T4(m)),
    ('K2_noneed', 'T3+ without "z needs" + T4', lambda m: T3p(m, need=False) or T4(m)),
    ('K2_Yany', 'T3+ with any number of giving helpers + T4', lambda m: T3p(m, ymax=99) or T4(m)),
    ('K4', 'NA1 moves (NA kept, |U| <= 1)', lambda m: m.keep and m.nU <= 1),
    ('K5', 'NA kept', lambda m: m.keep),
    ('KU1', '|U| <= 1, NA free', lambda m: m.nU <= 1),
]
SNAMES = [x[0] for x in SINGLE]
KNAMES = [x[0] for x in KEYG]


def evaluate(pd, want_fail_detail=True):
    """every predicate on one profile. Returns {'f', 'states', 'keys_pos', 'single': {name: {'fail': [state idx],
    'small': Counter(shape), 'margin': least number of repairs over the states}}, 'keyg': {name: {...keys}}}"""
    n = len(pd.P)
    res = {'f': pd.f, 'states': 0, 'keys': 0, 'keys_pos': 0, 'single': {}, 'keyg': {}}
    st = [p for p in range(n) if pd.d[p] > 0]
    res['states'] = len(st)
    for name, _, _ in SINGLE: res['single'][name] = {'fail': [], 'small': collections.Counter(), 'margin': None, 'nrep': []}
    for p in st:
        better = [q for q in range(n) if pd.d[q] < pd.d[p]]
        mvs = [(q, pd.move(p, q)) for q in better]
        for name, _, R in SINGLE:
            reps = [mv for q, mv in mvs if R(mv)]
            e = res['single'][name]
            e['nrep'].append(len(reps))
            if e['margin'] is None or len(reps) < e['margin']: e['margin'] = len(reps)
            if not reps: e['fail'].append(p)
            else: e['small'][shape(min(reps, key=size_key))] += 1
    # key graph
    K = collections.defaultdict(list)
    for p in range(n): K[pd.key[p]].append(p)
    dstar = {k: min(pd.d[p] for p in ps) for k, ps in K.items()}
    res['keys'] = len(K)
    pos = [k for k in K if dstar[k] > 0]
    res['keys_pos'] = len(pos)
    for name, _, _ in KEYG: res['keyg'][name] = {'fail': [], 'small': collections.Counter(), 'margin': None, 'nrep': []}
    for k in pos:
        tq = [q for q in range(n) if pd.key[q] != k and dstar[pd.key[q]] < dstar[k]]
        mvs = [pd.move(p, q) for p in K[k] for q in tq]
        for name, _, E in KEYG:
            reps = [mv for mv in mvs if E(mv)]
            e = res['keyg'][name]
            e['nrep'].append(len(reps))
            if e['margin'] is None or len(reps) < e['margin']: e['margin'] = len(reps)
            if not reps: e['fail'].append(k)
            else: e['small'][shape(min(reps, key=size_key))] += 1
    res['dstar'] = dstar
    return res
