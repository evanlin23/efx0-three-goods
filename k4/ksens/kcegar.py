"""At most D improving chains from every maximum-matching start, for EVERY strict profile of one hypergraph, at any
k <= 5, by ordinal CEGAR (k4/ksens.md §8).  Written independently of the certifier's k4/oc1cert/ (branch
compute/k4-oc1max-cert), which does the same for k = 4 cores; the two cross-check each other at k = 4.

Statement OC_D^max for a hypergraph (agents' relevant sets R_i, |R_i| <= 5): for every strict additive profile and every
serial-dictatorship start Y whose picks form a maximum matching, the picks, or the bases after at most D improving
chains in sequence (k4/sdc.md §29; official rule: no agent hands on an empty base, unless --empty-pass), have a
complete EFX0 allocation in which at most A agents (default 1) hold two or more goods outside their base.

Types.  The question compares disjoint sets of one agent's goods only (SD picks; a chain agent's new base against its
disjoint old base, or a superset of it; EFX0), so it depends on a strict profile only through each agent's strict
order type.  Representatives: types5.py for five goods (516 per ranking, 61,920 in all), and the same grid scan for
d <= 4 goods (grid bound d times the largest (d-1)-minor of a {-1, 0, 1} matrix: 1, 2, 6, 16), giving 1, 2, 12, 336
types.

Outer SAT (CaDiCaL), two encodings of the types:
  lazy (default): the comparison bits c_i(S, T) = [v_i(S) > v_i(T)] are free variables, created when first needed.
    After each solve, each agent's assigned bits are checked against its type list (numpy): if no strict type has
    those signs, a minimal conflicting set of the bits is extracted (progressive deletion) and blocked by a clause,
    and the outer is solved again.  Exact, because agents' types are independent.
  --onehot: exactly one type per agent (one-hot); each bit is defined as the disjunction of the types with that sign.
Both: picks p_i(g) or none_i, a matching of size nu; Y is an SD outcome:
(a) every good i prefers to its pick (every good of R_i, when i has no pick) is picked by another agent, and (b) the
digraph "i prefers Y_j to Y_i" is acyclic, encoded with a strict total order before(j, i) (then that order produces
Y); every witness found so far does not apply.

Witness (Y*, Q): the exact picks Y* and the comparisons Q it needs: every chain agent's gain v_i(new minus old) >
v_i(old minus new) on R_i, layer by layer, and EFX0 of the final allocation X, v_i(X_i) > v_i(X_j minus g) on R_i for
every j != i and g in X_j (nonempty right side).  Given Y = Y*, the chains are legal and X completes them under every
profile satisfying Q, so the clause  not(Y = Y*) or not(Q)  removes exactly profiles the witness repairs.

Inner search (no SAT), on the integer representative: a one-absorber completion of the picks by backtracking
(k3max.find_completion), then every state of 1, ..., D chains (brute.Inst.chains), each with the same search.

Result: 'certified' (the outer is UNSAT: OC_D^max holds for every strict profile of the hypergraph) or a FAIL
(profile, picks) with no repair within D chains, which the caller re-checks.

Agents with six or more goods (lazy mode only): no type list.  Their bits are checked by an exact rational LP
(ratlp.py: is there v > 0 with the assigned strict signs?), behind a pool of known strict value vectors (random ones
with distinct subset sums, plus every LP solution) tried first with numpy; an infeasible assignment is blocked by the
LP's Farkas core.  The representative given to the inner search is that strict integer vector.

Grid mode for agents with six goods (grid6=FILE, typesk.py output): their types are restricted to the strict types
with a decreasing integer representative in [1, B]^6 (a SUBSET of all strict types: a 'certified' verdict then covers
only profiles whose six-good agents have such a type, while a FAIL is a genuine counterexample).  Realization: the 15
singleton bits must form a transitive ranking (else a 3-cycle is blocked); under that ranking the other bits are
checked against the grid list with numpy; a conflict is blocked by a minimal set of those bits together with all
the ranking's singleton literals (sound: the clause only excludes that ranking).

    python3 k4/ksens/kcegar.py '[[sets]]' D [--A=1] [--empty-pass] [--any-start] [--grid6=FILE]"""
import sys, os, json, gzip, itertools, time, collections
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')   # one BLAS thread: the grid products are small, and runs share CPUs
import _paths
import brute, k3max
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

HERE = os.path.dirname(os.path.abspath(__file__))
TYPES5 = os.path.join(HERE, '..', '..', 'results', 'k4_ksens', 'types5.json.gz')
_REPS = {}
# exact grid mode (k4/ksens.md §8): real points found by the LP, in ranking coordinates (decreasing), with their signs on
# every comparison; and the exact verdict on each set of comparisons tested (ranking coordinates, ranking included).
# Both are facts about R^d, independent of the instance and of the grid, so they are shared by every Cegar in a process.
_GX = {}
_CORE_LP = {}


def reps(d):
    """strictly decreasing integer representatives of the strict order types of d goods with a fixed ranking"""
    if d in _REPS: return _REPS[d]
    if d == 5: r = [tuple(v) for v in json.load(gzip.open(TYPES5, 'rt'))['reps']]
    else:
        B = {1: 1, 2: 2, 3: 6, 4: 16}[d]
        P = [(S, T) for S in range(1, 1 << d) for T in range(S + 1, 1 << d) if S & T == 0]; seen = {}
        for v in itertools.combinations(range(B, 0, -1), d):
            sums = [sum(v[g] for g in range(d) if S >> g & 1) for S in range(1 << d)]
            if any(sums[S] == sums[T] for S, T in P): continue
            sg = tuple(sums[S] > sums[T] for S, T in P); key = (max(v), sum(v), v)
            if sg not in seen or key < seen[sg][0]: seen[sg] = (key, v)
        r = sorted(kv[1] for kv in seen.values())
    _REPS[d] = r; return r


def agent_types(R):
    """every strict type of an agent with relevant goods R, as {good: value}"""
    d = len(R); out = []
    for perm in itertools.permutations(range(d)):
        for r in reps(d): out.append({R[perm[k]]: r[k] for k in range(d)})
    return out


class Cegar:
    def __init__(self, sets, m=None, D=2, A=1, empty_pass=False, require_max=True, lazy=True, lp_min=6, grid6=None,
                 grid_fast=True, grid_exact=False):
        self.R = [sorted(s) for s in sets]; self.n = n = len(sets)
        self.m = m or 1 + max(max(s) for s in sets); self.D, self.A, self.ep = D, A, empty_pass
        self.gridd = json.load(gzip.open(grid6, 'rt'))['k'] if grid6 is not None else None   # 6; less to validate the mode
        self.G = [grid6 is not None and len(R) == self.gridd for R in self.R]
        self.LP = [len(R) >= lp_min and not self.G[i] for i, R in enumerate(self.R)]   # lp_min < 6: test the LP route
        self.R6 = None; self.grid_fast = grid_fast; self.gpool = [[] for _ in sets]
        self.gexact = grid_exact; self.gextra = [[] for _ in sets]; self.gstats = collections.Counter()
        if grid6 is not None and any(self.G):
            import numpy as _np
            self.R6 = _np.array(json.load(gzip.open(grid6, 'rt'))['reps'], dtype=_np.int64)
            # the signs of every comparison v(S) > v(T) (disjoint S, T over the six ranking positions) on the grid,
            # packed: GP[gidx[(S, T)]] is a uint64 bitset over the grid points (padding bits 0)
            dd = self.gridd; sub = _np.array([[S >> g & 1 for g in range(dd)] for S in range(1 << dd)], dtype=_np.int64)
            sums = self.R6 @ sub.T; prs = [(S_, T_) for S_ in range(1, 1 << dd) for T_ in range(1, 1 << dd) if S_ & T_ == 0]
            self.gidx = {p: j for j, p in enumerate(prs)}
            GT = _np.stack([sums[:, S_] > sums[:, T_] for S_, T_ in prs])
            pk = _np.packbits(GT, axis=1); pad = (-pk.shape[1]) % 8
            self.GP = _np.ascontiguousarray(_np.pad(pk, ((0, 0), (0, pad)))).view(_np.uint64)
        assert lazy or not any(self.LP), 'the one-hot mode needs type lists (at most five goods per agent)'
        self.T = [None if self.LP[i] or self.G[i] else agent_types(R) for i, R in enumerate(self.R)]
        self.pool = IDPool(); self.S = Cadical153(); self.cmpv = {}; self.iters = 0; self.kinds = collections.Counter()
        self.lazy = lazy; self.cuts = 0; self.bitv = {}; self.bits_of = [[] for _ in range(n)]
        import numpy as np
        self.np = np; self.TV = [None if self.T[i] is None else np.array([[t[g] for g in self.R[i]] for t in self.T[i]],
                                 dtype=np.int64) for i in range(n)]
        self.rowv = {}; self.lpcalls = 0; rng = __import__('random').Random(12345); self.vpool = [None] * n
        for i in range(n):
            if not self.LP[i]: continue
            d = len(self.R[i]); seeds = []
            while len(seeds) < 4000:
                u = [rng.randint(1, 1 << 30) for _ in range(d)]
                sums = set(sum(u[g] for g in range(d) if S >> g & 1) for S in range(1 << d))
                if len(sums) == 1 << d: seeds.append(u)
            self.vpool[i] = np.array(seeds, dtype=np.int64)
        self.oriented = [[] for _ in range(n)]
        self.rep_of = [list(self.vpool[i][0]) if self.vpool[i] is not None else list(self.R6[0]) if self.G[i] else None
                       for i in range(n)]
        v = self.pool.id
        self.TRUE = v(('TRUE',)); self.S.add_clause([self.TRUE])
        if not lazy:
            self.t = [[v(('t', i, k)) for k in range(len(self.T[i]))] for i in range(n)]
            for i in range(n): self._exactly_one(self.t[i])
        self.p = [{g: v(('p', i, g)) for g in self.R[i]} for i in range(n)]
        self.none = [v(('none', i)) for i in range(n)]
        for i in range(n): self._exactly_one(list(self.p[i].values()) + [self.none[i]])
        for g in range(self.m):
            lits = [self.p[i][g] for i in range(n) if g in self.p[i]]
            for a, b in itertools.combinations(lits, 2): self.S.add_clause([-a, -b])
        self.nu = k3max.nu(self.R)
        if require_max:
            enc = CardEnc.equals(lits=[-x for x in self.none], bound=self.nu, vpool=self.pool, encoding=EncType.seqcounter)
            for c in enc.clauses: self.S.add_clause(c)
        # SD: a strict total order 'before'
        self.bf = {}
        for a, b in itertools.combinations(range(n), 2): self.bf[(a, b)] = v(('bf', a, b))
        for a, b, c in itertools.permutations(range(n), 3):
            self.S.add_clause([-self.before(a, b), -self.before(b, c), self.before(a, c)])
        for i in range(n):
            for h in self.R[i]:
                for g in self.R[i]:
                    if g == h: continue
                    c = self.cmp(i, (g,), (h,))
                    hold = [self.p[j][g] for j in range(n) if j != i and g in self.p[j]]
                    self.S.add_clause([-self.p[i][h], -c] + hold)
                    for j in range(n):
                        if j != i and g in self.p[j]:
                            self.S.add_clause([-self.p[i][h], -c, -self.p[j][g], self.before(j, i)])
            for g in self.R[i]:
                hold = [self.p[j][g] for j in range(n) if j != i and g in self.p[j]]
                self.S.add_clause([-self.none[i]] + hold)
                for j in range(n):
                    if j != i and g in self.p[j]: self.S.add_clause([-self.none[i], -self.p[j][g], self.before(j, i)])

    def before(self, a, b):
        return self.bf[(a, b)] if a < b else -self.bf[(b, a)]

    def _exactly_one(self, lits):
        self.S.add_clause(lits)
        if len(lits) <= 6:
            for a, b in itertools.combinations(lits, 2): self.S.add_clause([-a, -b])
        else:
            for c in CardEnc.atmost(lits=lits, bound=1, vpool=self.pool, encoding=EncType.seqcounter).clauses:
                self.S.add_clause(c)

    def cmp(self, i, A, B):
        """literal of [v_i(A) > v_i(B)] for disjoint nonempty A, B inside R_i"""
        A, B = tuple(sorted(A)), tuple(sorted(B))
        if (A, B) > (B, A): return -self.cmp(i, B, A)
        key = (i, A, B)
        if key in self.cmpv: return self.cmpv[key]
        col = {g: c for c, g in enumerate(self.R[i])}
        if self.LP[i] or self.G[i]:
            lit = self.pool.id(('c',) + key); self.bits_of[i].append(lit)
            row = [(1 if g in A else 0) - (1 if g in B else 0) for g in self.R[i]]; self.rowv[lit] = row
            self.cmpv[key] = lit
            # monotonicity: A2 within A1 and B1 within B2 give [v(A2) > v(B2)] -> [v(A1) > v(B1)]
            sA, sB = set(A), set(B)
            for A1, B1, L1 in ((sA, sB, lit), (sB, sA, -lit)):
                for A2, B2, L2 in self.oriented[i]:
                    if A2 <= A1 and B1 <= B2: self.S.add_clause([-L2, L1])
                    if A1 <= A2 and B2 <= B1: self.S.add_clause([-L1, L2])
            self.oriented[i] += [(sA, sB, lit), (sB, sA, -lit)]
            # phase hint: the sign under the agent's current representative
            rp = self.rep_of[i]; self.S.set_phases([lit if sum(a * x for a, x in zip(row, rp)) > 0 else -lit])
            return lit
        TV = self.TV[i]
        mask = TV[:, [col[g] for g in A]].sum(1) > TV[:, [col[g] for g in B]].sum(1)
        sat = None if self.lazy else [int(k) for k in self.np.nonzero(mask)[0]]
        if mask.all(): lit = self.TRUE
        elif not mask.any(): lit = -self.TRUE
        elif self.lazy:
            lit = self.pool.id(('c',) + key); self.bitv[lit] = mask; self.bits_of[i].append(lit)
        else:
            lit = self.pool.id(('c',) + key); tl = self.t[i]
            if 2 * len(sat) <= len(tl):
                self.S.add_clause([-lit] + [tl[k] for k in sat])
                for k in sat: self.S.add_clause([-tl[k], lit])
            else:
                sk = set(sat); uns = [k for k in range(len(tl)) if k not in sk]
                self.S.add_clause([lit] + [tl[k] for k in uns])
                for k in uns: self.S.add_clause([-tl[k], -lit])
        self.cmpv[key] = lit; return lit

    def reqs_gain(self, old, new):
        Q = []
        for i in range(self.n):
            if new[i] == old[i]: continue
            Ri = set(self.R[i]); a = (new[i] - old[i]) & Ri; b = (old[i] - new[i]) & Ri
            assert a, 'a chain agent gained nothing it values'
            if b: Q.append((i, a, b))
        return Q

    def reqs_efx(self, X):
        Q = []
        for i in range(self.n):
            Ri = set(self.R[i]); a = X[i] & Ri
            for j in range(self.n):
                if j == i: continue
                for g in X[j]:
                    b = (X[j] - {g}) & Ri
                    if not b: continue
                    assert a, 'EFX0 witness with an empty own bundle'
                    Q.append((i, a, b))
        return Q

    def inner(self, vals, Y):
        n, m = self.n, self.m; V = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in vals[i].items(): V[i][g] = x
        base = tuple(frozenset([g]) if g is not None else frozenset() for g in Y)
        X = k3max.find_completion(V, base, m, self.A)
        if X is not None: self.kinds['picks'] += 1; return self.reqs_efx(X)
        I = brute.Inst([self.R[i] for i in range(n)], [[vals[i][g] for g in self.R[i]] for i in range(n)], m)
        frontier = {base: []}
        for d in range(1, self.D + 1):
            nxt = {}
            for st, Q in frontier.items():
                for st2 in sorted(I.chains(list(st), empty_pass=self.ep), key=lambda s: sorted(map(sorted, s))):
                    if st2 in nxt or st2 in frontier: continue
                    Q2 = Q + self.reqs_gain(st, st2); X = k3max.find_completion(V, st2, m, self.A)
                    if X is not None: self.kinds['%d chains' % d] += 1; return Q2 + self.reqs_efx(X)
                    nxt[st2] = Q2
            frontier = nxt
        return None

    def run(self, time_limit=None, verbose=False):
        t0 = time.time()
        while True:
            if time_limit and time.time() - t0 > time_limit: return 'timeout', None
            if not self.S.solve(): return 'certified', None
            mdl = set(l for l in self.S.get_model() if l > 0)
            if self.lazy:
                ty = self.realize(mdl)
                if ty is None: continue          # a realizability cut was added
            else:
                ty = [next(k for k, x in enumerate(self.t[i]) if x in mdl) for i in range(self.n)]
            self.iters += 1
            Y = tuple(next((g for g, x in self.p[i].items() if x in mdl), None) for i in range(self.n))
            vals = [ty[i] if self.LP[i] or self.G[i] else self.T[i][ty[i]] for i in range(self.n)]
            Q = self.inner(vals, Y)
            if Q is None: return 'FAIL', (vals, Y)
            cl = [-self.p[i][Y[i]] if Y[i] is not None else -self.none[i] for i in range(self.n)]
            cl += [-self.cmp(i, a, b) for i, a, b in set((i, frozenset(a), frozenset(b)) for i, a, b in Q)]
            self.S.add_clause([l for l in cl if l != -self.TRUE])
            if verbose and self.iters % 200 == 0:
                print('   iter', self.iters, 'cuts', self.cuts, 'LP calls', self.lpcalls, dict(self.kinds),
                      '%.0f s' % (time.time() - t0), flush=True)

    def realize(self, mdl):
        """lazy mode: a type per agent with the signs the model gives its bits, or None after blocking a minimal
        conflicting set of bits of one agent (progressive deletion: the first prefix that empties the type set ends
        with a critical bit; repeat on the bits before it, keeping the critical ones)"""
        np = self.np; ty = []
        for i in range(self.n):
            lits = [b if b in mdl else -b for b in self.bits_of[i]]
            if self.G[i]:
                r = self.realize_grid(i, lits)
                if r is None: return None
                ty.append(r); continue
            if self.LP[i]:
                rows = [self.rowv[l] if l > 0 else [-x for x in self.rowv[-l]] for l in lits]
                if rows:
                    ok = (self.vpool[i] @ np.array(rows, dtype=np.int64).T > 0).all(1)
                    hit = int(np.argmax(ok)) if ok.any() else None
                else: hit = 0
                if hit is None:
                    import ratlp
                    self.lpcalls += 1; st, w = ratlp.realize_fast(rows, len(self.R[i]))
                    if st != 'ok':
                        self.S.add_clause([-lits[k] for k in w]); self.cuts += 1
                        return None
                    self.vpool[i] = np.vstack([np.array([w], dtype=np.int64), self.vpool[i]]); vec = list(w)
                else: vec = [int(x) for x in self.vpool[i][hit]]
                ty.append({g: int(x) for g, x in zip(self.R[i], vec)})
                if vec != self.rep_of[i]:          # steer the unconstrained bits towards this realizable point
                    self.rep_of[i] = vec
                    self.S.set_phases([b if sum(a * x for a, x in zip(self.rowv[b], vec)) > 0 else -b for b in self.bits_of[i]])
                continue
                import ratlp
                self.S.add_clause([-lits[k] for k in w]); self.cuts += 1
                return None
            vec = lambda l: self.bitv[l] if l > 0 else ~self.bitv[-l]
            ok = np.ones(len(self.T[i]), dtype=bool)
            for l in lits: ok &= vec(l)
            if ok.any(): ty.append(int(np.argmax(ok))); continue
            core = []; rest = lits
            while True:
                base = np.ones(len(self.T[i]), dtype=bool)
                for l in core: base &= vec(l)
                if not base.any(): break
                cur = base.copy(); crit = None
                for k, l in enumerate(rest):
                    cur &= vec(l)
                    if not cur.any(): crit = k; break
                core.append(rest[crit]); rest = rest[:crit]
            self.S.add_clause([-l for l in core]); self.cuts += 1
            return None
        return ty

    def realize_grid(self, i, lits):
        """grid mode: a value dict for agent i, or None after adding a blocking clause.  Same answers as
        realize_grid_ref (the first version, kept as the reference): a recent point satisfying every bit is tried first;
        then every bit is a precomputed bitset over the grid (its sign at each grid point), the first point of the AND
        of all of them is the answer, and the core is found by the same progressive deletion, on prefix ANDs.  With
        grid_exact every cut is first confirmed by the exact LP of ratlp.py; a bit set that the grid misses but the LP
        realizes gets the LP's point (kept in gextra), so the verdicts cover every strict profile, not only the grid."""
        if not self.grid_fast: return self.realize_grid_ref(i, lits)
        np = self.np; R = self.R[i]; d = len(R)
        sing = {}; other = []
        for l in lits:
            row = self.rowv[abs(l)]
            if sum(1 for x in row if x) == 2:
                a = next(R[c] for c, x in enumerate(row) if x == 1); b = next(R[c] for c, x in enumerate(row) if x == -1)
                sing[(a, b) if l > 0 else (b, a)] = l          # a beats b
            else: other.append(l)
        wins = {g: sum(1 for (a, b) in sing if a == g) for g in R}
        if sorted(wins.values()) != list(range(d)):          # not transitive: block a 3-cycle
            for a, b, c in itertools.permutations(R, 3):
                if (a, b) in sing and (b, c) in sing and (c, a) in sing:
                    self.S.add_clause([-sing[(a, b)], -sing[(b, c)], -sing[(c, a)]]); self.cuts += 1; return None
            raise AssertionError('incomplete ranking bits')
        order = sorted(R, key=lambda g: -wins[g]); pos = {g: k for k, g in enumerate(order)}
        # signed rows of every bit, in the agent's coordinates R
        A = np.array([self.rowv[l] if l > 0 else [-x for x in self.rowv[-l]] for l in lits], dtype=np.int64).reshape(-1, d)
        pool = self.gpool[i] + self.gextra[i]
        if pool:
            P = np.array(pool, dtype=np.int64); okp = (P @ A.T > 0).all(1)
            if okp.any():
                vec_ = pool[int(np.argmax(okp))]; return self._grid_found(i, vec_)
        pool = self.gpool[i]
        if self.gexact is True: return self._grid_exact(i, lits, sing, other, pos)
        # each non-singleton bit is a comparison v(S) > v(T) in ranking coordinates: a packed bitset over the grid
        keys = []
        for l in other:
            row = self.rowv[abs(l)]; s = 1 if l > 0 else -1; Sm = Tm = 0
            for c, x in enumerate(row):
                if s * x > 0: Sm |= 1 << pos[R[c]]
                elif s * x < 0: Tm |= 1 << pos[R[c]]
            keys.append(self.gidx[(Sm, Tm)])
        Mk = self.GP[keys]                                      # (bits, words)
        if len(keys):
            cum = np.bitwise_and.accumulate(Mk, axis=0); alive = cum.any(1)
            feasible = bool(alive[-1])
        else: feasible = True
        if feasible:
            k0 = int(np.argmax(np.unpackbits(cum[-1].view(np.uint8)))) if len(keys) else 0
            v = self.R6[k0]; vec_ = [int(v[pos[g]]) for g in R]
            pool.insert(0, vec_); del pool[64:]
            return self._grid_found(i, vec_)
        crit = int(np.argmin(alive)); core = [crit]; rest = list(range(crit))   # progressive deletion, as in the reference
        while True:
            base = np.bitwise_and.reduce(Mk[core], axis=0)
            if not base.any(): break
            cur = np.bitwise_and.accumulate(Mk[rest], axis=0) & base
            k = int(np.argmin(cur.any(1))); core.append(rest[k]); rest = rest[:k]
        cut = [other[k] for k in core] + list(sing.values())
        if self.gexact == 'v1':
            # exact mode, first version: the grid core is a cut only if no positive real point satisfies it (rational LP); otherwise
            # the whole bit set goes to the LP, which gives a point outside the grid or an exact core
            import ratlp
            sg = lambda l: self.rowv[l] if l > 0 else [-x for x in self.rowv[-l]]
            self.gstats['core LP'] += 1
            if ratlp.realize_check([sg(l) for l in cut], d):
                self.gstats['full LP'] += 1; st, w = ratlp.realize_fast([sg(l) for l in lits], d)
                if st == 'ok':
                    self.gstats['points off the grid'] += 1; vec_ = [int(x) for x in w]
                    self.gextra[i].append(vec_); return self._grid_found(i, vec_)
                cut = [lits[k] for k in w]; self.gstats['LP cores'] += 1
        self.S.add_clause([-l for l in cut]); self.cuts += 1
        return None

    def _gx(self):
        d = self.gridd
        if d not in _GX:
            prs = sorted(self.gidx, key=self.gidx.get)
            _GX[d] = {'pts': [], 'seen': set(), 'bits': self.np.zeros((len(prs), 0), dtype=bool), 'prs': prs}
        return _GX[d]

    def _gx_add(self, u):
        X = self._gx(); t = tuple(u)
        if t in X['seen']: return
        sub = lambda S: sum(u[g] for g in range(len(u)) if S >> g & 1)
        col = self.np.array([[sub(S) > sub(T)] for S, T in X['prs']], dtype=bool)
        X['bits'] = self.np.hstack([X['bits'], col]); X['pts'].append(list(t)); X['seen'].add(t)

    def _grid_exact(self, i, lits, sing, other, pos):
        """exact grid mode: the points are the grid plus every real point found so far (_GX); a core of the bits over
        these points becomes a cut only after the exact LP (ratlp.realize) proves it unrealizable over the reals (its
        sub-core is the cut); if the LP realizes it, its point joins _GX and the core is recomputed.  So a cut is always
        valid for every strict profile, and a returned point always satisfies every bit."""
        import ratlp
        np = self.np; R = self.R[i]; d = len(R)
        keys = []
        for l in other:
            row = self.rowv[abs(l)]; s = 1 if l > 0 else -1; Sm = Tm = 0
            for c, x in enumerate(row):
                if s * x > 0: Sm |= 1 << pos[R[c]]
                elif s * x < 0: Tm |= 1 << pos[R[c]]
            keys.append(self.gidx[(Sm, Tm)])
        X = self._gx(); prs = X['prs']; rank_rows = [[1 if g == a else -1 if g == a + 1 else 0 for g in range(d)] for a in range(d - 1)]
        def vec_of(u): return [int(u[pos[g]]) for g in R]
        for attempt in range(50):
            Mk = self.GP[keys]; Xk = X['bits'][keys]           # grid bitsets; extra points as booleans
            if not keys:
                return self._grid_found(i, vec_of(self.R6[0]))
            cum = np.bitwise_and.accumulate(Mk, axis=0); alive = cum.any(1)
            cx = np.logical_and.accumulate(Xk, axis=0) if Xk.shape[1] else None
            if cx is not None: alive = alive | cx.any(1)
            if alive[-1]:
                if cum[-1].any(): u = self.R6[int(np.argmax(np.unpackbits(cum[-1].view(np.uint8))))]
                else: u = X['pts'][int(np.argmax(cx[-1]))]; self.gstats['extra point used'] += 1
                vec_ = vec_of(u); self.gpool[i].insert(0, vec_); del self.gpool[i][64:]
                return self._grid_found(i, vec_)
            crit = int(np.argmin(alive)); core = [crit]; rest = list(range(crit))
            while True:
                base = np.bitwise_and.reduce(Mk[core], axis=0).any()
                bx = Xk[core].all(0) if cx is not None else None
                if not base and not (bx is not None and bx.any()): break
                b0 = np.bitwise_and.reduce(Mk[core], axis=0)
                a = (np.bitwise_and.accumulate(Mk[rest], axis=0) & b0).any(1)
                if bx is not None: a = a | (np.logical_and.accumulate(Xk[rest], axis=0) & bx).any(1)
                k = int(np.argmin(a)); core.append(rest[k]); rest = rest[:k]
            ck = frozenset(keys[k] for k in core)
            res = _CORE_LP.get(ck)
            if res is None:
                ckl = sorted(ck); rows = [[(1 if prs[j][0] >> g & 1 else 0) - (1 if prs[j][1] >> g & 1 else 0) for g in range(d)]
                                          for j in ckl] + rank_rows
                st, w = ratlp.realize(rows, d); self.gstats['core LP'] += 1
                res = ('ok', list(w)) if st == 'ok' else ('conflict', frozenset(ckl[t] for t in w if t < len(ckl)))
                _CORE_LP[ck] = res
            else: self.gstats['core LP cached'] += 1
            if res[0] == 'conflict':
                cut = [other[k] for k in core if keys[k] in res[1]] + list(sing.values())
                self.S.add_clause([-l for l in cut]); self.cuts += 1; return None
            self._gx_add(res[1]); self.gstats['points added'] += 1
        # fallback (not expected): the full LP decides
        sg = lambda l: self.rowv[l] if l > 0 else [-x for x in self.rowv[-l]]
        self.gstats['full LP'] += 1; st, w = ratlp.realize_fast([sg(l) for l in lits], d)
        if st == 'ok':
            vec_ = [int(x) for x in w]; self.gextra[i].append(vec_); return self._grid_found(i, vec_)
        self.S.add_clause([-lits[k] for k in w]); self.cuts += 1; return None

    def _grid_found(self, i, vec_):
        if vec_ != self.rep_of[i]:
            self.rep_of[i] = vec_
            self.S.set_phases([b if sum(a * x for a, x in zip(self.rowv[b], vec_)) > 0 else -b for b in self.bits_of[i]])
        return {g: x for g, x in zip(self.R[i], vec_)}

    def realize_grid_ref(self, i, lits):
        """grid mode, first version (the reference for realize_grid)"""
        np = self.np; R = self.R[i]; d = len(R); col = {g: c for c, g in enumerate(R)}
        sing = {}; other = []
        for l in lits:
            row = self.rowv[abs(l)]
            if sum(1 for x in row if x) == 2:
                a = next(R[c] for c, x in enumerate(row) if x == 1); b = next(R[c] for c, x in enumerate(row) if x == -1)
                sing[(a, b) if l > 0 else (b, a)] = l          # a beats b
            else: other.append(l)
        wins = {g: sum(1 for (a, b) in sing if a == g) for g in R}
        if sorted(wins.values()) != list(range(d)):          # not transitive: block a 3-cycle
            for a, b, c in itertools.permutations(R, 3):
                if (a, b) in sing and (b, c) in sing and (c, a) in sing:
                    self.S.add_clause([-sing[(a, b)], -sing[(b, c)], -sing[(c, a)]]); self.cuts += 1; return None
            raise AssertionError('incomplete ranking bits')
        order = sorted(R, key=lambda g: -wins[g]); pos = {g: k for k, g in enumerate(order)}
        def vec(l):
            row = self.rowv[abs(l)]; w = np.zeros(d, dtype=np.int64)
            for c, x in enumerate(row): w[pos[R[c]]] = x
            m = self.R6 @ w
            return m > 0 if l > 0 else m < 0
        ok = np.ones(len(self.R6), dtype=bool)
        for l in other: ok &= vec(l)
        if ok.any():
            v = self.R6[int(np.argmax(ok))]; vals = {g: int(v[pos[g]]) for g in R}
            vec_ = [vals[g] for g in R]
            if vec_ != self.rep_of[i]:
                self.rep_of[i] = vec_
                self.S.set_phases([b if sum(a * x for a, x in zip(self.rowv[b], vec_)) > 0 else -b for b in self.bits_of[i]])
            return vals
        core = []; rest = other
        while True:
            base = np.ones(len(self.R6), dtype=bool)
            for l in core: base &= vec(l)
            if not base.any(): break
            cur = base.copy(); crit = None
            for k, l in enumerate(rest):
                cur &= vec(l)
                if not cur.any(): crit = k; break
            core.append(rest[crit]); rest = rest[:crit]
        self.S.add_clause([-l for l in core] + [-l for l in sing.values()]); self.cuts += 1
        return None

    def close(self):
        self.S.delete()


if __name__ == '__main__':
    sets = json.loads(sys.argv[1]); D = int(sys.argv[2])
    A = int(next((a[4:] for a in sys.argv if a.startswith('--A=')), 1))
    C = Cegar(sets, D=D, A=A, empty_pass='--empty-pass' in sys.argv, require_max='--any-start' not in sys.argv,
              lazy='--onehot' not in sys.argv, grid6=next((a[8:] for a in sys.argv if a.startswith('--grid6=')), None))
    r, w = C.run(verbose=True)
    print(r, 'iterations', C.iters, 'realizability cuts', C.cuts, dict(C.kinds), json.dumps(w) if w else '')
