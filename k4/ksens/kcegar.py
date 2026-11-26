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

Outer SAT (CaDiCaL): exactly one type per agent (one-hot); comparison bits c_i(S, T) <-> [v_i(S) > v_i(T)] defined
lazily as the disjunction of the types with that sign; picks p_i(g) or none_i, a matching of size nu; Y is an SD outcome:
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

    python3 k4/ksens/kcegar.py '[[sets]]' D [--A=1] [--empty-pass] [--any-start]"""
import sys, os, json, gzip, itertools, time, collections
import _paths
import brute, k3max
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

HERE = os.path.dirname(os.path.abspath(__file__))
TYPES5 = os.path.join(HERE, '..', '..', 'results', 'k4_ksens', 'types5.json.gz')
_REPS = {}


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
    def __init__(self, sets, m=None, D=2, A=1, empty_pass=False, require_max=True):
        self.R = [sorted(s) for s in sets]; self.n = n = len(sets)
        self.m = m or 1 + max(max(s) for s in sets); self.D, self.A, self.ep = D, A, empty_pass
        self.T = [agent_types(R) for R in self.R]
        self.pool = IDPool(); self.S = Cadical153(); self.cmpv = {}; self.iters = 0; self.kinds = collections.Counter()
        v = self.pool.id
        self.TRUE = v(('TRUE',)); self.S.add_clause([self.TRUE])
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
        sat = [k for k, val in enumerate(self.T[i]) if sum(val[g] for g in A) > sum(val[g] for g in B)]
        if len(sat) == len(self.T[i]): lit = self.TRUE
        elif not sat: lit = -self.TRUE
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
            mdl = set(l for l in self.S.get_model() if l > 0); self.iters += 1
            ty = [next(k for k, x in enumerate(self.t[i]) if x in mdl) for i in range(self.n)]
            Y = tuple(next((g for g, x in self.p[i].items() if x in mdl), None) for i in range(self.n))
            vals = [self.T[i][ty[i]] for i in range(self.n)]
            Q = self.inner(vals, Y)
            if Q is None: return 'FAIL', (vals, Y)
            cl = [-self.p[i][Y[i]] if Y[i] is not None else -self.none[i] for i in range(self.n)]
            cl += [-self.cmp(i, a, b) for i, a, b in set((i, frozenset(a), frozenset(b)) for i, a, b in Q)]
            self.S.add_clause([l for l in cl if l != -self.TRUE])
            if verbose and self.iters % 200 == 0: print('   iter', self.iters, dict(self.kinds), '%.0f s' % (time.time() - t0), flush=True)

    def close(self):
        self.S.delete()


if __name__ == '__main__':
    sets = json.loads(sys.argv[1]); D = int(sys.argv[2])
    A = int(next((a[4:] for a in sys.argv if a.startswith('--A=')), 1))
    C = Cegar(sets, D=D, A=A, empty_pass='--empty-pass' in sys.argv, require_max='--any-start' not in sys.argv)
    r, w = C.run(verbose=True)
    print(r, 'iterations', C.iters, dict(C.kinds), json.dumps(w) if w else '')
