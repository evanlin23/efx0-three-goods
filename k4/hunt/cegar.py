"""CEGAR valuation synthesis for a fixed k = 4 core (workstream proof/k4-hunt, notes in k4/hunt.md).

Question for a core H (agent i values the goods sets[i], 3 or 4 of them): is there a strict balanced type profile
(equivalently, by K4.OT / K4.MC0(c), integer values) under which NO complete allocation is EFX₀?

Loop (2QBF-style CEGAR, "exists profile, forall allocation, not EFX₀"):
  outer SAT  : find a profile under which every allocation found so far violates EFX₀;
  inner SAT  : find an EFX₀ allocation for that profile (search4.Core.inner, full EFX₀, no shape limit);
  until the outer is UNSAT (the core is certified for every profile of the domains) or the inner is UNSAT (a
  counterexample candidate; it is re-checked by two independent encodings before anything is claimed).

Outer encoding (ordinal): one-hot type variables z[i][t]; for each agent i, own set O ⊆ R_i and threat set T ⊆ R_i ∖ O,
a comparison bit b(i, O, T) ⇔ "v_i(T) > v_i(O)" (defined through z). Agent i is unsafe in allocation X iff some
maximal threat set T of X (T = X_j ∩ R_i if X_j has a good outside R_i, else (X_j ∩ R_i) ∖ h for h ∈ X_j, |X_j| ≥ 2)
has b(i, O_i, T). So each allocation adds the short clause OR_i OR_T b(i, O_i, T). Learned clauses over the b bits
generalise across types, which is what the DFS scanners (scan.c, scan2.c) cannot do.

Every allocation of the certificate is EFX₀-checked for the profiles it blocks by construction of the clause, and the
coverage claim is re-checked by k4/hunt/check.py (own type enumeration, raw definition, one-hot encoding, another
SAT solver). Automorphism images of each allocation are added too (sound for any allocation)."""
import sys, os, json, time, itertools, math
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import search4 as S4


def threats(i, S, owner):
    """Own set O and the inclusion-maximal threat sets of agent i (bitmasks over positions in S) in allocation owner."""
    pos = {g: p for p, g in enumerate(S)}
    O, groups = 0, {}
    for g, j in enumerate(owner):
        if j == i:
            if g in pos: O |= 1 << pos[g]
            continue
        G, extra = groups.get(j, (0, False))
        if g in pos: G |= 1 << pos[g]
        else: extra = True
        groups[j] = (G, extra)
    T = set()
    for G, extra in groups.values():
        if not G: continue
        if extra: T.add(G)
        elif G & (G - 1):
            for p in range(len(S)):
                if G >> p & 1: T.add(G & ~(1 << p))
    T = [t for t in T if not any(u != t and u & t == t for u in T)]
    return O, sorted(T)


def automorphisms(sets, m, cap=256):
    """Automorphisms (agent map, good map) of the incidence structure, at most cap of them."""
    n = len(sets)
    G = nx.Graph()
    G.add_nodes_from((('a', i) for i in range(n)), side=0)
    G.add_nodes_from((('g', g) for g in range(m)), side=1)
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    out = []
    for iso in GraphMatcher(G, G, node_match=lambda a, b: a['side'] == b['side']).isomorphisms_iter():
        ma = [iso[('a', i)][1] for i in range(n)]
        mg = [iso[('g', g)][1] for g in range(m)]
        out.append((ma, mg))
        if len(out) >= cap: break
    return out


class Hunt:
    def __init__(self, sets, m, domains=None, solver='cd15', tries=4, use_aut=True, seed=1, per_profile=False):
        self.sets, self.m, self.n = [list(S) for S in sets], m, len(sets)
        self.C = S4.Core(self.n, m, self.sets)
        if domains is not None:                       # restricted domains: lists of type vectors (in S's order)
            self.C.dom = [list(map(tuple, D)) for D in domains]
        self.dom = self.C.dom
        self.ss = []                                  # ss[i][t, mask] = v_t(mask)
        for i, S in enumerate(self.sets):
            k = len(S)
            V = np.array(self.dom[i], dtype=np.int64)
            self.ss.append(np.stack([V[:, [p for p in range(k) if M >> p & 1]].sum(axis=1) for M in range(1 << k)], 1))
        self.vp = IDPool()
        self.z = [[self.vp.id(('z', i, t)) for t in range(len(D))] for i, D in enumerate(self.dom)]
        self.out = Solver(name=solver)
        for i, zi in enumerate(self.z):
            for c in CardEnc.equals(zi, 1, vpool=self.vp, encoding=EncType.seqcounter if len(zi) > 8 else EncType.pairwise).clauses:
                self.out.add_clause(c)
        self.b = {}
        self.tries, self.rng = tries, np.random.default_rng(seed)
        self.auts = automorphisms(self.sets, m) if use_aut else [(list(range(self.n)), list(range(m)))]
        self._inner = None                            # search4's inner SAT, built on first use
        self.per_profile = per_profile                # inner SAT built per proposal from its values (large n)
        self.allocs, self.fails, self.nclauses = [], [], 0
        self.cert = []                                # every allocation whose clause was added (images included)
        self.seen = set()

    def bit(self, i, O, T):
        key = (i, O, T)
        if key in self.b: return self.b[key]
        b = self.b[key] = self.vp.id(('b',) + key)
        pos = np.flatnonzero(self.ss[i][:, T] > self.ss[i][:, O])
        if len(pos) == 0: self.out.add_clause([-b])
        else:
            self.out.add_clause([-b] + [self.z[i][t] for t in pos])
            for t in pos: self.out.add_clause([-self.z[i][t], b])
        return b

    def clause(self, owner):
        cl = []
        for i, S in enumerate(self.sets):
            O, Ts = threats(i, S, owner)
            cl += [self.bit(i, O, T) for T in Ts]
        return cl

    def safe_sets(self, owner):
        res = []
        for i, S in enumerate(self.sets):
            O, Ts = threats(i, S, owner)
            ok = np.ones(len(self.dom[i]), dtype=bool)
            for T in Ts: ok &= self.ss[i][:, T] <= self.ss[i][:, O]
            res.append(ok)
        return res

    def add_alloc(self, owner):
        for ma, mg in self.auts:
            img = [0] * self.m
            for g in range(self.m): img[mg[g]] = ma[owner[g]]
            key = tuple(img)
            if key in self.seen: continue
            self.seen.add(key)
            self.cert.append(img)
            self.out.add_clause(self.clause(img)); self.nclauses += 1

    @property
    def sol(self): return self.inner()[0]
    @property
    def x(self): return self.inner()[1]
    @property
    def zin(self): return self.inner()[2]

    def inner(self):
        if self._inner is None: self._inner = self.C.inner(None, None)
        return self._inner

    def profile_allocation(self, prof):
        """EFX₀ allocation for one profile with k4/sdc/sdclib.Enc (values = the types' representatives), complete."""
        sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'sdc'))
        from sdclib import Enc
        from pysat.solvers import Cadical153
        E = Enc(self.sets, [list(self.dom[i][t]) for i, t in enumerate(prof)], self.m)
        s = Cadical153(bootstrap_with=E.cl + [[-E.x[g][self.n]] for g in range(self.m)])
        A = None
        if s.solve():
            mod = set(l for l in s.get_model() if l > 0)
            A = [next(j for j in range(self.n) if E.x[g][j] in mod) for g in range(self.m)]
        s.delete()
        return A

    def best_allocation(self, prof):
        if self.per_profile: return self.profile_allocation(prof)
        C, x, z = self.C, self.x, self.zin
        xs = [x[g][j] for g in range(self.m) for j in range(self.n)]
        best, bestv = None, None
        for k in range(self.tries):
            if k: self.sol.set_phases([v if b else -v for v, b in zip(xs, self.rng.integers(0, 2, len(xs)))])
            if not self.sol.solve(assumptions=[z[i][t] for i, t in enumerate(prof)]): return None
            mod = self.sol.get_model()
            A = [next(j for j in range(self.n) if mod[x[g][j] - 1] > 0) for g in range(self.m)]
            vol = sum(math.log(max(1, s.sum())) for s in self.safe_sets(A))
            if bestv is None or vol > bestv: best, bestv = A, vol
        return best

    def run(self, cap=1, time_limit=None, log=None):
        """Returns 'certified', 'counterexample' (cap failing profiles found) or 'timeout'."""
        t0 = time.time()
        it = 0
        while True:
            if time_limit and time.time() - t0 > time_limit: return 'timeout'
            if not self.out.solve(): return 'certified' if not self.fails else 'counterexample'
            mod = self.out.get_model()
            prof = [next(t for t, v in enumerate(zi) if mod[v - 1] > 0) for zi in self.z]
            it += 1
            A = self.best_allocation(prof)
            if A is None:
                self.fails.append(prof)
                if log: log(f"  FAIL profile {[list(self.dom[i][t]) for i, t in enumerate(prof)]}")
                if len(self.fails) >= cap: return 'counterexample'
                self.out.add_clause([-self.z[i][t] for i, t in enumerate(prof)])
                continue
            ok = self.safe_sets(A)
            assert all(ok[i][t] for i, t in enumerate(prof)), 'inner and outer encodings disagree'
            self.allocs.append(A)
            self.add_alloc(A)

    def stats(self):
        return {'allocs': len(self.allocs), 'clauses': self.nclauses, 'bits': len(self.b), 'auts': len(self.auts)}


def efx0_raw(sets, vals, owner, n):
    """Raw EFX₀ check with explicit values (vals[i][p] is agent i's value of sets[i][p])."""
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    B = [[g for g, j in enumerate(owner) if j == a] for a in range(n)]
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in B[i])
        for j in range(n):
            if j == i: continue
            for h in B[j]:
                if own < sum(v[i].get(g, 0) for g in B[j] if g != h): return False
    return True


if __name__ == '__main__':
    sets = json.loads(sys.argv[1]); m = 1 + max(g for S in sets for g in S)
    H = Hunt(sets, m, tries=int(os.environ.get('TRIES', 4)))
    t0 = time.time()
    r = H.run()
    print(r, H.stats(), round(time.time() - t0, 2))
