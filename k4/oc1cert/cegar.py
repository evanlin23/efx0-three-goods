"""OC1^max for EVERY strict profile of a fixed k = 4 core hypergraph, by ordinal CEGAR (workstream compute/k4-oc1max-cert;
notes in k4/oc1cert.md).

The statement (K4.SDC.OC1MAX, k4/sdc.md §29 and §31).  For a type profile tau (one strict balanced order type per
agent, K4.OT; (C4) for two-private agents) and an SD order whose picks Y form a maximum matching of the agent /
relevant-good graph: the picks have a one-absorber EFX0 completion, or one official move (an addition, a chain or a
ring; k4/sdc/oc1_mc2_rand.py Inst.moves) leads to bases that have one.  "One-absorber": every junk good (a good in no
base) is given to some agent, and at most one agent receives two or more junk goods.

Every comparison this needs is between disjoint sets of goods, so it depends on tau only through the agents' order
types: SD picks compare single goods, the improving conditions compare a new base with a disjoint old base, EFX0
compares X_i with X_j minus a good.

2QBF-style loop, "exists (tau, Y) forall repairs: the repair fails":
  outer SAT : find a type profile tau and picks Y such that
              - Y is a matching (a good is picked at most once, a pick is a relevant good) with nu(H) picks;
              - Y is the SD outcome of some order under tau: (a) every good an agent prefers to its pick (every relevant
                good, if it has none) is picked, (b) the digraph "i prefers Y_j to Y_i" is acyclic (then any reverse
                topological order produces Y; conversely in any order a wanted pick is taken earlier);
              - every witness found so far fails at (tau, Y);
  inner     : for the integer representative of tau, look for a witness at Y: a completion of the picks, or a move and a
              completion of the moved bases (incremental SAT with type assumptions, raw move rules);
  until the outer is UNSAT (OC1^max holds for every profile of the hypergraph) or the inner finds nothing (a
  counterexample candidate: re-checked with the raw checker of k4/sdc/oc1_mc2_rand.py before anything is claimed).

A witness W = (F, Y*_F, B'_F, imp, X): the agents F whose bases the move changes (F = {} for a completion of the
picks), their picks Y*_F, their new bases B'_F, the improving comparisons imp, and a complete allocation X containing
the moved bases.  W repairs (tau, Y) whenever
  1. Y_x = Y*_x for x in F;
  2. Y_j lies in X_j (or j has no pick) for j outside F;
  3. at most one agent is an absorber: |X_j minus B'_j| >= 2, with B'_j = {Y_j} outside F;
  4. tau satisfies every comparison of imp, and X is EFX0 under tau.
(Given 1 and 2 the sets the move adds are junk at Y, because they lie in the movers' X bundles and every other pick
lies in its holder's bundle; the move then produces B'_F and leaves the others' bases; so W is a legal move and a
one-absorber completion at Y.)  The negation of 1-4 is a clause over pick literals, comparison bits and pairs of
pickless agents, so a witness found at one (tau, Y) blocks every (tau', Y') it repairs.  Automorphism images of each
witness are added as well (sound: the statement is invariant under automorphisms of the hypergraph, and the type
domains are too).

The certificate is the list of witnesses (after compaction by an UNSAT core); k4/oc1cert/check.py re-checks it with
its own type enumeration, the raw move rules, per-matching SD regions encoded through orders, and another solver."""
import itertools, json, math, os, sys, time
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

HERE = os.path.dirname(os.path.abspath(__file__))
OT = json.load(open(os.path.join(HERE, '..', 'order_types.json')))
STRICT_BAL = {k: [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict'] and t['balanced']] for k in (3, 4)}
TRUE, FALSE = 'T', 'F'


def neg(l):
    return FALSE if l is TRUE else TRUE if l is FALSE else -l


def domain(S, deg):
    """Strict balanced types of an agent with good list S (integer representatives in S's order); (C4) for two
    private goods p, q: p + q < s + t (k4/search4.py, LEDGER K4.CORE)."""
    priv = [p for p, g in enumerate(S) if deg[g] == 1]
    dom = STRICT_BAL[len(S)]
    if len(priv) == 2:
        dom = [v for v in dom if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
    return dom


def max_matching_size(sets, m):
    G = nx.Graph()
    G.add_nodes_from(('a', i) for i in range(len(sets)))
    G.add_nodes_from(('g', g) for g in range(m))
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    M = nx.bipartite.maximum_matching(G, top_nodes=[('a', i) for i in range(len(sets))])
    return len(M) // 2


def automorphisms(sets, m, cap=256):
    n = len(sets)
    G = nx.Graph()
    G.add_nodes_from((('a', i) for i in range(n)), side=0)
    G.add_nodes_from((('g', g) for g in range(m)), side=1)
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    out = []
    for iso in GraphMatcher(G, G, node_match=lambda a, b: a['side'] == b['side']).isomorphisms_iter():
        out.append(([iso[('a', i)][1] for i in range(n)], [iso[('g', g)][1] for g in range(m)]))
        if len(out) >= cap: break
    return out


def nonempty_subsets(xs):
    for r in range(1, len(xs) + 1):
        yield from itertools.combinations(xs, r)


def subsets(xs):
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


class Witness:
    """See the module docstring.  fix: {agent: pick or None}; newb: {agent: tuple of goods}; imp: [(agent, new, old)];
    X: owner of every good; moves: the moves as found, applied in turn from the picks (for the certificate and the
    checker), each (kind, path, H)."""
    __slots__ = ('fix', 'newb', 'imp', 'X', 'moves', 'owner')

    def __init__(self, fix, newb, imp, X, moves, owner=None):
        self.fix, self.newb, self.imp, self.X, self.moves = fix, newb, imp, tuple(X), tuple(moves)
        self.owner = owner        # S* runs only: the completion's owner

    @property
    def kind(self):
        return 'picks' if not self.moves else self.moves[0][0] if len(self.moves) == 1 else '%d moves' % len(self.moves)

    def image(self, ma, mg):
        f = lambda S: tuple(sorted(mg[g] for g in S))
        return Witness({ma[x]: (None if y is None else mg[y]) for x, y in self.fix.items()},
                       {ma[x]: f(B) for x, B in self.newb.items()},
                       [(ma[x], f(a), f(b)) for x, a, b in self.imp],
                       _perm_owner(self.X, ma, mg),
                       [(k, tuple(ma[x] for x in path), tuple(f(h) for h in H)) for k, path, H in self.moves],
                       None if self.owner is None else ma[self.owner])

    def key(self):
        return (tuple(sorted(self.fix.items(), key=lambda t: t[0])), self.X, self.moves, self.owner)

    def to_json(self):
        d = {'picks': {str(x): y for x, y in sorted(self.fix.items())}, 'X': ''.join(map(str, self.X))}
        if self.owner is not None: d['owner'] = self.owner
        if len(self.moves) <= 1:
            k, path, H = self.moves[0] if self.moves else ('picks', (), ())
            d.update({'kind': k, 'path': list(path), 'H': [list(h) for h in H]})
        else:
            d.update({'kind': 'seq', 'moves': [{'kind': k, 'path': list(path), 'H': [list(h) for h in H]}
                                               for k, path, H in self.moves]})
        return d


def _perm_owner(X, ma, mg):
    out = [0] * len(X)
    for g, a in enumerate(X): out[mg[g]] = ma[a]
    return out


class Cert:
    def __init__(self, sets, m=None, cap_aut=256, solver='cd15', tries=3, seed=1, keep=2, require_max=True, depth=1, kcand=6, prime=False, sstar=False, r2=None):
        self.sets = [list(S) for S in sets]; self.n = n = len(sets)
        self.m = m = m if m is not None else 1 + max(g for S in sets for g in S)
        self.R = [set(S) for S in self.sets]
        self.pos = [{g: p for p, g in enumerate(S)} for S in self.sets]
        deg = [sum(g in S for S in self.sets) for g in range(m)]
        self.dom = [domain(S, deg) for S in self.sets]
        self.ss = []
        for i, S in enumerate(self.sets):
            k = len(S); V = np.array(self.dom[i], dtype=np.int64)
            self.ss.append(np.stack([V[:, [p for p in range(k) if M >> p & 1]].sum(axis=1) for M in range(1 << k)], 1))
        self.nu = max_matching_size(self.sets, m)
        self.require_max = require_max
        self.auts = automorphisms(self.sets, m, cap_aut) if cap_aut else [(list(range(n)), list(range(m)))]
        self.tries, self.keep, self.depth, self.kcand, self.prime = tries, keep, depth, kcand, prime
        self.sstar = sstar        # S*-shaped completions (k4/oc1_hall.md §2 on claude/k4-oc1-hall)
        self.r2 = r2              # 'm' (R2-M) or 'star' (R2*): TTC's forms at perfect starts with >= 2 receivers
        self.rng = np.random.default_rng(seed)
        self._build_outer(solver)
        self._build_inner()
        self.witnesses = []          # every witness whose clause was added (images included)
        self.wclauses = []
        self.seen = set()
        self.found = []              # witnesses found by the inner (before images)
        self.fails = []
        self.oc1_fails = []          # (profile, picks) where the inner needed two moves (OC1^max fails there)

    # ------------------------------------------------------------------ outer
    def mask(self, i, S):
        return sum(1 << self.pos[i][g] for g in S if g in self.pos[i])

    def cmp(self, i, A, B):
        """Literal for v_i(A) > v_i(B), A and B disjoint position masks over sets[i]."""
        if A == 0: return FALSE
        if B == 0: return TRUE
        if A < B: return self._bit(i, A, B)
        return -self._bit(i, B, A)

    def _bit(self, i, A, B):
        key = (i, A, B)
        b = self.bits.get(key)
        if b is not None: return b
        b = self.bits[key] = self.vp.id(('c',) + key)
        pos = np.flatnonzero(self.ss[i][:, A] > self.ss[i][:, B])
        if len(pos) == 0: self.out.add_clause([-b])
        elif len(pos) == len(self.dom[i]): self.out.add_clause([b])
        else:
            self.out.add_clause([-b] + [self.z[i][t] for t in pos])
            for t in pos: self.out.add_clause([-self.z[i][t], b])
        return b

    def _clause(self, lits):
        cl = []
        for l in lits:
            if l is TRUE: return None
            if l is FALSE: continue
            cl.append(l)
        return cl

    def _build_outer(self, solver):
        n, m, vp = self.n, self.m, IDPool()
        self.vp = vp; self.bits = {}
        self.out = out = Solver(name=solver)
        self.z = [[vp.id(('z', i, t)) for t in range(len(D))] for i, D in enumerate(self.dom)]
        for zi in self.z:
            for c in CardEnc.equals(zi, 1, vpool=vp, encoding=EncType.seqcounter if len(zi) > 8 else EncType.pairwise).clauses:
                out.add_clause(c)
        self.p = [{g: vp.id(('p', i, g)) for g in S} for i, S in enumerate(self.sets)]
        self.pn = [vp.id(('pn', i)) for i in range(n)]
        for i in range(n):
            lits = list(self.p[i].values()) + [self.pn[i]]
            for c in CardEnc.equals(lits, 1, vpool=vp, encoding=EncType.pairwise).clauses: out.add_clause(c)
        holders = {g: [self.p[i][g] for i in range(n) if g in self.R[i]] for g in range(m)}
        for g in range(m):
            if len(holders[g]) > 1:
                for c in CardEnc.atmost(holders[g], 1, vpool=vp, encoding=EncType.pairwise).clauses: out.add_clause(c)
        # maximum matching: at most n - nu pickless agents (a matching has at most nu picks)
        if self.require_max and n - self.nu < n:
            for c in CardEnc.atmost(self.pn, n - self.nu, vpool=vp, encoding=EncType.seqcounter).clauses: out.add_clause(c)
        # SD (a): a pickless agent's goods are all picked; a pick beats every unpicked relevant good
        for i in range(n):
            for g in self.sets[i]:
                others = [self.p[j][g] for j in range(n) if j != i and g in self.R[j]]
                out.add_clause([-self.pn[i]] + others)
                for h in self.sets[i]:
                    if h == g: continue
                    cl = self._clause([-self.p[i][h]] + others + [self.cmp(i, self.mask(i, [h]), self.mask(i, [g]))])
                    if cl is not None: out.add_clause(cl)
        # SD (b): wants digraph among pick holders, acyclic
        self.w = {}
        for i in range(n):
            for j in range(n):
                if i != j and self.R[i] & self.R[j]: self.w[(i, j)] = vp.id(('w', i, j))
        for (i, j), wij in self.w.items():
            for g in self.R[i] & self.R[j]:
                for h in self.sets[i]:
                    if h == g: continue
                    cl = self._clause([-self.p[i][h], -self.p[j][g], neg(self.cmp(i, self.mask(i, [g]), self.mask(i, [h]))), wij])
                    if cl is not None: out.add_clause(cl)
        for k in range(2, n + 1):
            for cyc in itertools.permutations(range(n), k):
                if cyc[0] != min(cyc): continue
                edges = [(cyc[t], cyc[(t + 1) % k]) for t in range(k)]
                if all(e in self.w for e in edges): out.add_clause([-self.w[e] for e in edges])
        if self.r2:
            # perfect starts only, with at least two receivers (pick holders whose pick no other agent prefers)
            for i in range(n): out.add_clause([-self.pn[i]])
            self.rec = [vp.id(('rec', j)) for j in range(n)]
            for j in range(n):
                for i in range(n):
                    if (i, j) in self.w: out.add_clause([-self.rec[j], -self.w[(i, j)]])
            minrec = int(os.environ.get('R2_MINREC', '2'))     # 2 is R2's hypothesis; 1 is a sanity test (must fail)
            for c in CardEnc.atleast(self.rec, minrec, vpool=vp, encoding=EncType.seqcounter).clauses: out.add_clause(c)
        # pairs of pickless agents (for the absorber count)
        self.dpair = {}
        if n - (self.nu if self.require_max else 0) >= 2:
            for a, b in itertools.combinations(range(n), 2):
                d = self.dpair[(a, b)] = vp.id(('d', a, b))
                out.add_clause([-d, self.pn[a]]); out.add_clause([-d, self.pn[b]])

    def witness_clause(self, W):
        """Literals of 'W does not repair (tau, Y)', or None if W never applies (two fixed absorbers)."""
        n = self.n; X = W.X
        bundles = [[] for _ in range(n)]
        for g, a in enumerate(X): bundles[a].append(g)
        lits = []
        for x, y in W.fix.items():
            lits.append(-(self.pn[x] if y is None else self.p[x][y]))
        fixed_abs = 0; cand2 = []
        for j in range(n):
            if j in W.fix:
                if len(set(bundles[j]) - set(W.newb[j])) >= 2: fixed_abs += 1
                continue
            lits += [self.p[j][g] for g in self.sets[j] if X[g] != j]
            if len(bundles[j]) >= 3: fixed_abs += 1
            elif len(bundles[j]) == 2: cand2.append(j)
        if fixed_abs >= 2: return None
        if fixed_abs == 1: lits += [self.pn[j] for j in cand2]
        else: lits += [self.dpair[(a, b)] for a, b in itertools.combinations(cand2, 2) if (a, b) in self.dpair]
        for x, new, old in W.imp:
            A, B = self.mask(x, set(new) - set(old)), self.mask(x, set(old) - set(new))
            lits.append(neg(self.cmp(x, A, B)))
        for i in range(n):
            O, Ts = self.threats(i, X)
            lits += [self.cmp(i, T, O) for T in Ts]
        return self._clause(lits)

    def threats(self, i, X):
        """Own mask O and the inclusion-maximal threat masks of agent i in allocation X (as in k4/hunt/cegar.py)."""
        pos = self.pos[i]; O = 0; groups = {}
        for g, j in enumerate(X):
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
                for p in range(len(self.sets[i])):
                    if G >> p & 1: T.add(G & ~(1 << p))
        return O, sorted(t for t in T if not any(u != t and u & t == t for u in T))

    def add_witness(self, W):
        added = 0
        for ma, mg in self.auts:
            I = W.image(ma, mg)
            k = I.key()
            if k in self.seen: continue
            self.seen.add(k)
            cl = self.witness_clause(I)
            if cl is None: continue
            self.witnesses.append(I); self.wclauses.append(cl)
            self.out.add_clause(cl); added += 1
        return added

    # ------------------------------------------------------------------ inner
    def _build_inner(self):
        n, m, vp = self.n, self.m, IDPool()
        x = [[vp.id(('x', g, j)) for j in range(n)] for g in range(m)]
        cl = []
        for g in range(m):
            cl += CardEnc.equals([x[g][j] for j in range(n)], 1, vpool=vp, encoding=EncType.pairwise).clauses
        u = [vp.id(('u', g)) for g in range(m)]
        big = [vp.id(('big', j)) for j in range(n)]
        for j in range(n):
            for g, h in itertools.combinations(range(m), 2):
                cl.append([-x[g][j], -x[h][j], -u[g], -u[h], big[j]])
        cl += CardEnc.atmost(big, 1, vpool=vp, encoding=EncType.pairwise).clauses
        self.iown = self.inh = None
        if self.sstar or self.r2:
            # S*: one owner (any agent) takes any number of junk goods; a non-holder (assumption nh) other than the
            # owner takes none; a holder other than the owner takes at most one (big -> owner)
            own = [vp.id(('own', j)) for j in range(n)]; nh = [vp.id(('nh', j)) for j in range(n)]
            cl += CardEnc.atmost(own, 1, vpool=vp, encoding=EncType.pairwise).clauses
            for j in range(n):
                cl.append([-big[j], own[j]])
                for g in range(m): cl.append([-nh[j], -x[g][j], -u[g], own[j]])
            self.iown, self.inh = own, nh
        z = []
        for i, S in enumerate(self.sets):
            k = len(S); ss = self.ss[i]
            smin = np.stack([np.array(self.dom[i])[:, [p for p in range(k) if M >> p & 1]].min(axis=1) if M else
                             np.zeros(len(self.dom[i]), dtype=np.int64) for M in range(1 << k)], 1)
            ext = {j: vp.id(('e', i, j)) for j in range(n) if j != i}
            for j in ext:
                cl += [[-x[h][j], ext[j]] for h in range(m) if h not in self.R[i]]
            gl = [[] for _ in range(len(self.dom[i]))]     # gl[t]: the guards that type t switches on
            z.append(gl)
            for O in range(1 << k):
                for G in range(1, 1 << k):
                    if G & O: continue
                    for kind, bad in (('E', ss[:, O] < ss[:, G] - smin[:, G]), ('F', ss[:, O] < ss[:, G])):
                        pos = np.flatnonzero(bad)
                        if not len(pos): continue
                        gd = vp.id(('gd', i, O, G, kind))
                        for j in ext:
                            base = [-gd] + [x[S[p]][i] for p in range(k) if not O >> p & 1] \
                                   + [-x[S[p]][j] for p in range(k) if G >> p & 1]
                            cl.append(base if kind == 'E' else base + [-ext[j]])
                        for t in pos: gl[t].append(gd)
        self.inn = Solver(name='cd15', bootstrap_with=cl)
        self.ix, self.iz, self.iu = x, z, u

    def nonholders(self, prof, base):
        """S*: the agents that are not holders at these bases under the profile (two or more base goods, or one base
        good that some other agent prefers to its own base)"""
        vals = self.vals_of(prof)
        V = lambda i, S: sum(vals[i].get(g, 0) for g in S)
        out = []
        for j, B in enumerate(base):
            if len(B) >= 2 or (len(B) == 1 and any(i != j and vals[i].get(B[0], 0) > V(i, base[i]) for i in range(self.n))):
                out.append(j)
        return out

    def complete(self, prof, base, tries=1, shape=None):
        """One-absorber EFX0 completions of the bases (list of goods per agent) under the profile (type indices);
        returns up to `tries` allocations (owner lists), or [].  With sstar: S*-shaped, and self.last_owner is set."""
        holder = {g: a for a, B in enumerate(base) for g in B}
        ass = [gd for i, t in enumerate(prof) for gd in self.iz[i][t]]     # the type's guards (others stay free)
        ass += [self.ix[g][a] for g, a in holder.items()]
        ass += [(-self.iu[g] if g in holder else self.iu[g]) for g in range(self.m)]
        if self.sstar:
            NH = set(self.nonholders(prof, [list(b) for b in base]))
            ass += [(self.inh[j] if j in NH else -self.inh[j]) for j in range(self.n)]
            self.last_owners = []
        elif self.r2 and shape is not None:
            kind, x0 = shape
            if kind in ('m', 'star'):
                # R2-M / R2*: nobody takes two junk goods; with 'm' (owner x0) the holders of two or more base goods
                # other than x0 take none
                ass += [-self.iown[j] for j in range(self.n)]
                ass += [(self.inh[j] if (kind == 'm' and j != x0 and len(base[j]) >= 2) else -self.inh[j]) for j in range(self.n)]
            elif kind == 'o':
                # R2-O: one absorber, and only the agent x0 (here: the chosen owner u) may take two or more
                ass += [-self.iown[j] for j in range(self.n) if j != x0]
                ass += [-self.inh[j] for j in range(self.n)]
            else:
                # R2-C: any one-absorber completion
                ass += [-self.inh[j] for j in range(self.n)]
        elif self.r2:
            ass += [-self.inh[j] for j in range(self.n)]       # the plain one-absorber completion
        res = []
        xs = [self.ix[g][j] for g in range(self.m) for j in range(self.n)]
        for k in range(tries):
            if k: self.inn.set_phases([v if b else -v for v, b in zip(xs, self.rng.integers(0, 2, len(xs)))])
            if not self.inn.solve(assumptions=ass): return res
            mod = self.inn.get_model()
            res.append(tuple(next(j for j in range(self.n) if mod[self.ix[g][j] - 1] > 0) for g in range(self.m)))
            if self.sstar:
                self.last_owners.append(next((j for j in range(self.n) if mod[self.iown[j] - 1] > 0), None))
        return res

    def sstar_witness(self, prof, Y, st, X, owner, moves, imps):
        """An S* witness: every pick fixed; besides the moves' comparisons, every junk receiver other than the owner
        must stay unwanted: v_i(B'_i) > v_i(g) for each other agent i valuing its single base good g."""
        held = {g for b in st for g in b}
        recv = {X[g] for g in range(self.m) if g not in held}
        req = list(imps)
        for j in recv:
            if j == owner or not st[j]: continue
            g = st[j][0]
            for i in range(self.n):
                if i != j and g in self.R[i]: req.append((i, tuple(st[i]), (g,)))
        fix = {a: Y[a] for a in range(self.n)}
        newb = {a: tuple(st[a]) for a in range(self.n)}
        if owner is None: owner = 0                  # no junk receiver needs to own: any agent will do
        return Witness(fix, newb, req, X, moves, owner)

    def vals_of(self, prof):
        return [dict(zip(S, self.dom[i][t])) for i, (S, t) in enumerate(zip(self.sets, prof))]

    def moves(self, base, vals):
        """Every official move from the bases (k4/sdc/oc1_mc2_rand.py Inst.moves): additions, chains (a chain never
        hands on an empty base), rings.  Yields (kind, path, Hs, newbases {agent: goods}, imp [(agent, new, old)])."""
        n, R = self.n, self.R
        held = {g for B in base for g in B}
        J = [g for g in range(self.m) if g not in held]
        def V(i, S):
            d = vals[i]; t = 0
            for g in S: t += d.get(g, 0)
            return t
        for x in range(n):
            for H in nonempty_subsets([g for g in J if g in R[x]]):
                nb = tuple(sorted(base[x] + H))
                yield 'add', (x,), (H,), {x: nb}, [(x, nb, tuple(base[x]))]
        def ext(path, used, Hs):
            xt = path[-1]
            if len(path) >= 2:
                x0 = path[0]
                pool = [g for g in J if g not in used and g in R[x0]] + [g for g in base[xt] if g in R[x0]]
                v0 = V(x0, base[x0])
                for H0 in nonempty_subsets(pool):
                    if V(x0, H0) > v0:
                        nb = {x0: tuple(sorted(H0))}
                        imp = [(x0, nb[x0], tuple(base[x0]))]
                        for t in range(1, len(path)):
                            nb[path[t]] = tuple(sorted(base[path[t - 1]] + Hs[t]))
                            imp.append((path[t], nb[path[t]], tuple(base[path[t]])))
                        yield 'chain', tuple(path), (tuple(H0),) + tuple(Hs[1:]), nb, imp
            if len(path) >= n or not base[xt]: return
            for y in range(n):
                if y in path: continue
                vy = V(y, base[y]); vt = V(y, base[xt])
                for H in subsets([g for g in J if g not in used and g in R[y]]):
                    if vt + V(y, H) > vy:
                        yield from ext(path + [y], used | set(H), Hs + [H])
        if not self.prime:
            for x in range(n): yield from ext([x], frozenset(), [()])
        else:
            # OC1' (kgen/rounds.md §4.6 on proof/kgen-rounds): every non-end chain agent may also take goods of the
            # end's base B_e that it values; the end takes junk only.  The end e is fixed first, so every pool is
            # known and each improving condition is exact when the agent joins.
            def extp(e, path, used, Hs):
                xt = path[-1]
                if xt == e:
                    x0 = path[0]
                    pool = [g for g in J if g not in used and g in R[x0]] + [g for g in base[e] if g not in used and g in R[x0]]
                    v0 = V(x0, base[x0])
                    for H0 in nonempty_subsets(pool):
                        if V(x0, H0) > v0:
                            nb = {x0: tuple(sorted(H0))}
                            imp = [(x0, nb[x0], tuple(base[x0]))]
                            for t in range(1, len(path)):
                                nb[path[t]] = tuple(sorted(base[path[t - 1]] + Hs[t]))
                                imp.append((path[t], nb[path[t]], tuple(base[path[t]])))
                            mid = any(g in base[e] for t in range(1, len(path) - 1) for g in Hs[t])
                            yield ('chainp' if mid else 'chain'), tuple(path), (tuple(H0),) + tuple(Hs[1:]), nb, imp
                    return
                if len(path) >= n or not base[xt]: return
                for y in range(n):
                    if y in path: continue
                    if y == e: pool = [g for g in J if g not in used and g in R[y]]
                    else: pool = [g for g in J if g not in used and g in R[y]] + [g for g in base[e] if g not in used and g in R[y]]
                    vy = V(y, base[y]); vt = V(y, base[xt])
                    for H in subsets(pool):
                        if vt + V(y, H) > vy:
                            yield from extp(e, path + [y], used | set(H), Hs + [H])
            for e in range(n):
                for x in range(n):
                    if x != e: yield from extp(e, [x], frozenset(), [()])
        for r in range(2, n + 1):
            for cyc in itertools.permutations(range(n), r):
                if cyc[0] != min(cyc): continue

                def ring(i, used, Hs):
                    if i == r:
                        nb, imp = {}, []
                        for t in range(r):
                            nb[cyc[t]] = tuple(sorted(base[cyc[t - 1]] + Hs[t]))
                            imp.append((cyc[t], nb[cyc[t]], tuple(base[cyc[t]])))
                        yield 'ring', tuple(cyc), tuple(Hs), nb, imp; return
                    w, pred = cyc[i], cyc[i - 1]
                    if not base[pred]: return
                    vw = V(w, base[w]); vp_ = V(w, base[pred])
                    for H in subsets([g for g in J if g not in used and g in R[w]]):
                        if vp_ + V(w, H) > vw: yield from ring(i + 1, used | set(H), Hs + [H])
                yield from ring(0, frozenset(), [])

    def volume(self, W):
        """log of the number of type profiles under which W's comparisons hold (W's generality in tau)."""
        tot = 0.0
        for i in range(self.n):
            O, Ts = self.threats(i, W.X)
            ok = np.ones(len(self.dom[i]), dtype=bool)
            for T in Ts: ok &= self.ss[i][:, T] < self.ss[i][:, O]
            for x, new, old in W.imp:
                if x == i:
                    ok &= self.ss[i][:, self.mask(i, set(new) - set(old))] > self.ss[i][:, self.mask(i, set(old) - set(new))]
            tot += math.log(max(1, ok.sum()))
        return tot

    def inner_r2(self, prof, Y):
        """R2-M / R2*: a one-absorber completion of the picks, else a canonical chain (x0 frozen and valuing junk, x1
        preferring x0's pick to its own, ending at a receiver) whose bases have the R2 shape's completion."""
        base = [(y,) if y is not None else () for y in Y]
        # the one-absorber completion of the picks: the same constraints as without r2, since nobody owns
        # (assumptions: no nh), and own[] free (big -> own; at most one own)
        Xs = self.complete(prof, base, self.tries)
        if Xs:
            return sorted([Witness({}, {}, [], X, ()) for X in Xs], key=self.volume, reverse=True)[:1]
        vals = self.vals_of(prof)
        wants = lambda i, j: Y[j] in vals[i] and vals[i][Y[j]] > vals[i].get(Y[i], 0)
        held = set(Y)
        frozen = [any(wants(i, j) for i in range(self.n) if i != j) for j in range(self.n)]
        recv = [not frozen[j] for j in range(self.n)]
        cands = []
        for kind, path, Hs, nb, imp in self.moves(list(base), vals):
            if kind != 'chain' or len(path) < 2: continue
            x0, x1, z = path[0], path[1], path[-1]
            if not (frozen[x0] and any(g in self.R[x0] and g not in held for g in range(self.m)) and wants(x1, x0) and recv[z]):
                continue
            st = [list(nb.get(a, base[a])) for a in range(self.n)]
            owner, Xs = None, []
            if self.r2 in ('o', 'og'):      # the owner: a receiver at the picks, not on the chain
                for u in range(self.n):
                    if recv[u] and u not in path:
                        Xs = self.complete(prof, st, 1, shape=('o', u))
                        if Xs: owner = u; break
                if not Xs and self.r2 == 'og':  # generous reading: no owner at all (nobody takes two junk goods)
                    Xs = self.complete(prof, st, 1, shape=('star', x0))
            else:
                Xs = self.complete(prof, st, 1, shape=(self.r2, x0))
            if not Xs: continue
            req = list(imp) + [(x1, (Y[x0],), (Y[x1],))]
            req += [(i, (Y[i],), (Y[z],)) for i in range(self.n) if i != z and Y[z] in self.R[i]]
            if owner is not None:
                req += [(i, (Y[i],), (Y[owner],)) for i in range(self.n) if i != owner and Y[owner] in self.R[i]]
            W = Witness({a: Y[a] for a in range(self.n)}, {a: tuple(st[a]) for a in range(self.n)}, req, Xs[0],
                        ((kind, path, Hs),), owner)
            cands.append(W)
            if len(cands) >= self.kcand: break
        return sorted(cands, key=self.volume, reverse=True)[:self.keep]

    def inner(self, prof, Y):
        if self.r2: return self.inner_r2(prof, Y)
        """Witnesses at (prof, Y): the best completions of the picks, else the best (move sequence, completion) pairs
        with the fewest moves (at most self.depth)."""
        base = [(y,) if y is not None else () for y in Y]
        Xs = self.complete(prof, base, self.tries)
        if Xs:
            if self.sstar:
                Ws = [self.sstar_witness(prof, Y, base, X, o, (), []) for X, o in zip(Xs, self.last_owners)]
            else:
                Ws = [Witness({}, {}, [], X, ()) for X in Xs]
            return sorted(Ws, key=self.volume, reverse=True)[:1]
        vals = self.vals_of(prof)
        start = tuple(base)
        seen = {start}
        level = [(start, (), {}, [])]        # (state, moves, changed bases {agent: base}, improving comparisons)
        for d in range(self.depth):
            cands, nxt = [], []
            for st, mv, nbs, imps in level:
                for kind, path, Hs, nb, imp in self.moves(list(st), vals):
                    st2 = tuple(nb.get(a, st[a]) for a in range(self.n))
                    if st2 in seen: continue
                    seen.add(st2)
                    nbs2 = {**nbs, **nb}; mv2 = mv + ((kind, path, Hs),); imps2 = imps + imp
                    nxt.append((st2, mv2, nbs2, imps2))
                    Xs = self.complete(prof, [list(b) for b in st2], 1)
                    if Xs:
                        if self.sstar:
                            cands.append(self.sstar_witness(prof, Y, st2, Xs[0], self.last_owners[0], mv2, imps2))
                        else:
                            fix = {x: (base[x][0] if base[x] else None) for x in nbs2}
                            cands.append(Witness(fix, nbs2, imps2, Xs[0], mv2))
                        if len(cands) >= self.kcand: break
                if len(cands) >= self.kcand: break
            if cands:
                if d >= 1: self.oc1_fails.append((list(prof), tuple(Y)))     # no witness with one move: OC1 fails here
                return sorted(cands, key=self.volume, reverse=True)[:self.keep]
            level = nxt
        return []

    # ------------------------------------------------------------------ loop
    def run(self, time_limit=None, log=None, max_fail=1):
        t0 = time.time(); self.iters = 0
        while True:
            if time_limit and time.time() - t0 > time_limit: return 'timeout'
            if not self.out.solve(): return 'certified' if not self.fails else 'FAIL'
            mod = self.out.get_model(); pos = set(l for l in mod if l > 0)
            prof = [next(t for t, v in enumerate(zi) if v in pos) for zi in self.z]
            Y = tuple(next((g for g, v in self.p[i].items() if v in pos), None) for i in range(self.n))
            self.iters += 1
            Ws = self.inner(prof, Y)
            if not Ws:
                self.fails.append((prof, Y))
                if log: log('  NO WITNESS: profile %s picks %s' % ([list(self.dom[i][t]) for i, t in enumerate(prof)], Y))
                if len(self.fails) >= max_fail: return 'FAIL'
                # block this exact (profile, picks) pair and continue
                self.out.add_clause([-self.z[i][t] for i, t in enumerate(prof)] +
                                    [-(self.pn[i] if y is None else self.p[i][y]) for i, y in enumerate(Y)])
                continue
            for W in Ws:
                assert self.witness_clause(W) is not None
                self.found.append(W)
                self.add_witness(W)

    def compact(self):
        """A subset of the witness clauses that is still UNSAT with the outer's constraints (an UNSAT core)."""
        n_w = len(self.wclauses)
        # the outer constraints, rebuilt on a fresh solver, with a selector per witness clause
        base = Cert.__new__(Cert)
        base.__dict__.update({k: v for k, v in self.__dict__.items() if k in ('sets', 'n', 'm', 'R', 'pos', 'dom', 'ss', 'nu', 'require_max', 'r2')})
        base._build_outer('cd15')
        cls = [base.witness_clause(W) for W in self.witnesses]
        s2 = [base.vp.id(('sel', k)) for k in range(n_w)]
        for c, s in zip(cls, s2): base.out.add_clause(c + [-s])
        assert not base.out.solve(assumptions=s2)
        core = set(base.out.get_core() or [])
        keep = [W for W, s in zip(self.witnesses, s2) if s in core]
        base.out.delete()
        return keep

    def stats(self):
        kinds = {}
        for W in self.found: kinds[W.kind] = kinds.get(W.kind, 0) + 1
        return {'iters': self.iters, 'found': len(self.found), 'kinds': kinds, 'clauses': len(self.wclauses),
                'bits': len(self.bits), 'auts': len(self.auts), 'nu': self.nu}


if __name__ == '__main__':
    sets = json.loads(sys.argv[1])
    t0 = time.time()
    C = Cert(sets)
    r = C.run(log=print)
    print(r, C.stats(), '%.2f s' % (time.time() - t0))
    if r == 'certified':
        k = C.compact()
        print('compact', len(k), 'of', len(C.witnesses), '%.2f s' % (time.time() - t0))
