"""Conjecture D for beta = 3 (connected cores with m = 2n - 2): the constructive proof of proofs/beta3.md as an algorithm.
construct(n, m, sets, rank) returns an allocation (X[g] = agent holding good g) following the proof step by step and
raises ProofError if a claim the proof makes along the way fails:
  1. a Q-plan for the Q-agents' rankings (section 3, conditions (P1)-(P5)): found by search here, and certified to
     exist for every beta = 3 core by dg_beta3.py (the finite check of Lemma 7 over the reduced cores);
  2. balanced components of K: every P-agent holds its private good and one shared good (Lemma 4);
  3. active components: the multi-collector theorem (Theorem 2, class MultiCollector) with the Q-agents' single goods
     as pins;
  4. the large bundle: the main collector's (private goods of J and the spares), or the dump target (Theorem 5).
The same code runs every connected core with any beta >= 2 that has a Q-plan (for beta = 2 and for cores without
Q-agents a Q-plan always exists, Corollary 3). EFX0 is not decided here: verify_beta3.py checks every output with the
raw definition. rank[i] = (a, b, c): agent i's goods from best to worst."""
import collections, itertools
import networkx as nx


class ProofError(AssertionError):
    """A claim of the written proof failed on a concrete instance (a counterexample to the proof, not to D)."""


def claim(cond, msg):
    if not cond: raise ProofError(msg)


class Core:
    """Structure of a connected core that does not depend on the ranking profile."""

    def __init__(self, n, m, sets):
        self.n, self.m, self.sets = n, m, [tuple(S) for S in sets]
        deg = collections.Counter(g for S in sets for g in S)
        claim(all(len(set(S)) == 3 for S in sets) and set(deg) == set(range(m)), "not a core")
        claim(all(sum(deg[g] == 1 for g in S) <= 1 for S in sets), "agent with two private goods")
        self.deg = deg
        self.priv = [next((g for g in S if deg[g] == 1), None) for S in sets]
        self.shared = [g for g in range(m) if deg[g] >= 2]
        self.P = [i for i in range(n) if self.priv[i] is not None]
        self.Q = [i for i in range(n) if self.priv[i] is None]
        self.ends = {e: tuple(g for g in sets[e] if g != self.priv[e]) for e in self.P}
        K = nx.MultiGraph(); K.add_nodes_from(self.shared)
        for e in self.P: K.add_edge(*self.ends[e], key=e)
        self.K = K
        claim(nx.is_connected(self.H()), "core not connected")
        self.comps = [sorted(C) for C in nx.connected_components(K)]
        self.comp = {v: k for k, C in enumerate(self.comps) for v in C}
        self.cedges = [[] for _ in self.comps]
        for e in self.P: self.cedges[self.comp[self.ends[e][0]]].append(e)
        self.base = [len(self.cedges[k]) - len(C) for k, C in enumerate(self.comps)]
        # Lemma 1 (counting): sum of base(C) = beta - 1 - 2q, with beta = 2n - m + 1
        claim(sum(self.base) == 2 * n - m - 2 * len(self.Q), "counting identity")

    def H(self):
        H = nx.Graph()
        for i, S in enumerate(self.sets):
            H.add_node(('a', i))
            for g in S:
                if g != self.priv[i]: H.add_edge(('a', i), ('g', g))
        return H


# ---------------------------------------------------------------------------------------------------------------------
# Q-plans (section 3)

ROLE_ORDER = ('a', 'b', 'ab', 'ac', 'bc')


def role_goods(r, rz):
    a, b, c = rz
    return {'a': (a,), 'b': (b,), 'ab': (a, b), 'ac': (a, c), 'bc': (b, c)}[r]


def plan_eps(core, Y, Z):
    eps = list(core.base)
    for gs in Y.values():
        for g in gs: eps[core.comp[g]] += 1
    for g in Z: eps[core.comp[g]] += 1
    return eps


def check_plan(core, qrank, plan):
    """Conditions (P1)-(P5) of a Q-plan (proofs/beta3.md section 3). plan = (Y, Z, T): Y[z] = goods of Q-agent z,
    Z = spares, T = dump target (None, or a 2-holder's goods, or a 1-tuple (v,) of a shared good held by a P-agent).
    Returns None if the plan is valid, else the reason."""
    Y, Z, T = plan
    held = [g for gs in Y.values() for g in gs]
    if set(Y) != set(core.Q): return "Y is not defined on the Q-agents"
    if len(set(held)) != len(held) or set(held) & set(Z) or len(set(Z)) != len(Z): return "a good held twice"
    if not all(g in core.comp for g in list(held) + list(Z)): return "a held good is not shared"
    ones = {Y[z][0] for z in core.Q if len(Y[z]) == 1}
    for z in core.Q:
        a, b, c = qrank[z]
        if tuple(Y[z]) not in [role_goods(r, (a, b, c)) for r in ROLE_ORDER]: return f"Y[{z}] is not a role"
        if tuple(Y[z]) == (b,) and a not in ones: return f"b-pin {z}: a_z not held alone by a Q-agent"
    eps = plan_eps(core, Y, Z)
    two = {g for gs in Y.values() if len(gs) == 2 for g in gs}
    for k, e in enumerate(eps):
        if e < 0: return f"(P1) component {k} has excess {e}"
        if e >= 1 and any(core.comp[g] == k for g in two | set(Z)): return f"(P2) active component {k}"
    active = any(e >= 1 for e in eps)
    if active or not Z:
        if T is not None: return "dump target without need"
        L = set(Z)
    else:
        if T is None: return "(P3) spares but no collector and no dump target"
        if not (any(tuple(T) == tuple(Y[z]) for z in core.Q if len(Y[z]) == 2)
                or (len(T) == 1 and T[0] in core.comp and T[0] not in held and T[0] not in Z)): return "(P3) target"
        L = set(Z) | set(T)
    for z in core.Q:
        a, b, c = qrank[z]
        if tuple(Y[z]) == (a,) and b in L and c in L: return f"(P4) a-pin {z}"
        if tuple(Y[z]) == (b,) and a in L: return f"(P5) b-pin {z}"
    return None


def find_plan(core, qrank):
    """First Q-plan in a fixed search order (roles in ROLE_ORDER, fewest spares first), or None."""
    Q = core.Q
    for roles in itertools.product(ROLE_ORDER, repeat=len(Q)):
        Y = {z: role_goods(r, qrank[z]) for z, r in zip(Q, roles)}
        held = [g for gs in Y.values() for g in gs]
        if len(set(held)) != len(held): continue
        ones = {Y[z][0] for z in Q if len(Y[z]) == 1}
        if any(r == 'b' and qrank[z][0] not in ones for z, r in zip(Q, roles)): continue
        eps = plan_eps(core, Y, ())
        if min(eps, default=0) < -1: continue
        two = {core.comp[g] for gs in Y.values() if len(gs) == 2 for g in gs}
        if any(e >= 1 and k in two for k, e in enumerate(eps)): continue
        needy = [k for k, e in enumerate(eps) if e == -1]
        cands = [[v for v in core.comps[k] if v not in held] for k in needy]
        for Z in itertools.product(*cands):
            if not Z:
                plan = (Y, (), None)
                if check_plan(core, qrank, plan) is None: return plan
                continue
            if any(e >= 1 for e in eps):
                plan = (Y, tuple(Z), None)
                if check_plan(core, qrank, plan) is None: return plan
                continue
            targets = [tuple(Y[z]) for z in Q if len(Y[z]) == 2]
            targets += [(v,) for v in core.shared if v not in held and v not in Z]
            for T in targets:
                plan = (Y, tuple(Z), T)
                if check_plan(core, qrank, plan) is None: return plan
    return None


# ---------------------------------------------------------------------------------------------------------------------
# Theorem 2: the multi-collector theorem

class MultiCollector:
    """Vertices V, agents E (each with two endpoints in V and a private good), pins (vertices held alone by an outside
    agent), |E| + |pins| = |V| + k with k >= 1. State: collectors W (k agents of E holding no vertex) and cover[v] for
    every unpinned v (the agent of E - W whose head is v)."""

    def __init__(self, V, E, ends, priv, rank, pins):
        self.V, self.E, self.ends, self.priv, self.rank, self.pins = list(V), list(E), ends, priv, rank, set(pins)
        self.k = len(self.E) + len(self.pins) - len(self.V)
        claim(self.k >= 1, "multi-collector: no deficit")
        claim(self.pins <= set(self.V), "multi-collector: pin outside V")
        claim(all(len(set(ends[e])) == 2 and set(ends[e]) <= set(self.V) for e in self.E), "multi-collector: edge")

    def other(self, e, v):
        x, y = self.ends[e]
        return y if v == x else x

    def status(self, e, head):
        a, b, c = self.rank[e]
        if head == a: return 'happy'
        if head == b and a == self.other(e, head): return 'transparent'
        return 'bad'

    def walk(self, x, cover, head):
        """Walk from vertex x: (True, None) on success, (False, path) on reaching a bad agent,
        path = [(v_0, e_1), ..., (v_{k-1}, e_k)] with e_k bad and e_1..e_{k-1} transparent."""
        path, seen = [], set()
        while True:
            if x in self.pins: return True, None
            e = cover[x]
            s = self.status(e, head[e])
            if s == 'happy': return True, None
            path.append((x, e))
            if s == 'bad': return False, path
            if e in seen: return True, None                                  # a cycle of transparent agents
            seen.add(e)
            x = self.other(e, x)

    def needs(self, w):
        a, b, c = self.rank[w]
        p = self.priv[w]
        return [] if p == a else [a] if p == b else [a, b]

    def solve(self, W, cover):
        W = list(W)
        head = {e: v for v, e in cover.items()}
        claim(len(W) == self.k and set(head) == set(self.E) - set(W), "multi-collector: bad state")
        claim(set(cover) == set(self.V) - self.pins, "multi-collector: cover")
        switches = 0
        while True:
            bad = sum(self.status(e, head[e]) == 'bad' for e in head)
            fail = None
            for w in W:
                for x in self.needs(w):
                    ok, path = self.walk(x, cover, head)
                    if not ok: fail = (w, x, path); break
                if fail: break
            if fail is None: break
            w, x, path = fail
            ys = [y for y, _ in path]; es = [e for _, e in path]
            claim(len(set(ys)) == len(ys) and len(set(es)) == len(es) and not set(es) & set(W), "switch: walk")
            new = es[-1]
            del head[new]
            for i, e in enumerate(es[:-1]):                                  # the transparent prefix moves to tails
                head[e] = self.other(e, ys[i]); cover[head[e]] = e
            head[w] = x; cover[x] = w
            W[W.index(w)] = new
            claim(sum(self.status(e, head[e]) == 'bad' for e in head) == bad - 1, "switch: potential did not drop")
            claim(set(cover) == set(self.V) - self.pins and all(head[cover[v]] == v for v in cover), "switch: cover")
            switches += 1
        J = [e for e in head if self.status(e, head[e]) != 'bad' and self.walk(head[e], cover, head)[0]]
        return W, head, J, switches


def orient(V, E, ends, marks):
    """Lemma 4: in a connected multigraph (V, E) with marked vertices, an injective head map h: E' -> V - marks with
    h(e) an endpoint of e, covering every unmarked vertex, where E' = E minus |E| - |V| + |marks| edges (the
    collectors). Built as in the proof: a spanning forest with one marked vertex per tree, oriented away from it,
    or a spanning unicyclic subgraph oriented along its cycle when nothing is marked."""
    G = nx.MultiGraph(); G.add_nodes_from(V)
    for e in E: G.add_edge(*ends[e], key=e)
    marks = [v for v in V if v in marks]
    used, cover = set(), {}
    if marks:
        T = nx.minimum_spanning_tree(nx.Graph(G))                            # spanning tree (simple graph)
        root = marks[0]
        parent = dict(nx.bfs_predecessors(T, root))
        forest = [(parent[v], v) for v in parent if v not in marks]          # cut the edge above every other mark
        for u, v in forest:
            e = next(k for k in G[u][v] if k not in used)
            used.add(e); cover[v] = e
    else:
        cyc = nx.find_cycle(G)                                               # a cycle, possibly two parallel edges
        for u, v, e in cyc: used.add(e); cover[v] = e
        onc = {v for _, v, _ in cyc}
        seen = set(onc); frontier = list(onc)
        while frontier:
            u = frontier.pop()
            for _, v, e in G.edges(u, keys=True):
                if v not in seen:
                    seen.add(v); used.add(e); cover[v] = e; frontier.append(v)
    claim(set(cover) == set(V) - set(marks), "Lemma 4: cover")
    return cover, [e for e in E if e not in used]


# ---------------------------------------------------------------------------------------------------------------------

_CACHE = {}


def cached(key, fn):
    if key not in _CACHE: _CACHE[key] = fn()
    return _CACHE[key]


def construct(n, m, sets, rank, info=None):
    info = info if info is not None else {}
    key = tuple(map(tuple, sets))
    core = cached((key, 'core'), lambda: Core(n, m, sets))
    qrank = {z: tuple(rank[z]) for z in core.Q}
    plan = cached((key, 'plan', tuple(sorted(qrank.items()))), lambda: find_plan(core, qrank))
    claim(plan is not None, "no Q-plan (Lemma 7 fails)")
    claim(check_plan(core, qrank, plan) is None, "Q-plan invalid")
    Y, Z, T = plan
    eps = plan_eps(core, Y, Z)
    X = [None] * m
    for z, gs in Y.items():
        for g in gs: X[g] = z
    marks = {g for gs in Y.values() for g in gs} | set(Z)
    active = [k for k, e in enumerate(eps) if e >= 1]
    # balanced components: every P-agent holds its private good and one shared good (Lemma 4 with no collector)
    def balanced():
        out = {}
        for k, e in enumerate(eps):
            if e != 0: continue
            cover, rest = orient(core.comps[k], core.cedges[k], core.ends, marks)
            claim(not rest, "balanced component with a collector")
            out.update(cover)
        return out
    bal = cached((key, 'bal', tuple(sorted(Y.items())), Z), balanced)
    for v, e in bal.items(): X[v] = e; X[core.priv[e]] = e
    info.update(q=len(core.Q), roles=''.join(sorted('1' if len(g) == 1 else '2' for g in Y.values())),
                spares=len(Z), active=len(active), dump=T is not None)
    if not active:
        claim(T is not None or not Z, "spares without a home")
        if Z:
            owner = next(z for z in core.Q if tuple(Y[z]) == tuple(T)) if len(T) == 2 else X[T[0]]
            for g in Z: X[g] = owner
            info['large'] = 'dump-Q' if len(T) == 2 else 'dump-P'
        else:
            info['large'] = 'none'
        info.update(collectors=0, J=0, switches=0)
        claim(None not in X, "unassigned good")
        return X
    # active components: Theorem 2 on their union, pins = the Q-agents' single goods in them
    V = [v for k in active for v in core.comps[k]]
    E = [e for k in active for e in core.cedges[k]]
    pins = [v for v in V if v in marks]
    claim(all(len(Y[X[v]]) == 1 for v in pins), "(P2) pin of a 2-holder in an active component")
    MC = MultiCollector(V, E, core.ends, core.priv, rank, pins)
    def initial():
        cover, W = {}, []
        for k in active:
            c, rest = orient(core.comps[k], core.cedges[k], core.ends, marks)
            claim(len(rest) == eps[k], "Lemma 4: number of collectors")
            cover.update(c); W += rest
        return W, cover
    W0, cover0 = cached((key, 'init', tuple(sorted(Y.items())), Z), initial)
    W, head, J, sw = MC.solve(W0, dict(cover0))
    main = W[0]
    for e in E:
        if e in W: X[core.priv[e]] = e; continue
        X[head[e]] = e
        X[core.priv[e]] = main if e in J else e
    for g in Z: X[g] = main
    info.update(collectors=len(W), J=len(J), switches=sw, large='collector')
    claim(None not in X, "unassigned good")
    return X
