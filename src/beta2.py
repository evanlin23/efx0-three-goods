"""Conjecture D for beta = 2 (connected cores with m = 2n - 1): the constructive proof of proofs/beta2.md as an algorithm.
construct(n, m, sets, rank) returns an allocation (X[g] = agent holding good g) following the proof's case analysis
step by step, asserting each claim the proof makes along the way:
  pi = n       collector theorem (Theorem 1) on the multigraph K: shared goods = vertices, agents = edges;
  pi < n       Lemma O (a branch agent holds its top alone, everyone else two own goods), when its top lies in a tree
               component of G - z; otherwise the dumbbell cases H1 (pi = n - 1), H2 and H2' (pi = n - 2).
Nothing here decides EFX0: check.py-style verification is done separately with the raw definition (verify_beta2.py).
rank[i] = (a, b, c): agent i's goods from best to worst."""
import collections
import networkx as nx


class ProofError(AssertionError):
    """A claim of the written proof failed on a concrete instance (a counterexample to the proof, not to D)."""


def claim(cond, msg):
    if not cond: raise ProofError(msg)


def classify(n, m, sets):
    deg = collections.Counter(g for S in sets for g in S)
    priv = [next((g for g in S if deg[g] == 1), None) for S in sets]
    shared = [g for g in range(m) if deg[g] >= 2]
    claim(all(len(set(S)) == 3 for S in sets) and set(deg) == set(range(m)), "not a core")
    claim(all(sum(deg[g] == 1 for g in S) <= 1 for S in sets), "agent with two private goods")
    claim(m == 2 * n - 1, "beta != 2")
    return deg, priv, shared


def H_graph(n, sets, priv):
    """Incidence graph without private goods: agents ('a', i), shared goods ('g', g)."""
    H = nx.Graph()
    for i, S in enumerate(sets):
        H.add_node(('a', i))
        for g in S:
            if g != priv[i]: H.add_edge(('a', i), ('g', g))
    return H


def lemma_O(n, m, sets, z, g):
    """Allocation in which z holds exactly {g} and every other agent exactly two of its own goods (Hall; the proof
    shows it exists when the component of g in G - z is a tree)."""
    B = nx.Graph()
    left = [(i, k) for i in range(n) if i != z for k in (0, 1)]
    B.add_nodes_from(left, bipartite=0)
    for i, S in enumerate(sets):
        if i == z: continue
        for h in S:
            if h != g:
                for k in (0, 1): B.add_edge((i, k), ('good', h))
    M = nx.bipartite.maximum_matching(B, top_nodes=left)
    claim(all(u in M for u in left), f"Lemma O: no 2-matching for z={z}, g={g}")
    X = [None] * m
    X[g] = z
    for (i, k) in left: X[M[(i, k)][1]] = i
    claim(None not in X, "Lemma O: a good is unassigned")
    return X


class Collector:
    """Theorem 1 (collector theorem). Vertices V (shared goods), agents E (each with two endpoints in V and a private
    good), pins (vertices held alone by an outside agent), |E| + |pins| = |V| + 1. State: collector w and cover[v] for
    every unpinned v (an agent of E - w whose head is v)."""

    def __init__(self, V, E, ends, priv, rank, pins):
        self.V, self.E, self.ends, self.priv, self.rank, self.pins = list(V), list(E), ends, priv, rank, set(pins)
        claim(len(self.E) + len(self.pins) == len(self.V) + 1, "collector: |E| + |pins| != |V| + 1")
        claim(self.pins <= set(self.V), "collector: pin outside V")
        claim(all(len(set(ends[e])) == 2 and set(ends[e]) <= set(self.V) for e in self.E), "collector: bad edge")

    def initial(self, w0):
        """An orientation of E - w0 covering every unpinned vertex exactly once, or None."""
        free = [v for v in self.V if v not in self.pins]
        B = nx.Graph(); B.add_nodes_from(('e', e) for e in self.E if e != w0)
        for e in self.E:
            if e == w0: continue
            for v in self.ends[e]:
                if v not in self.pins: B.add_edge(('e', e), ('v', v))
        top = [('e', e) for e in self.E if e != w0]
        M = nx.bipartite.maximum_matching(B, top_nodes=top)
        if not all(t in M for t in top) or len(top) != len(free): return None
        return {M[('e', e)][1]: e for e in self.E if e != w0}

    def other(self, e, v):
        x, y = self.ends[e]
        return y if v == x else x

    def status(self, e, head):
        a, b, c = self.rank[e]
        if head == a: return 'happy'
        if head == b and a == self.other(e, head): return 'transparent'      # type C holding b, a = its tail
        return 'bad'

    def walk(self, x, cover, head):
        """Backward walk from vertex x: returns (True, None) on success, (False, path) on reaching a bad agent,
        path = [(y_0, c_1), ..., (y_{k-1}, c_k)] with c_k bad and c_1..c_{k-1} transparent."""
        path, seen = [], set()
        while True:
            if x in self.pins: return True, None
            c = cover[x]
            s = self.status(c, head[c])
            if s == 'happy': return True, None
            path.append((x, c))
            if s == 'bad': return False, path
            if c in seen: return True, None                                  # a cycle of transparent agents
            seen.add(c)
            x = self.other(c, x)

    def needs(self, w):
        a, b, c = self.rank[w]
        p = self.priv[w]
        return [] if p == a else [a] if p == b else [a, b]

    def solve(self, w, cover):
        head = {e: v for v, e in cover.items()}
        claim(len(cover) == len(self.V) - len(self.pins) and set(head) == set(self.E) - {w}, "collector: bad state")
        switches = 0
        while True:
            bad = sum(self.status(e, head[e]) == 'bad' for e in head)
            fail = None
            for x in self.needs(w):
                ok, path = self.walk(x, cover, head)
                if not ok: fail = (x, path); break
            if fail is None: break
            x, path = fail
            ys = [y for y, _ in path]; cs = [c for _, c in path]
            claim(len(set(ys)) == len(ys) and len(set(cs)) == len(cs) and w not in cs, "switch: walk not simple")
            newb = cs[-1]
            del head[newb]
            for i, c in enumerate(cs[:-1]):                                  # reverse the transparent prefix
                head[c] = self.other(c, ys[i]); cover[head[c]] = c
            head[w] = x; cover[x] = w
            w = newb
            claim(sum(self.status(e, head[e]) == 'bad' for e in head) == bad - 1, "switch: potential did not drop")
            claim(set(cover) == set(self.V) - self.pins and all(head[cover[v]] == v for v in cover), "switch: cover")
            switches += 1
        J = [e for e in head if self.walk(head[e], cover, head)[0] and self.status(e, head[e]) != 'bad']
        return w, head, J, switches


_CACHE = {}


def cached(key, fn):
    if key not in _CACHE: _CACHE[key] = fn()
    return _CACHE[key]


def construct(n, m, sets, rank, info=None):
    """Allocation for ranking profile rank (rank[i] = (a, b, c)); results that depend only on the core (and on the
    agents' top goods) are cached."""
    core = tuple(map(tuple, sets))
    deg, priv, shared = cached((core, 'classify'), lambda: classify(n, m, sets))
    P = [i for i in range(n) if priv[i] is not None]
    Q = [i for i in range(n) if priv[i] is None]
    claim(len(Q) <= 2, "more than two agents without a private good")
    H = cached((core, 'H'), lambda: H_graph(n, sets, priv))
    cached((core, 'connected'), lambda: claim(nx.is_connected(H), "core not connected"))
    X = [None] * m
    info = info if info is not None else {}

    def run_collector(V, E, pins, Z, w0_candidates, outside):
        ends = {e: [g for g in sets[e] if g != priv[e]] for e in E}
        C = Collector(V, E, ends, priv, rank, pins)
        def first():
            for w0 in w0_candidates:
                cover = C.initial(w0)
                if cover is not None: return w0, cover
            raise ProofError("collector: no initial orientation")
        w0, cover = cached((core, 'initial', tuple(V), tuple(E), tuple(sorted(pins))), first)
        w, head, J, sw = C.solve(w0, dict(cover))
        for e in E:
            if e == w: continue
            X[head[e]] = e
            X[priv[e]] = w if e in J else e
        X[priv[w]] = w
        for g in Z: X[g] = w
        for g, i in outside.items(): X[g] = i
        info.update(case=info.get('case'), collector=w, J=len(J), switches=sw)
        claim(None not in X, "collector: unassigned good")
        return X

    if not Q:                                                               # pi = n: Theorem 1 on K
        info['case'] = 'pi=n'
        C0 = Collector(shared, list(range(n)), {e: [g for g in sets[e] if g != priv[e]] for e in range(n)}, priv, rank, [])
        cached((core, 'all-w0'), lambda: claim(all(C0.initial(w0) is not None for w0 in range(n)),
                                               "pi=n: some K - w has no orientation"))
        return run_collector(shared, list(range(n)), [], [], [0], {})

    def tree_comp(z, g):
        Hz = H.copy(); Hz.remove_node(('a', z))
        return nx.is_tree(Hz.subgraph(nx.node_connected_component(Hz, ('g', g))))
    for z in Q:                                                             # Lemma O
        if cached((core, 'tree', z, rank[z][0]), lambda: tree_comp(z, rank[z][0])):
            info['case'] = f'lemma-O(pi=n-{len(Q)})'
            return list(cached((core, 'O', z, rank[z][0]), lambda: lemma_O(n, m, sets, z, rank[z][0])))

    def loop_part(z, Hz):
        """Components of H - z that are trees (the loop of a dumbbell at z, minus z); returns (goods, agents)."""
        trees = [c for c in nx.connected_components(Hz) if nx.is_tree(Hz.subgraph(c))]
        claim(len(trees) == 1, "not a dumbbell at z")
        c = trees[0]
        return [g for t, g in c if t == 'g'], [i for t, i in c if t == 'a']

    def path_assign(z, goods, agents):
        """The loop at z minus z is a path x ... y (goods at both ends); give every loop agent one good and return
        the good next to z left over (s), with the assignment."""
        s = next(g for g in goods if H.has_edge(('a', z), ('g', g)))
        sub = H.subgraph([('g', g) for g in goods if g != s] + [('a', i) for i in agents])
        M = nx.bipartite.maximum_matching(sub, top_nodes=[('a', i) for i in agents])
        claim(all(('a', i) in M for i in agents) and len(agents) == len(goods) - 1, "loop: no perfect assignment")
        return s, {M[('a', i)][1]: i for i in agents}

    if len(Q) == 1:                                                         # H1: dumbbell(q, o), a_q on the o side
        q = Q[0]; aq = rank[q][0]; info['case'] = 'H1'
        def h1():
            Hq = H.copy(); Hq.remove_node(('a', q))
            lg, la = loop_part(q, Hq)
            claim(len(lg) == len(la) + 1 and aq not in lg, "H1: shape")
            s, loopX = path_assign(q, lg, la)
            side = nx.node_connected_component(Hq, ('g', aq))
            V = sorted(g for t, g in side if t == 'g'); E = sorted(i for t, i in side if t == 'a')
            claim(len(E) == len(V), "H1: o side not unicyclic")
            return s, loopX, V, E
        s, loopX, V, E = cached((core, 'H1', aq), h1)
        for g, i in loopX.items(): X[g] = i; X[priv[i]] = i
        return run_collector(V, E, [aq], [s], E, {aq: q})

    u, v = Q                                                                # pi = n - 2: dumbbell(u, v)
    def dumbbell():
        Huv = H.copy(); Huv.remove_nodes_from([('a', u), ('a', v)])
        parts = {}
        for c in nx.connected_components(Huv):
            att = frozenset(z for z in (u, v) if any(H.has_edge(('a', z), x) for x in c))
            parts.setdefault(att, []).append(c)
        claim(sorted(map(len, parts.values())) == [1, 1, 1]
              and set(parts) == {frozenset([u]), frozenset([v]), frozenset([u, v])}, "pi=n-2: not a dumbbell")
        loops = {}
        for z in (u, v):
            Hz = H.copy(); Hz.remove_node(('a', z))
            loops[z] = loop_part(z, Hz)
        return parts[frozenset([u, v])][0], loops, {z: path_assign(z, *loops[z]) for z in (u, v)}
    bridge, loops, spare = cached((core, 'dumbbell'), dumbbell)
    au, av = rank[u][0], rank[v][0]
    claim(('g', au) in bridge and ('g', av) in bridge, "pi=n-2: a top is not on the bridge side")
    su, loopX = spare[u]
    for g, i in loopX.items(): X[g] = i; X[priv[i]] = i
    if au == av:                                                            # H2': the bridge is the single good g
        info['case'] = "H2'"
        claim(len(bridge) == 1, "H2': bridge longer than one good")
        lg, la = loops[v]; bv = rank[v][1]
        claim(bv in lg, "H2': b_v not on v's loop")
        def loop_v():
            sub = H.subgraph([('g', g) for g in lg if g != bv] + [('a', i) for i in la])
            M = nx.bipartite.maximum_matching(sub, top_nodes=[('a', i) for i in la])
            claim(all(('a', i) in M for i in la) and len(la) == len(lg) - 1, "H2': loop at v")
            return {M[('a', i)][1]: i for i in la}
        X[au] = u
        X[bv] = v; X[su] = v                                                # v holds b_v and the spare good s_u
        for g, i in cached((core, "H2'", bv), loop_v).items(): X[g] = i; X[priv[i]] = i
        claim(None not in X, "H2': unassigned good")
        info.update(collector=None, J=0, switches=0)
        return X
    sv, loopX = spare[v]
    for g, i in loopX.items(): X[g] = i; X[priv[i]] = i
    info['case'] = 'H2'
    V = sorted(g for t, g in bridge if t == 'g'); E = sorted(i for t, i in bridge if t == 'a')
    claim(len(E) >= 1 and len(V) == len(E) + 1, "H2: bridge shape")
    return run_collector(V, E, [au, av], [su, sv], E, {au: u, av: v})
