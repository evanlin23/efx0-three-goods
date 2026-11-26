"""The algorithm of Lianeas-Sgouritsa-Sotiriou (arXiv 2608.03171v1, Section 3: Algorithms 1-3), for additive
valuations, instrumented with the paper's invariants.  Workstream proof/k4-girth; notes in k4/girth.md.

Model (paper, Section 2): agents are vertices; good g is the hyperedge e_g = {i : v_i(g) > 0}.  The paper allows a
vertex of e to value e at 0; here an edge is exactly its set of positive valuers, which is the hypergraph of the
instance.  Girth: a cycle is (x1, e1, ..., xk, ek, x1), k >= 2, distinct vertices, distinct edges, x_t, x_t+1 in e_t.

Labels: vertex `zero` gets label 0, its neighbours labels 1..n0, the rest n0+1..n-1 (orders given by the caller);
"vertices are prioritized based on their labels, in a decreasing order" (p. 4).

    Algorithm 1 FixProp3: while some j and unallocated e have v_j(e) > v_j(X_j): j = the largest label with this
        property; X_j <- {argmax_{e in U_j} v_j(e)} (j's old bundle becomes unallocated).
    Algorithm 2: X = empty; FixProp3; while some ENVIED i has v_i(U_i(X)) > v_i(X_i): X_i <- U_i(X); FixProp3.
    Algorithm 3: while some unallocated e contains a non-envied vertex j: X_j <- X_j + e.  Then X_0 <- X_0 + U(X).

The paper leaves three choices open: which envied i in Algorithm 2 (line 3), which pair (e, j) in Algorithm 3
(line 1), and argmax ties.  `pick` = 'max' (largest label / smallest good index) or a random.Random instance.

Instrumentation (check=True): after every atomic step the partial allocation is tested for strong envy (raw EFX0:
v_i(X_i) >= v_i(X_j) - v_i(h) for all h in X_j); the first step that creates strong envy is recorded with its kind:
    'FP3'  FixProp3 line 3 (Lemma 3.1: cannot happen, no girth used)
    'A2L4' Algorithm 2 line 4 (Lemma 3.2: uses Obs 2.1, girth >= 3)
    'A3L2' Algorithm 3 line 2 (Lemma 3.5 first part: uses Obs 2.1)
    'A3L4' Algorithm 3 line 4 (Lemma 3.5 second part: uses Property (2), hence Lemma 3.4, and Obs 2.1)
and at the end of Algorithm 2 Properties (1)-(4) are evaluated (`props`), with the reason Property (2) fails.
A line-2 step that makes its receiver envied (not strongly) is recorded as `soft_break` ('A3L4:G5env').

Extensions (k4/girth.md sections 3-5; none of them is in the paper):
    complete_with_sink, clean_sinks, flex      Algorithm 3 with a sink chosen after Algorithm 2 (Lemma SINK)
    complete_safe_sink, flex2                  the same with the G5 repair (orient only without creating envy)
    find_rotation, lss_rot                     LSS-ROT: Algorithm 2 interleaved with the F5/F6 rotations (linear only)
    park_slack_state, park_any_state           parking: PARK + SLACK, or exhaustive (every leftover to a non-envied agent)
    park_dynamic                               dynamic parking (receivers non-envied at the moment of receiving)
    Run.alg2_safe, lss_dyn, lss_dyn_safe       Algorithm 2 with the G1 repair; Conjecture DYN's pipeline
"""
import itertools
import random


class Inst:
    """n agents, m goods; R[i] = set of goods i values positively; v[i][g] > 0 for g in R[i] (absent = 0)."""

    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else 1 + max((g for S in sets for g in S), default=-1)
        self.v = [dict() for _ in range(self.n)]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V):
                if x > 0:
                    self.v[i][g] = x
        self.R = [frozenset(self.v[i]) for i in range(self.n)]
        self.edge = [frozenset(i for i in range(self.n) if g in self.R[i]) for g in range(self.m)]

    @classmethod
    def from_dicts(cls, ds, m=None):
        sets = [sorted(d) for d in ds]
        return cls(sets, [[d[g] for g in s] for s, d in zip(sets, ds)], m)

    def val(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)

    def threat(self, i, B):
        """max over h in B of v_i(B - h): the largest value i may not exceed... i strongly envies B iff v_i(X_i) < it"""
        if not B:
            return 0
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in B) - min(vi.get(g, 0) for g in B)

    def neighbours(self, i):
        return sorted(set().union(*(self.edge[g] for g in self.R[i])) - {i}) if self.R[i] else []

    def deg(self, i):
        return len(self.R[i])

    def __repr__(self):
        return 'Inst(%r)' % [{g: self.v[i][g] for g in sorted(self.R[i])} for i in range(self.n)]


# ---------------------------------------------------------------- hypergraph structure

def big_edges(I):
    """distinct goods with >= 2 valuers, as (g, frozenset)"""
    return [(g, e) for g, e in enumerate(I.edge) if len(e) >= 2]


def two_cycles(I):
    """pairs {i, j} of agents sharing >= 2 goods (each such pair, with the shared goods)"""
    out = []
    for i in range(I.n):
        for j in range(i + 1, I.n):
            sh = sorted(I.R[i] & I.R[j])
            if len(sh) >= 2:
                out.append((i, j, sh))
    return out


def triangles(I):
    """triples x < y < z with distinct goods e(x,y), e(y,z), e(z,x); one witness per triple"""
    out = []
    for x, y, z in itertools.combinations(range(I.n), 3):
        exy, eyz, ezx = I.R[x] & I.R[y], I.R[y] & I.R[z], I.R[z] & I.R[x]
        hit = None
        for a in exy:
            for b in eyz:
                if b == a:
                    continue
                for c in ezx:
                    if c != a and c != b:
                        hit = (a, b, c)
                        break
                if hit: break
            if hit: break
        if hit:
            out.append((x, y, z, hit))
    return out


def girth_at_least(I, k):
    """girth >= 3: no 2-cycle; girth >= 4: also no triangle.  (k in {2, 3, 4})"""
    if k <= 2:
        return True
    if two_cycles(I):
        return False
    if k == 3:
        return True
    return not triangles(I)


# ---------------------------------------------------------------- envy

def strong_envy_pairs(I, X):
    out = []
    for i in range(I.n):
        vi = I.val(i, X[i])
        for j in range(I.n):
            if j != i and X[j] and vi < I.threat(i, X[j]):
                out.append((i, j))
    return out


def is_efx0(I, X):
    return not strong_envy_pairs(I, X)


def envied(I, X, j):
    return any(I.val(i, X[i]) < I.val(i, X[j]) for i in range(I.n) if i != j)


def enviers(I, X, j):
    return [i for i in range(I.n) if i != j and I.val(i, X[i]) < I.val(i, X[j])]


# ---------------------------------------------------------------- labels

def labels(I, zero, nb_order=None, rest_order=None):
    """lab[agent] = label: zero -> 0, its neighbours 1..n0 (in nb_order), the rest n0+1.. (in rest_order)"""
    nb = I.neighbours(zero)
    rest = [a for a in range(I.n) if a != zero and a not in nb]
    nb = list(nb_order) if nb_order is not None else nb
    rest = list(rest_order) if rest_order is not None else rest
    lab = [None] * I.n
    lab[zero] = 0
    for t, a in enumerate(nb):
        lab[a] = 1 + t
    for t, a in enumerate(rest):
        lab[a] = 1 + len(nb) + t
    assert sorted(lab) == list(range(I.n))
    return lab


def random_labels(I, zero, rng):
    nb = I.neighbours(zero)
    rest = [a for a in range(I.n) if a != zero and a not in nb]
    rng.shuffle(nb)
    rng.shuffle(rest)
    return labels(I, zero, nb, rest)


# ---------------------------------------------------------------- the algorithm

class Run:
    def __init__(self, I, lab, pick='max', check=True):
        self.I, self.lab, self.check = I, lab, check
        self.rng = pick if isinstance(pick, random.Random) else None
        self.X = [frozenset() for _ in range(I.n)]
        self.U = set(range(I.m))
        self.zero = lab.index(0)
        self.first_break = None
        self.soft_break = None
        self.events = []
        self.steps = 0
        self.props = None

    def _choose(self, items, key):
        """items: candidates; key: larger is preferred under 'max'"""
        if self.rng is not None:
            return self.rng.choice(items)
        return max(items, key=key)

    def _after(self, kind, who, detail=None):
        self.steps += 1
        if self.steps > 100000:
            raise RuntimeError('no termination')
        if self.check and self.first_break is None:
            se = strong_envy_pairs(self.I, self.X)
            if se:
                self.first_break = (kind, who, se, detail, [sorted(b) for b in self.X], sorted(self.U))

    def U_of(self, i):
        return self.U & self.I.R[i]

    def fixprop3(self):
        I = self.I
        while True:
            cand = [j for j in range(I.n) if any(I.v[j].get(e, 0) > I.val(j, self.X[j]) for e in self.U)]
            if not cand:
                return
            j = max(cand, key=lambda a: self.lab[a])          # the maximum vertex: no choice left
            best = max(I.v[j].get(e, 0) for e in self.U_of(j))
            es = [e for e in self.U_of(j) if I.v[j][e] == best]
            e = self._choose(es, key=lambda g: -g)
            self.U |= self.X[j]
            self.X[j] = frozenset([e])
            self.U.discard(e)
            self.events.append(('FP3', j, e))
            self._after('FP3', j, e)

    def alg2(self):
        I = self.I
        self.fixprop3()
        while True:
            cand = [i for i in range(I.n) if envied(I, self.X, i) and I.val(i, self.U_of(i)) > I.val(i, self.X[i])]
            if not cand:
                break
            i = self._choose(cand, key=lambda a: self.lab[a])
            new = frozenset(self.U_of(i))
            self.U |= self.X[i]
            self.X[i] = new
            self.U -= new
            self.events.append(('A2L4', i, tuple(sorted(new))))
            self._after('A2L4', i, tuple(sorted(new)))
            self.fixprop3()
        self.props = self.properties()

    def alg3(self):
        I = self.I
        while True:
            pairs = [(e, j) for e in sorted(self.U) for j in sorted(I.edge[e]) if not envied(I, self.X, j)]
            if not pairs:
                break
            e, j = self._choose(pairs, key=lambda p: (-p[0], self.lab[p[1]]))
            self.X[j] = self.X[j] | {e}
            self.U.discard(e)
            self.events.append(('A3L2', j, e))
            self._after('A3L2', j, e)
            if self.soft_break is None and envied(I, self.X, j):
                self.soft_break = ('A3L2env', j, e)       # Lemma 3.5 says j stays non-envied (uses Obs. 2.1)
        z = self.zero
        rest = frozenset(self.U)
        self.X[z] = self.X[z] | rest
        self.U = set()
        self.events.append(('A3L4', z, tuple(sorted(rest))))
        self._after('A3L4', z, tuple(sorted(rest)))

    def properties(self):
        """Properties (1)-(4) at the end of Algorithm 2, with the reason (2) fails (see k4/girth.md, uses G2-G4)"""
        I, X, z = self.I, self.X, self.zero
        p = {}
        p[1] = is_efx0(I, X) and all(X[i] <= I.R[i] for i in range(I.n))
        bad2 = []
        if envied(I, X, z):
            bad2.append(('zero-envied', z))
        for i in I.neighbours(z):
            if not envied(I, X, i):
                continue
            shared = I.R[i] & I.R[z]
            if X[i] & shared:
                continue                                   # holds (one of) the edge(s) it shares with 0
            why = []
            if len(X[i]) > 1:
                why.append('G2')                           # several edges, envied without strong envy (2-cycle)
            else:
                (e,) = tuple(X[i])
                for j in enviers(I, X, i):
                    if j in I.neighbours(z) and j != z:
                        if shared & I.R[j]:
                            why.append('G3')               # j in an edge shared by 0 and i
                        else:
                            why.append('G4')               # j a neighbour of 0 outside it: triangle 0-i-j
                    elif self.lab[j] > self.lab[i]:
                        why.append('PRIO')                 # higher label envies: priority argument broken
                    else:
                        why.append('OTHER')
            bad2.append(('nb-envied', i, tuple(sorted(set(why)))))
        p[2] = not bad2
        p['2why'] = bad2
        p[3] = all(I.val(i, X[i]) >= I.v[i].get(e, 0) for i in range(I.n) for e in self.U)
        p[4] = all(I.val(i, X[i]) >= I.val(i, self.U_of(i)) for i in range(I.n) if envied(I, X, i))
        return p

    def run(self):
        self.alg2()
        self.alg3()
        assert not self.U and sorted(g for b in self.X for g in b) == list(range(self.I.m))
        return self


def lss(I, zero=0, lab=None, pick='max', check=True):
    if lab is None:
        lab = labels(I, zero)
    return Run(I, lab, pick, check).run()


def classify(r):
    """reason for a run's failure (None if EFX0).  For a break at Algorithm 3 line 4 the strong envier i of X_0 is an
    envied neighbour of 0 (see k4/girth.md, section 2); then
        'A3L4:G6'          i holds a good it shares with 0, and X_0 holds another one (a 2-cycle 0-i): use G6
        'A3L4:P2(...)'     i holds no good it shares with 0, so Property (2) failed for i; the reasons G2/G3/G4 say
                           which girth use of Lemma 3.4 broke (PRIO/OTHER: none of them)
        'A3L4:G5env'       an earlier line-2 step made its receiver envied (not strongly: a 2-cycle), which Lemma 3.5
                           excludes with Obs. 2.1; that receiver's later leftovers then reached X_0"""
    if is_efx0(r.I, r.X):
        return None                     # (r.first_break may be set: a transient break, repaired later)
    fb = r.first_break
    kind = fb[0]
    if kind != 'A3L4':
        return kind
    I, z = r.I, r.zero
    if r.soft_break is not None:
        return 'A3L4:G5env'          # line 2 made a receiver envied (2-cycle), so its later leftovers went to X_0
    out = set()
    for (i, j) in fb[2]:
        if j != z:
            out.add('A3L4:notzero')
            continue
        if i not in I.neighbours(z):
            out.add('A3L4:nonnb')
            continue
        hold = r.X[i] & I.R[z]
        if hold:
            out.add('A3L4:G6')
            continue
        why = [t for t in r.props['2why'] if t[0] == 'nb-envied' and t[1] == i]
        out.add('A3L4:P2(' + ','.join(why[0][2]) + ')' if why else 'A3L4:P2(?)')
    return '|'.join(sorted(out))


# ---------------------------------------------------------------- random girth >= 4 hypergraphs (sanity)

def random_girth4(n, tries, rng, maxsize=4, pzero=0.0, vmax=20):
    """random hypergraph of girth >= 4 on n vertices (any degree) with random additive values; size-1 and size-0
    edges allowed (several at one vertex too: they are on no cycle, see k4/girth.md)"""
    edges = []
    adj = {}                                   # (x, y) -> edge index, x < y (linear: unique)
    for _ in range(tries):
        s = rng.choice(range(0, maxsize + 1))
        e = sorted(rng.sample(range(n), min(s, n)))
        ok = True
        for x, y in itertools.combinations(e, 2):
            if (x, y) in adj:
                ok = False
                break
        if ok and len(e) >= 2:
            # triangle check: for x in e, y in e, z outside with z~x and z~y through distinct edges
            nb = {x: {w for (a, b) in adj for w in (a, b) if x in (a, b) and w != x} for x in e}
            for x, y in itertools.combinations(e, 2):
                if (nb[x] & nb[y]) - set(e):
                    ok = False
                    break
        if not ok:
            continue
        k = len(edges)
        edges.append(e)
        for x, y in itertools.combinations(e, 2):
            adj[(x, y)] = k
    sets = [[] for _ in range(n)]
    vals = [[] for _ in range(n)]
    for g, e in enumerate(edges):
        for x in e:
            sets[x].append(g)
            vals[x].append(0 if rng.random() < pzero else rng.randint(1, vmax))
    return Inst(sets, vals, len(edges))


if __name__ == '__main__':
    import sys
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    bad = 0
    for t in range(2000):
        n = rng.randint(2, 9)
        I = random_girth4(n, rng.randint(3, 25), rng, maxsize=rng.choice([2, 3, 4, 5]), pzero=rng.choice([0, 0.2]))
        assert girth_at_least(I, 4)
        for z in range(I.n):
            for rep in range(3):
                lab = random_labels(I, z, rng) if rep else labels(I, z)
                r = lss(I, lab=lab, pick=rng if rep == 2 else 'max')
                assert r.first_break is None and r.soft_break is None and r.props[2] and r.props[4]
                if not is_efx0(I, r.X):
                    bad += 1
                    print('FAIL', I, lab, classify(r), r.first_break)
    print('girth>=4 sanity: failures', bad)


# ---------------------------------------------------------------- flexible sink (k4/girth.md, section 3)

def complete_with_sink(I, X, U, s, pick='max'):
    """Algorithm 3 with sink s instead of vertex 0: orient every unallocated edge containing a non-envied vertex
    other than s to such a vertex; then give what is left to s.  Returns the complete allocation (list)."""
    X = list(X)
    U = set(U)
    rng = pick if isinstance(pick, random.Random) else None
    while True:
        pairs = [(e, j) for e in sorted(U) for j in sorted(I.edge[e]) if j != s and not envied(I, X, j)]
        if not pairs:
            break
        e, j = rng.choice(pairs) if rng else pairs[0]
        X[j] = X[j] | {e}
        U.discard(e)
    X[s] = X[s] | frozenset(U)
    return X


def clean_sinks(I, X):
    """non-envied s whose bundle no envied agent values (the CS condition of k4/girth.md, section 3)"""
    env = [i for i in range(I.n) if envied(I, X, i)]
    return [s for s in range(I.n) if s not in env and not any(X[s] & I.R[i] for i in env)]


def flex(I, lab, pick='max'):
    """Algorithm 2 with labels lab, then the flexible-sink completion with every non-envied s; returns
    (Run after Algorithm 2, list of sinks that give an EFX0 allocation, clean sinks)"""
    r = Run(I, lab, pick)
    r.alg2()
    good = []
    for s in range(I.n):
        if envied(I, r.X, s):
            continue
        Y = complete_with_sink(I, r.X, r.U, s)
        if is_efx0(I, Y):
            good.append(s)
    return r, good, clean_sinks(I, r.X)


def complete_safe_sink(I, X, U, s):
    """Completion with the G5 repair: orient an unallocated good e to a non-envied valuer j != s only if no agent
    then envies X_j + e; everything left goes to the sink s.  (For 2-cycles: k4/girth.md, section 5.)"""
    X = list(X)
    U = set(U)
    changed = True
    while changed:
        changed = False
        for e in sorted(U):
            for j in sorted(I.edge[e]):
                if j == s or envied(I, X, j):
                    continue
                B = X[j] | {e}
                if all(I.val(k, X[k]) >= I.val(k, B) for k in range(I.n) if k != j):
                    X[j] = B
                    U.discard(e)
                    changed = True
                    break
            if changed:
                break
    X[s] = X[s] | frozenset(U)
    return X


def flex2(I, lab, pick='max'):
    """Algorithm 2, then complete_safe_sink with every non-envied s; returns (Run, sinks that work)"""
    r = Run(I, lab, pick)
    r.alg2()
    good = [s for s in range(I.n) if not envied(I, r.X, s) and is_efx0(I, complete_safe_sink(I, r.X, r.U, s))]
    return r, good


# ---------------------------------------------------------------- LSS + rotations + parking (k4/girth.md, section 4)

def _envy_paths_to(I, X, i):
    """for an envied agent i: dict source -> path [r = r_q, ..., r_0 = i] along envy arcs (BFS, shortest)"""
    prev = {i: None}
    order = [i]
    out = {}
    while order:
        a = order.pop(0)
        for k in enviers(I, X, a):
            if k not in prev:
                prev[k] = a
                order.append(k)
                if not envied(I, X, k):
                    path = [k]
                    while path[-1] != i:
                        path.append(prev[path[-1]])
                    out[k] = path
    return out


def find_rotation(I, X, U):
    """an F5 (envy cycle) or F6 rotation (k4/girth.md, section 4) that is a Pareto improvement, as new bundles X'
    (list) and new unallocated set; None if there is none.  Linear hypergraphs."""
    # F6: source r with an envy path to envied i, r dangerous for i
    for i in range(I.n):
        if not envied(I, X, i):
            continue
        Ui = U & I.R[i]
        for r, path in sorted(_envy_paths_to(I, X, i).items()):
            if I.val(i, X[r] | Ui) > I.val(i, X[i]):
                hs = [h for h in X[r] if h in I.R[i]]
                Y = list(X)
                newU = set(U)
                for t in range(len(path) - 1):          # path[t] envies path[t+1]
                    Y[path[t]] = X[path[t + 1]]
                newU |= X[r] - set(hs)
                Y[i] = frozenset(hs) | frozenset(Ui)
                newU -= Ui
                return Y, newU, ('F6', r, i, tuple(path))
    # F5: an envy cycle (DFS over the envy graph)
    succ = [[k for k in range(I.n) if k != a and I.val(a, X[a]) < I.val(a, X[k])] for a in range(I.n)]
    color = [0] * I.n
    stack = []

    def dfs(a):
        color[a] = 1
        stack.append(a)
        for k in succ[a]:
            if color[k] == 1:
                return stack[stack.index(k):]
            if color[k] == 0:
                c = dfs(k)
                if c:
                    return c
        color[a] = 2
        stack.pop()
        return None

    for a in range(I.n):
        if color[a] == 0:
            cyc = dfs(a)
            if cyc:
                Y = list(X)
                for t, b in enumerate(cyc):
                    Y[b] = X[cyc[(t + 1) % len(cyc)]]
                return Y, set(U), ('F5', tuple(cyc))
    return None


def lss_rot(I, lab, pick='max', cap=10000):
    """LSS's Algorithm 2, then repeatedly: an F5/F6 rotation followed by FixProp3 and Algorithm 2's loop, until none
    applies.  Values never decrease (each step is a Pareto improvement), so it stops.  Returns the Run."""
    r = Run(I, lab, pick)
    r.alg2()
    for _ in range(cap):
        rot = find_rotation(I, r.X, r.U)
        if rot is None:
            break
        r.X, r.U, ev = rot[0], rot[1], rot[2]
        r.events.append(ev)
        r._after(ev[0], None, ev)
        r.alg2_resume()
    return r


def _alg2_resume(self):
    """FixProp3, then Algorithm 2's loop, from the current state"""
    I = self.I
    self.fixprop3()
    while True:
        cand = [i for i in range(I.n) if envied(I, self.X, i) and I.val(i, self.U_of(i)) > I.val(i, self.X[i])]
        if not cand:
            break
        i = self._choose(cand, key=lambda a: self.lab[a])
        new = frozenset(self.U_of(i))
        self.U |= self.X[i]
        self.X[i] = new
        self.U -= new
        self.events.append(('A2L4', i, tuple(sorted(new))))
        self._after('A2L4', i, tuple(sorted(new)))
        self.fixprop3()


Run.alg2_resume = _alg2_resume


def park_slack_state(I, X, U):
    """PARK + SLACK completion of a state (bundles X, unallocated U); exhaustive over the choices for the goods
    whose valuers are all envied; goods with a non-envied valuer are oriented to one first.  None if impossible."""
    X = [frozenset(b) for b in X]
    env = [i for i in range(I.n) if envied(I, X, i)]
    N = [u for u in range(I.n) if u not in env]
    S = {i: {u for u in N if I.val(i, X[u] | (U & I.R[i])) <= I.val(i, X[i])} for i in env}
    Y = [set(b) for b in X]
    L = []
    for e in sorted(U):
        nb = [j for j in sorted(I.edge[e]) if j not in env]
        if nb:
            Y[nb[0]].add(e)
        elif I.edge[e]:
            L.append(e)
        elif N:
            Y[N[0]].add(e)
    opts = []
    for e in L:
        common = set(N)
        for i in I.edge[e]:
            common &= S[i]
        opts.append([('park', u) for u in sorted(common)] + [('slack', u) for u in N if len(Y[u]) == 1])
    for choice in itertools.product(*opts):
        slack = [u for k, u in choice if k == 'slack']
        if len(set(slack)) < len(slack) or set(slack) & {u for k, u in choice if k == 'park'}:
            continue
        Z = [set(b) for b in Y]
        for e, (k, u) in zip(L, choice):
            Z[u].add(e)
        if is_efx0(I, Z):
            return Z
    return None


def park_any_state(I, X, U, limit=None):
    """Completion by parking: every unallocated good goes to some non-envied agent (of the state X); exhaustive
    backtracking with raw EFX0 checks.  Pruning is sound: the threat v_k(B) - min_{g in B} v_k(g) of a bundle only grows
    when goods are added, and receivers only gain.  Returns the completed allocation or None."""
    X = [frozenset(b) for b in X]
    env = {i for i in range(I.n) if envied(I, X, i)}
    N = [u for u in range(I.n) if u not in env]
    if not N:
        return None
    goods = sorted(U, key=lambda g: -len(I.edge[g]))
    Y = [set(b) for b in X]

    def safe(u):
        B = Y[u]
        return all(I.val(k, Y[k]) >= I.threat(k, B) for k in range(I.n) if k != u)

    def rec(t):
        if t == len(goods):
            return is_efx0(I, Y)
        g = goods[t]
        for u in N:
            Y[u].add(g)
            if safe(u) and rec(t + 1):
                return True
            Y[u].discard(g)
        return False

    return [set(b) for b in Y] if rec(0) else None

def park_dynamic(I, X, U, budget=200000):
    """Dynamic parking: repeatedly give some unallocated good to an agent that is non-envied in the CURRENT partial
    allocation, keeping it EFX0 (raw check), until nothing is left; depth-first search over the choices with a node
    budget.  Lemma SLACK's absorptions are such steps in any hypergraph.  Returns the allocation or None."""
    Y = [set(b) for b in X]
    left = set(U)
    count = [0]
    seen = set()

    def rec():
        if not left:
            return True
        key = tuple(frozenset(b) for b in Y)
        if key in seen:
            return False
        seen.add(key)
        count[0] += 1
        if count[0] > budget:
            return False
        for g in sorted(left, key=lambda h: -len(I.edge[h])):
            for u in range(I.n):
                if envied(I, Y, u):
                    continue
                Y[u].add(g)
                left.discard(g)
                if is_efx0(I, Y) and rec():
                    return True
                Y[u].discard(g)
                left.add(g)
        return False

    return [set(b) for b in Y] if rec() else None


def lss_dyn(I, lab, pick='max', rotations=False):
    """LSS's Algorithm 2 (with the F5/F6 rotations if rotations=True; linear instances only), then dynamic parking"""
    r = lss_rot(I, lab, pick) if rotations else Run(I, lab, pick)
    if not rotations:
        r.alg2()
    return r, park_dynamic(I, r.X, r.U)


def _alg2_safe(self):
    """Algorithm 2 with the G1 repair (k4/girth.md section 5): line 4 gives the envied agent i the most valuable subset
    T of U_i with v_i(T) > v_i(X_i) that keeps EFX0 (raw check); agents with no such T are skipped until something
    changes.  Everything else as in Algorithm 2."""
    I = self.I
    self.fixprop3()
    stuck = set()
    while True:
        cand = [i for i in range(I.n) if i not in stuck and envied(I, self.X, i)
                and I.val(i, self.U_of(i)) > I.val(i, self.X[i])]
        if not cand:
            break
        i = self._choose(cand, key=lambda a: self.lab[a])
        Ui = sorted(self.U_of(i))
        best = None
        for k in range(len(Ui), 0, -1):
            for T in itertools.combinations(Ui, k):
                T = frozenset(T)
                if I.val(i, T) <= I.val(i, self.X[i]):
                    continue
                Y = list(self.X)
                Y[i] = T
                if is_efx0(I, Y) and (best is None or I.val(i, T) > I.val(i, best)):
                    best = T
        if best is None:
            stuck.add(i)
            continue
        self.U |= self.X[i]
        self.X[i] = best
        self.U -= best
        self.events.append(('A2L4s', i, tuple(sorted(best))))
        self._after('A2L4s', i, tuple(sorted(best)))
        self.fixprop3()
        stuck = set()


Run.alg2_safe = _alg2_safe


def lss_dyn_safe(I, lab, pick='max'):
    """Algorithm 2 with the G1 repair, then dynamic parking"""
    r = Run(I, lab, pick)
    r.alg2_safe()
    return r, (park_dynamic(I, r.X, r.U) if is_efx0(I, r.X) else None)
