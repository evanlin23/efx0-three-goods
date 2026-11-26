"""Library for the (k, p) = (4, 3) workstream (proof/k4-p3, k4/p3.md): instances in which every agent values at most four
goods and every good is valued by at most three agents. Written independently of k4/sdc/sdclib.py.

  Inst(sets, vals, m)            additive instance; v[i] maps good -> value (> 0 exactly on R_i = sets[i])
  efx0(I, X)                     raw EFX0 check of a (partial) allocation X (list of bundles); goods not in any bundle
                                 are ignored, so a partial allocation is checked as one
  strongly_envies(I, i, Xi, B)   does i, holding Xi, strongly envy bundle B?
  sd(I, order)                   serial dictatorship: each agent in turn takes its favourite remaining good
  Complete(I)                    SAT model of EFX0 (partial or complete) allocations, with queries that fix goods, forbid
                                 owners, or require goods to stay unallocated
  instance sets: suite_p3(), screen_p3(), cores_p3(files), random_core43(rng, n), ht3 (k4/p3/ht3.py)
"""
import itertools, gzip, json, os, random, sys
from pysat.solvers import Cadical153

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


class Inst:
    def __init__(self, sets, vals, m=None, name=''):
        self.sets = [list(S) for S in sets]
        self.n = len(sets)
        self.m = m if m is not None else 1 + max(max(S) for S in sets)
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.R = [set(S) for S in sets]
        self.V = [[i for i in range(self.n) if g in self.R[i]] for g in range(self.m)]
        self.name = name

    def val(self, i, B):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in B)

    def p(self):
        return max(len(x) for x in self.V)

    def k(self):
        return max(len(S) for S in self.sets)

    def rank(self, i):
        return sorted(self.sets[i], key=lambda g: (-self.v[i][g], g))

    def as_json(self):
        return {'name': self.name, 'm': self.m, 'sets': self.sets,
                'vals': [[self.v[i][g] for g in S] for i, S in enumerate(self.sets)]}


def strongly_envies(I, i, Xi, B):
    if not B:
        return False
    own = I.val(i, Xi)
    vals = [I.v[i].get(g, 0) for g in B]
    return sum(vals) - min(vals) > own


def efx0(I, X):
    for i in range(I.n):
        for j in range(I.n):
            if i != j and strongly_envies(I, i, X[i], X[j]):
                return False
    return True


def bundles(I, owner):
    """owner[g] in range(n) or None/n (unallocated) -> list of bundles"""
    X = [[] for _ in range(I.n)]
    for g, a in enumerate(owner):
        if a is not None and 0 <= a < I.n:
            X[a].append(g)
    return X


def sd(I, order):
    left = set(range(I.m)); pick = [None] * I.n
    for i in order:
        av = [g for g in I.sets[i] if g in left]
        if av:
            g = max(av, key=lambda h: (I.v[i][h], -h)); pick[i] = g; left.discard(g)
    return pick


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


class Complete:
    """SAT model: x[g][a] (a = n: unallocated). EFX0 among all agents (unallocated goods ignored)."""

    def __init__(self, I):
        self.I = I; n, m = I.n, I.m
        self.top = 0
        self.x = [[self.new() for a in range(n + 1)] for g in range(m)]
        self.cl = []
        for g in range(m):
            self.cl.append([self.x[g][a] for a in range(n + 1)])
            for a in range(n + 1):
                for b in range(a + 1, n + 1):
                    self.cl.append([-self.x[g][a], -self.x[g][b]])
        # hold[i][S]: i holds exactly S of R_i
        self.hold = []
        for i in range(n):
            Ri = I.sets[i]; d = {}
            for S in subsets(Ri):
                y = self.new(); d[S] = y
                for g in Ri:
                    self.cl.append([-y, self.x[g][i] if g in S else -self.x[g][i]])
                self.cl.append([y] + [-self.x[g][i] for g in S] + [self.x[g][i] for g in Ri if g not in S])
            self.hold.append(d)
        # other[j][T]: j holds a good outside T (T a subset of some R_i)
        self.other = {}
        for i in range(n):
            vi = I.v[i]; Ri = I.sets[i]
            for S, y in self.hold[i].items():
                vs = sum(vi[g] for g in S)
                rest = [g for g in Ri if g not in S]
                mins = []
                for T in subsets(rest):
                    if not T or sum(vi[g] for g in T) <= vs: continue
                    if any(set(U) <= set(T) for U in mins): continue
                    mins.append(T)
                for T in mins:
                    for j in range(n):
                        if j == i: continue
                        z = self.other_var(j, T)
                        self.cl.append([-y, -z] + [-self.x[g][j] for g in T])

    def new(self):
        self.top += 1; return self.top

    def other_var(self, j, T):
        key = (j, T)
        if key not in self.other:
            z = self.new(); self.other[key] = z
            outs = [self.x[h][j] for h in range(self.I.m) if h not in T]
            self.cl.append([-z] + outs)
            for o in outs:
                self.cl.append([z, -o])
        return self.other[key]

    def big_bound(self, t, size=3):
        """clauses: at most t agents hold >= size goods"""
        from pysat.card import CardEnc, EncType
        n, m = self.I.n, self.I.m
        big = []
        cl = []
        for a in range(n):
            b = self.new(); big.append(b)
            # sequential counter: s[c] = "at least c+1 of the goods seen so far go to a" (only the forcing direction)
            prev = [None] * size
            for g in range(m):
                xg = self.x[g][a]; cur = [self.new() for _ in range(size)]
                cl.append([-xg, cur[0]])
                if prev[0] is not None: cl.append([-prev[0], cur[0]])
                for c in range(1, size):
                    if prev[c - 1] is not None: cl.append([-xg, -prev[c - 1], cur[c]])
                    if prev[c] is not None: cl.append([-prev[c], cur[c]])
                prev = cur
            cl.append([-prev[size - 1], b])
        enc = CardEnc.atmost(lits=big, bound=t, top_id=self.top, encoding=EncType.seqcounter)
        self.top = max(self.top, enc.nv)
        return cl + enc.clauses

    def solve(self, fixed=None, forbid=None, allowed=None, complete=True, extra=()):
        """fixed: {g: a}; forbid: iterable of (g, a); allowed: {g: set of agents} (a = n means unallocated);
        complete: no good unallocated. Returns owner list or None."""
        n = self.I.n; assum = []
        for g, a in (fixed or {}).items():
            assum.append(self.x[g][a])
        for g, a in (forbid or ()):
            assum.append(-self.x[g][a])
        for g, A in (allowed or {}).items():
            for a in range(n + 1):
                if a not in A: assum.append(-self.x[g][a])
        if complete:
            for g in range(self.I.m): assum.append(-self.x[g][n])
        with Cadical153(bootstrap_with=self.cl + [list(c) for c in extra]) as s:
            if not s.solve(assumptions=assum):
                return None
            mod = set(l for l in s.get_model() if l > 0)
        own = []
        for g in range(self.I.m):
            a = next(a for a in range(n + 1) if self.x[g][a] in mod)
            own.append(a if a < n else None)
        return own


# ---------------------------------------------------------------- instance sets
def _suite():
    out = []
    import glob
    for f in sorted(glob.glob(os.path.join(ROOT, 'k4/suite/instances/*.json'))):
        d = json.load(open(f))
        if d.get('vals') and d.get('sets'):
            m = d.get('m') or 1 + max(max(s) for s in d['sets'])
            out.append(Inst(d['sets'], d['vals'], m, d.get('id', os.path.basename(f))))
    return out


def suite_p3():
    return [I for I in _suite() if I.p() <= 3]


def screen_p3():
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'de4'))
    cwd = os.getcwd(); os.chdir(os.path.join(ROOT, 'k4', 'de4'))
    try:
        from ss_screen import screen_set
        L = [Inst(J.sets, [[J.v[i][g] for g in J.sets[i]] for i in range(J.n)], J.m, name) for name, J in screen_set()]
    finally:
        os.chdir(cwd)
    return [I for I in L if I.p() <= 3]


def core_lists_p3():
    import glob
    return sorted(glob.glob(os.path.join(ROOT, 'results/k4_p3/*_p3.json.gz')))


def cores_from(file):
    d = json.load(gzip.open(file, 'rt'))
    return [(r['m'], r['sets']) for r in d['cores']]


def random_types(rng, sets, m):
    sys.path.insert(0, os.path.join(ROOT, 'k4'))
    import check4
    doms = check4.core_domains(sets, m, False)
    return [[D[rng.randrange(len(D))][g] for g in S] for D, S in zip(doms, sets)]


def random_core43(rng, n, p4=0.5, maxpriv=2):
    sys.path.insert(0, os.path.join(ROOT, 'k4'))
    import p3_run
    p3_run.MAXPRIV = maxpriv
    return p3_run.random_core43(rng, n, p4)


def phase1(I, tau=None):
    """LB4's Phase 1 (k4/lb4.md section 2): serial dictatorship; a P-step takes the unprocessed agent that has lost a
    good with the smallest key (rank of its favourite remaining good, or d_i if none; number of remaining goods;
    index); otherwise an insertion step takes the tau[j]-th unprocessed agent (index order: tau = None, always 0).
    Returns (picks, processing order)."""
    G = set(range(I.m)); pick = [None] * I.n; done = []; rest = list(range(I.n)); j = 0
    ranks = [I.rank(i) for i in range(I.n)]
    while rest:
        lost = [i for i in rest if not I.R[i] <= G]
        if lost:
            def key(i):
                av = [r for r, g in enumerate(ranks[i]) if g in G]
                return (av[0] if av else len(ranks[i]), len(av), i)
            i = min(lost, key=key)
        else:
            i = rest[(tau[j] if tau else 0) % len(rest)]; j += 1
        av = [g for g in ranks[i] if g in G]
        if av: pick[i] = av[0]; G.discard(av[0])
        rest.remove(i); done.append(i)
    return pick, done
