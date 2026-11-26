"""Viswanathan-Mehta's 4-limited EFX algorithm (AAMAS 2024 extended abstract, p. 2535), as reconstructed in k4/vm.md,
with every choice point exposed and every reading of the sketch selectable.  Written from the abstract's text only.

Instance: sets[i] (the goods agent i values positively), vals[i] (their values, same order), m (number of goods).
Goods outside every R_i are junk.

Readings (k4/vm.md section 2):
  rank   'G'  k-th ranked = k-th in i's ranking of all of R_i (the edge exists only if that good is still available)
         'R'  k-th ranked among the goods of R_i that are still available when the graph is built
  aout   'matched'  Phase I removes only the matched A-agents from N^r (unmatched ones go on to Phase II)
         'all'      Phase I removes all of A from N^r (the literal text)
  n1a    True   N_1 (EFX-graph node set) includes the Phase I agents (they hold their 1st-ranked good)
         False  only agents matched in M_1 of Phase II
  junk   'any'  the leftover goods (valued by nobody) go to one arbitrary agent (a choice point)
         'L3'   envy cycles are rotated away, then all junk goes to a source of the envy graph (L3)
  egraph 'efx'  the EFX graph of the text (ordinary EFX-envy toward X_i' + j, nodes: j-valuers in N_1 u N_2^r)

Choice points (resolved by a Chooser): who gets each contested good in each matching; which unassigned valued good
the EFX-graph step takes next; which source receives it; the junk recipient.
"""
import itertools, random

# ------------------------------------------------------------------ instances and the raw definitions
class Inst:
    def __init__(self, sets, vals, m=None):
        self.n = len(sets)
        self.m = m if m is not None else (1 + max((g for S in sets for g in S), default=-1))
        self.sets = [list(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        for i in range(self.n):
            assert all(x > 0 for x in self.v[i].values())
        # ranking: by value, ties by good index
        self.rank = [sorted(self.sets[i], key=lambda g: (-self.v[i][g], g)) for i in range(self.n)]

    def val(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)

    def valued_by(self, g):
        return [i for i in range(self.n) if g in self.v[i]]

    def to_json(self):
        return {'sets': self.sets, 'vals': [[self.v[i][g] for g in self.sets[i]] for i in range(self.n)], 'm': self.m}


def efx_violations(I, X, zero=True):
    """List (i, j, g): agent i, bundle X_j, removed good g with v_i(X_j - g) > v_i(X_i).
    zero=True: EFX0 (any g); zero=False: ordinary EFX (only g with v_i(g) > 0)."""
    out = []
    for i in range(I.n):
        own = I.val(i, X[i])
        for j in range(I.n):
            if j == i:
                continue
            tot = I.val(i, X[j])
            for g in X[j]:
                vg = I.v[i].get(g, 0)
                if not zero and vg == 0:
                    continue
                if tot - vg > own:
                    out.append((i, j, g))
    return out


def is_efx(I, X):
    return not efx_violations(I, X, zero=False)


def is_efx0(I, X):
    return not efx_violations(I, X, zero=True)


def efx_envies(I, X, i, B):
    """ordinary EFX-envy of agent i toward bundle B (the text's definition)"""
    own = I.val(i, X[i]); tot = I.val(i, B)
    return any(tot - I.v[i][g] > own for g in B if g in I.v[i])


def efx0_envies(I, X, i, B):
    if len(B) < 2:
        return False
    own = I.val(i, X[i]); tot = I.val(i, B)
    return tot - min(I.v[i].get(g, 0) for g in B) > own


# ------------------------------------------------------------------ choosers
class Stuck(Exception):
    pass


class Chooser:
    """Resolves choice points from a script (list of indices; past its end: 0, or random if rng is given);
    records the choices made and the branching at each choice point (DFS enumeration)."""
    def __init__(self, script=(), rng=None):
        self.script = list(script); self.made = []; self.branch = []; self.rng = rng

    def pick(self, kind, options):
        if not options:
            raise Stuck(kind)
        if len(options) == 1:
            return options[0]
        p = len(self.made)
        if p < len(self.script):
            k = self.script[p]
        elif self.rng is not None:
            k = self.rng.randrange(len(options))
        else:
            k = 0
        self.made.append(k); self.branch.append(len(options))
        return options[k]


def all_runs(run, I, limit=None, **kw):
    """DFS over every resolution of the choice points; yields (choices, result) where result is run's value or the
    Stuck exception raised."""
    script = []; count = 0
    while True:
        ch = Chooser(script)
        try:
            res = run(I, ch, **kw)
        except Stuck as e:
            res = e
        yield list(ch.made), res
        count += 1
        if limit is not None and count >= limit:
            return
        full, br = ch.made, ch.branch
        k = len(full) - 1
        while k >= 0 and full[k] + 1 >= br[k]:
            k -= 1
        if k < 0:
            return
        script = full[:k] + [full[k] + 1]


# ------------------------------------------------------------------ the algorithm
def matching_step(I, ch, agents, avail, k, rank, tag, X, owner, log):
    """maximum matching in G_k(agents, avail): every agent has at most one edge (its k-th ranked good), so a maximum
    matching gives each claimed good to one of its claimants.  Returns the set of matched agents."""
    claim = {}
    for i in sorted(agents):
        if rank == 'G':
            r = I.rank[i]
            g = r[k - 1] if len(r) >= k else None
            if g is not None and g not in avail:
                g = None
        else:
            r = [g for g in I.rank[i] if g in avail]
            g = r[k - 1] if len(r) >= k else None
        if g is not None:
            claim.setdefault(g, []).append(i)
    matched = set()
    for g in sorted(claim):
        i = ch.pick((tag, g), claim[g])
        X[i].append(g); owner[g] = i; avail.discard(g); matched.add(i)
        log.append((tag, i, g))
    return matched


def vm_run(I, ch, rank='G', aout='matched', n1a=True, junk='L3', record=False, stop=None):
    """stop='II': return (X, flags) after Phase II; stop='IIIm': after Phase III's matchings (before the EFX graph)"""
    n, m = I.n, I.m
    X = [[] for _ in range(n)]; owner = {}; avail = set(range(m)); log = []
    flags = {}
    # Phase I
    def strong(i):
        r = I.rank[i]
        if not r:
            return False
        a = I.v[i][r[0]]; b = I.v[i][r[1]] if len(r) > 1 else 0; c = I.v[i][r[2]] if len(r) > 2 else 0
        return a > b + c
    A = set(i for i in range(n) if strong(i))
    MA = matching_step(I, ch, A, avail, 1, 'G', 'I', X, owner, log)
    Nr = set(range(n)) - (A if aout == 'all' else MA)
    # Phase II
    Nk = {}
    for k in (1, 2, 3, 4):
        Mk = matching_step(I, ch, Nr, avail, k, rank, 'II.%d' % k, X, owner, log)
        Nk[k] = Mk; Nr -= Mk
    flags['A'] = sorted(A); flags['MA'] = sorted(MA); flags['Nr'] = sorted(Nr)
    flags['N'] = {k: sorted(v) for k, v in Nk.items()}
    if stop == 'II':
        return X, flags
    # Phase III: N_3 get a 4th choice; N_2 a 3rd, then the rest of N_2 a 4th
    matching_step(I, ch, Nk[3], avail, 4, 'G' if rank == 'G' else rank, 'III.3-4', X, owner, log)
    N2r = matching_step(I, ch, Nk[2], avail, 3, rank, 'III.2-3', X, owner, log)
    matching_step(I, ch, Nk[2] - N2r, avail, 4, rank, 'III.2-4', X, owner, log)
    flags['N2r'] = sorted(N2r)
    if stop == 'IIIm':
        return X, flags
    S = set(Nk[1]) | set(N2r) | (set(MA) if n1a else set())
    # claim check: only agents in S value unassigned goods
    outside = sorted(set(i for g in avail for i in I.valued_by(g)) - S)
    if outside:
        flags['claim_outside'] = outside
    # EFX-graph step
    pre_efx_ok = True
    while True:
        valued = sorted(g for g in avail if I.valued_by(g))
        if not valued:
            break
        g = ch.pick('egood', valued)
        nodes = [i for i in sorted(S) if g in I.v[i]]
        if not nodes:
            flags['no_nodes'] = flags.get('no_nodes', 0) + 1
            raise Stuck(('no_nodes', g, X))
        hasin = set()
        for i in nodes:
            for i2 in nodes:
                if i2 != i and efx_envies(I, X, i, X[i2] + [g]):
                    hasin.add(i2)
        sources = [i for i in nodes if i not in hasin]
        if not sources:
            raise Stuck(('no_source', g, [list(b) for b in X]))
        s = ch.pick(('esrc', g), sources)
        X[s].append(g); owner[g] = s; avail.discard(g); log.append(('III.efx', s, g))
    # leftover goods: valued by nobody
    J = sorted(avail)
    flags['pre_junk'] = [list(b) for b in X]
    if J:
        if junk == 'any':
            s = ch.pick('junk', list(range(n)))
        else:
            s = l3_source(I, X)
        for g in J:
            X[s].append(g); log.append(('junk', s, g))
    if record:
        flags['log'] = log
    return X, flags


def envy_graph(I, X):
    return {i: [j for j in range(I.n) if j != i and I.val(i, X[j]) > I.val(i, X[i])] for i in range(I.n)}


def l3_source(I, X):
    """rotate envy cycles until the envy graph is acyclic (in place), return an unenvied agent"""
    while True:
        E = envy_graph(I, X)
        cyc = find_cycle(E, I.n)
        if cyc is None:
            break
        # agent cyc[t] takes the bundle of cyc[t+1] (whom it envies)
        B = [list(X[c]) for c in cyc]
        for t, c in enumerate(cyc):
            X[c] = B[(t + 1) % len(cyc)]
    envied = set(j for i in range(I.n) for j in envy_graph(I, X)[i])
    return min(i for i in range(I.n) if i not in envied)


def find_cycle(E, n):
    """a cycle c_0 -> c_1 -> ... -> c_0 of the digraph E (c_t envies c_{t+1}), or None"""
    color = [0] * n; parent = [-1] * n
    for s in range(n):
        if color[s]:
            continue
        stack = [(s, iter(E[s]))]; color[s] = 1
        while stack:
            u, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                color[u] = 2; stack.pop(); continue
            if color[nxt] == 0:
                color[nxt] = 1; parent[nxt] = u; stack.append((nxt, iter(E[nxt])))
            elif color[nxt] == 1:
                path = []; w = u
                while w != nxt:
                    path.append(w); w = parent[w]
                path.append(nxt)
                return path[::-1]
    return None
