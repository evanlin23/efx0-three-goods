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


# ------------------------------------------------------------------ EFX0 repairs (k4/vm.md section 6)
def safe_add(I, X, s, g):
    """adding g to X_s keeps the allocation EFX0 (given it is EFX0 now): nobody EFX0-envies X_s + g"""
    B = X[s] + [g]
    return not any(efx0_envies(I, X, i, B) for i in range(I.n) if i != s)


def vm0_run(I, ch, f2=True, rot=False, order='choice', base=None, record=False, stop=None):
    """VM with F1 (EFX0 graph: any agent whose bundle stays EFX0-unenvied may take the good), F2 (Phase III matchings
    only to claimants for which the addition is EFX0-safe; other goods wait for the F1 step), F3 (junk by L3).
    rot=True: rotate envy cycles away before every F1 placement.  order: 'choice' (any unassigned valued good next) or
    'fixed' (smallest index first).  base: an optional one-good matching to start from instead of Phases I-II
    (list of good or None per agent; its agents are then grouped by the rank of their good)."""
    n, m = I.n, I.m
    X = [[] for _ in range(n)]; avail = set(range(m)); log = []; flags = {}
    if base is None:
        def strong(i):
            r = I.rank[i]
            if not r: return False
            a = I.v[i][r[0]]; b = I.v[i][r[1]] if len(r) > 1 else 0; c = I.v[i][r[2]] if len(r) > 2 else 0
            return a > b + c
        A = set(i for i in range(n) if strong(i)); owner = {}
        MA = matching_step(I, ch, A, avail, 1, 'G', 'I', X, owner, log)
        Nr = set(range(n)) - MA; Nk = {}
        for k in (1, 2, 3, 4):
            Nk[k] = matching_step(I, ch, Nr, avail, k, 'G', 'II.%d' % k, X, owner, log); Nr -= Nk[k]
    else:
        Nk = {k: set() for k in (1, 2, 3, 4)}
        for i, g in enumerate(base):
            if g is not None:
                X[i].append(g); avail.discard(g); log.append(('base', i, g))
                Nk[I.rank[i].index(g) + 1].add(i)
    if stop == 'II':
        return X, flags

    def mstep(agents, k, tag):
        claim = {}
        for i in sorted(agents):
            r = I.rank[i]
            g = r[k - 1] if len(r) >= k else None
            if g is not None and g in avail:
                claim.setdefault(g, []).append(i)
        got = set()
        for g in sorted(claim):
            opts = [i for i in claim[g] if (not f2) or safe_add(I, X, i, g)]
            if not opts:
                continue
            i = ch.pick((tag, g), opts)
            X[i].append(g); avail.discard(g); got.add(i); log.append((tag, i, g))
        return got
    mstep(Nk[3], 4, 'III.3-4')
    N2r = mstep(Nk[2], 3, 'III.2-3')
    mstep(Nk[2] - N2r, 4, 'III.2-4')
    if stop == 'IIIm':
        return X, flags
    while True:
        valued = sorted(g for g in avail if I.valued_by(g))
        if not valued:
            break
        g = ch.pick('egood', valued) if order == 'choice' else valued[0]
        if rot:
            l3_source(I, X)            # rotates in place; EFX0 is preserved by rotations
        cands = [s for s in range(n) if safe_add(I, X, s, g)]
        if not cands:
            raise Stuck(('no_safe', g, [list(b) for b in X]))
        s = ch.pick(('esrc', g), cands)
        X[s].append(g); avail.discard(g); log.append(('F1', s, g))
    J = sorted(avail)
    if J:
        s = l3_source(I, X)
        for g in J:
            X[s].append(g); log.append(('junk', s, g))
    if record:
        flags['log'] = log
    return X, flags


def vm_strip_run(I, ch, rot=True, which='choice', **kw):
    """F5: V-M (main reading) to a complete EFX allocation, then strip: while some zero-good EFX0 violation (i envies
    X_j, z in X_j, v_i(z) = 0) exists, remove such a z from X_j (choice of violation: 'choice' or 'first'); then
    re-place the stripped goods one by one into bundles that stay EFX0-unenvied (F1, rotation before each placement
    if rot), junk last by L3.  Raises Stuck if a stripped good has no safe place or stripping does not reach EFX0."""
    X, fl = vm_run(I, ch, junk='L3')
    X = [list(b) for b in X]
    pool = []
    for _ in range(4 * I.m + 4):
        viol = efx_violations(I, X, zero=True)
        if not viol:
            break
        zv = sorted(set((j, g) for (i, j, g) in viol if I.v[i].get(g, 0) == 0))
        if not zv:
            raise Stuck(('positive_violation', [list(b) for b in X]))
        j, g = ch.pick('strip', zv) if which == 'choice' else zv[0]
        X[j].remove(g); pool.append(g)
    else:
        raise Stuck(('strip_loop', [list(b) for b in X]))
    if efx_violations(I, X, zero=True):
        raise Stuck(('strip_not_efx0', [list(b) for b in X]))
    valued = sorted(g for g in pool if I.valued_by(g)); junk = sorted(g for g in pool if not I.valued_by(g))
    while valued:
        g = ch.pick('regood', valued)
        valued.remove(g)
        if rot:
            l3_source(I, X)
        cands = [s for s in range(I.n) if safe_add(I, X, s, g)]
        if not cands:
            raise Stuck(('no_safe', g, [list(b) for b in X]))
        s = ch.pick(('resrc', g), cands)
        X[s].append(g)
    if junk:
        s = l3_source(I, X)
        X[s] += junk
    return X, {}


def upgrades(I, X, pool):
    """F6 moves: (i, S) with X_i a single good y, S a subset of the pool inside R_i with v_i(S) > v_i(y), and the
    state after X_i := S (y back to the pool) EFX0 (nobody EFX0-envies S; i's own value only rises)"""
    out = []
    P = sorted(g for g in pool)
    for i in range(I.n):
        if len(X[i]) != 1:
            continue
        y = X[i][0]; vy = I.v[i].get(y, 0)
        mine = [g for g in P if g in I.v[i]]
        for r in range(1, min(4, len(mine)) + 1):
            for S in itertools.combinations(mine, r):
                if I.val(i, S) <= vy:
                    continue
                if any(I.val(i, [h for h in S if h != g]) > vy for g in S):
                    continue                           # minimal: every proper subset is worth at most y
                Y = [list(b) for b in X]; Y[i] = list(S)
                if not any(efx0_envies(I, Y, k, Y[i]) for k in range(I.n) if k != i) and \
                        not any(efx0_envies(I, Y, i, Y[j]) for j in range(I.n) if j != i):
                    out.append((i, S))
    return out


def vm6_run(I, ch, rot=True, upg='choice', base=None, record=False):
    """F6: as vm0_run (F2, F1 with rotation, F3), but before every F1 placement the chooser may instead apply an
    upgrade move (upgrades()).  upg='choice': upgrades and 'place' are choice points; 'eager': apply the first
    upgrade whenever one exists; 'stuck': upgrades only when the chosen good has no safe place."""
    X, fl = vm0_run(I, ch, f2=True, rot=rot, base=base, stop='IIIm')
    X = [list(b) for b in X]
    held = set(g for b in X for g in b)
    pool = set(g for g in range(I.m) if g not in held)
    log = []
    for step in range((16 * I.n + 1) * (I.m + 1) + 10):
        valued = sorted(g for g in pool if I.valued_by(g))
        if not valued:
            break
        if rot:
            l3_source(I, X)
        ups = upgrades(I, X, pool) if upg in ('choice', 'eager') else []
        if ups:
            if upg == 'eager':
                act = ups[0]
            else:
                act = ch.pick('upg', ups + ['place'])
            if act != 'place':
                i, S = act; y = X[i][0]
                X[i] = list(S); pool -= set(S); pool.add(y); log.append(('upg', i, y, S))
                continue
        g = ch.pick('egood', valued)
        cands = [s for s in range(I.n) if safe_add(I, X, s, g)]
        if not cands and upg == 'stuck':
            ups = upgrades(I, X, pool)
            if ups:
                i, S = ch.pick('upg', ups); y = X[i][0]
                X[i] = list(S); pool -= set(S); pool.add(y); log.append(('upg', i, y, S))
                continue
        if not cands:
            raise Stuck(('no_safe', g, [list(b) for b in X]))
        s = ch.pick(('esrc', g), cands)
        X[s].append(g); pool.discard(g); log.append(('F1', s, g))
    else:
        raise Stuck(('loop',))
    J = sorted(pool)
    if J:
        s = l3_source(I, X)
        X[s] += J
    fl = {'log': log} if record else {}
    return X, fl


def exchanges(I, X, pool):
    """F6x moves: (i, j, z, P) with X_i = {y} a single good, z in X_j (j != i), P a subset of the pool: i gets
    {z} + P, j gets X_j - z + y; both strictly gain; the new state is EFX0.  Also the pool-only upgrades (j = None)."""
    out = [(i, None, None, S) for (i, S) in upgrades(I, X, pool)]
    P = sorted(pool)
    for i in range(I.n):
        if len(X[i]) != 1:
            continue
        y = X[i][0]; vy = I.v[i].get(y, 0)
        mine = [g for g in P if g in I.v[i]]
        for j in range(I.n):
            if j == i or y not in I.v[j]:
                continue
            for z in X[j]:
                if z not in I.v[i]:
                    continue
                Bj = [h for h in X[j] if h != z] + [y]
                if I.val(j, Bj) <= I.val(j, X[j]):
                    continue
                for r in range(0, min(3, len(mine)) + 1):
                    for S in itertools.combinations(mine, r):
                        Bi = [z] + list(S)
                        if I.val(i, Bi) <= vy:
                            continue
                        Y = [list(b) for b in X]; Y[i] = Bi; Y[j] = Bj
                        if not efx_violations(I, Y, zero=True):
                            out.append((i, j, z, S))
    return out


def vm6x_run(I, ch, rot=True, mode='choice', base=None, record=False):
    """F6x: as vm6_run with upgrade moves replaced by exchanges() (pool-only upgrades included).
    mode='choice': moves and 'place' are choice points; 'eager': a move is applied whenever one exists (which one is
    a choice point); 'eager1': the first move in exchanges()'s order; 'stuck': moves only when the chosen good has no
    safe place."""
    X, fl = vm0_run(I, ch, f2=True, rot=rot, base=base, stop='IIIm')
    X = [list(b) for b in X]
    held = set(g for b in X for g in b)
    pool = set(g for g in range(I.m) if g not in held)
    log = []

    def apply(mv):
        i, j, z, S = mv; y = X[i][0]
        if j is None:
            X[i] = list(S)
        else:
            X[j] = [h for h in X[j] if h != z] + [y]; X[i] = [z] + list(S); y = None
        pool.difference_update(S)
        if y is not None:
            pool.add(y)
        log.append(('move', mv))
    for step in range((16 * I.n + 1) * (I.m + 1) + 10):
        valued = sorted(g for g in pool if I.valued_by(g))
        if not valued:
            break
        if rot:
            l3_source(I, X)
        if mode in ('choice', 'eager', 'eager1'):
            mv = exchanges(I, X, pool)
            if mv:
                act = ch.pick('mv', mv + ['place']) if mode == 'choice' else (mv[0] if mode == 'eager1' else ch.pick('mv', mv))
                if act != 'place':
                    apply(act); continue
        g = ch.pick('egood', valued)
        cands = [s for s in range(I.n) if safe_add(I, X, s, g)]
        if not cands and mode == 'stuck':
            mv = exchanges(I, X, pool)
            if mv:
                apply(ch.pick('mv', mv)); continue
        if not cands:
            raise Stuck(('no_safe', g, [list(b) for b in X]))
        s = ch.pick(('esrc', g), cands)
        X[s].append(g); pool.discard(g); log.append(('F1', s, g))
    else:
        raise Stuck(('loop',))
    J = sorted(pool)
    if J:
        s = l3_source(I, X)
        X[s] += J
    return X, ({'log': log} if record else {})
