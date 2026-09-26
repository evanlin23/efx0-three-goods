"""Referee checks for Theorem C of proofs/local_search.md (Algorithm LS2), written from the raw definitions.

This file does not use src/ls_alg.c or src/local_search.py. Every quantity is computed numerically from a balanced
realization of the ranking profile: envy (v_i(Y_j) > v_i(Y_i)), envy of a good, sources, a-holders, levels (rank of
v_i(S_i) among the eight subset sums of R_i), dirty triples, and EFX0 (v_i(X_i) >= v_i(X_j minus g) for all
i != j, g in X_j). EFX0 of every produced allocation is checked under three balanced realizations.

Mode `states`: for every core with n <= N (the connected cores of results/certs_lb_2_6.json.gz and the disconnected
ones of results/certs_lb_disconnected_4_6.json.gz), every strict ranking profile and every junk-free EFX0 partial
allocation Y (each good in the pool or with one of its valuers), it checks under the preconditions the proof of
Theorem C uses:
- Lemma 1: the (F)/(Q) rule equals the raw definition (three realizations);
- Claim 1: every instance of steps 1-6 (step 1 and 2 always; steps 3-5 when step 1 does not apply; step 6 when
  steps 1-5 do not apply and no bundle is empty) gives a junk-free EFX0 allocation with larger sum of levels, and
  keeps bundles of at most two goods (Claim 5) when Y has them;
- Claim 2 (f), (g), (h) when U is nonempty, steps 1-6 do not apply and no bundle is empty;
- Claim 3: when moreover an SDR exists, for every SDR, every choice of dirty triples, successors f(s) and envy paths
  P_s, every cycle of f and start s_1, and every shortest closed sub-walk C of W (read linearly and cyclically): C
  is a simple cycle with a dirty edge, the taken sets are disjoint, and the move gives a junk-free EFX0 allocation
  with larger sum of levels and bundles of at most two goods;
- Claim 4 and Claim 5: Phase 2 (a) for every empty bundle, and Phase 2 (b) for every maximum matching and every
  unmatched s*, gives a complete EFX0 allocation (raw), with at most one bundle of more than two goods when Y's
  bundles have at most two; the facts the proof asserts about T, D(T) and M hold.
With --sample=K only K random profiles per core are taken (and every junk-free state of each).
Mode `runs`: Algorithm LS2 from the empty allocation with random choices at every choice point, on every profile
of every core with n <= N (or K random profiles per core with --sample=K): the output is complete, EFX0 (raw,
three realizations), has at most one bundle of more than two goods, and Phase 1 takes at most 7n steps.

Usage: python3 k3/ls2_referee.py states N [--sample=K] [--seed=S] [--jobs=J]   (K random profiles per core)
       python3 k3/ls2_referee.py runs N [--sample=K] [--seed=S] [--jobs=J]
"""
import sys, os, json, gzip, itertools, random, collections, time, multiprocessing

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
PERMS = list(itertools.permutations(range(3)))
REALS = [(4, 3, 2), (10, 9, 2), (10, 6, 5)]      # balanced realizations of a > b > c
POOL = -1

def load_cores(nmax):
    out = []
    for f in ['certs_lb_2_6.json.gz', 'certs_lb_disconnected_4_6.json.gz']:
        for r in json.load(gzip.open(os.path.join(ROOT, 'results', f))):
            if r['n'] <= nmax:
                out.append((r['n'], r['m'], [tuple(S) for S in r['sets']]))
    return out

class Inst:
    """A core with a strict ranking profile: rank[i] = (a_i, b_i, c_i); val[k][i][g] under realization k."""
    def __init__(self, n, m, rank):
        self.n, self.m, self.rank = n, m, rank
        self.R = [set(r) for r in rank]
        self.val = [[{r[0]: x[0], r[1]: x[1], r[2]: x[2]} for r in rank] for x in REALS]
        self.valuers = [[i for i in range(n) if g in self.R[i]] for g in range(m)]
        self.levels = []
        for i in range(n):
            v = self.val[0][i]; sums = sorted(sum(v[g] for g in S) for k in range(4) for S in itertools.combinations(rank[i], k))
            assert len(set(sums)) == 8
            self.levels.append({s: t for t, s in enumerate(sums)})

def bundles_of(inst, own):
    B = [[] for _ in range(inst.n)]
    for g, o in enumerate(own):
        if o != POOL: B[o].append(g)
    return B

def V(inst, k, i, S):
    v = inst.val[k][i]; return sum(v.get(g, 0) for g in S)

def efx0(inst, own, k=None):
    """Raw EFX0 of a (partial) allocation under realization k (all three if k is None)."""
    ks = range(3) if k is None else [k]
    B = bundles_of(inst, own)
    for kk in ks:
        for i in range(inst.n):
            mine = V(inst, kk, i, B[i])
            for j in range(inst.n):
                if j == i or len(B[j]) < 2: continue
                tot = V(inst, kk, i, B[j])
                for g in B[j]:
                    if tot - inst.val[kk][i].get(g, 0) > mine: return False
    return True

def lemma1(inst, own):
    """Lemma 1's rule (F) and (Q), from the ranking only."""
    B = bundles_of(inst, own)
    free = lambda g: own[g] == POOL or len(B[own[g]]) == 1
    for i in range(inst.n):
        a, b, c = inst.rank[i]
        S = set(B[i]) & inst.R[i]
        if len(S) >= 2: continue
        if S == {a}:
            if own[b] != POOL and own[b] == own[c] and len(B[own[b]]) >= 3: return False
            continue
        need = {frozenset(): (a, b, c), frozenset([c]): (a, b), frozenset([b]): (a,)}[frozenset(S)]
        if not all(free(g) for g in need): return False
    return True

class State:
    """Everything the proof uses about a junk-free partial allocation, computed numerically (realization 0)."""
    def __init__(self, inst, own):
        self.inst, self.own = inst, list(own)
        n = inst.n
        self.B = bundles_of(inst, own)
        self.U = [g for g in range(inst.m) if own[g] == POOL]
        self.vown = [V(inst, 0, i, self.B[i]) for i in range(n)]
        self.env = [[j != i and V(inst, 0, i, self.B[j]) > self.vown[i] for j in range(n)] for i in range(n)]
        self.source = [not any(self.env[k][j] for k in range(n)) for j in range(n)]
        self.onegood = [j for j in range(n) if self.source[j] and len(self.B[j]) == 1]
        self.aholder = [i for i in range(n) if self.B[i] == [inst.rank[i][0]]]
        self.level = sum(inst.levels[i][self.vown[i]] for i in range(n))
        self.envies_good = lambda i, u: u in inst.R[i] and inst.val[0][i][u] > self.vown[i]
        self.dirty = []                                  # (i, u, s)
        Uset = set(self.U)
        for s in self.onegood:
            y = self.B[s][0]
            for i in self.aholder:
                a, b, c = inst.rank[i]
                for u, w in ((b, c), (c, b)):
                    if u in Uset and w == y: self.dirty.append((i, u, s))
        self.D = collections.defaultdict(set)
        for i, u, s in self.dirty: self.D[s].add(u)
        # reachability by envy paths
        self.reach = [[False] * n for _ in range(n)]
        for s in range(n):
            st = [s]; seen = {s}
            while st:
                x = st.pop()
                for y in range(n):
                    if self.env[x][y] and y not in seen: seen.add(y); st.append(y)
            for y in seen: self.reach[s][y] = True

def paths(st, s, t, limit=1000):
    """All simple envy paths from s to t (lists of agents)."""
    out = []
    def rec(p):
        if len(out) >= limit: return
        x = p[-1]
        if x == t and len(p) > 1: out.append(list(p)); return
        for y in range(st.inst.n):
            if st.env[x][y] and y not in p: rec(p + [y])
    rec([s])
    return out

def cycles(st):
    """All simple envy cycles (each once, from its smallest agent)."""
    n = st.inst.n; out = []
    for s in range(n):
        def rec(p):
            x = p[-1]
            for y in range(n):
                if st.env[x][y]:
                    if y == s and len(p) >= 2: out.append(list(p))
                    elif y > s and y not in p: rec(p + [y])
        rec([s])
    return out

def apply(inst, own, takes):
    """takes: {agent: set of goods}. The agents in `takes` get exactly these sets; every other good of their old
    bundles goes to the pool; everybody else keeps its bundle."""
    new = list(own)
    for g, o in enumerate(own):
        if o in takes: new[g] = POOL
    allg = [g for T in takes.values() for g in T]
    assert len(allg) == len(set(allg)), "taken sets not disjoint"
    for i, T in takes.items():
        for g in T: new[g] = i
    return new

def check_result(inst, st, new, tally, what, small):
    B = bundles_of(inst, new)
    if any(g not in inst.R[i] for i in range(inst.n) for g in B[i]): tally['FAIL junk ' + what] += 1; return False
    if not efx0(inst, new): tally['FAIL efx0 ' + what] += 1; return False
    if State(inst, new).level <= st.level: tally['FAIL level ' + what] += 1; return False
    if small and max(len(b) for b in B) > 2: tally['FAIL size ' + what] += 1; return False
    tally['ok ' + what] += 1
    return True

def steps_1_to_6(inst, st, tally, small):
    """Claim 1: every instance under its precondition. Returns the applicability flags of steps 1-6."""
    U = st.U; n = inst.n; Uset = set(U)
    s1 = [(i, u) for i in range(n) for u in U if st.envies_good(i, u)]
    for i, u in s1:
        check_result(inst, st, apply(inst, st.own, {i: {u}}), tally, 'step1', small)
    cyc = cycles(st)
    for C in cyc:
        L = len(C)
        takes = {C[t]: set(st.B[C[(t + 1) % L]]) & inst.R[C[t]] for t in range(L)}
        check_result(inst, st, apply(inst, st.own, takes), tally, 'step2', small)
    s3 = s4 = s5 = []
    if not s1:
        s3 = [i for i in st.aholder if inst.rank[i][1] in Uset and inst.rank[i][2] in Uset]
        for i in s3:
            check_result(inst, st, apply(inst, st.own, {i: {inst.rank[i][1], inst.rank[i][2]}}), tally, 'step3', small)
        s4 = [(i, u) for i in st.aholder for u in inst.rank[i][1:] if u in Uset
              and (inst.rank[i][1] in Uset) != (inst.rank[i][2] in Uset) and not any(st.env[k][i] for k in range(n))]
        for i, u in s4:
            check_result(inst, st, apply(inst, st.own, {i: {inst.rank[i][0], u}}), tally, 'step4', small)
        s5 = [(s, u) for s in st.onegood for u in U if u in inst.R[s]]
        for s, u in s5:
            check_result(inst, st, apply(inst, st.own, {s: {st.B[s][0], u}}), tally, 'step5', small)
    empty = any(len(b) == 0 for b in st.B)
    s6 = []
    if not (s1 or cyc or s3 or s4 or s5) and not empty:
        for i, u, s in st.dirty:
            for P in paths(st, s, i):
                s6.append(1)
                takes = {P[q]: set(st.B[P[q + 1]]) & inst.R[P[q]] for q in range(len(P) - 1)}
                takes[i] = {u, st.B[s][0]}
                check_result(inst, st, apply(inst, st.own, takes), tally, 'step6', small)
    return bool(s1), bool(cyc), bool(s3), bool(s4), bool(s5), bool(s6), empty

def sdrs(st):
    srcs = st.onegood; out = []
    def rec(t, used, cur):
        if t == len(srcs): out.append(dict(cur)); return
        for u in sorted(st.D[srcs[t]]):
            if u not in used:
                cur[srcs[t]] = u; rec(t + 1, used | {u}, cur); del cur[srcs[t]]
    rec(0, frozenset(), {})
    return out

def claim3(inst, st, tally, small, cap=4000):
    """Step 7 over every choice point (up to `cap` combinations per state)."""
    count = 0
    for ell in sdrs(st):
        srcs = st.onegood
        per = []                                          # per source: list of (i_s, f(s), P_s)
        for s in srcs:
            opts = []
            for i, u, s2 in st.dirty:
                if s2 != s or u != ell[s]: continue
                for f in srcs:
                    if f == s: continue
                    for P in paths(st, f, i):
                        opts.append((i, f, P))
            if not opts:
                tally['FAIL claim2h-in-claim3'] += 1; return
            per.append(opts)
        for choice in itertools.product(*per):
            count += 1
            if count > cap: tally['claim3 capped'] += 1; return
            ch = dict(zip(srcs, choice))
            f = {s: ch[s][1] for s in srcs}
            # cycles of f
            seen_cyc = set()
            for s0 in srcs:
                x = s0; path = []
                while x not in path: path.append(x); x = f[x]
                cyc = path[path.index(x):]
                key = frozenset(cyc)
                if key in seen_cyc: continue
                seen_cyc.add(key)
                if len(cyc) < 2: tally['FAIL f fixed point'] += 1; return
                for start in range(len(cyc)):
                    s_list = cyc[start:] + cyc[:start]           # s_1, f(s_1)=s_2, ...
                    k = len(s_list)
                    # W: start at s_1; for j = k..1 follow P_{s_j} (from s_{j+1} to i_{s_j}) then dirty edge to s_j
                    W = [s_list[0]]; lab = []                    # lab[t] = ('env',) or ('dirty', s) for edge W[t]->W[t+1]
                    for j in range(k - 1, -1, -1):
                        sj = s_list[j]; i_s, fs, P = ch[sj]
                        assert fs == s_list[(j + 1) % k] and P[0] == W[-1]
                        for q in range(1, len(P)): W.append(P[q]); lab.append(('env',))
                        W.append(sj); lab.append(('dirty', sj))
                    L = len(W) - 1
                    assert W[0] == W[L]
                    for cyclic in (False, True):
                        cands = []
                        idx = range(L) if cyclic else range(L + 1)
                        best = None
                        for p in range(L):
                            for d in range(1, L + 1):
                                q = p + d
                                if not cyclic and q > L: break
                                if W[p % L if cyclic else p] == W[q % L if cyclic else q] and (cyclic or q <= L):
                                    if best is None or d < best: best = d; cands = [p]
                                    elif d == best: cands.append(p)
                                    break
                        for p in cands:
                            Cv = [W[(p + t) % L if cyclic else p + t] for t in range(best)]
                            Cl = [lab[(p + t) % L if cyclic else p + t] for t in range(best)]
                            if len(set(Cv)) != len(Cv): tally['FAIL C not simple'] += 1; continue
                            if not any(l[0] == 'dirty' for l in Cl): tally['FAIL C no dirty edge'] += 1; continue
                            takes = {}
                            for t in range(best):
                                a_, b_ = Cv[t], Cv[(t + 1) % best]
                                if Cl[t][0] == 'env':
                                    if not st.env[a_][b_]: tally['FAIL not an envy edge'] += 1
                                    takes[a_] = set(st.B[b_]) & inst.R[a_]
                                else:
                                    s = Cl[t][1]; assert b_ == s
                                    takes[a_] = {ell[s]} | set(st.B[s])
                            try:
                                new = apply(inst, st.own, takes)
                            except AssertionError:
                                tally['FAIL claim3 taken sets not disjoint'] += 1; continue
                            check_result(inst, st, new, tally, 'step7', small)

def matchings(st):
    """All maximum matchings between the one-good sources and goods (s - u iff u in D(s)), as dicts s -> u."""
    srcs = st.onegood; best = [0]; out = []
    def rec(t, used, cur):
        if t == len(srcs):
            if len(cur) > best[0]: best[0] = len(cur); out.clear()
            if len(cur) == best[0]: out.append(dict(cur))
            return
        s = srcs[t]
        for u in sorted(st.D[s]):
            if u not in used:
                cur[s] = u; rec(t + 1, used | {u}, cur); del cur[s]
        rec(t + 1, used, cur)
    rec(0, frozenset(), {})
    return out

def phase2_b(inst, st, M, sstar):
    """Phase 2 (b) with maximum matching M (source -> good) and the unmatched source s*. Returns the allocation, and
    checks the facts the proof of Claim 4 asserts."""
    Minv = {u: s for s, u in M.items()}
    T = {sstar}; frontier = [sstar]
    while frontier:
        s = frontier.pop()
        for u in st.D[s]:
            if u in Minv and Minv[u] not in T: T.add(Minv[u]); frontier.append(Minv[u])
    DT = set().union(*[st.D[s] for s in T]) if T else set()
    facts = all(u in Minv for u in DT) and all(Minv[u] in T and Minv[u] != sstar for u in DT)
    new = list(st.own)
    for u in st.U:
        new[u] = Minv[u] if u in DT else sstar
    return new, facts

def check_final(inst, st, new, tally, what, small):
    if any(o == POOL for o in new): tally['FAIL incomplete ' + what] += 1; return
    if not efx0(inst, new): tally['FAIL efx0 ' + what] += 1; return
    if small and sum(1 for b in bundles_of(inst, new) if len(b) > 2) > 1: tally['FAIL shape ' + what] += 1; return
    tally['ok ' + what] += 1

def check_state(inst, own, tally):
    st = State(inst, own)
    small = max(len(b) for b in st.B) <= 2
    if not st.U: return
    f1, f2, f3, f4, f5, f6, empty = steps_1_to_6(inst, st, tally, small)
    if f1 or f2 or f3 or f4 or f5: pass
    elif empty:
        # Phase 1 stops; Phase 2 (a) with every empty bundle
        for e in range(inst.n):
            if not st.B[e]:
                new = list(st.own)
                for u in st.U: new[u] = e
                check_final(inst, st, new, tally, 'phase2a', small)
    elif not f6:
        # Claim 2 (f), (g), (h)
        n = inst.n
        ok_f = all(len(st.B[s]) == 1 for s in range(n) if st.source[s] and any(st.env[s][j] for j in range(n)))
        ok_g = len(st.onegood) > 0
        ok_h = all(any(s2 != s and st.reach[s2][i] for s2 in st.onegood) for i, u, s in st.dirty)
        tally['claim2 states'] += 1
        for nm, ok in (('f', ok_f), ('g', ok_g), ('h', ok_h)):
            if not ok: tally['FAIL claim2' + nm] += 1
        if sdrs(st):
            claim3(inst, st, tally, small)
        else:
            Ms = matchings(st)
            for M in Ms:
                for sstar in st.onegood:
                    if sstar in M: continue
                    new, facts = phase2_b(inst, st, M, sstar)
                    if not facts: tally['FAIL claim4 matching facts'] += 1
                    check_final(inst, st, new, tally, 'phase2b', small)

def worker_states(args):
    n, m, sets, sample, seed = args
    tally = collections.Counter()
    choices = [[POOL] + [i for i in range(n) if g in sets[i]] for g in range(m)]
    rng = random.Random(seed * 7919 + hash((n, m, tuple(sets))) % 100003)
    profs = ([tuple(rng.randrange(6) for _ in range(n)) for _ in range(sample)] if sample
             else itertools.product(range(6), repeat=n))
    for prof in profs:
        rank = [tuple(sets[i][p] for p in PERMS[prof[i]]) for i in range(n)]
        inst = Inst(n, m, rank)
        for own in itertools.product(*choices):
            ok = efx0(inst, own, 0)
            if ok != lemma1(inst, own) or ok != efx0(inst, own, 1) or ok != efx0(inst, own, 2):
                tally['FAIL lemma1'] += 1
            if not ok: continue
            tally['states'] += 1
            check_state(inst, own, tally)
    return n, tally

# ------------------------------------------------------------------------------------------------------------------
# Full runs of LS2 with random choices
# ------------------------------------------------------------------------------------------------------------------

def ls2_random(inst, rng):
    n, m = inst.n, inst.m
    own = [POOL] * m; steps = 0
    while True:
        st = State(inst, own)
        if not st.U: return own, steps, 'complete'
        U = st.U; Uset = set(U)
        opts = [('1', i, u) for i in range(n) for u in U if st.envies_good(i, u)]
        if not opts:
            cyc = cycles(st)
            if cyc: opts = [('2', C) for C in cyc]
        if not opts:
            opts = [('3', i) for i in st.aholder if inst.rank[i][1] in Uset and inst.rank[i][2] in Uset]
        if not opts:
            opts = [('4', i, u) for i in st.aholder for u in inst.rank[i][1:] if u in Uset
                    and (inst.rank[i][1] in Uset) != (inst.rank[i][2] in Uset) and not any(st.env[k][i] for k in range(n))]
        if not opts:
            opts = [('5', s, u) for s in st.onegood for u in U if u in inst.R[s]]
        if not opts and any(len(b) == 0 for b in st.B):
            e = rng.choice([e for e in range(n) if not st.B[e]])
            for u in U: own[u] = e
            return own, steps, 'phase2a'
        if not opts:
            opts = [('6', i, u, s, P) for i, u, s in st.dirty for P in paths(st, s, i)]
        if not opts:
            S = sdrs(st)
            if S:
                ell = rng.choice(S)
                # one random instance of step 7
                ch = {}
                for s in st.onegood:
                    o = [(i, f, P) for i, u, s2 in st.dirty if s2 == s and u == ell[s]
                         for f in st.onegood if f != s for P in paths(st, f, i)]
                    ch[s] = rng.choice(o)
                s0 = rng.choice(st.onegood); path = []
                while s0 not in path: path.append(s0); s0 = ch[s0][1]
                cyc = path[path.index(s0):]
                r = rng.randrange(len(cyc)); s_list = cyc[r:] + cyc[:r]; k = len(s_list)
                W = [s_list[0]]; lab = []
                for j in range(k - 1, -1, -1):
                    sj = s_list[j]; i_s, fs, P = ch[sj]
                    for q in range(1, len(P)): W.append(P[q]); lab.append(('env',))
                    W.append(sj); lab.append(('dirty', sj))
                L = len(W) - 1; best = None; cands = []
                for p in range(L):
                    for d in range(1, L - p + 1):
                        if W[p] == W[p + d]:
                            if best is None or d < best: best = d; cands = [p]
                            elif d == best: cands.append(p)
                            break
                p = rng.choice(cands)
                takes = {}
                for t in range(best):
                    a_, b_ = W[p + t], W[p + t + 1]
                    if lab[p + t][0] == 'env': takes[a_] = set(st.B[b_]) & inst.R[a_]
                    else: s = lab[p + t][1]; takes[a_] = {ell[s]} | set(st.B[s])
                own = apply(inst, own, takes); steps += 1; continue
            Ms = matchings(st); M = rng.choice(Ms)
            sstar = rng.choice([s for s in st.onegood if s not in M])
            new, facts = phase2_b(inst, st, M, sstar)
            assert facts
            return new, steps, 'phase2b'
        o = rng.choice(opts)
        if o[0] == '1': own = apply(inst, own, {o[1]: {o[2]}})
        elif o[0] == '2':
            C = o[1]; L = len(C)
            own = apply(inst, own, {C[t]: set(st.B[C[(t + 1) % L]]) & inst.R[C[t]] for t in range(L)})
        elif o[0] == '3': own = apply(inst, own, {o[1]: {inst.rank[o[1]][1], inst.rank[o[1]][2]}})
        elif o[0] == '4': own = apply(inst, own, {o[1]: {inst.rank[o[1]][0], o[2]}})
        elif o[0] == '5': own = apply(inst, own, {o[1]: {st.B[o[1]][0], o[2]}})
        elif o[0] == '6':
            _, i, u, s, P = o
            takes = {P[q]: set(st.B[P[q + 1]]) & inst.R[P[q]] for q in range(len(P) - 1)}
            takes[i] = {u, st.B[s][0]}
            own = apply(inst, own, takes)
        steps += 1

def worker_runs(args):
    n, m, sets, sample, seed = args
    rng = random.Random(seed * 7919 + hash((n, m, tuple(sets))) % 100003)
    tally = collections.Counter(); maxsteps = 0
    profs = ([tuple(rng.randrange(6) for _ in range(n)) for _ in range(sample)] if sample
             else itertools.product(range(6), repeat=n))
    for prof in profs:
        rank = [tuple(sets[i][p] for p in PERMS[prof[i]]) for i in range(n)]
        inst = Inst(n, m, rank)
        X, steps, how = ls2_random(inst, rng)
        maxsteps = max(maxsteps, steps)
        tally['runs'] += 1; tally[how] += 1
        if any(o == POOL for o in X) or not efx0(inst, X): tally['FAIL output'] += 1
        if sum(1 for b in bundles_of(inst, X) if len(b) > 2) > 1: tally['FAIL shape'] += 1
        if steps > 7 * n: tally['FAIL steps'] += 1
    return n, tally, maxsteps

def main():
    args = sys.argv[1:]
    opt = {a.split('=')[0]: a.split('=')[1] for a in args if a.startswith('--') and '=' in a}
    pos = [a for a in args if not a.startswith('--')]
    mode, N = pos[0], int(pos[1]); jobs = int(opt.get('--jobs', 4))
    cores = load_cores(N)
    t0 = time.time(); per = collections.Counter(c[0] for c in cores)
    total = collections.Counter(); ms = collections.Counter()
    with multiprocessing.Pool(jobs) as pool:
        sample, seed = int(opt.get('--sample', 0)), int(opt.get('--seed', 1))
        if mode == 'states':
            for n, tally in pool.imap_unordered(worker_states, [(n, m, s, sample, seed) for n, m, s in cores]):
                total.update(tally)
        else:
            for n, tally, mx in pool.imap_unordered(worker_runs, [(n, m, s, sample, seed) for n, m, s in cores]):
                total.update(tally); ms[n] = max(ms[n], mx)
    fails = {k: v for k, v in total.items() if k.startswith('FAIL')}
    print(f"ls2_referee {mode} n <= {N}: {len(cores)} cores {dict(sorted(per.items()))}; {time.time() - t0:.0f} s")
    print("counts:", dict(sorted((k, v) for k, v in total.items() if not k.startswith('FAIL'))))
    if mode == 'runs': print("most Phase-1 steps by n:", dict(sorted(ms.items())), "(bound 7n)")
    print("failures:", fails if fails else 0)
    return 1 if fails else 0

if __name__ == '__main__':
    sys.exit(main())
