#!/usr/bin/env python3
"""Referee checks for CH-A, CH-B (kgen/charity.md §2-§3, branch claude/kgen-charity). Shares no code with
kgen/charity/.

(1) `packing`: the packing inequality cited from Sivashankar (arXiv 2607.27455, Theorem 3), as used in CH-R:
    a p-partite digraph (parts V_1..V_p, edges only between different parts) in which every vertex has an
    in-neighbour in every other part and no *rainbow cycle* (a directed cycle with at most one vertex per part)
    satisfies (p - 1)! * sum |V_i| <= prod |V_i|.  For every size vector with (p-1)! sum > prod (p <= 4, parts <= 4),
    a SAT search (python-sat) for such a digraph must be UNSAT; for size vectors with equality-or-slack we also
    report whether one exists (sanity).

(2) `states`: Pareto maxima of small additive instances (brute force over all partial allocations, raw EFX0), plus
    the constructions S'(sigma, k) of §5 rebuilt from the text. At every Pareto maximum with a nonempty pool:
    Lemmas CH2 (sources hold >= 2 goods), CH3 (every champion option's agent values g, is not the source, is not in
    C(s)), CH4 (sigma <= sum mu_t), Lemma CH5/CH6 (the source digraph D over *all* champion options has no rainbow
    cycle), CH-R (the digraph Gamma has the in-neighbour property and no rainbow cycle, and the packing inequality
    holds), and the bounds of CH-A and CH-B.
"""
import itertools, math, sys, json, random
from pysat.solvers import Minisat22

def packing_sat(sizes):
    """search a p-partite digraph with in-neighbour condition and no rainbow cycle."""
    p = len(sizes)
    verts = [(i, a) for i in range(p) for a in range(sizes[i])]
    idx = {}
    def var(u, w):
        if (u, w) not in idx:
            idx[(u, w)] = len(idx) + 1
        return idx[(u, w)]
    cls = []
    for w in verts:
        for i in range(p):
            if i != w[0]:
                cls.append([var(u, w) for u in verts if u[0] == i])
    # forbid every rainbow cycle: sequences of distinct parts, one vertex each, length >= 2
    for L in range(2, p + 1):
        for parts in itertools.permutations(range(p), L):
            if parts[0] != min(parts):
                continue  # rotation canonical
            for choice in itertools.product(*[range(sizes[i]) for i in parts]):
                cyc = [(parts[t], choice[t]) for t in range(L)]
                cls.append([-var(cyc[t], cyc[(t + 1) % L]) for t in range(L)])
    s = Minisat22(bootstrap_with=cls)
    r = s.solve()
    s.delete()
    return r

def packing_run(pmax, smax):
    res = []
    viol = 0; sat_viol = 0; tested = 0
    for p in range(2, pmax + 1):
        for sizes in itertools.combinations_with_replacement(range(1, smax + 1), p):
            lhs = math.factorial(p - 1) * sum(sizes); rhs = math.prod(sizes)
            r = packing_sat(list(sizes))
            tested += 1
            if lhs > rhs:
                viol += 1
                if r:
                    sat_viol += 1
                    res.append(("COUNTEREXAMPLE", sizes))
            res.append((sizes, lhs, rhs, "exists" if r else "none"))
    print(json.dumps(dict(source=f"packing p<={pmax} sizes<={smax}", size_vectors=tested,
                          vectors_violating_inequality=viol, digraphs_found_for_violating_vectors=sat_viol)))
    for x in res:
        print(x)

# ------------------------------------------------------------------ states

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx0(v, X):
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2:
                tot = val(v, i, X[j])
                if any(tot - v[i][h] > t for h in X[j]):
                    return False
    return True

def pareto_maxima(v, m):
    n = len(v)
    states = {}
    for f in itertools.product(range(-1, n), repeat=m):
        X = [set() for _ in range(n)]
        for g, a in enumerate(f):
            if a >= 0:
                X[a].add(g)
        if not efx0(v, X):
            continue
        vec = tuple(val(v, i, X[i]) for i in range(n))
        alloc = sum(1 for a in f if a >= 0)
        states.setdefault(vec, []).append((alloc, [frozenset(x) for x in X]))
    vecs = list(states)
    out = []
    for w in vecs:
        if any(u != w and all(a >= b for a, b in zip(u, w)) for u in vecs):
            continue
        best = max(a for a, _ in states[w])
        for a, X in states[w]:
            if a == best:
                out.append(X)
    return out

def envy_graph(v, X):
    n = len(X)
    return {i: {j for j in range(n) if j != i and val(v, i, X[j]) > val(v, i, X[i])} for i in range(n)}

def reach(G, s):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for w in G[u]:
            if w not in seen:
                seen.add(w); st.append(w)
    return seen

def options(v, X, B):
    """champion options (Z, t) of a set B: Z ⊆ B inclusion-minimal envied (someone envies Z, nobody envies Z - h), t envies Z."""
    n = len(X); out = []
    B = sorted(B)
    def envied_by(Z):
        return [t for t in range(n) if val(v, t, Z) > val(v, t, X[t])]
    for k in range(1, len(B) + 1):
        for Z in itertools.combinations(B, k):
            Z = set(Z); E = envied_by(Z)
            if E and all(not envied_by(Z - {h}) for h in Z):
                out.extend((frozenset(Z), t) for t in E)
    return out

def rainbow_cycle(edges, verts):
    """edges: list of (u, w, colour). Is there a directed cycle with distinct vertices and distinct colours?
    (length 1 allowed: a loop.)"""
    adj = {}
    for u, w, c in edges:
        adj.setdefault(u, []).append((w, c))
    def dfs(start, u, usedv, usedc):
        for w, c in adj.get(u, []):
            if c in usedc:
                continue
            if w == start:
                return True
            if w not in usedv and dfs(start, w, usedv | {w}, usedc | {c}):
                return True
        return False
    return any(dfs(s, s, {s}, frozenset()) for s in verts)

def check_state(v, X, m, k, d, cnt, ex, tag):
    n = len(X)
    P = set(range(m)) - set().union(*X)
    if not P:
        return
    cnt["states_with_pool"] += 1
    cnt["max_pool"] = max(cnt["max_pool"], len(P))
    G = envy_graph(v, X)
    S = [s for s in range(n) if not any(s in G[i] for i in range(n))]
    C = {s: reach(G, s) for s in S}
    # strong charity
    if any(val(v, i, P) > val(v, i, X[i]) for i in range(n)):
        cnt["charity_fail"] += 1
    if any(len(X[s]) < 2 for s in S):
        cnt["CH2_fail"] += 1
    D_edges = []; champs = {}
    for s in S:
        for g in P:
            opts = options(v, X, set(X[s]) | {g})
            if not opts:
                cnt["no_option_fail"] += 1
            for Z, t in opts:
                if not (v[t][g] > 0 and t != s and t not in C[s] and g in Z and all(v[t][h] > 0 for h in Z)):
                    cnt["CH3_fail"] += 1
                    if len(ex) < 5:
                        ex.append(("CH3", tag, v, [sorted(x) for x in X], s, g, sorted(Z), t))
                for s2 in S:
                    if t in C[s2]:
                        D_edges.append((s, s2, g))
            champs[(s, g)] = sorted(set(t for Z, t in opts))
    if rainbow_cycle(D_edges, S):
        cnt["D_rainbow_fail"] += 1
        if len(ex) < 5:
            ex.append(("D_rainbow", tag, v, [sorted(x) for x in X]))
    # CH4 for every g
    mu = {t: len([s for s in S if s != t and set(X[s]) & {h for h in range(m) if v[t][h] > 0}]) for t in range(n)}
    for g in P:
        Vg = [t for t in range(n) if v[t][g] > 0]
        if len(S) > sum(mu[t] for t in Vg):
            cnt["CH4_fail"] += 1
    # CH-R with every selection c(s, g) among the options (sampled) and assigned sources sigma(a)
    Pl = sorted(P)
    sel_lists = [champs[(s, g)] for s in S for g in Pl]
    sels = list(itertools.islice(itertools.product(*sel_lists), 64))
    for sel in sels:
        c = {}
        for (s, g), t in zip([(s, g) for s in S for g in Pl], sel):
            c[(s, g)] = t
        sig = {a: min(s for s in S if a in C[s]) for a in range(n)}
        V = {g: sorted({sig[c[(s, g)]] for s in S}) for g in Pl}
        edges = []
        for g in Pl:
            for h in Pl:
                if g == h:
                    continue
                for s2 in V[h]:
                    s1 = sig[c[(s2, g)]]
                    if s1 not in V[g]:
                        cnt["CHR_inneighbour_fail"] += 1
                    edges.append(((g, s1), (h, s2), (g, h)))
        # rainbow cycle in Gamma: distinct parts; colour = part of the tail vertex
        ge = [(u, w, u[0]) for u, w, _ in edges]
        if rainbow_cycle(ge, [(g, s) for g in Pl for s in V[g]]):
            cnt["CHR_rainbow_fail"] += 1
        p = len(Pl); ns = [len(V[g]) for g in Pl]
        if math.factorial(p - 1) * sum(ns) > math.prod(ns):
            cnt["packing_fail"] += 1
        cnt["CHR_tests"] += 1
    p = len(P)
    if k >= 2 and p * (p - 1) > math.e * max(k - 2, 0) * n:
        cnt["CHA_fail"] += 1
    if p >= math.e * d:
        cnt["CHB_fail"] += 1

def sprime(sigma, k):
    """S'(sigma, k) of charity.md §5, rebuilt from the text. Returns (v, m, X, k, d)."""
    goods = {}; agents = []  # agent: dict good -> value; bundle
    def newg(name):
        goods[name] = len(goods); return goods[name]
    pool = [newg(("g", t)) for t in range(1, sigma)]
    X = []; vals = []
    # sources
    src = []
    for j in range(sigma):
        xj = newg(("x", j)); xpj = newg(("xp", j))
        vals.append({xj: 2, xpj: 2}); X.append({xj, xpj}); src.append(len(vals) - 1)
    # champions c(g, j): hold y, value y 10, x_j 6, g 6
    champ = {}
    for j in range(sigma):
        for t, g in enumerate(pool):
            y = newg(("y", t, j))
            vals.append({y: 10, goods[("x", j)]: 6, g: 6}); X.append({y}); champ[(t, j)] = len(vals) - 1
    # trees: champions c(., j-1) are leaves below s_j; source has <= k-2 children, relay <= k-1, relays hold z valued 4
    for j in range(sigma):
        leaves = [champ[(t, (j - 1) % sigma)] for t in range(len(pool))]
        def build(parent, kids, cap):
            # attach `kids` under parent with at most cap children, inserting relays as needed
            if len(kids) <= cap:
                for c_ in kids:
                    vals[parent][next(iter(X[c_]))] = 5
                return
            groups = [kids[i::cap] for i in range(cap)]
            for grp in groups:
                if len(grp) == 1:
                    vals[parent][next(iter(X[grp[0]]))] = 5
                    continue
                z = newg(("z", len(goods)))
                vals.append({z: 4}); X.append({z}); r = len(vals) - 1
                vals[parent][z] = 5
                build(r, grp, k - 1)
        build(src[j], leaves, k - 2)
    n = len(vals); m = len(goods)
    v = [[vals[i].get(g, 0) for g in range(m)] for i in range(n)]
    kk = max(sum(1 for x in row if x > 0) for row in v)
    d = max(sum(1 for i in range(n) if v[i][g] > 0) for g in range(m))
    return v, m, X, kk, d

def states_run(N, nlo, nhi, mlo, mhi, kmax, seed):
    rng = random.Random(seed)
    keys = ["instances", "pareto_maxima", "states_with_pool", "max_pool", "charity_fail", "CH2_fail", "no_option_fail",
            "CH3_fail", "D_rainbow_fail", "CH4_fail", "CHR_tests", "CHR_inneighbour_fail", "CHR_rainbow_fail",
            "packing_fail", "CHA_fail", "CHB_fail"]
    cnt = {x: 0 for x in keys}; ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        v = [[0] * m for _ in range(n)]
        pool = list(range(m))
        for i in range(n):
            for g in rng.sample(pool, rng.randint(1, min(kmax, m))):
                v[i][g] = rng.randint(1, 12)
        k = max(sum(1 for x in r if x > 0) for r in v)
        d = max(sum(1 for i in range(n) if v[i][g] > 0) for g in range(m))
        cnt["instances"] += 1
        for X in pareto_maxima(v, m):
            cnt["pareto_maxima"] += 1
            check_state(v, X, m, k, d, cnt, ex, "random")
    print(json.dumps(dict(source=f"Pareto maxima, random N={N} n={nlo}..{nhi} m={mlo}..{mhi} k<={kmax} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

def family_run(smax, k):
    keys = ["instances", "pareto_maxima", "states_with_pool", "max_pool", "charity_fail", "CH2_fail", "no_option_fail",
            "CH3_fail", "D_rainbow_fail", "CH4_fail", "CHR_tests", "CHR_inneighbour_fail", "CHR_rainbow_fail",
            "packing_fail", "CHA_fail", "CHB_fail"]
    for sigma in range(2, smax + 1):
        cnt = {x: 0 for x in keys}; ex = []
        v, m, X, kk, d = sprime(sigma, k)
        cnt["instances"] = 1
        if not efx0(v, X):
            print("S' state not EFX0!", sigma, k)
        check_state(v, X, m, kk, d, cnt, ex, f"S'({sigma},{k})")
        if m <= 8:
            pms = pareto_maxima(v, m)
            cnt["pareto_maxima"] = len(pms)
            cnt["state_is_pareto_max"] = any(all(set(a) == set(b) for a, b in zip(Y, X)) for Y in pms)
        print(json.dumps(dict(source=f"S'({sigma},{k}) n={len(v)} m={m} k={kk} d={d} (state of §5, not re-proved Pareto-max here)", **cnt)))
        for e in ex:
            print("EXAMPLE", e)

if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "packing":
        packing_run(int(a[1]), int(a[2]))
    elif a[0] == "states":
        states_run(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), int(a[6]), int(a[7]))
    elif a[0] == "family":
        family_run(int(a[1]), int(a[2]))

def sfam(sigma, k):
    """S(sigma, k) of charity.md §4 (CH-D), rebuilt from the text."""
    goods = {}
    def newg(name):
        goods[name] = len(goods); return goods[name]
    pool = [newg(("g", t)) for t in range(1, sigma)]
    vals = []; X = []; src = []
    for j in range(sigma):
        xj = newg(("x", j)); xpj = newg(("xp", j))
        vals.append({xpj: 1}); X.append({xj, xpj}); src.append(len(vals) - 1)
    champ = {}
    for j in range(sigma):
        for t, g in enumerate(pool):
            y = newg(("y", t, j))
            vals.append({y: 10, goods[("x", j)]: 6, g: 6}); X.append({y}); champ[(t, j)] = len(vals) - 1
    for j in range(sigma):
        leaves = [champ[(t, (j - 1) % sigma)] for t in range(len(pool))]
        def build(parent, kids, cap):
            if len(kids) <= cap:
                for c_ in kids:
                    vals[parent][next(iter(X[c_]))] = 2
                return
            for grp in [kids[i::cap] for i in range(cap)]:
                if len(grp) == 1:
                    vals[parent][next(iter(X[grp[0]]))] = 2; continue
                z = newg(("z", len(goods)))
                vals.append({}); X.append({z}); r = len(vals) - 1
                vals[parent][z] = 2
                build(r, grp, k)
        build(src[j], leaves, k - 1)
    n = len(vals); m = len(goods)
    v = [[vals[i].get(g, 0) for g in range(m)] for i in range(n)]
    kk = max(sum(1 for x in row if x > 0) for row in v)
    d = max(sum(1 for i in range(n) if v[i][g] > 0) for g in range(m))
    return v, m, X, kk, d

if __name__ == "__main__" and sys.argv[1] == "sfam":
    keys = ["instances", "states_with_pool", "max_pool", "charity_fail", "CH2_fail", "no_option_fail", "CH3_fail",
            "D_rainbow_fail", "CH4_fail", "CHR_tests", "CHR_inneighbour_fail", "CHR_rainbow_fail", "packing_fail",
            "CHA_fail", "CHB_fail"]
    for sigma in range(2, int(sys.argv[2]) + 1):
        cnt = {x: 0 for x in keys}; ex = []
        v, m, X, kk, d = sfam(sigma, int(sys.argv[3]))
        cnt["instances"] = 1
        ok = efx0(v, X)
        check_state(v, X, m, kk, d, cnt, ex, f"S({sigma})")
        print(json.dumps(dict(source=f"S({sigma},{sys.argv[3]}) of CH-D n={len(v)} m={m} k={kk} d={d} EFX0={ok}", **cnt)))
        for e in ex:
            print("EXAMPLE", e)
