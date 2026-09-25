"""Independent brute-force check of the counterexamples to conjecture GM4 (k4/gm4.md §2).  Plain Python, raw
definitions only; shares no code with gm4_explore.c, gm4_fast.c or gm4_analyze.py.

For each instance (explicit integer values; every agent's subset sums on its relevant goods are distinct):
  1. it is a k = 4 core: every agent has 3 or 4 relevant goods, is strictly balanced (top < sum of the others), has at
     most d - 2 private goods (two only with p + q < s + t), every good is relevant to someone, and the core is
     connected;
  2. the stated partial allocation Y is junk-free and EFX0: v_i(Y_i) >= v_i(Y_j - {g}) for all i != j, g in Y_j
     (every good may be removed, including goods worth 0 to i);
  3. Y maximizes the level sum  sum_i #{T subset R_i : v_i(T) < v_i(Y_i)}  over ALL junk-free EFX0 partial
     allocations (every good to the pool or to one of its valuers: all of them are enumerated);
  4. [GM4] no placement of the pool: no assignment of the pool goods to agents (any agents, valued or not) gives a
     complete EFX0 allocation containing Y (so in particular no junk placement);
  5. [dead end] no complete EFX0 allocation X has v_i(X_i) >= v_i(Y_i) for every i (all n^m allocations);
  6. it lists every level-sum maximum and says which admit a placement, and counts the complete EFX0 allocations;
  7. [LS4+ fails under some choices] Y is reached from the empty allocation by single-agent rebundles (M1 moves of
     k4/local_search4.md §2: one agent h replaces Y_h by Z subset R_h cap (Y_h cup U) with v_h(Z) > v_h(Y_h), result
     EFX0), found by breadth-first search; M1 has priority in LS4 and LS4+, so this path is a valid run of both, and at
     Y no M1, R, X or coalition move applies (Y is a maximum and every such move raises the level sum; the envy graph
     is acyclic) and no placement exists, so LS4+_n stops there with failure.
Instances of kind GM4S (a maximum that admits a placement but no single dump) replace 4, 5 and 7 by:
  4'. the pool is nonempty, no bundle of Y is empty, and for EVERY agent s, adding all of the pool to Y_s does not
      give an EFX0 allocation (so neither the empty-bundle dump nor any single dump works), and
  5'. some assignment of the pool goods to agents not valuing them is EFX0 (printed).
Instances of kind H1 (a maximum where a source that envies someone fails the single dump; another source's works)
replace 4-7 by: 4''. the pool is nonempty; source s envies some agent and adding the pool to Y_s is not EFX0 (or s
values a pool good); and for some other source t, adding the pool to Y_t is EFX0 with t valuing no pool good.
Instances of kind ALL (the existence form GM4E fails: EVERY maximum lacks a placement) replace 4-7 by:
  4'''. every level-sum maximum has a nonempty pool and no assignment of its pool to any agents is EFX0; and
  5'''. complete EFX0 allocations exist, and the largest level sum of one (of its valued part) is below the maximum.
Instances of kind POT (a maximum of the convex potentials sum_i 2^(l_i) and leximax, i.e. the level vector sorted in
decreasing order compared lexicographically, that admits no placement) replace 3-7 by:
  3''''. Y maximizes sum_i 2^(l_i), and Y is leximax-maximal, over all junk-free EFX0 partial allocations;
  4''''. no assignment of the pool of Y to any agents is EFX0; the other maxima of each potential are listed.
Exit status 0 iff every claim holds for every instance.
Usage: python3 k4/gm4_counterexample.py
"""
import itertools, sys

# label, (goods of agent i with values), stated maximum Y (list of bundles), kind
INSTANCES = [
    ("A: pure n=4, m=7",
     [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 2, 3: 7, 5: 8, 6: 4}, {3: 6, 4: 3, 5: 4, 6: 8}],
     [{0, 2}, {1, 4}, {5}, {6}], 'GM4'),
    ("B: pure n=4, m=7",
     [{0: 4, 2: 2, 5: 8, 6: 5}, {1: 3, 4: 6, 5: 8, 6: 10}, {2: 4, 3: 5, 4: 2, 6: 8}, {3: 5, 4: 4, 5: 8, 6: 2}],
     [{0, 2}, {1, 4}, {6}, {5}], 'GM4'),
    ("C: pure n=4, m=7",
     [{0: 2, 2: 4, 5: 8, 6: 3}, {1: 2, 2: 4, 3: 7, 6: 10}, {1: 1, 4: 6, 5: 4, 6: 8}, {3: 8, 4: 6, 5: 10, 6: 3}],
     [{0, 2}, {6}, {1, 4}, {5}], 'GM4'),
    ("D: pure n=4, m=7",
     [{0: 10, 2: 7, 4: 2, 5: 6}, {0: 8, 3: 4, 4: 1, 6: 6}, {1: 1, 2: 4, 5: 8, 6: 6}, {1: 3, 3: 6, 5: 10, 6: 2}],
     [{2, 4}, {0}, {5}, {1, 3}], 'GM4'),
    ("E: n=4, m=7, two 4-good agents",
     [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}],
     [{0, 4}, {1, 3}, {2}, {5}], 'GM4'),
    ("F: n=4, m=7, two 4-good agents",
     [{0: 3, 2: 8, 4: 4, 5: 6}, {1: 3, 3: 6, 5: 10, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}],
     [{0, 4}, {1, 3}, {2}, {5}], 'GM4'),
    ("S: n=4, m=6, one 4-good agent (GM4S only: a split placement is needed)",
     [{0: 1, 2: 6, 3: 4, 4: 8}, {1: 2, 2: 3, 5: 4}, {1: 3, 4: 4, 5: 2}, {3: 3, 4: 2, 5: 4}],
     [{4}, {5}, {1}, {3}], 'GM4S'),
    ("H: n=4, m=6, one 4-good agent (H1 fails: an envier source cannot take the pool)",
     [{0: 4, 1: 2, 4: 8, 5: 7}, {2: 4, 3: 2, 5: 3}, {2: 4, 4: 2, 5: 3}, {3: 3, 4: 4, 5: 2}],
     [{4}, {5}, {2}, {3}], 'H1'),
    ("G: pure n=4, m=7 (GM4E fails: no maximum admits a placement; instance A with agent 2's type changed)",
     [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 3, 3: 6, 5: 8, 6: 4}, {3: 6, 4: 3, 5: 4, 6: 8}],
     [{0, 2}, {1, 4}, {5}, {6}], 'ALL'),
    ("P: pure n=4, m=7 (a maximum of sum 2^l and of leximax without placement)",
     [{0: 1, 2: 6, 5: 8, 6: 4}, {1: 1, 4: 6, 5: 4, 6: 8}, {2: 4, 3: 5, 4: 2, 6: 8}, {3: 5, 4: 4, 5: 8, 6: 2}],
     [{0, 2}, {1, 4}, {6}, {5}], 'POT'),
]

def v(vals, i, S):
    return sum(vals[i].get(g, 0) for g in S)

def efx0(vals, X):
    n = len(X)
    for i in range(n):
        own = v(vals, i, X[i])
        for j in range(n):
            if j == i: continue
            for g in X[j]:
                if v(vals, i, X[j] - {g}) > own: return False
    return True

def level(vals, i, S):
    R = sorted(vals[i])
    x = v(vals, i, S)
    return sum(1 for k in range(len(R) + 1) for T in itertools.combinations(R, k) if v(vals, i, T) < x)

def m1_path(vals, Y, n, m):
    """shortest sequence of M1 moves from the empty allocation to Y (breadth-first), or [] if none"""
    R = [set(d) for d in vals]
    key = lambda X: tuple(frozenset(b) for b in X)
    start = key([set() for _ in range(n)]); prev = {start: None}; queue = [start]; target = key(Y)
    while queue and target not in prev:
        nxt = []
        for S in queue:
            X = [set(b) for b in S]; P = set(range(m)) - set().union(*X)
            for h in range(n):
                cand = sorted(R[h] & (X[h] | P))
                for k in range(1, len(cand) + 1):
                    for Z in itertools.combinations(cand, k):
                        if v(vals, h, Z) <= v(vals, h, X[h]): continue
                        X2 = [set(b) for b in X]; X2[h] = set(Z)
                        if not efx0(vals, X2): continue
                        K = key(X2)
                        if K not in prev: prev[K] = S; nxt.append(K)
        queue = nxt
    path, K = [], (target if target in prev else None)
    while K is not None: path.append(K); K = prev[K]
    return list(reversed(path))

def check(label, vals, Y, kind):
    n = len(vals); m = 1 + max(g for d in vals for g in d)
    Y = [set(b) for b in Y]
    ok = True
    def claim(c, text):
        nonlocal ok
        print(f"  [{'ok' if c else 'FAILED'}] {text}")
        ok &= bool(c)
    print(label)
    R = [set(d) for d in vals]
    deg = [sum(g in R[i] for i in range(n)) for g in range(m)]
    core = all(len(R[i]) in (3, 4) for i in range(n)) and all(d >= 1 for d in deg)
    for i in range(n):
        top = max(vals[i].values()); core &= top < sum(vals[i].values()) - top
        sums = [v(vals, i, T) for k in range(1, len(R[i]) + 1) for T in itertools.combinations(sorted(R[i]), k)]
        core &= len(set(sums)) == len(sums)
        priv = [g for g in R[i] if deg[g] == 1]
        core &= len(priv) <= len(R[i]) - 2
        if len(priv) == 2: core &= v(vals, i, priv) < v(vals, i, R[i] - set(priv))
    seen, todo = {0}, [0]                       # connectivity of the agent-good incidence graph
    while todo:
        a = todo.pop()
        for b in range(n):
            if b not in seen and R[a] & R[b]: seen.add(b); todo.append(b)
    core &= len(seen) == n
    claim(core, "k = 4 core (degrees 3-4, strictly balanced, strict, private-good rule, every good valued, connected)")
    claim(all(Y[i] <= R[i] for i in range(n)) and efx0(vals, Y), "Y is junk-free and EFX0")
    U = set(range(m)) - set().union(*Y)
    ly = sum(level(vals, i, Y[i]) for i in range(n))
    if kind == 'POT':
        allst = []
        for owners in itertools.product(*[[None] + [i for i in range(n) if g in R[i]] for g in range(m)]):
            X = [set() for _ in range(n)]
            for g, i in enumerate(owners):
                if i is not None: X[i].add(g)
            if efx0(vals, X): allst.append((X, [level(vals, i, X[i]) for i in range(n)]))
        def placeable(Z):
            P = sorted(set(range(m)) - set().union(*Z))
            for asg in itertools.product(range(n), repeat=len(P)):
                X = [set(b) for b in Z]
                for u, j in zip(P, asg): X[j].add(u)
                if efx0(vals, X): return True
            return False
        for name, f in (('sum 2^l', lambda l: sum(2 ** x for x in l)), ('leximax', lambda l: sorted(l, reverse=True))):
            best = max(f(l) for X, l in allst)
            mx = [X for X, l in allst if f(l) == best]
            claim(Y in mx, f"Y maximizes {name} over all junk-free EFX0 partial allocations ({len(mx)} maxima)")
            for Z in mx: print(f"    {[sorted(b) for b in Z]} pool {sorted(set(range(m)) - set().union(*Z))} placement: {placeable(Z)}")
        claim(U and not placeable(Y), f"pool {sorted(U)} of Y is nonempty and no assignment of it to any agents is EFX0")
        return ok
    best, maxima = -1, []
    for owners in itertools.product(*[[None] + [i for i in range(n) if g in R[i]] for g in range(m)]):
        X = [set() for _ in range(n)]
        for g, i in enumerate(owners):
            if i is not None: X[i].add(g)
        if not efx0(vals, X): continue
        s = sum(level(vals, i, X[i]) for i in range(n))
        if s > best: best, maxima = s, []
        if s == best: maxima.append(X)
    claim(ly == best and Y in maxima, f"Y maximizes the level sum over all junk-free EFX0 partial allocations ({ly} = {best})")
    def placeable(Z):
        P = sorted(set(range(m)) - set().union(*Z))
        for asg in itertools.product(range(n), repeat=len(P)):
            X = [set(b) for b in Z]
            for u, j in zip(P, asg): X[j].add(u)
            if efx0(vals, X): return True
        return False
    if kind == 'ALL':
        claim(all(not placeable(Z) for Z in maxima), f"none of the {len(maxima)} level-sum maxima admits a placement (GM4E fails)")
        for Z in maxima:
            print(f"    {[sorted(b) for b in Z]} pool {sorted(set(range(m)) - set().union(*Z))} levels {[level(vals, i, Z[i]) for i in range(n)]}")
        comp = []
        for owners in itertools.product(range(n), repeat=m):
            X = [set(g for g in range(m) if owners[g] == i) for i in range(n)]
            if efx0(vals, X): comp.append(X)
        bestc = max(sum(level(vals, i, X[i] & R[i]) for i in range(n)) for X in comp) if comp else -1
        claim(comp and bestc < best, f"{len(comp)} complete EFX0 allocations exist; their largest level sum is {bestc} < {best}")
        path = m1_path(vals, Y, n, m)
        claim(path, f"Y is reached from the empty allocation by {len(path) - 1} M1 moves")
        for K in path: print("    ", [sorted(b) for b in K])
        return ok
    if kind == 'H1':
        sig = [v(vals, i, Y[i]) for i in range(n)]
        src = [s_ for s_ in range(n) if all(v(vals, i, Y[s_]) <= sig[i] for i in range(n) if i != s_)]
        envier = {s_ for s_ in src if any(v(vals, s_, Y[j]) > sig[s_] for j in range(n) if j != s_)}
        dump = {s_ for s_ in src if not (R[s_] & U) and efx0(vals, [Y[i] | U if i == s_ else Y[i] for i in range(n)])}
        claim(U and envier - dump, f"pool {sorted(U)}; sources {src}; enviers {sorted(envier)}; single dump works at {sorted(dump)}: an envier source fails")
        claim(dump, "some source admits the single dump (GM4S holds here)")
        return ok
    if kind == 'GM4S':
        single = [s_ for s_ in range(n) if efx0(vals, [Y[i] | U if i == s_ else Y[i] for i in range(n)])]
        claim(U and all(Y) and not single, f"pool {sorted(U)} nonempty, no empty bundle, and no agent can take the whole pool (GM4S fails)")
        P = sorted(U); found = []
        for asg in itertools.product(*[[j for j in range(n) if u not in R[j]] for u in P]):
            X = [set(b) for b in Y]
            for u, j in zip(P, asg): X[j].add(u)
            if efx0(vals, X): found.append(dict(zip(P, asg)))
        claim(found, f"junk placements (pool good -> agent) that are EFX0: {found}")
        return ok
    claim(U and not placeable(Y), f"pool {sorted(U)} is nonempty and no assignment of it to any agents is EFX0 (GM4 fails)")
    comp = []
    for owners in itertools.product(range(n), repeat=m):
        X = [set(g for g in range(m) if owners[g] == i) for i in range(n)]
        if efx0(vals, X): comp.append(X)
    dom = [X for X in comp if all(v(vals, i, X[i]) >= v(vals, i, Y[i]) for i in range(n))]
    claim(not dom, f"dead end: none of the {len(comp)} complete EFX0 allocations gives every agent at least v_i(Y_i)")
    print(f"  level-sum maxima: {len(maxima)}; with a placement: {sum(placeable(Z) for Z in maxima)}")
    for Z in maxima:
        print(f"    {[sorted(b) for b in Z]} pool {sorted(set(range(m)) - set().union(*Z))} placement: {placeable(Z)}")
    bestc = max(sum(level(vals, i, X[i] & R[i]) for i in range(n)) for X in comp)
    key = lambda X: tuple(frozenset(b) for b in X)
    start = key([set() for _ in range(n)]); prev = {start: None}; queue = [start]; target = key(Y)
    while queue and target not in prev:
        nxt = []
        for S in queue:
            X = [set(b) for b in S]; P = set(range(m)) - set().union(*X)
            for h in range(n):
                cand = sorted(R[h] & (X[h] | P))
                for k in range(1, len(cand) + 1):
                    for Z in itertools.combinations(cand, k):
                        if v(vals, h, Z) <= v(vals, h, X[h]): continue
                        X2 = [set(b) for b in X]; X2[h] = set(Z)
                        if not efx0(vals, X2): continue
                        K = key(X2)
                        if K not in prev: prev[K] = S; nxt.append(K)
        queue = nxt
    path = []
    K = target if target in prev else None
    while K is not None: path.append(K); K = prev[K]
    envy = {(i, j) for i in range(n) for j in range(n) if i != j and v(vals, i, Y[j]) > v(vals, i, Y[i])}
    def cyc():
        col = {}
        def dfs(a):
            col[a] = 1
            for (x, y) in envy:
                if x == a and (col.get(y) == 1 or (y not in col and dfs(y))): return True
            col[a] = 2; return False
        return any(a not in col and dfs(a) for a in range(n))
    claim(path and not cyc(), f"Y is reached from the empty allocation by {len(path) - 1} M1 moves, and its envy graph is acyclic (LS4+_n can stop at Y with failure)")
    for K in reversed(path): print("    ", [sorted(b) for b in K])
    print(f"  largest level sum of a complete EFX0 allocation: {bestc} (maximum over partial ones: {best})")
    return ok

if __name__ == '__main__':
    allok = True
    for label, vals, Y, kind in INSTANCES:
        allok &= check(label, vals, Y, kind)
    print("ALL CLAIMS HOLD" if allok else "SOME CLAIM FAILED")
    sys.exit(0 if allok else 1)
