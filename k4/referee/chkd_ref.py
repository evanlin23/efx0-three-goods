#!/usr/bin/env python3
"""Referee check of Theorem CH-KD (kgen/charity.md §8 at 1e986c6/0c85d91, branch claude/kgen-charity).
Written from §8's text; shares no code with kgen/charity/ (helper predicates reused from my own charity_ref.py).

1. The table: max p with p! <= d^(p-1), and min{(k-2)d - 1, that} for k = 4, 5, d <= 10.
2. The rules (R), (U0), (U1), (U2 along a shortest rainbow cycle of D over all options), run from the empty allocation
   (and from the S(sigma, k) / S'(sigma, k) states of §4-§5) on random instances, with random rule choices. Asserted:
   EFX0 after every rule; Step 1 (shortest rainbow cycle: distinct t's, vertex-disjoint envy paths) at every U2; the
   potential (welfare, -|P|) rises lexicographically at every rule; at the stop: acyclic envy graph, strong charity,
   parts 1-3 of the theorem, and Corollary CH-KD'.
"""
import itertools, math, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from charity_ref import val, efx0, envy_graph, reach, options, rainbow_cycle, sfam, sprime

def table():
    rows = {}
    for d in range(1, 11):
        p = 1
        while math.factorial(p + 1) <= d ** p:
            p += 1
        rows[d] = dict(packing=p, k4=min(2 * d - 1, p), k5=min(3 * d - 1, p))
    return rows

def sources(v, X):
    G = envy_graph(v, X); n = len(X)
    return [s for s in range(n) if not any(s in G[i] for i in range(n))], G

def find_cycle(G, n):
    color = {}; parent = {}
    def dfs(u):
        color[u] = 1
        for w in G[u]:
            if color.get(w) == 1:
                cyc = [w]; x = u
                while x != w:
                    cyc.append(x); x = parent[x]
                return cyc[::-1]
            if w not in color:
                parent[w] = u
                r = dfs(w)
                if r:
                    return r
        color[u] = 2
        return None
    for s in range(n):
        if s not in color:
            r = dfs(s)
            if r:
                return r
    return None

def path(G, s, t):
    prev = {s: None}; q = [s]
    while q:
        u = q.pop(0)
        if u == t:
            break
        for w in G[u]:
            if w not in prev:
                prev[w] = u; q.append(w)
    p = [t]
    while prev[p[-1]] is not None:
        p.append(prev[p[-1]])
    return p[::-1]

def shortest_rainbow(v, X, P, S, G):
    """edges s ->_g s' with an option (Z, t) of X_s ∪ {g}, t ∈ C(s'); return a shortest rainbow cycle with its options."""
    C = {s: reach(G, s) for s in S}
    edges = {}
    for s in S:
        for g in P:
            for Z, t in options(v, X, set(X[s]) | {g}):
                for s2 in S:
                    if t in C[s2]:
                        edges.setdefault((s, s2), []).append((g, Z, t))
    best = None
    for L in range(1, len(S) + 1):
        for seq in itertools.permutations(S, L):
            if seq[0] != min(seq):
                continue
            lists = [edges.get((seq[i], seq[(i + 1) % L]), []) for i in range(L)]
            if any(not l for l in lists):
                continue
            for choice in itertools.product(*lists):
                if len({c[0] for c in choice}) == L:
                    return seq, choice
    return None

def run_rules(v, X, rng, st, ex):
    n = len(X); m = len(v[0])
    X = [set(x) for x in X]
    def pot(X):
        P = set(range(m)) - set().union(*X)
        return (sum(val(v, i, X[i]) for i in range(n)), -len(P))
    for step in range(5000):
        P = set(range(m)) - set().union(*X)
        S, G = sources(v, X)
        before = pot(X)
        moves = []
        cyc = find_cycle(G, n)
        if cyc:
            moves.append("R")
        u0 = [(g, j) for g in P for j in range(n) if efx0(v, [x | {g} if a == j else x for a, x in enumerate(X)])]
        if u0:
            moves.append("U0")
        if P and any(val(v, i, P) > val(v, i, X[i]) for i in range(n)):
            moves.append("U1")
        rc = None
        if not cyc and P:
            rc = shortest_rainbow(v, X, P, S, G)
            if rc:
                moves.append("U2")
        if not moves:
            return X, st
        mv = rng.choice(moves)
        if mv == "R":
            Y = list(X)
            for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                Y[a] = X[b]
            X = [set(y) for y in Y]
        elif mv == "U0":
            g, j = rng.choice(u0); X[j] = X[j] | {g}
        elif mv == "U1":
            opts = options(v, X, P)
            Z, i = rng.choice(opts)
            X[i] = set(Z)
        else:
            seq, choice = rc
            L = len(seq)
            ts = [choice[i][2] for i in range(L)]           # t_{i+1} champions X_{s_i} ∪ g_i, t_{i+1} ∈ C(s_{i+1})
            paths = [path(G, seq[(i + 1) % L], ts[i]) for i in range(L)]
            st["u2"] += 1
            flat = [x for p in paths for x in p]
            if len(set(ts)) != L or len(set(flat)) != len(flat):
                st["step1_fail"] += 1
                if len(ex) < 4:
                    ex.append(("step1", v, [sorted(x) for x in X], seq))
                return X, st
            Y = [set(x) for x in X]
            for i in range(L):
                p = paths[i]
                for a, b in zip(p, p[1:]):
                    Y[a] = set(X[b])
                g, Z, t = choice[i]
                Y[ts[i]] = set(Z)
            X = Y
        st["rules"] += 1; st[mv] += 1
        if not efx0(v, X):
            st["efx0_fail"] += 1
            if len(ex) < 4:
                ex.append(("efx0", mv, v))
            return X, st
        if not pot(X) > before:
            st["potential_fail"] += 1
            if len(ex) < 4:
                ex.append(("potential", mv, v))
    st["no_stop"] += 1
    return X, st

def check_stop(v, X, st, ex, tag):
    n = len(X); m = len(v[0])
    P = set(range(m)) - set().union(*X)
    S, G = sources(v, X)
    k = max(sum(1 for x in row if x > 0) for row in v)
    d = max((sum(1 for i in range(n) if v[i][g] > 0) for g in range(m)), default=0)
    st["stops"] += 1
    if find_cycle(G, n):
        st["stop_cyclic"] += 1
    if any(val(v, i, P) > val(v, i, X[i]) for i in range(n)):
        st["stop_charity_fail"] += 1
    p = len(P)
    st["max_pool"] = max(st["max_pool"], p)
    if p:
        st["stops_with_pool"] += 1
        bound2 = (k - 2) * min(sum(1 for i in range(n) if v[i][g] > 0) for g in P) - 1
        ok = k >= 3 and p <= bound2 and math.factorial(p) <= max(d, 1) ** (p - 1)
        # Corollary CH-KD' for every d' >= 1
        for dd in range(1, d + 1):
            low = [g for g in P if sum(1 for i in range(n) if v[i][g] > 0) <= dd]
            q = len(low)
            if q and math.factorial(q) > dd ** (q - 1):
                ok = False
        if not ok:
            st["bound_fail"] += 1
            if len(ex) < 4:
                ex.append(("bound", tag, p, k, d))

if __name__ == "__main__":
    print(json.dumps(dict(table=table())))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    st = {x: 0 for x in ["instances", "rules", "R", "U0", "U1", "U2", "u2", "step1_fail", "efx0_fail", "potential_fail",
                         "no_stop", "stops", "stop_cyclic", "stop_charity_fail", "stops_with_pool", "max_pool",
                         "bound_fail"]}
    ex = []
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    for _ in range(N):
        n = rng.randint(2, 5); m = rng.randint(2, 8); kmax = rng.choice([2, 3, 4])
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g in rng.sample(range(m), rng.randint(1, min(kmax, m))):
                v[i][g] = rng.randint(1, 12)
        st["instances"] += 1
        X, st = run_rules(v, [set() for _ in range(n)], rng, st, ex)
        check_stop(v, X, st, ex, "random")
    # the stranded families: their states are stopping states (CH-D) or Pareto maxima (CH-E); run the rules from them
    for sigma in range(2, 5):
        for k in (3, 4):
            for fam in (sfam, sprime):
                v, m, X0, kk, d = fam(sigma, k)
                st["instances"] += 1
                X, st = run_rules(v, X0, rng, st, ex)
                check_stop(v, X, st, ex, f"{fam.__name__}({sigma},{k})")
    print(json.dumps(st))
    for e in ex:
        print("EXAMPLE", e)
