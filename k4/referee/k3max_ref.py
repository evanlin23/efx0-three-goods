#!/usr/bin/env python3
"""Referee spot check of ksens's exhaustive k = 3 one-chain claim (k4/ksens.md §8, branch claude/k4-ksens at 08883f6).
Own code: hypergraph enumeration, type representatives, SD, official chains (t >= 1, nonempty passed bases, sets in the
junk and the receivers' relevant goods, strict gains), one-absorber completions by brute force, raw EFX0. Nothing from
k4/ksens/ is run.

Claim: for every connected agent-good hypergraph with n agents each valuing <= 3 goods, every strict profile and every
SD start, the picks or the bases after one chain have a one-absorber completion.
Strict profiles are covered exactly by order-type representatives (every comparison is between disjoint subsets of one
agent's <= 3 goods): per agent a ranking, and for 3 goods (4,3,2) or (6,3,2) (top below / above the other two).

n = 3: every hypergraph (up to isomorphism; the note says 52) and every type profile. n = 4: a random sample.
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, efx0, rel, sd

def hypergraphs(n, maxdeg=3):
    """connected hypergraphs: goods = nonempty agent sets (multiset), every agent in 1..maxdeg goods; up to agent
    permutation (and good relabelling). Canonical form: min over agent permutations of the sorted good list."""
    seen = set(); out = []
    subsets = [frozenset(c) for r in range(1, n + 1) for c in itertools.combinations(range(n), r)]
    def connected(goods):
        adj = {i: set() for i in range(n)}
        for g in goods:
            for a in g:
                adj[a] |= g
        comp = {0}; st = [0]
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in comp:
                    comp.add(w); st.append(w)
        return len(comp) == n
    def canon(goods):
        best = None
        for p in itertools.permutations(range(n)):
            t = tuple(sorted(tuple(sorted(p[a] for a in g)) for g in goods))
            if best is None or t < best:
                best = t
        return best
    def rec(goods, deg, start):
        if goods and all(d >= 1 for d in deg) and connected(goods):
            cf = canon(goods)
            if cf not in seen:
                seen.add(cf); out.append([set(g) for g in cf])
        for idx in range(start, len(subsets)):
            g = subsets[idx]
            if all(deg[a] < maxdeg for a in g):
                d2 = list(deg)
                for a in g:
                    d2[a] += 1
                rec(goods + [g], d2, idx)
    rec([], [0] * n, 0)
    return out

def type_reps(r):
    base = {1: [(1,)], 2: [(2, 1)], 3: [(4, 3, 2), (6, 3, 2)]}[r]
    out = []
    for b in base:
        for perm in itertools.permutations(range(r)):
            out.append(tuple(b[perm[i]] for i in range(r)))
    return sorted(set(out))

def chain_states(v, B, J):
    n = len(B); R = [rel(v, i) for i in range(n)]
    def subsets(S):
        S = sorted(S)
        for k in range(len(S) + 1):
            for c in itertools.combinations(S, k):
                yield set(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            if any(not B[x] for x in seq[:-1]):
                continue
            def rec(i, used, nb):
                if i > t:
                    for H0 in subsets(((J - used) | B[seq[-1]]) & R[seq[0]]):
                        if H0 and val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            c = [set(b) for b in nb]; c[seq[0]] = set(H0); yield c
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((J - used) & R[xi]):
                    if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                        c = [set(b) for b in nb]; c[xi] = B[pr] | Hi
                        yield from rec(i + 1, used | Hi, c)
            yield from rec(1, set(), [set(b) for b in B])

def one_absorber(v, B):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    for f in itertools.product(range(n), repeat=len(J)):
        cnt = [0] * n
        for a in f:
            cnt[a] += 1
        if sum(1 for x in cnt if x >= 2) > 1:
            continue
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            X[a].add(g)
        if efx0(v, X):
            return True
    return False

def check_profile(v, n, c, ex):
    m = len(v[0]); seen = set()
    for o in itertools.permutations(range(n)):
        yd = sd(v, o); Y = tuple(yd[i] for i in range(n))
        if Y in seen:
            continue
        seen.add(Y); c["starts"] += 1
        B = [({y} if y is not None else set()) for y in Y]
        if one_absorber(v, B):
            continue
        c["need_chain"] += 1
        J = set(range(m)) - set().union(*B)
        if not any(one_absorber(v, s) for s in chain_states(v, B, J)):
            c["FAIL"] += 1
            if len(ex) < 5:
                ex.append((v, Y))

def build(H, n, reps):
    m = len(H)
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        gs = [g for g in range(m) if i in H[g]]
        for g, x in zip(gs, reps[i]):
            v[i][g] = x
    return v

def exhaustive(n):
    from collections import Counter
    Hs = hypergraphs(n)
    c = Counter(); ex = []
    c["hypergraphs"] = len(Hs)
    for H in Hs:
        degs = [sum(1 for g in H if i in g) for i in range(n)]
        tag = "m>=n" if len(H) >= n else "m<n"
        c["hypergraphs_" + tag] += 1
        for reps in itertools.product(*[type_reps(d) for d in degs]):
            cc = Counter()
            check_profile(build(H, n, reps), n, cc, ex)
            c["profiles_" + tag] += 1
            for k2, x in cc.items():
                c[k2 + "_" + tag] += x
    print(json.dumps(dict(source=f"k = 3 one chain, exhaustive n = {n}", **dict(c))))
    for e in ex:
        print("EXAMPLE", e)

def sample(n, N, seed):
    from collections import Counter
    rng = random.Random(seed)
    Hs = hypergraphs(n)
    c = Counter(); ex = []
    c["hypergraphs"] = len(Hs)
    for _ in range(N):
        H = rng.choice(Hs)
        degs = [sum(1 for g in H if i in g) for i in range(n)]
        reps = [rng.choice(type_reps(d)) for d in degs]
        c["profiles"] += 1
        check_profile(build(H, n, reps), n, c, ex)
    print(json.dumps(dict(source=f"k = 3 one chain, sample n = {n} N={N} seed={seed}", **dict(c))))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    if sys.argv[1] == "ex":
        exhaustive(int(sys.argv[2]))
    else:
        sample(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
