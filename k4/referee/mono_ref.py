#!/usr/bin/env python3
"""Referee check of Theorem M3 (monotone/k3.md, branch claude/monotone-k at 06e4b02). Own code, raw EFX0 for monotone
set functions (stored as tables over subsets of R_i). Nothing from monotone/ is run or imported.

1. Lemma S3, exhaustively: every strict total order of 2^R extending inclusion (r = 1, 2, 3), realized as ranks; the
   surrogate weights of the proof; every disjoint pair compared.
2. Random monotone instances with |R_i| <= 3 (n = 2..4, m <= 7): nondegenerate (strictly increasing, injective) and
   degenerate (ties, zeros); EFX0 existence by brute force; for nondegenerate ones, the EFX0 allocations of v and of
   the additive surrogate w coincide (Step 3).
3. The perturbation of Step 1 on degenerate instances: v + eps*w is nondegenerate with the same relevant sets.
4. The eight-good instance described in monotone/amm_check.py's docstring (Akrami et al. arXiv 2604.18216v4 §3.1.1, not
   read here [unverified]): monotone, relevant-goods counts, and the number of EFX0 allocations of u and of v.
"""
import itertools, random, sys, json
from fractions import Fraction

def subsets(R):
    R = sorted(R)
    for k in range(len(R) + 1):
        for c in itertools.combinations(R, k):
            yield frozenset(c)

class Mono:
    """v(S) = f(S ∩ R) from a table f on 2^R."""
    def __init__(self, R, f):
        self.R = frozenset(R); self.f = f
    def __call__(self, S):
        return self.f[frozenset(S) & self.R]

def linear_extensions(r):
    items = list(subsets(range(r)))
    out = []
    def rec(placed, order):
        if len(order) == len(items):
            out.append(list(order)); return
        for S in items:
            if S not in placed and all(T in placed for T in items if T < S):
                placed.add(S); order.append(S)
                rec(placed, order)
                order.pop(); placed.discard(S)
    rec(set(), [])
    return out

def surrogate(v, R):
    R = sorted(R)
    s = sorted(R, key=lambda g: -v({g}))
    w = {}
    if len(R) == 3:
        wt = (4, 3, 2) if v({s[0]}) < v({s[1], s[2]}) else (6, 3, 2)
        w = dict(zip(s, wt))
    elif len(R) == 2:
        w = dict(zip(s, (2, 1)))
    elif len(R) == 1:
        w = {s[0]: 1}
    return w

def s3_exhaustive():
    res = {}
    for r in (1, 2, 3):
        exts = linear_extensions(r)
        bad = 0
        for order in exts:
            f = {S: i for i, S in enumerate(order)}
            v = Mono(range(r), f)
            w = surrogate(v, range(r))
            for A in subsets(range(r)):
                for B in subsets(range(r)):
                    if A & B:
                        continue
                    if (v(A) < v(B)) != (sum(w[g] for g in A) < sum(w[g] for g in B)):
                        bad += 1
        res[r] = dict(orders=len(exts), mismatches=bad)
    print(json.dumps(dict(check="Lemma S3, every nondegenerate monotone order", **{f"r={r}": x for r, x in res.items()})))

def efx0(V, X):
    n = len(X)
    for i in range(n):
        t = V[i](X[i])
        for j in range(n):
            if i != j and X[j] and any(V[i](X[j] - {g}) > t for g in X[j]):
                return False
    return True

def all_efx0(V, n, m):
    out = []
    for f in itertools.product(range(n), repeat=m):
        X = [frozenset(g for g in range(m) if f[g] == i) for i in range(n)]
        if efx0(V, X):
            out.append(tuple(X))
    return out

def rand_mono(rng, R, degenerate):
    f = {}
    for S in subsets(R):
        if not S:
            f[S] = 0; continue
        base = max(f[S - {g}] for g in S)
        inc = rng.choice([0, 0, 1, 2, 3, 5]) if degenerate else rng.randint(1, 9) + rng.random()
        f[S] = base + inc
    return f

def relevant(V, m):
    return {g for g in range(m) if any(V(S | {g}) > V(S) for S in subsets(range(m)) if g not in S)}

def random_instances(N, seed):
    rng = random.Random(seed)
    c = dict(instances=0, nondeg=0, deg=0, no_efx0=0, step3_mismatch=0, perturb_tests=0, perturb_fail=0)
    for it in range(N):
        n = rng.randint(2, 4); m = rng.randint(n, 7)
        deg = it % 2 == 1
        Rs = [set(rng.sample(range(m), rng.randint(1, min(3, m)))) for _ in range(n)]
        fs = [rand_mono(rng, R, deg) for R in Rs]
        V = [Mono(R, f) for R, f in zip(Rs, fs)]
        c["instances"] += 1; c["deg" if deg else "nondeg"] += 1
        E = all_efx0(V, n, m)
        if not E:
            c["no_efx0"] += 1
        if not deg:
            W = []
            for R, v in zip(Rs, V):
                w = surrogate(v, R)
                W.append(lambda S, w=w: sum(w.get(g, 0) for g in S))
            if set(E) != set(all_efx0(W, n, m)):
                c["step3_mismatch"] += 1
        else:
            # Step 1: v + eps * sum 2^t over S ∩ R_i is nondegenerate on R_i, with relevant set R_i
            for R, v in zip(Rs, V):
                Rl = sorted(R)
                wt = {g: 2 ** (t + 1) for t, g in enumerate(Rl)}
                eps = Fraction(1, 1000)
                f2 = {S: Fraction(v(S)) + eps * sum(wt[g] for g in S) for S in subsets(R)}
                v2 = Mono(R, f2)
                c["perturb_tests"] += 1
                inj = len(set(f2.values())) == len(f2)
                mono = all(f2[S] < f2[S | {g}] for S in subsets(R) for g in R if g not in S)
                if not (inj and mono and relevant(v2, m) == set(R)):
                    c["perturb_fail"] += 1
    print(json.dumps(dict(check=f"random monotone 3-limited instances N={N} seed={seed}", **c)))

def amm():
    TYPE = ["A", "A", "B", "B", "C", "C", "x", "y"]
    def pair(t, s1, s2):
        U, V = [z for z in "ABC" if z != t]
        if s1 == s2:
            return 1
        k = {s1, s2}
        if k == {t, "y"}: return 6
        if k == {U, V}: return 5
        if k == {t, "x"}: return 4
        if k in ({U, "y"}, {V, "y"}): return 3
        if k in ({t, U}, {t, V}): return 2
        return 1
    def u(t, S):
        S = sorted(S)
        if not S: return 0
        if len(S) == 1: return 1
        return max(pair(t, TYPE[g], TYPE[h]) for g, h in itertools.combinations(S, 2))
    def vv(t, S):
        U, V = [z for z in "ABC" if z != t]
        types = [TYPE[g] for g in S]
        if U in types and V in types and "x" in types:
            return 7
        return u(t, S)
    out = {}
    for name, fn in (("u", u), ("v", vv)):
        tabs = []
        for t in "ABC":
            f = {S: fn(t, S) for S in subsets(range(8))}
            tabs.append(Mono(range(8), f))
        mono = all(tab(S) <= tab(S | {g}) for tab in tabs for S in subsets(range(8)) for g in range(8))
        rel = [len(relevant(tab, 8)) for tab in tabs]
        out[name] = dict(monotone=mono, relevant_goods=rel, efx0_allocations=len(all_efx0(tabs, 3, 8)))
    print(json.dumps(dict(check="AMM eight-good instance (from the docstring's description)", **out)))

if __name__ == "__main__":
    s3_exhaustive()
    random_instances(int(sys.argv[1]) if len(sys.argv) > 1 else 3000, 1)
    amm()
