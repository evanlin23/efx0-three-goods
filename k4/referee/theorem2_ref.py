#!/usr/bin/env python3
"""Referee check of Theorem 2 (kgen/n3.md §9 at 418f876, branch claude/kgen-n3): two-agent OC1 (t >= 0) from either
order, every k, any values (ties and zeros). Written from the text; shares no code with kgen/.

1. Fact L (LPT is EFX0 for the cutter both ways), Lemma M, and the Tops Lemma (n = 2, 3, 4), on random values with
   ties and zeros, against the raw EFX0 definition.
2. The construction of the proof (cases 0, 1, 2), run on every valuation in small exhaustive grids and on random
   instances, from both orders. Its output must be EFX0 and must be an OC1(t >= 0) witness, checked with my own test:
   either the picks have a one-absorber completion equal to the output, or the output is a one-absorber completion of
   the bases after a valid chain (t = 0: a set H0 ⊆ J ∩ R_x added to x's pick with strict gain; t = 1: x0 takes
   H0 ⊆ (J ∪ B_x1) ∩ R_x0 worth more than its pick, x1 takes B_x0 ∪ H1, H1 ⊆ J ∩ R_x1, strict gain; the passed base
   B_x0 nonempty).
3. Independently of the construction, brute-force OC1(t >= 0) (every chain with t <= 1, every completion) on small
   instances.
"""
import itertools, random, sys, json

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx0(v, X):
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and X[j]:
                tot = val(v, i, X[j])
                if any(tot - v[i][h] > t for h in X[j]):
                    return False
    return True

def sd(v, order):
    m = len(v[0]); G = set(range(m)); y = {}
    for i in order:
        R = sorted((g for g in G if v[i][g] > 0), key=lambda g: (-v[i][g], g))
        y[i] = R[0] if R else None
        if R:
            G.discard(R[0])
    return y

def lpt(v, c, goods):
    P, Q = set(), set()
    for g in sorted(goods, key=lambda g: (-v[c][g], g)):
        (P if val(v, c, P) <= val(v, c, Q) else Q).add(g)
    return P, Q

def construction(v, a, b):
    """the proof of Theorem 2 for the order (a, b); returns X (dict agent -> set)."""
    m = len(v[0]); M = set(range(m))
    y = sd(v, [a, b]); ya, yb = y[a], y[b]
    if not any(v[a][g] > 0 for g in M):
        return {a: set(), b: set(M)}
    if not any(v[b][g] > 0 for g in M):
        return {a: set(M), b: set()}
    if yb is None:            # b values only y_a
        if v[a][ya] >= val(v, a, M - {ya}):
            return {a: {ya}, b: M - {ya}}
        return {a: M - {ya}, b: {ya}}
    def choose_and_m(P, Q):
        Sa, Sb = (P, Q) if val(v, a, P) >= val(v, a, Q) else (Q, P)
        Wz = {g for g in Sa if v[a][g] == 0}
        return Sa - Wz, Sb | Wz
    if v[b][ya] > v[b][yb]:
        P, Q = lpt(v, b, M)
        Xa, Xb = choose_and_m(P, Q)
        return {a: Xa, b: Xb}
    J = M - {ya, yb}
    P, Q = lpt(v, b, J)
    Sa, Sb = choose_and_m(P, Q)
    return {a: Sa | {ya}, b: Sb | {yb}}

def is_oc1_witness(v, a, b, X):
    """is X an OC1 (t >= 0) witness for the order (a, b)? My own test from the definitions."""
    m = len(v[0]); y = sd(v, [a, b])
    base = {i: ({y[i]} if y[i] is not None else set()) for i in (a, b)}
    J = set(range(m)) - base[a] - base[b]
    R = {i: {g for g in range(m) if v[i][g] > 0} for i in (a, b)}
    def one_abs(B):
        return all(B[i] <= X[i] for i in (a, b)) and sum(1 for i in (a, b) if len(X[i] - B[i]) >= 2) <= 1
    if not efx0(v, [X[0], X[1]]) or X[a] | X[b] != set(range(m)) or X[a] & X[b]:
        return False
    if one_abs(base):
        return True
    for x0 in (a, b):
        x1 = b if x0 == a else a
        # t = 0: H0 = X_x0 ∩ J ∩ R_x0 (largest choice; Lemma R of kgen/n3.md says largest is WLOG, re-derived)
        H0 = X[x0] & J & R[x0]
        if H0 and base[x0] <= X[x0]:
            B = dict(base); B[x0] = base[x0] | H0
            if one_abs(B):
                return True
        # t = 1: x0 -> x1; x0's base passed (nonempty); x0 takes H0 ⊆ (J ∪ B_x1) ∩ R_x0
        if base[x0] and base[x0] <= X[x1]:
            H0 = X[x0] & (J | base[x1]) & R[x0]
            H1 = X[x1] & J & R[x1]
            if val(v, x0, H0) > val(v, x0, base[x0]) and val(v, x1, base[x0] | H1) > val(v, x1, base[x1]):
                B = {x0: H0, x1: base[x0] | H1}
                if one_abs(B):
                    return True
    return False

def brute_oc1(v, a, b):
    m = len(v[0])
    for f in itertools.product((a, b), repeat=m):
        X = {a: {g for g in range(m) if f[g] == a}, b: {g for g in range(m) if f[g] == b}}
        if is_oc1_witness(v, a, b, X):
            return True
    return False

def lemma_checks(rng, N):
    c = dict(factL=0, factL_fail=0, lemmaM=0, lemmaM_fail=0, tops=0, tops_fail=0)
    for _ in range(N):
        m = rng.randint(1, 9)
        v = [[rng.choice([0, 0, 1, 2, 3, 5, 8]) for _ in range(m)] for _ in range(2)]
        P, Q = lpt(v, 0, set(range(m)))
        c["factL"] += 1
        for A, B in ((P, Q), (Q, P)):
            if B and val(v, 0, B) - min(v[0][g] for g in B) > val(v, 0, A):
                c["factL_fail"] += 1
        # Lemma M on random EFX0 2-agent allocations with v_c(X_c) >= v_c(X_d)
        f = [rng.randint(0, 1) for _ in range(m)]
        X = [{g for g in range(m) if f[g] == 0}, {g for g in range(m) if f[g] == 1}]
        if efx0(v, X) and val(v, 0, X[0]) >= val(v, 0, X[1]):
            W = {g for g in X[0] if v[0][g] == 0 and rng.random() < 0.7}
            Y = [X[0] - W, X[1] | W]
            c["lemmaM"] += 1
            if not (efx0(v, Y) and val(v, 0, Y[0]) >= val(v, 0, Y[1])):
                c["lemmaM_fail"] += 1
        # Tops Lemma, n = 2..4
        n = rng.randint(2, 4); m2 = rng.randint(n, n + 5)
        w = [[rng.choice([0, 1, 2, 3, 4]) for _ in range(m2)] for _ in range(n)]
        tops = rng.sample(range(m2), n)
        for i, t in enumerate(tops):
            w[i][t] = max(w[i]) + rng.choice([0, 1])
        rest = [g for g in range(m2) if g not in tops]
        for _r in range(5):
            f = [rng.randrange(n) for _ in rest]
            S = [{g for g, a_ in zip(rest, f) if a_ == i} for i in range(n)]
            if efx0(w, S):
                c["tops"] += 1
                if not efx0(w, [S[i] | {tops[i]} for i in range(n)]):
                    c["tops_fail"] += 1
    return c

if __name__ == "__main__":
    rng = random.Random(1)
    print(json.dumps(dict(source="Fact L, Lemma M, Tops Lemma (n = 2..4)", **lemma_checks(rng, 20000))))
    c = dict(starts=0, construction_fail=0, brute_starts=0, brute_fail=0, shapes={})
    ex = []
    grids = [((0, 1), 7), ((0, 1, 2), 5), ((0, 1, 2, 3), 4), ((0, 2, 3, 5), 4)]
    for vals, mmax in grids:
        for m in range(1, mmax + 1):
            for flat in itertools.product(vals, repeat=2 * m):
                v = [list(flat[:m]), list(flat[m:])]
                for a, b in ((0, 1), (1, 0)):
                    c["starts"] += 1
                    X = construction(v, a, b)
                    if not is_oc1_witness(v, a, b, X):
                        c["construction_fail"] += 1
                        if len(ex) < 5:
                            ex.append(("construction", v, (a, b), {k: sorted(s) for k, s in X.items()}))
    for _ in range(20000):
        m = rng.randint(1, 14)
        kind = rng.choice(["generic", "ties", "zeros", "sparse"])
        if kind == "generic":
            v = [[rng.random() * 10 for _ in range(m)] for _ in range(2)]
        elif kind == "ties":
            v = [[rng.randint(1, 3) for _ in range(m)] for _ in range(2)]
        elif kind == "zeros":
            v = [[rng.choice([0, 0, 1, 2, 4]) for _ in range(m)] for _ in range(2)]
        else:
            v = [[(rng.randint(1, 9) if rng.random() < 0.3 else 0) for _ in range(m)] for _ in range(2)]
        for a, b in ((0, 1), (1, 0)):
            c["starts"] += 1
            X = construction(v, a, b)
            if not is_oc1_witness(v, a, b, X):
                c["construction_fail"] += 1
                if len(ex) < 5:
                    ex.append(("construction", kind, v, (a, b)))
    # independent brute force of OC1 (t >= 0) at n = 2, small m
    for _ in range(3000):
        m = rng.randint(1, 8)
        v = [[rng.choice([0, 0, 1, 2, 3, 5]) for _ in range(m)] for _ in range(2)]
        for a, b in ((0, 1), (1, 0)):
            c["brute_starts"] += 1
            if not brute_oc1(v, a, b):
                c["brute_fail"] += 1
                if len(ex) < 5:
                    ex.append(("brute", v, (a, b)))
    print(json.dumps(dict(source="Theorem 2 construction (exhaustive grids + 20,000 random) and brute-force OC1 (3,000)",
                          **{k: x for k, x in c.items() if k != "shapes"})))
    for e in ex:
        print("EXAMPLE", e)
