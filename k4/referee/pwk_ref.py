#!/usr/bin/env python3
"""Referee check of Lemma PWk(a) (k4/ksens.md §7, branch claude/k4-ksens). Written from the text; the 'clean' values
(wanter values 2(f - j) for p_j, j = 0..f-1, and 1 for its own q; x values 20 for p and 19, 18, ... for D) are taken
from fam_ladder.clean as data. No shared code.

1. Clean family, f <= 6, W <= 5, r in {2, 3}: the proof's chain x1 -> w1 and its explicit completion, checked by the
   raw EFX0 definition (and the one-absorber shape).
2. Brute force OC1 (picks, or one improving chain of k4/sdc.md §29, then a one-absorber completion) on the clean family
   for small f, W, r <= 3.
3. Robustness of the statement: the family with *arbitrary* wanter values of the described shape (every p_j above its
   own q, same ranking p_1 > ... > p_f): (a) the proof's completion; (b) OC1 by brute force.
"""
import itertools, random, sys, json

def build(f, W, r, wvals=None, xvals=None):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r)); m = f + W + r
    v = [[0] * m for _ in range(f + W)]
    for j in range(f):
        v[j][P[j]] = 20
        for t, d in enumerate(D):
            v[j][d] = (xvals[j][t] if xvals else 19 - t)
    for i in range(W):
        for j in range(f):
            v[f + i][P[j]] = (wvals[i][j] if wvals else 2 * (f - j))
        v[f + i][Q[i]] = (wvals[i][f] if wvals else 1)
    return v, P, Q, D, m

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

def proof_completion(f, W, r, P, Q, D):
    """the allocation of the proof of (a), r in {2, 3}, W >= 1."""
    n = f + W
    X = [set() for _ in range(n)]
    x1, w1 = 0, f
    X[x1] = {D[0], D[1]}; X[w1] = {P[0]}
    for j in range(1, f):
        X[j] = {P[j]}
    for i in range(1, W):
        X[f + i] = {Q[i]}
    left = [Q[0]] + ([D[2]] if r == 3 else [])
    absorber = f + 1 if W >= 2 else (1 if f >= 2 else 0)
    X[absorber] |= set(left)
    return X, absorber

def one_absorber(v, B, m):
    n = len(B)
    held = set().union(*B); J = [g for g in range(m) if g not in held]
    for fn in itertools.product(range(n), repeat=len(J)):
        cnt = [0] * n
        for a in fn:
            cnt[a] += 1
        if sum(1 for c in cnt if c >= 2) > 1:
            continue
        X = [set(b) for b in B]
        for g, a in zip(J, fn):
            X[a].add(g)
        if efx0(v, X):
            return True
    return False

def chains(v, B, m):
    n = len(B)
    J = set(range(m)) - set().union(*B)
    R = [{g for g in range(m) if v[i][g] > 0} for i in range(n)]
    def subsets(S):
        S = sorted(S)
        for k in range(len(S) + 1):
            for c in itertools.combinations(S, k):
                yield set(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            def rec(i, used, nb):
                if i > t:
                    for H0 in subsets(((J - used) | B[seq[-1]]) & R[seq[0]]):
                        if H0 and val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            c = list(nb); c[seq[0]] = set(H0); yield c
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((J - used) & R[xi]):
                    if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                        c = list(nb); c[xi] = B[pr] | Hi
                        yield from rec(i + 1, used | Hi, c)
            yield from rec(1, set(), [set(b) for b in B])

def oc1(v, f, W, P, Q, m):
    B = [{P[j]} for j in range(f)] + [{Q[i]} for i in range(W)]
    if one_absorber(v, B, m):
        return 0
    for c in chains(v, B, m):
        if one_absorber(v, c, m):
            return 1
    return 2

if __name__ == "__main__":
    out = {"clean_proof_completion": 0, "clean_proof_completion_fail": 0, "clean_oc1": 0, "clean_oc1_fail": 0,
           "general_proof_completion": 0, "general_proof_completion_fail": 0, "general_oc1": 0, "general_oc1_fail": 0}
    ex = []
    for f in range(1, 7):
        for W in range(1, 6):
            for r in (2, 3):
                v, P, Q, D, m = build(f, W, r)
                X, a = proof_completion(f, W, r, P, Q, D)
                out["clean_proof_completion"] += 1
                if not efx0(v, X) or set().union(*X) != set(range(m)):
                    out["clean_proof_completion_fail"] += 1; ex.append(("clean", f, W, r))
    for f in range(1, 4):
        for W in range(1, 4):
            for r in (0, 1, 2, 3):
                if f + W > 5:
                    continue
                v, P, Q, D, m = build(f, W, r)
                out["clean_oc1"] += 1
                if oc1(v, f, W, P, Q, m) == 2:
                    out["clean_oc1_fail"] += 1; ex.append(("clean_oc1", f, W, r))
    rng = random.Random(5)
    for _ in range(300):
        f = rng.randint(2, 3); W = rng.randint(1, 2); r = rng.choice([2, 3])
        wv = []
        for i in range(W):
            ps = sorted(rng.sample(range(2, 30), f), reverse=True)
            wv.append(ps + [rng.randint(1, ps[-1] - 1)])
        v, P, Q, D, m = build(f, W, r, wvals=wv)
        X, a = proof_completion(f, W, r, P, Q, D)
        out["general_proof_completion"] += 1
        if not efx0(v, X):
            out["general_proof_completion_fail"] += 1
            if len(ex) < 4:
                ex.append(("general_completion", f, W, r, wv))
        out["general_oc1"] += 1
        if oc1(v, f, W, P, Q, m) == 2:
            out["general_oc1_fail"] += 1
            ex.append(("general_oc1", f, W, r, wv))
    print(json.dumps(out))
    for e in ex:
        print("EXAMPLE", e)

def fixed_completion(f, W, r, P, Q, D):
    """referee's fix for W = 1, f >= 2: q1 -> x2, d3 -> w1 (no absorber); otherwise the proof's completion."""
    if not (W == 1 and f >= 2):
        return proof_completion(f, W, r, P, Q, D)
    X = [set() for _ in range(f + W)]
    X[0] = {D[0], D[1]}; X[f] = {P[0]}
    for j in range(1, f):
        X[j] = {P[j]}
    X[1].add(Q[0])
    if r == 3:
        X[f].add(D[2])
    return X, None

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "fix":
    rng = random.Random(6); c = dict(tests=0, fail=0)
    for _ in range(3000):
        f = rng.randint(1, 6); W = rng.randint(1, 5); r = rng.choice([2, 3])
        wv = []
        for i in range(W):
            ps = sorted(rng.sample(range(2, 60), f), reverse=True)
            wv.append(ps + [rng.randint(1, ps[-1] - 1)])
        xv = [sorted(rng.sample(range(11, 20), r), reverse=True) for _ in range(f)]  # every pair > 20, each < 20
        v, P, Q, D, m = build(f, W, r, wvals=wv, xvals=xv)
        X, a = fixed_completion(f, W, r, P, Q, D)
        c["tests"] += 1
        if not efx0(v, X) or set().union(*X) != set(range(m)):
            c["fail"] += 1
    print(json.dumps(dict(source="fixed completion, general values, f<=6, W<=5, r in {2,3}", **c)))
