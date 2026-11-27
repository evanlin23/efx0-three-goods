#!/usr/bin/env python3
"""Lemma RF-B and Lemma REPAIR-Y (k4/oc1_hall.md §24.8 at 01f986d4) as general lemmas: random strict instances
(n = 3-6, <= 4 relevant goods), random SD orders with every agent holding a good; every (d, k, S) with S ⊆ J', |S| = 2
meeting (B1)-(B5) must give an EFX0 FULL(k, S); every (u, d, k, k', S) with t = Y_d, |S| = 2, J - S = {l} meeting
(R1)-(R3) must give an EFX0 REPAIR-Y allocation. Own code."""
import json, sys, random, itertools
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd

def wants(v, i, g, Y):
    return v[i][g] > v[i][Y[i]]

def run(N, seed):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        n = rng.randint(3, 6); m = rng.randint(n + 2, n + 4)
        v = [[0] * m for _ in range(n)]
        for a in range(n):
            k = rng.choice([2, 3, 4, 4])
            for g, x in zip(rng.sample(range(m), k), rng.sample(range(1, 60), k)):
                v[a][g] = x
        o = list(range(n)); rng.shuffle(o); Y = sd(v, o)
        if None in Y:
            continue
        p = [v[i][Y[i]] for i in range(n)]; J = set(range(m)) - set(Y)
        for d, k in itertools.permutations(range(n), 2):
            for S in itertools.combinations(sorted(J), 2):
                S = set(S); Z = {Y[k], Y[d]} | (J - S)
                if not (val(v, k, S) > p[k]): continue
                if not (wants(v, d, Y[k], Y) and not any(i not in (k, d) and wants(v, i, Y[k], Y) for i in range(n))): continue
                if any(i != d and wants(v, i, Y[d], Y) for i in range(n)): continue
                if (Z & rel(v, k)) != {Y[k]}: continue
                pass  # MUTATION: (B5) dropped
                X = [{Y[a]} for a in range(n)]; X[k] = set(S); X[d] = set(Z)
                c["RFB_hyp"] += 1; c["RFB_VIOLATION"] += not efx0(v, X)
        for u, d, k, kp in itertools.permutations(range(n), 4):
            for S in itertools.combinations(sorted(J), 2):
                S = set(S)
                if len(J - S) != 1: continue
                (l,) = J - S
                if not (val(v, k, S) > p[k] and wants(v, u, Y[k], Y)): continue
                if any(i != u and wants(v, i, Y[u], Y) for i in range(n)): continue
                if any(i != u and wants(v, i, Y[k], Y) for i in range(n)): continue
                if not all(i in (k, u) for i in range(n) if wants(v, i, Y[kp], Y)): continue
                if not (v[k][Y[kp]] <= val(v, k, S)): continue  # MUTATION: (U-b)-type bound dropped
                X = [{Y[a]} for a in range(n)]; X[u] = {Y[k], Y[u]}; X[k] = set(S); X[kp] = {Y[kp], l}
                c["RY_hyp"] += 1; c["RY_VIOLATION"] += not efx0(v, X)
    print(json.dumps(dict(source=f"MUTANT (B5 and the R3 bound dropped) N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
