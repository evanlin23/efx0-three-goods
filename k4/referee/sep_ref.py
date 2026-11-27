#!/usr/bin/env python3
"""Proposition SEP (k4/base_phantom.md §4.1 at 0e6d9abc) against the raw threat test: random phantoms k with
|R_k| <= 4, strict values, a pick y, an improving T ⊆ R_k - {y} (|T| = 1, 2, 3), P1-free (every good of R_k - T worth
<= v_k(T)); random bundles X disjoint from T. SEP: X threatens k only if |X| >= 3 and X holds >= 2 goods of R_k - T;
for |T| = 3 never; for |T| = 2 exactly when {y, l} ⊆ X, |X| >= 3, v(y) + v(l) > tau. Mutation: drop P1-freeness."""
import json, sys, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import threatened

def run(N, seed, mut):
    rng = random.Random(seed); c = Counter(); m = 9
    for _ in range(N):
        d = rng.choice([2, 3, 4]); R = rng.sample(range(m), d)
        v = [[0] * m]
        for g, x in zip(R, rng.sample(range(1, 80), d)):
            v[0][g] = x
        y = rng.choice(R); rest = [g for g in R if g != y]
        T = set(rng.sample(rest, rng.randint(1, len(rest))))
        tau = sum(v[0][g] for g in T)
        if not tau > v[0][y]:
            continue
        p1f = all(v[0][g] <= tau for g in R if g not in T)
        if not p1f and mut is None:
            continue
        others = [g for g in range(m) if g not in T]
        X = set(rng.sample(others, rng.randint(1, len(others))))
        thr = threatened(v, 0, X, tau)
        outside = [g for g in R if g not in T]
        c["tests"] += 1; c["threatened"] += thr
        nec = len(X) >= 3 and len(X & set(outside)) >= 2
        c["SEP_part1_VIOLATION"] += thr and not nec
        if len(T) == 3:
            c["SEP_triple_VIOLATION"] += thr
        if len(T) == 2 and len(R) == 4:
            l = next(g for g in outside if g != y)
            pred = {y, l} <= X and len(X) >= 3 and v[0][y] + v[0][l] > tau
            c["SEP_pair_tests"] += 1; c["SEP_pair_MISMATCH"] += pred != thr
    print(json.dumps(dict(source=f"Proposition SEP random N={N} seed={seed} mutation={mut}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else None)
