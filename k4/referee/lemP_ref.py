#!/usr/bin/env python3
"""Lemma P and Corollary 3 (kgen/n3.md §2, §11 at 0bfe9933), random check with my OC1 test (cert_ref.oc_depth: the
picks complete with one absorber, or do after one official §29 move, t >= 0 included). Random instances (n = 3-4,
<= 4 goods, values 1..20, ties allowed), random order. Lemma P: if some z has v_z(y_z) >= v_z(M - y_z) and OC1 holds for
π - z on I - z - y_z, then OC1 holds for π on I. Corollary 3 at n = 3: a top-heavy pick implies OC1 for π."""
import json, sys, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import sd, oc_depth

def run(N, seed):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        n = rng.randint(3, 4); m = rng.randint(n + 1, n + 3)
        v = [[0] * m for _ in range(n)]
        for a in range(n):
            for g in rng.sample(range(m), rng.randint(2, min(4, m))):
                v[a][g] = rng.randint(1, 20)
        o = list(range(n)); rng.shuffle(o); Y = sd(v, o)
        for z in range(n):
            if Y[z] is None or v[z][Y[z]] < sum(v[z]) - v[z][Y[z]]:
                continue
            goods = [g for g in range(m) if g != Y[z]]; agents = [a for a in range(n) if a != z]
            vs = [[v[a][g] for g in goods] for a in agents]
            Ys = sd(vs, [agents.index(a) for a in o if a != z])
            same = all((Ys[i] is None and Y[a] is None) or (Ys[i] is not None and goods[Ys[i]] == Y[a]) for i, a in enumerate(agents))
            c["top_heavy_cases"] += 1; c["P_picks_unchanged_FAIL"] += not same
            sub = oc_depth(vs, Ys, maxd=1) is not None
            full = oc_depth(v, Y, maxd=1) is not None
            c["sub_OC1"] += sub; c["LEMMA_P_VIOLATION"] += sub and not full
            if n == 3:
                c["n3_top_heavy"] += 1; c["COR3_VIOLATION"] += not full
            break
    print(json.dumps(dict(source=f"Lemma P / Corollary 3 random N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
