#!/usr/bin/env python3
"""Referee checks of Hall's Lemma RF-B' (k4/oc1_hall.md §24.10 at 7336e31c) and girth's Lemma RF-T / Corollary RF-T'
(k4/girth.md §7 at 3e64bf0d). Own code; nothing from k4/oc1_hall/ or k4/girth/ is run.

rfbp: random SD picks Y' (every agent holds a good); every d whose pick nobody wants, every k != d whose pick d wants,
every improving S ⊆ J' (|S| = 1..3); B' = "k takes S, d takes Y'_k" (d releases Y'_d). Claims: (G2) at B' (no free
good is wanted); then Lemma M^c's formula equals the brute-force S^c test for every owner (my mc_ref).
rft: random strict instances and orders; u = the last picker; Y' = SD(u, o - u) (RF-PATH); when the path has l >= 2,
d takes a junk good g, J = {g, j, z} with j ∈ R_p for an off-path p keeping its pick and v_p({g, j}) > p_p,
v_d(Y_p) > v_d(g): the allocation X of Lemma RF-T is complete, and raw EFX0(X) iff (W-d) and (W-p); (F1)-(F3) ⟹ EFX0."""
import itertools, json, sys, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd
from mc_ref import brute, formula, G2

def wants(v, i, g, Y):
    return v[i][g] > v[i][Y[i]]

def rand_inst(rng, nlo, nhi):
    n = rng.randint(nlo, nhi); m = rng.randint(n + 2, n + 3)
    v = [[0] * m for _ in range(n)]
    for a in range(n):
        k = rng.choice([2, 3, 4, 4])
        for g, x in zip(rng.sample(range(m), k), rng.sample(range(1, 60), k)):
            v[a][g] = x
    return v

def rfbp(N, seed):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        v = rand_inst(rng, 3, 5); n = len(v); m = len(v[0])
        o = list(range(n)); rng.shuffle(o); Y = sd(v, o)
        if None in Y:
            continue
        J = set(range(m)) - set(Y)
        for d in range(n):
            if any(i != d and wants(v, i, Y[d], Y) for i in range(n)):
                continue
            for k in range(n):
                if k == d or not wants(v, d, Y[k], Y):
                    continue
                for r in (1, 2, 3):
                    for S in itertools.combinations(sorted(J & rel(v, k)), r):
                        if not val(v, k, S) > v[k][Y[k]]:
                            continue
                        B = [{y} for y in Y]; B[k] = set(S); B[d] = {Y[k]}
                        c["states"] += 1
                        g2 = G2(v, B); c["G2_FAIL"] += not g2
                        if not g2:
                            continue
                        for own in range(n):
                            b = brute(v, B, own, 0)
                            f = formula(v, B, own, 0)
                            c["owner_tests"] += 1; c["Mc_MISMATCH"] += bool(b) != bool(f); c["Sc_exists"] += bool(b)
    print(json.dumps(dict(source=f"Lemma RF-B' N={N} seed={seed}", **dict(sorted(c.items())))))

def rft(N, seed):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        v = rand_inst(rng, 4, 7); n = len(v); m = len(v[0])
        o = list(range(n)); rng.shuffle(o); Y = sd(v, o)
        if None in Y:
            continue
        J = set(range(m)) - set(Y)
        if len(J) != 3:
            continue
        u = o[-1]; Ru = [g for g in range(m) if v[u][g] > 0]
        t = max(Ru, key=lambda g: (v[u][g], -g))
        if t == Y[u]:
            continue
        sig2 = [u] + o[:-1]; Yp = sd(v, sig2)
        if None in Yp:
            continue
        pos = {a: i for i, a in enumerate(o)}
        path = sorted([a for a in range(n) if a != u and Yp[a] != Y[a]], key=lambda a: pos[a])
        if len(path) < 2:
            continue
        d = path[-1]; g = Yp[d]
        if g not in J:
            continue
        full = [u] + path            # x_0 = u, x_1, ..., x_l = d
        for p in range(n):
            if p in full or Yp[p] != Y[p]:
                continue
            for j in sorted((J - {g}) & rel(v, p)):
                if not (v[p][g] + v[p][j] > v[p][Y[p]] and v[d][Y[p]] > v[d][g]):
                    continue
                (z,) = J - {g, j}
                X = [{Yp[a]} for a in range(n)]
                for i in range(1, len(full) - 1):
                    X[full[i]] = {Y[full[i + 1]]}
                X[full[0]] = {Y[full[1]]}
                xl1 = full[-2]; X[xl1] = {Y[d], z}; X[d] = {Y[p], Y[u]}; X[p] = {g, j}
                c["trades"] += 1
                comp = sum(map(len, X)) == m and set().union(*X) == set(range(m))
                c["X_complete"] += comp
                Wd = not any(i != xl1 and v[i][Y[d]] > val(v, i, X[i]) for i in range(n))
                Wp = not any(i != d and v[i][Y[p]] > val(v, i, X[i]) for i in range(n))
                e = efx0(v, X)
                c["EFX0"] += e; c["RFT_IFF_MISMATCH"] += e != (Wd and Wp)
                F1 = wants(v, d, Y[p], Y)
                F2 = not any(i not in full and wants(v, i, Y[d], Y) for i in range(n))
                F3 = all(i in (p, d, u) for i in range(n) if v[i][Y[p]] > 0)
                if F1 and F2 and F3:
                    c["F1_F2_F3"] += 1; c["RFTprime_VIOLATION"] += not e
    print(json.dumps(dict(source=f"Lemma RF-T / RF-T' random N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    {"rfbp": rfbp, "rft": rft}[sys.argv[1]](int(sys.argv[2]), int(sys.argv[3]))
