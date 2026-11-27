#!/usr/bin/env python3
"""Referee check, in passing, of Finding NC (T3) and Lemma RING-red (k4/oc1max_multi.md §6, branch
proof/k4-oc1max-multi at 1ccbb94). Own code (multi_ref.py / oc1hall_ref.py helpers), raw EFX0.

1. T3, order (0, 1, 2): hard at the picks; every canonical chain from a dangerous agent with every improving
   H0 ⊆ Pi ∩ R_k: is there a one-absorber completion (any owner) after it? (claim: none); the ring (0, 2, 1) with head
   junk {3} and H0 = {4, 2} satisfies (R1)-(R4) and has an S* completion owned by 0.
2. Random hard perfect starts: every dangerous ring (k = x0, ..., x_t = d in D; x_i (1 <= i < t) wants Y_{x_{i-1}};
   d takes Y_{x_{t-1}} ∪ H_t with gain; k takes {Y_d} ∪ G, G ⊆ J ∖ H_t, with gain): whenever (R1)-(R4) hold, brute
   force for an S* completion owned by k.
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd
from multi_ref import frozen_set, holders_of, oa_exists, sstar, subsets, canonical_chains

def oa_any(v, B):
    return oa_exists(v, B)

def rings(v, Y, F, D, J):
    n = len(Y); p = [v[i][Y[i]] if Y[i] is not None else 0 for i in range(n)]
    def ext(seq):
        last = seq[-1]
        for w in range(n):
            if w in seq or Y[last] is None:
                continue
            if w in D and len(seq) >= 1:
                yield seq + [w]                      # w as the ring's end d (takes Y_last plus junk)
            if v[w][Y[last]] > p[w]:
                yield from ext(seq + [w])
    for k in D:
        yield from ext([k])

def ring_states(v, Y, seq, J):
    n = len(Y); p = [v[i][Y[i]] if Y[i] is not None else 0 for i in range(n)]
    k, d = seq[0], seq[-1]
    for Ht in subsets(J & rel(v, d)):
        if not val(v, d, {Y[seq[-2]]} | Ht) > p[d]:
            continue
        for G in subsets((J - Ht) & rel(v, k)):
            H0 = {Y[d]} | G
            if not val(v, k, H0) > p[k]:
                continue
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            B[k] = set(H0)
            for i in range(1, len(seq) - 1):
                B[seq[i]] = {Y[seq[i - 1]]}
            B[d] = {Y[seq[-2]]} | Ht
            yield Ht, H0, B, J - G - Ht

def ring_hyp(v, B, k, d, H0, Jp):
    n = len(B); vp = [val(v, i, B[i]) for i in range(n)]
    R1 = not any(i != d and threatened(v, i, B[d], vp[i]) for i in range(n))
    R2 = not any(i != k and v[i][g] > vp[i] for i in range(n) for g in H0)
    Fp = frozen_set(v, B)
    R3 = not any(threatened(v, q, H0 | Jp, vp[q]) for q in ({d} | Fp) - {k})
    R4 = not any(len(H0 & rel(v, u)) >= 2 and val(v, u, H0 & rel(v, u)) > vp[u] for u in holders_of(v, B))
    return R1 and R2 and R3 and R4

def t3():
    m = 6
    v = [[0] * m for _ in range(3)]
    for g, x in {0: 38, 4: 36, 2: 6, 5: 1}.items(): v[0][g] = x
    for g, x in {4: 30, 1: 22, 3: 12}.items(): v[1][g] = x
    for g, x in {0: 38, 4: 28, 1: 20, 3: 12}.items(): v[2][g] = x
    yd = sd(v, (0, 1, 2)); Y = [yd[i] for i in range(3)]
    B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    p = [v[i][Y[i]] for i in range(3)]
    F = frozen_set(v, B); D = {x for x in F if any(v[x][g] > 0 for g in J)}
    DT = {x for x in D if threatened(v, x, J, p[x])}
    out = dict(picks=Y, junk=sorted(J), frozen=sorted(F), D=sorted(D), D_T=sorted(DT), hard=not oa_any(v, B))
    can = []
    for seq in canonical_chains(v, Y, F):
        k, z = seq[0], seq[-1]
        Pi = J | {Y[z]}
        for H0 in subsets(Pi & rel(v, k)):
            if val(v, k, H0) > p[k]:
                Bp = [set(b) for b in B]; Bp[k] = set(H0)
                for i in range(1, len(seq)):
                    Bp[seq[i]] = {Y[seq[i - 1]]}
                can.append(dict(chain=seq, H0=sorted(H0), one_absorber_after=oa_any(v, Bp)))
    out["canonical_chains_with_improving_H0"] = can
    B2 = [{4, 2}, {1, 3}, {0}]
    out["ring_(0,2,1)_R1-R4"] = ring_hyp(v, B2, 0, 1, {4, 2}, {5})
    out["ring_(0,2,1)_Sstar_owner0"] = sstar(v, B2, 0)
    print(json.dumps(dict(case="T3", **out)))

def run(N, nlo, nhi, seed):
    rng = random.Random(seed)
    c = dict(instances=0, hard=0, rings=0, ring_hyp=0, ring_fail=0)
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(n + 2, n + 3)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), 4), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        c["instances"] += 1
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for order in orders[:6]:
            yd = sd(v, order); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen or any(y is None for y in Y):
                continue
            seen.add(tuple(Y))
            B = [{y} for y in Y]; J = set(range(m)) - set(Y)
            if len(J) > 5 or oa_any(v, B):
                continue
            c["hard"] += 1
            F = frozen_set(v, B); D = {x for x in F if any(v[x][g] > 0 for g in J)}
            for seq in rings(v, Y, F, D, J):
                for Ht, H0, Bp, Jp in ring_states(v, Y, seq, J):
                    c["rings"] += 1
                    if ring_hyp(v, Bp, seq[0], seq[-1], H0, Jp):
                        c["ring_hyp"] += 1
                        if not sstar(v, Bp, seq[0]):
                            c["ring_fail"] += 1
                            print("EXAMPLE", v, Y, seq, sorted(Ht), sorted(H0))
    print(json.dumps(dict(source=f"RING-red N={N} n={nlo}..{nhi} seed={seed}", **c)))

if __name__ == "__main__":
    t3()
    run(*map(int, sys.argv[1:5]))
