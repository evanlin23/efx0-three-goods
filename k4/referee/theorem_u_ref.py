#!/usr/bin/env python3
"""Referee check of Theorem U and Corollary U1 (k4/oc1max_multi.md §3, branch proof/k4-oc1max-multi at d31a8f1 /
5371d9b). Own code (multi_ref.py / oc1hall_ref.py helpers), raw EFX0.

Hard perfect starts (one-absorber-hard by brute force) with D_T = {k} (J threatens k at p_k and no other dangerous
agent), any |D|. For every LONGEST canonical chain from k and every improving H0 ⊆ J ∩ R_k:
  Theorem U: if E_J ⊆ {z} and (z ∈ E_J ⟹ z unfrozen at B'), then an S* completion owned by k exists in which Y_z goes
  to z (z unfrozen at B') or to an unfrozen second wanter of a, and k's bundle ⊆ J.
  Corollary U1: at starts with exactly one unfrozen pick holder, the hypothesis always holds (and so every longest
  chain repairs).
Mutations: 'anychain' (not only longest chains), 'noEJ' (drop E_J ⊆ {z}).
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd
from multi_ref import frozen_set, holders_of, oa_exists, sstar, subsets, canonical_chains

def run(N, nlo, nhi, seed, mut=None):
    rng = random.Random(seed)
    c = dict(instances=0, hard=0, hard_DT1=0, hard_DT1_Dge2=0, u1_starts=0, u1_hyp_fail=0, tests=0, tests_Dge2=0,
             fail=0, owner_bundle_not_in_J=0)
    ex = []
    for it in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(n + 2, n + 3)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.choice([3, 4, 4])), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        c["instances"] += 1
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:6]:
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen or any(Y[i] is None and any(x > 0 for x in v[i]) for i in range(n)):
                continue
            seen.add(tuple(Y))
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            J = set(range(m)) - set().union(*B)
            if len(J) > 5 or oa_exists(v, B):
                continue
            c["hard"] += 1
            p = [val(v, i, B[i]) for i in range(n)]
            F = frozen_set(v, B)
            D = {d for d in F if any(v[d][g] > 0 for g in J)}
            DT = {d for d in D if threatened(v, d, J, p[d])}
            if len(DT) != 1:
                continue
            (k,) = DT
            c["hard_DT1"] += 1
            c["hard_DT1_Dge2"] += len(D) >= 2
            U = [u for u in range(n) if u not in F and Y[u] is not None]
            EJ = {u for u in U if threatened(v, u, J, p[u])}
            chains = [s for s in canonical_chains(v, Y, F) if s[0] == k]
            L = max((len(s) for s in chains), default=0)
            pool = chains if mut == "anychain" else [s for s in chains if len(s) == L]
            if len(U) == 1:
                c["u1_starts"] += 1
            for seq in pool:
                z = seq[-1]; a = Y[seq[-2]]
                for H0 in subsets(J & rel(v, k)):
                    if not val(v, k, H0) > p[k]:
                        continue
                    Bp = [set(b) for b in B]; Bp[k] = set(H0)
                    for i in range(1, len(seq)):
                        Bp[seq[i]] = {Y[seq[i - 1]]}
                    Fp = frozen_set(v, Bp)
                    hypEJ = EJ <= {z}
                    hyp2 = (z not in EJ) or (z not in Fp)
                    if len(U) == 1 and not (hypEJ and hyp2) and mut is None:
                        c["u1_hyp_fail"] += 1; ex.append(("U1hyp", v, Y, seq, sorted(H0)))
                    if not ((hypEJ or mut == "noEJ") and hyp2):
                        continue
                    c["tests"] += 1
                    c["tests_Dge2"] += len(D) >= 2
                    if z not in Fp:
                        us = [z]
                    else:
                        us = [w for w in holders_of(v, Bp) if w not in seq and v[w][a] > p[w] and w not in F]
                    ok = any(sstar(v, Bp, k, forced={Y[z]: u}) for u in us)
                    if not ok:
                        c["fail"] += 1
                        if len(ex) < 6:
                            ex.append(("U", mut, v, Y, seq, sorted(H0), us))
    print(json.dumps(dict(source=f"Theorem U / U1 N={N} n={nlo}..{nhi} seed={seed} mutation={mut}", **c)))
    for e in ex[:6]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    a = list(map(int, sys.argv[1:5]))
    run(*a, mut=(sys.argv[5] if len(sys.argv) > 5 else None))
