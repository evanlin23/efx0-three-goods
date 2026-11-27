#!/usr/bin/env python3
"""Referee spot check of K4.MATCH.LIFT.N4 (k4/matching.md §6 at 7e6cd80): every n = 4 start with no one-move repair
(the certifier's export results/k4_oc1max/two_move_starts_n4.json.gz, 112,880 starts) satisfies LIFT-SHAPE⁺.
Own code (cert_ref.py / lift_ref.py helpers), raw EFX0; the matching session's witnesses are NOT used: for each
sampled start my own search looks for a witness from scratch.

Per sampled start: SD picks of a stored order, perfect, no one-absorber completion at the picks or after any official
move; exactly one holder z; and some (P1, P2) with:
  P1 an official chain from a dangerous agent k ending at z, agents after the head take no junk, |H0^1| = 2,
     H0^1 ⊆ J ∪ {y_z}, improving for a second dangerous agent k' != k, z a holder after P1;
  P2 canonical at B1, head h != k, ending at z, z's new single good t its favourite good;
  (L3), and either (L1) and (L2') [case (a): h takes X - g, z takes {t, g}] or (Lb) [case (b): h takes X];
  and the resulting allocation raw EFX0.
"""
import json, gzip, random, sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk, oc_depth
from lift_ref import p1_chains, apply_chain, canonical_p2, holders, frozen_set, threatened

def lift_shape(v, Y):
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(Y)
    B = [{y} for y in Y]; p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    for seq1, Hs, H01 in p1_chains(v, Y, J):
        k, z = seq1[0], seq1[-1]
        if k not in D or not any(kp != k and kp in D and val(v, kp, H01) > p[kp] for kp in range(n)):
            continue
        B1 = apply_chain(B, seq1, Hs, H01)
        if z not in holders(v, B1):
            continue
        J1 = set(range(m)) - set().union(*B1)
        for seq2, H02 in canonical_p2(v, B1, J1, z, k):
            h = seq2[0]
            B2 = [set(b) for b in B1]
            for i in range(1, len(seq2)):
                B2[seq2[i]] = set(B1[seq2[i - 1]])
            B2[h] = set(H02)
            (t,) = B2[z]
            if not all(v[z][t] >= v[z][g] for g in rel(v, z)):
                continue
            J2 = set(range(m)) - set().union(*B2); X = H02 | J2
            vb = [val(v, i, B2[i]) for i in range(n)]
            L3 = all(len(X & rel(v, i)) <= 1 for i in range(n) if i not in (h, z))
            if not L3:
                continue
            G = J2 & rel(v, z); g = max(sorted(G), key=lambda x: v[z][x]) if G else None
            L1 = not any(i != z and v[i][t] > vb[i] for i in range(n))
            L2 = val(v, z, H02 & rel(v, z)) <= v[z][t] + (v[z][g] if g is not None else 0)
            Lb = val(v, z, X & rel(v, z)) <= v[z][t]
            for case in ("a", "b"):
                if case == "a" and not (L1 and L2):
                    continue
                if case == "b" and not Lb:
                    continue
                A = [set(b) for b in B2]
                if case == "a" and g is not None:
                    A[h] = X - {g}; A[z] = {t, g}
                else:
                    A[h] = set(X)
                if efx0(v, A) and set().union(*A) == set(range(m)):
                    return case
                return "construction_not_efx0"
    return None

def main(path, N, seed):
    rng = random.Random(seed)
    d = json.load(gzip.open(path))
    allst = [(H["sets"], s) for H in d["hypergraphs"] for s in H["starts"]]
    from collections import Counter
    c = Counter(); ex = []
    c["exported_starts"] = len(allst)
    for sets, s in rng.sample(allst, min(N, len(allst))):
        v = mk(sets, s["vals"]); Y = s["picks"]; n = len(v)
        c["sampled"] += 1
        if sd(v, s["orders"][0]) != list(Y) or any(y is None for y in Y):
            c["picks_mismatch"] += 1; continue
        if oc_depth(v, Y, 1) is not None:
            c["not_hard"] += 1; ex.append(("not hard", sets, s["vals"], Y)); continue
        B = [{y} for y in Y]
        if len(holders(v, B)) != 1:
            c["holders_not_1"] += 1
        r = lift_shape(v, Y)
        c["case_" + str(r)] += 1
        if r not in ("a", "b") and len(ex) < 5:
            ex.append(("no shape", sets, s["vals"], Y, r))
    print(json.dumps(dict(source=f"LIFT-SHAPE+ spot check on the n = 4 export, sample N={N} seed={seed}", **dict(sorted(c.items())))))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
