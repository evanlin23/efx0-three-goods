#!/usr/bin/env python3
"""Referee check of Hall's RF residue proofs at n = 4 (k4/oc1_hall.md §24.6, §24.8 on claude/k4-oc1-hall at 01f986d4):
the certified facts that Lemma RF-A1 and Proposition RF-B4 use, recomputed with my own code from the certifier's n = 4
export (two_move_starts_n4.json.gz: 112,880 starts, 292,080 failing orders), and the conclusions of RF-A1, RF-B and
REPAIR-Y tested by raw EFX0. Nothing from k4/oc1_hall/ is run.

Per failing order o: u = the unique receiver of Y (must be o's last picker); Y' = SD(u, o - u); RF starts deduplicated
by (profile, Y'). At Y': U' = unfrozen agents, J' = junk, D_T' = frozen agents threatened by J' at their pick.
A1: |U'| = 1, D_T' = ∅, path u -> w -> d with d taking a junk good g. B: |U'| = 1, |D_T'| = 2.
A1: (A1-i)..(A1-iv) and the completion (w: {Y_d} ∪ J' - h, d: {g, h}) raw EFX0.
B: k = the agent of D_T' whose pick d wants and nobody else does; S = the junk goods k and k' share; Z = {Y'_k, Y'_d}
∪ (J' - S); (B1)..(B5); FULL(k, S) raw EFX0; facts (a) and (c) incl. R_u and (U-b); REPAIR-Y's hypotheses at Y and its
allocation; (U-b) strict where |J - S| = 1."""
import json, gzip, sys, itertools
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from oc1hall_ref import threatened

def wants(v, i, g, Y):
    return g is not None and v[i][g] > v[i][Y[i]]

def frozen(v, n, Y, a):
    return any(i != a and wants(v, i, Y[a], Y) for i in range(n))

def main(path):
    d0 = json.load(gzip.open(path)); c = Counter(); seen = set()
    for H in d0["hypergraphs"]:
        for s in H["starts"]:
            v = mk(H["sets"], s["vals"]); n = len(v); m = len(v[0]); Y = list(s["picks"])
            J = set(range(m)) - set(Y)
            rec = [a for a in range(n) if not frozen(v, n, Y, a)]
            DT = [a for a in range(n) if frozen(v, n, Y, a) and threatened(v, a, J, v[a][Y[a]])]
            for o in s["orders"]:
                c["orders"] += 1
                if len(rec) != 1 or rec[0] != o[-1]:
                    c["FAIL_receiver_not_unique_last"] += 1; continue
                u = rec[0]
                Yp = sd(v, [u] + [a for a in o if a != u])
                key = json.dumps([H["sets"], s["vals"], Yp])
                if key in seen:
                    continue
                seen.add(key); c["RF_starts"] += 1
                Jp = set(range(m)) - set(Yp)
                Up = [a for a in range(n) if not frozen(v, n, Yp, a)]
                DTp = [a for a in range(n) if frozen(v, n, Yp, a) and threatened(v, a, Jp, v[a][Yp[a]])]
                path = [a for a in range(n) if a != u and Yp[a] != Y[a]]
                if len(Up) >= 2:
                    c["class_R2"] += 1; continue
                if len(DTp) == 1:
                    c["class_U1"] += 1; continue
                dd = Up[0]
                if not DTp:
                    c["class_A"] += 1
                    if len(path) == 2 and Yp[dd] in J:
                        c["A1"] += 1; a1(v, n, m, Y, Yp, J, Jp, u, path, dd, DT, c)
                    else:
                        c["A_other"] += 1
                    continue
                if len(DTp) == 2:
                    c["class_B"] += 1; b(v, n, m, Y, Yp, J, Jp, u, path, dd, DTp, c)
                    continue
                c["class_other"] += 1
    print(json.dumps(dict(source="Hall RF residue facts at n = 4 (own code)", **dict(sorted(c.items())))))

def a1(v, n, m, Y, Yp, J, Jp, u, path, d, DT, c):
    pos = path  # sorted by agent index; recover w as the agent whose pick u takes
    w = next(a for a in path if Y[a] == Yp[u])
    if d != next(a for a in path if a != w):
        c["A1_FAIL_path"] += 1; return
    g = Yp[d]; Rd = rel(v, d)
    JdY = J & Rd; JpRd = Jp & Rd
    hs = sorted(JpRd)
    i_ok = d in DT and len(JdY) == 2 and g in JdY and len(hs) == 1 and hs[0] in JdY
    c["A1_i"] += i_ok
    if not i_ok:
        return
    h = hs[0]
    W = {Y[d]} | (Jp - {h})
    Ru = rel(v, u)
    ii_ok = (W & Ru) == {Y[d], Y[u]} and v[u][Y[d]] + v[u][Y[u]] < v[u][Y[w]]
    k2s = [a for a in DT if a != d]
    iii_ok = len(k2s) == 1 and v[k2s[0]][g] > 0 and v[k2s[0]][h] > 0 and not wants(v, k2s[0], Y[d], Yp)
    k2 = k2s[0] if k2s else None
    iv_ok = not any(frozen(v, n, Yp, q) and v[q][Y[d]] > 0 for q in range(n) if q not in (w, u, k2))
    c["A1_ii"] += ii_ok; c["A1_iii"] += iii_ok; c["A1_iv"] += iv_ok
    X = [{Yp[a]} for a in range(n)]; X[w] = set(W); X[d] = {g, h}
    ok = efx0(v, X) and sum(map(len, X)) == m and set().union(*X) == set(range(m))
    c["A1_completion_EFX0"] += ok
    c["A1_LEMMA_VIOLATION"] += (ii_ok and iii_ok and iv_ok) and not ok

def b(v, n, m, Y, Yp, J, Jp, u, path, d, DTp, c):
    cand = [a for a in DTp if wants(v, d, Yp[a], Yp) and not any(i not in (a, d) and wants(v, i, Yp[a], Yp) for i in range(n))]
    c[f"B_candidates_{len(cand)}"] += 1
    if len(cand) != 1:
        return
    k = cand[0]; kp = next(a for a in DTp if a != k)
    S = Jp & rel(v, k) & rel(v, kp)
    Z = {Yp[k], Yp[d]} | (Jp - S)
    B1 = len(S) == 2 and val(v, k, S) > v[k][Yp[k]]
    B2 = wants(v, d, Yp[k], Yp) and not any(i not in (k, d) and wants(v, i, Yp[k], Yp) for i in range(n))
    B3 = not any(i != d and wants(v, i, Yp[d], Yp) for i in range(n))
    B4 = (Z & rel(v, k)) == {Yp[k]}
    B5 = all(len(Z & rel(v, i)) < 2 or val(v, i, Z) - min(v[i][g] for g in Z) <= v[i][Yp[i]] for i in range(n) if i not in (k, d))
    for name, x in (("B1", B1), ("B2", B2), ("B3", B3), ("B4", B4), ("B5", B5)):
        c["B_" + name] += x
    X = [{Yp[a]} for a in range(n)]; X[k] = set(S); X[d] = set(Z)
    full = efx0(v, X) and sum(map(len, X)) == m
    c["B_FULL_EFX0"] += full
    c["B_LEMMA_RFB_VIOLATION"] += (B1 and B2 and B3 and B4 and B5) and not full
    # facts (a), (c)
    a_ok = len(S) == 2 and wants(v, k, Yp[kp], Yp)
    others2 = [i for i in range(n) if i not in (k, d) and len(Z & rel(v, i)) >= 2]
    t = Yp[u]
    Ru_ok = rel(v, u) == {t, Y[kp], Y[u], Y[k]}
    Ub = v[u][Y[kp]] >= v[u][Y[u]] + v[u][Y[k]]
    c["B_fact_a"] += a_ok; c["B_fact_c_only_u"] += others2 == [u]; c["B_fact_c_Ru"] += Ru_ok; c["B_fact_Ub"] += Ub
    c["B_w_equals_d"] += path == [d]
    # REPAIR-Y at Y (|J - S| = 1)
    if len(J - S) == 1 and t == Y[d]:
        c["B_JminusS_1"] += 1
        (l,) = J - S
        R1 = val(v, k, S) > v[k][Y[k]] and wants(v, u, Y[k], Y)
        R2 = not any(wants(v, i, Y[u], Y) for i in range(n) if i != u) and not any(i != u and wants(v, i, Y[k], Y) for i in range(n))
        Fk = v[k][Y[kp]] <= val(v, k, S)
        wanters = all(i in (k, u) for i in range(n) if wants(v, i, Y[kp], Y))
        R3u = v[u][Y[kp]] <= v[u][Y[u]] + v[u][Y[k]]
        XR = [{Y[a]} for a in range(n)]; XR[u] = {Y[k], Y[u]}; XR[k] = set(S); XR[kp] = {Y[kp], l}
        okR = efx0(v, XR)
        c["RY_R1_R2_Fk_wanters"] += R1 and R2 and Fk and wanters
        c["RY_R3u_holds"] += R3u
        c["RY_allocation_EFX0"] += okR
        c["RY_LEMMA_VIOLATION"] += (R1 and R2 and Fk and wanters and R3u) and not okR
        c["RY_Ub_strict"] += v[u][Y[kp]] > v[u][Y[u]] + v[u][Y[k]]

if __name__ == "__main__":
    main(sys.argv[1])
