#!/usr/bin/env python3
"""Referee check of the named SLOT residue instances of §10 (K4.MULTI.SLOT2; k4/oc1max_multi.md at b107719): log720,
log613, n4_3#947.0. Own code; the instances are read from K4.MULTI.DATA as data only.

Per instance: (1) no (k in D, longest canonical chain from k, h in J + {Y_z}) meets Theorem S's hypotheses ((S-a),
(S-b), (S-c), (S-d')); (2) the least kept-out set |H| of an S* completion with owner k after some canonical chain from
some k in D and improving H0 ⊆ Pi (raw EFX0, brute force over every S*-shaped allocation); (3) for log613, the printed
value lists of §10 against the data, and the Hall-violation narrative with the data's values.
"""
import json, gzip, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, sd
from multi_ref import frozen_set, canonical_chains, subsets, sstar_allocs
from theorem_s_ref import after_chain

def load(paths, names):
    """names: {name: picks} (a name can label several starts of one instance)."""
    out = {}
    for path in paths:
        for line in gzip.open(path, "rt"):
            d = json.loads(line)
            if d["name"] in names and d["picks"] == names[d["name"]] and d["name"] not in out:
                I = d["inst"]; n = len(I["sets"]); m = I["m"]
                v = [[0] * m for _ in range(n)]
                for i in range(n):
                    for g, x in zip(I["sets"][i], I["vals"][i]):
                        v[i][g] = x
                yd = sd(v, d["order"]); Y = [yd[i] for i in range(n)]
                assert Y == d["picks"], (d["name"], Y, d["picks"])
                out[d["name"]] = (v, Y, d["order"])
    return out

def theorem_s_applies(v, Y):
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B); p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    U = [u for u in range(n) if u not in F and Y[u] is not None]
    allch = list(canonical_chains(v, Y, F))
    for k in D:
        ch = [s for s in allch if s[0] == k]
        L = max(len(s) for s in ch)
        for seq in [s for s in ch if len(s) == L]:
            z = seq[-1]; a = Y[seq[-2]]
            for h in sorted(J) + [Y[z]]:
                W = (J | {Y[z]}) - {h}
                if not val(v, k, W) > p[k]:
                    continue
                if any(threatened(v, d, W, p[d]) for d in D if d != k):
                    continue
                if any(threatened(v, u, W, p[u]) for u in U if u != z):
                    continue
                H0 = {g for g in W if v[k][g] > 0}
                zf = z in frozen_set(v, after_chain(Y, seq, H0))
                if not threatened(v, z, W, v[z][a] + (0 if zf else v[z][h])):
                    return (k, seq, h)
    return None

def least_H(v, Y):
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B); p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    best = None
    for seq in canonical_chains(v, Y, F):
        k = seq[0]
        if k not in D:
            continue
        Pi = J | {Y[seq[-1]]}
        for H0 in subsets({g for g in Pi if v[k][g] > 0}):
            if not val(v, k, H0) > p[k]:
                continue
            Bp = after_chain(Y, seq, H0)
            for X in sstar_allocs(v, Bp, k):
                if efx0(v, X):
                    H = sum(len(X[i]) - len(Bp[i]) for i in range(n) if i != k)
                    if best is None or H < best[0]:
                        best = (H, seq, sorted(H0), [sorted(x) for x in X])
    return best

def theorem_u_covers(v, Y):
    """Theorem U's hypotheses (§3) at a start of K4.MULTI.DATA (all hard): D_T = {k}; some longest canonical chain
    from k with E_J ⊆ {z} and (z in E_J => z unfrozen after P)."""
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B); p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    DT = [d for d in D if threatened(v, d, J, p[d])]
    if len(DT) != 1:
        return False
    (k,) = DT
    EJ = {u for u in range(n) if u not in F and Y[u] is not None and threatened(v, u, J, p[u])}
    ch = [s for s in canonical_chains(v, Y, F) if s[0] == k]
    L = max(len(s) for s in ch)
    for seq in [s for s in ch if len(s) == L]:
        z = seq[-1]
        H0 = {g for g in J if v[k][g] > 0}
        if EJ <= {z} and (z not in EJ or z not in frozen_set(v, after_chain(Y, seq, H0))):
            return True
    return False

def main(paths):
    names = {"log720": [3, 7, 6, 5], "log613": [1, 2, 3], "n4_3#947.0": [4, 3, 6, 5, 7]}
    I = load(paths, names)
    for nm in names:
        v, Y, order = I[nm]
        print(json.dumps(dict(instance=nm, n=len(Y), m=len(v[0]), picks=Y, theorem_S_or_U_applies=str(theorem_s_applies(v, Y)),
                              least_H=str(least_H(v, Y)))))
    cu = 0; tot = 0
    for path in paths:
        for line in gzip.open(path, "rt"):
            d = json.loads(line); J_ = d["inst"]; n = len(J_["sets"]); m = J_["m"]
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(J_["sets"][i], J_["vals"][i]):
                    v[i][g] = x
            yd = sd(v, d["order"]); tot += 1; cu += theorem_u_covers(v, [yd[i] for i in range(n)])
    print(json.dumps(dict(starts=tot, theorem_U_covers=cu)))
    v, Y, order = I["log613"]
    data = {i: {g: v[i][g] for g in range(len(v[i])) if v[i][g] > 0} for i in range(len(v))}
    printed = {0: {0: 3, 1: 4, 2: 10, 3: 8}, 1: {2: 8, 4: 2, 5: 3, 6: 4}, 2: {3: 7, 4: 3, 5: 5, 6: 6}}
    print(json.dumps(dict(log613_data_values=str(data), printed_values=str(printed),
                          agree={i: data[i] == printed[i] for i in data})))
    # the narrative with the data's values: k = 1, chain (1, 0), H0 = {4, 5, 6}
    Bp = after_chain(Y, [1, 0], {4, 5, 6}); Jp = sorted(set(range(len(v[0]))) - set().union(*Bp))
    print(json.dumps(dict(k1_Bprime=[sorted(b) for b in Bp], Jprime=Jp, frozen_after=sorted(frozen_set(v, Bp)),
                          X_H1_threatens_2={h: threatened(v, 2, ({0, 1, 4, 5, 6} - {h}), val(v, 2, Bp[2])) for h in Jp},
                          agent2_values_Jprime=[v[2][g] for g in Jp],
                          H01_allocation_efx0=efx0(v, [{2, 1}, {4, 5, 6}, {3, 0}]))))
    # the same narrative with the printed values
    w = [[0] * 7 for _ in range(3)]
    for i, d in printed.items():
        for g, x in d.items():
            w[i][g] = x
    Yp = [sd(w, order)[i] for i in range(3)]
    print(json.dumps(dict(printed_picks_with_data_order=Yp,
                          printed_H01_allocation_efx0=efx0(w, [{2, 1}, {4, 5, 6}, {3, 0}]),
                          printed_v2_456_minus_cheapest=val(w, 2, {4, 5, 6}) - min(w[2][g] for g in (4, 5, 6)),
                          printed_p2=w[2][3])))

if __name__ == "__main__":
    main(sys.argv[1:])
