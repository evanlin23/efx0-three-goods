#!/usr/bin/env python3
"""Per-stage breakdown at the 7 n = 5 starts with no REC-S configuration (K4.MULTI.RECS.EXIST.N5): for every order
giving the picks and every dangerous k: E(k), improving pool pairs T ⊆ (J ∪ {Y_z}) ∩ R_k, SD-E, Theorem S cases of I-,
raw EFX0 of the final allocation. Own code; data from the certifier's summary file, read as data."""
import itertools, json, gzip, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from multi_ref import frozen_set
from rec_s_ref import earliest_wanter_chain, reduce_inst, theorem_s_cases
WANT = {38, 419, 447, 773, 813, 963, 1073}
for line in gzip.open(sys.argv[1], "rt"):
    d = json.loads(line)
    if d["idx"] not in WANT:
        continue
    for s in d.get("oc1_fails", []):
        v = mk(d["sets"], s["vals"]); Y = s["picks"]; n = len(Y); m = len(v[0])
        orders = [list(o) for o in itertools.permutations(range(n)) if sd(v, list(o)) == list(Y)]
        J = set(range(m)) - set(Y); F = frozen_set(v, [{y} for y in Y]); D = sorted(d_ for d_ in F if any(v[d_][g] > 0 for g in J))
        c = Counter(orders=len(orders), dangerous=len(D))
        for sigma in orders:
            for k in D:
                E = earliest_wanter_chain(v, list(Y), sigma, k)
                if E is None or E == "CYCLE":
                    c["E_none_or_cycle"] += 1; continue
                pool = (J | {Y[E[-1]]}) & rel(v, k)
                for T in itertools.combinations(sorted(pool), 2):
                    T = set(T)
                    if not val(v, k, T) > v[k][Y[k]]:
                        continue
                    c["improving_pool_pairs"] += 1
                    agents, goods, vm, Ym, B1 = reduce_inst(v, list(Y), E, T)
                    if [sd(vm, [agents.index(a) for a in sigma if a != k])[i] for i in range(len(agents))] != list(Ym):
                        c["SDE_fails"] += 1; continue
                    c["SDE_holds"] += 1
                    cases = list(theorem_s_cases(vm, Ym))
                    c["theorem_S_cases"] += len(cases)
                    for kq, sq, h, H0, r, Am in cases:
                        X = [set() for _ in range(n)]
                        for i, a in enumerate(agents):
                            X[a] = {goods[g] for g in Am[i]}
                        X[k] = set(T); c["final_raw_EFX0"] += efx0(v, X)
        print(json.dumps(dict(idx=d["idx"], picks=Y, **dict(sorted(c.items())))))
