#!/usr/bin/env python3
"""Referee re-validation of K4.MULTI.RECS.N4 (k4/oc1max_multi.md §12 at b8bdc69): the 112,880 REC-S witnesses
(results/k4_oc1max_multi/recs_witnesses_n4.json.gz) against the certifier's n = 4 export (two_move_starts_n4.json.gz,
sha256 6159e38d...). Own code (cert_ref / multi_ref / rec_s_ref helpers); check_recs.py is read, not run or imported.

  coverage : the witness starts are exactly the export's starts (same sets, values, picks; as multisets).
  validity : per witness, the picks are the SD outcome of its order; k in D; P1 = E(k) (my earliest-wanter chain);
             T a pair inside (J + {Y_z}) ∩ R_k, improving; move 1 and move 2 replayed as §29 official moves by my
             own simulator (cert_ref.apply_move: H sets inside relevant goods and current junk, strict gains);
             (L); Lemma SD-E; k' dangerous in I- at B1-; the completion is a partition, extends move 2 by junk only,
             has at most one absorber, gives k exactly T, and is raw EFX0.
  REC-S    : whether the witness's (k', P2, h, H0', allocation) is one of the Theorem S cases (relaxed form, longest
             canonical chain) that my theorem_s_cases enumerates in I- at B1-, and whether (K) holds (so that REC-S
             as stated, not only the shape, applies).
"""
import json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk, apply_move
from multi_ref import frozen_set
from rec_s_ref import earliest_wanter_chain, reduce_inst, theorem_s_cases
from oc1hall_ref import threatened

def key(sets, vals, picks):
    return json.dumps([sets, vals, list(picks)])

def validate(st):
    sets, vals, picks, w = st["sets"], st["vals"], st["picks"], st["witness"]
    r = Counter()
    if w is None:
        r["no_witness"] += 1; return r
    v = mk(sets, vals); n = len(v); m = len(v[0])
    order = w["order"]; Y = sd(v, order)
    if list(Y) != list(picks):
        r["FAIL_picks"] += 1; return r
    B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    k = w["k"]
    if k not in D:
        r["FAIL_k_not_dangerous"] += 1; return r
    E = earliest_wanter_chain(v, list(Y), order, k)
    if E != w["P1"]:
        r["FAIL_P1_not_Ek"] += 1; return r
    z = E[-1]; T = set(w["T"])
    if len(T) != 2 or not T <= (J | {Y[z]}) & rel(v, k) or not val(v, k, T) > p[k]:
        r["FAIL_T"] += 1; return r
    S1 = apply_move(v, B, dict(kind="chain", path=E, H=[sorted(T)] + [[] for _ in E[1:]]))
    if S1 is None:
        r["FAIL_move1_not_official"] += 1; return r
    if not all(v[i][g] < val(v, i, S1[i]) for i in range(n) if i != k and any(v[i]) for g in T):
        r["FAIL_L"] += 1; return r
    agents, goods, vm, Ym, B1 = reduce_inst(v, list(Y), E, T)
    sig = [agents.index(a) for a in order if a != k]
    if list(sd(vm, sig)) != list(Ym):
        r["FAIL_SDE"] += 1; return r
    P2, H0 = w["P2"], set(w["H0_2"])
    if k in P2:
        r["FAIL_P2_touches_k"] += 1; return r
    Bm = [{y} for y in Ym]; Jm = set(range(len(goods))) - set(Ym)
    Fm = frozen_set(vm, Bm); Dm = {d for d in Fm if any(vm[d][g] > 0 for g in Jm)}
    if agents.index(P2[0]) not in Dm:
        r["FAIL_k2_not_dangerous_in_Iminus"] += 1; return r
    S2 = apply_move(v, S1, dict(kind="chain", path=P2, H=[sorted(H0)] + [[] for _ in P2[1:]]))
    if S2 is None:
        r["FAIL_move2_not_official"] += 1; return r
    X = [set(x) for x in w["X"]]
    J2 = set(range(m)) - set().union(*S2)
    if sum(len(x) for x in X) != m or set().union(*X) != set(range(m)):
        r["FAIL_not_partition"] += 1; return r
    if any(not S2[i] <= X[i] or not (X[i] - S2[i]) <= J2 for i in range(n)):
        r["FAIL_not_extension"] += 1; return r
    if sum(1 for i in range(n) if len(X[i] - S2[i]) >= 2) > 1:
        r["FAIL_absorbers"] += 1; return r
    if X[k] != T:
        r["FAIL_Xk"] += 1; return r
    if not efx0(v, X):
        r["FAIL_EFX0"] += 1; return r
    r["valid"] += 1
    # REC-S as stated: is the witness one of the Theorem S cases in I-, and does (K) hold?
    k2m = agents.index(P2[0]); P2m = [agents.index(a) for a in P2]
    hm = goods.index(w["h"]) if w["h"] in goods else None
    Xm = [{goods.index(g) for g in X[a]} for a in agents]
    match = False; anyK = False
    for kq, sq, h, H0q, rr, Am in theorem_s_cases(vm, Ym):
        Xq = [set() for _ in range(n)]
        for i, a in enumerate(agents):
            Xq[a] = {goods[g] for g in Am[i]}
        Xq[k] = set(T)
        K = not any(len(Xq[j]) >= 2 and threatened(v, k, Xq[j], val(v, k, T)) for j in range(n) if j != k)
        anyK |= K
        if kq == k2m and list(sq) == P2m and h == hm and [set(a) for a in Am] == Xm:
            match = True
    r["witness_is_a_theorem_S_case"] += match
    r["REC_S_applies_for_this_order_k_T"] += anyK
    r["H0_contains_worthless_goods"] += any(v[P2[0]][g] == 0 for g in H0)
    return r

def main(witness_path, export_path, procs):
    W = json.load(gzip.open(witness_path))["starts"]
    E = json.load(gzip.open(export_path))
    ex = Counter(key(H["sets"], s["vals"], s["picks"]) for H in E["hypergraphs"] for s in H["starts"])
    wk = Counter(key(st["sets"], st["vals"], st["picks"]) for st in W)
    c = Counter(export_starts=sum(ex.values()), witness_starts=sum(wk.values()),
                export_starts_without_witness=sum((ex - wk).values()), witness_starts_not_in_export=sum((wk - ex).values()))
    with Pool(procs) as pool:
        for r in pool.imap_unordered(validate, W, chunksize=100):
            c.update(r)
    print(json.dumps(dict(source="K4.MULTI.RECS.N4 witnesses re-validated", **dict(sorted(c.items())))))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
