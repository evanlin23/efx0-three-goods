#!/usr/bin/env python3
"""Referee check of Proposition K-loc (k4/oc1max_multi.md §14 on proof/k4-oc1max-multi at 6b6cf7b) and of Lemma WG
(§13). Own code (rec_s_ref / theorem_s_ref / multi_ref / cert_ref helpers), raw EFX0; nothing from
k4/oc1max_multi/ is run or imported. Data files are read as data.

K-loc (and the referee's corrected localization, where l sits after P': at q, or at q's successor on P'): for every order giving the picks, every k in D, every improving pair T ⊆ (J ∪ {Y_z}) ∩ R_k of E(k), and every
Theorem S case (relaxed, longest chain) of I- with its allocation X-: does (K) fail (some bundle of X- threatens k at
v_k(T))? K-loc's prediction: (K) holds whenever the receiver r and the head z' avoid q (the holder at B1 of a pick l
with v_k(l) > v_k(T)), and z' != x_1 when k values a third pool good. Counted: cases where (K) fails although K-loc
predicts it holds, classified by where l sits in X- and how it got there.
WG: at states after canonical chains (data and random), every owner o and agent i: if (W2) and (W3) hold (with or
without (W1)), the allocation "o takes B_o ∪ (J ∩ R_i), |H| distinct holders take one good of H = J - R_i each" is
raw EFX0.
"""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from multi_ref import frozen_set, canonical_chains, subsets
from oc1hall_ref import threatened
from rec_s_ref import earliest_wanter_chain, reduce_inst, theorem_s_cases
from theorem_s_ref import after_chain

def kloc_start(args):
    v, Y, orders = args
    c = Counter(); ex = []
    n = len(Y); m = len(v[0])
    B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    for sigma in orders:
        for k in sorted(D):
            E = earliest_wanter_chain(v, list(Y), list(sigma), k)
            if E is None or E == "CYCLE":
                continue
            z = E[-1]
            pool = (J | {Y[z]})
            for T in itertools.combinations(sorted(pool & rel(v, k)), 2):
                T = set(T)
                if not val(v, k, T) > p[k]:
                    continue
                agents, goods, vm, Ym, B1 = reduce_inst(v, list(Y), E, T)
                if [sd(vm, [agents.index(a) for a in sigma if a != k])[i] for i in range(len(agents))] != list(Ym):
                    c["SDE_fail"] += 1; continue
                ells = [g for g in rel(v, k) if g not in T and g != Y[k]]
                tauk = val(v, k, T)
                qs = {}
                for g in ells:
                    if g in Y and v[k][g] > tauk:
                        h = [a for a in range(n) if B1[a] == {g}]
                        if h:
                            qs[g] = h[0]
                third = [g for g in ells if g in pool - T and p[k] + v[k][g] > tauk]
                for kq, sq, h, H0, r, Am in theorem_s_cases(vm, Ym):
                    X = [set() for _ in range(n)]
                    for i, a in enumerate(agents):
                        X[a] = {goods[g] for g in Am[i]}
                    X[k] = set(T)
                    Kfails = any(len(X[j]) >= 2 and threatened(v, k, X[j], tauk) for j in range(n) if j != k)
                    rI = agents[r]; zI = agents[sq[-1]]; P2 = [agents[a] for a in sq]
                    safe_pred = all(q not in (rI, zI) for q in qs.values()) and not (zI == E[1] and third)
                    # corrected localization: where l sits after P' (q itself, or q's successor on P')
                    def after(q):
                        return P2[P2.index(q) + 1] if q in P2 and q != zI else q
                    safe_fix = all(q != zI and after(q) != rI for q in qs.values()) and not (zI == E[1] and third)
                    c["corrected_KLOC_COUNTEREXAMPLE"] += (Kfails and safe_fix)
                    c["corrected_predicts_fail_but_K_holds"] += ((not safe_fix) and not Kfails)
                    c["cases"] += 1; c["K_fails"] += Kfails
                    if Kfails and safe_pred:
                        c["KLOC_COUNTEREXAMPLE"] += 1
                        how = []
                        for g, q in qs.items():
                            holder = [a for a in range(n) if g in X[a]][0]
                            if len(X[holder]) >= 2:
                                how.append(("l travelled along P'" if q in P2 and q != zI else "other", "q", q, "l ends at", holder,
                                            "receiver", rI, "head", zI))
                        c["kloc_cex_" + (how[0][0] if how else "unclassified")] += 1
                        if len(ex) < 3:
                            ex.append(dict(v=v, picks=list(Y), order=list(sigma), k=k, E=E, T=sorted(T), P2=P2, h=goods[h] if h < len(goods) else h,
                                           receiver=rI, X=[sorted(x) for x in X], how=how))
    return c, ex

def wg_state(v, Bst, c):
    n = len(Bst); m = len(v[0]); J = set(range(m)) - set().union(*Bst)
    b = [val(v, i, Bst[i]) for i in range(n)]
    fr = frozen_set(v, Bst)
    if any(v[i][g] > b[i] for i in range(n) for g in J):
        return  # (G2) fails
    if any(len(Bst[q]) >= 2 and any(threatened(v, i, Bst[q], b[i]) for i in range(n) if i != q) for q in range(n)):
        return  # (G1) fails (multi-good base bundles threaten nobody)
    for o in range(n):
        holders = [u for u in range(n) if u != o and len(Bst[u]) <= 1 and u not in fr]
        for i in range(n):
            if i == o:
                continue
            H = J - rel(v, i)
            X = set(Bst[o]) | (J & rel(v, i))
            W1 = Bst[o] <= rel(v, i)
            W2 = not any(threatened(v, a, X, b[a]) for a in range(n) if a != o)
            W3 = len(holders) >= len(H)
            if not (W2 and W3):
                continue
            c["wg_cases"] += 1; c["wg_cases_with_W1"] += W1
            A = [set(x) for x in Bst]; A[o] = X
            for u, g in zip(holders, sorted(H)):
                A[u] = A[u] | {g}
            if not efx0(v, A):
                c["WG_FAIL" + ("" if W1 else "_without_W1")] += 1

def wg_run(N, seed):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        n = rng.randint(3, 5); m = rng.randint(n + 2, n + 4)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.choice([3, 4, 4])), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        o_ = list(range(n)); rng.shuffle(o_)
        Y = sd(v, o_)
        if None in Y:
            continue
        F = frozen_set(v, [{y} for y in Y]); J = set(range(m)) - set(Y)
        for seq in canonical_chains(v, Y, F):
            k = seq[0]
            for H0 in subsets((J | {Y[seq[-1]]}) & rel(v, k)):
                if val(v, k, H0) > v[k][Y[k]]:
                    c["states"] += 1
                    wg_state(v, after_chain(Y, seq, H0), c)
    print(json.dumps(dict(source=f"Lemma WG random N={N} seed={seed}", **dict(sorted(c.items())))))

def load_export(path):
    d = json.load(gzip.open(path))
    for H in d["hypergraphs"]:
        for s in H["starts"]:
            v = mk(H["sets"], s["vals"]); Y = s["picks"]
            orders = [o for o in itertools.permutations(range(len(Y))) if sd(v, list(o)) == list(Y)]
            yield v, Y, orders

def load_jsonl(path):
    f = gzip.open(path, "rt") if path.endswith(".gz") else open(path)
    for line in f:
        d = json.loads(line); n = len(d["sets"]); m = 1 + max(g for s in d["sets"] for g in s)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(d["sets"][i], d["vals"][i]):
                v[i][g] = x
        Y = sd(v, d["order"])
        orders = [o for o in itertools.permutations(range(n)) if sd(v, list(o)) == list(Y)]
        yield v, Y, orders

def kloc_run(kind, path, procs):
    it = load_export(path) if kind == "export" else load_jsonl(path)
    c = Counter(); ex = []
    with Pool(procs) as pool:
        for cc, ee in pool.imap_unordered(kloc_start, it, chunksize=50):
            c.update(cc); c["starts"] += 1
            if ee and len(ex) < 3:
                ex += ee
    print(json.dumps(dict(source=f"Proposition K-loc on {path.rsplit('/', 1)[-1]}", **dict(sorted(c.items())))))
    for e in ex[:3]:
        print("EXAMPLE", json.dumps(e))

if __name__ == "__main__":
    if sys.argv[1] == "wg":
        wg_run(int(sys.argv[2]), int(sys.argv[3]))
    else:
        kloc_run(sys.argv[1], sys.argv[2], int(sys.argv[3]))
