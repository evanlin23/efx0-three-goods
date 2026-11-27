#!/usr/bin/env python3
"""Referee re-validation of K4.MATCH.RSD.N4 (k4/matching.md §6, proof/k4-matching at 8498cde0): the 112,880 RSD
witnesses (results/k4_matching/rsd_n4_witnesses.json.gz) against the certifier's n = 4 export. Own code (cert_ref.py:
SD, raw EFX0, §29 move simulation); check_rsd.py was read, not run or imported.

Per witness, from the definitions of §6 ("Iterated reduction"): the picks are an SD outcome; for each reduction step at
the current instance (present agents and goods) and state: k present, holding one good wanted by another present agent,
valuing a junk good of the current instance; P = (k, x_1, ..., x_t) distinct present agents, each x_i strictly
preferring x_{i-1}'s good to its own; T ⊆ (junk ∪ B_{x_t}) ∩ R_k with v_k(T) > v_k(B_k); the stored state is the result;
(L*) T threatens no other present agent at its value after P; after deleting k and T every present bundle is one good
and the state is the SD outcome of some order of the smaller instance. Also: each step is a §29 official move of the
full instance I from the full state (my simulator). Final allocation: keeps the last state's bundles, deleted agents
hold exactly T, at most one present agent receives two or more goods, a partition, raw EFX0 in I; and (Φ) as Lemma
PHANTOM predicts (the exact phantom conditions agree with the raw threat test on every deleted agent).
"""
import itertools, json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk, apply_move
from oc1hall_ref import threatened

def sd_sub(v, order, agents, goods):
    taken = set(); Y = {}
    for i in order:
        R = [g for g in goods if v[i][g] > 0 and g not in taken]
        if R:
            g = max(R, key=lambda g: (v[i][g], -g)); Y[i] = g; taken.add(g)
        else:
            Y[i] = None
    return Y

def phantom_pred(v, k, T, y, X):
    """Lemma PHANTOM's exact condition for bundle X (disjoint from T)."""
    Rk = rel(v, k); tau = val(v, k, T)
    if len(T) == 3:
        return False
    ells = [g for g in Rk if g not in T and g != y]
    l = ells[0] if ells else None
    if l is None:
        return False
    P1 = l in X and len(X) >= 2 and v[k][l] > tau
    P2 = y in X and l in X and len(X) >= 3 and v[k][y] + v[k][l] > tau
    return P1 or P2

def check(args):
    sets, vals, picks, orders, w = args
    c = Counter()
    v = mk(sets, vals); n = len(v); m = len(v[0])
    if not any(sd(v, list(o)) == list(picks) for o in (orders or itertools.permutations(range(n)))):
        c["FAIL_picks"] += 1; return c
    S = [{y} for y in picks]; present = set(range(n)); goods = set(range(m)); deleted = []
    full = [set(s) for s in S]
    for st in w["steps"]:
        k, T, P = st["k"], set(st["T"]), st["P"]
        J = goods - set().union(*(S[a] for a in present))
        if k not in present or len(S[k]) != 1 or P[0] != k or len(set(P)) != len(P) or any(a not in present for a in P) or len(P) < 2:
            c["FAIL_step_agents"] += 1; return c
        (g,) = S[k]
        if not any(i != k and v[i][g] > val(v, i, S[i]) for i in present):
            c["FAIL_k_not_frozen"] += 1; return c
        if not any(v[k][h] > 0 for h in J):
            c["FAIL_k_not_dangerous"] += 1; return c
        for i in range(1, len(P)):
            if len(S[P[i - 1]]) != 1 or not val(v, P[i], S[P[i - 1]]) > val(v, P[i], S[P[i]]):
                c["FAIL_chain"] += 1; return c
        if not T <= (J | S[P[-1]]) & rel(v, k) or not val(v, k, T) > val(v, k, S[k]):
            c["FAIL_T"] += 1; return c
        new = [set(s) for s in S]
        for i in range(1, len(P)):
            new[P[i]] = set(S[P[i - 1]])
        new[k] = set(T)
        if [sorted(new[a]) if a in present else None for a in range(n)] != [sorted(x) if a in present else None for a, x in enumerate(st["state"])]:
            # deleted agents' entries in the stored state may hold their T; compare present agents only
            if any(sorted(new[a]) != sorted(st["state"][a]) for a in present):
                c["FAIL_state"] += 1; return c
        if any(threatened(v, a, T, val(v, a, new[a])) for a in present if a != k):
            c["FAIL_Lstar"] += 1; return c
        # official §29 move of the full instance from the full state
        mv = dict(kind="chain", path=P, H=[sorted(T)] + [[] for _ in P[1:]])
        res = apply_move(v, full, mv)
        if res is None:
            c["not_official_in_I"] += 1
        else:
            full = res
        present.discard(k); goods -= T; deleted.append((k, T, list(S[k])[0]))
        S = new
        if any(len(S[a]) != 1 for a in present):
            c["FAIL_not_single"] += 1; return c
        ok = any(all(sd_sub(v, o, present, goods)[a] == next(iter(S[a])) for a in present)
                 for o in itertools.permutations(sorted(present)))
        if not ok:
            c["FAIL_not_SD"] += 1; return c
    X = [set(x) for x in w["alloc"]]
    if sum(len(x) for x in X) != m or set().union(*X) != set(range(m)):
        c["FAIL_partition"] += 1; return c
    if any(X[k] != T for k, T, y in deleted) or any(not S[a] <= X[a] for a in present):
        c["FAIL_keeps"] += 1; return c
    if sum(1 for a in present if len(X[a] - S[a]) >= 2) > 1:
        c["FAIL_absorbers"] += 1; return c
    if not efx0(v, X):
        c["FAIL_EFX0"] += 1; return c
    # Lemma PHANTOM's prediction against the raw threat, for every deleted agent and every other bundle
    for k, T, y in deleted:
        for j in range(n):
            if j != k:
                if phantom_pred(v, k, T, y, X[j]) != threatened(v, k, X[j], val(v, k, T)):
                    c["PHANTOM_MISMATCH"] += 1
                c["phantom_tests"] += 1
    c["valid"] += 1
    c["T_sizes_" + "_".join(str(len(T)) for _, T, _ in deleted)] += 1
    return c

def main(export, wit, procs):
    E = json.load(gzip.open(export))
    rows = []; seen = set()
    for H in E["hypergraphs"]:
        for s in H["starts"]:
            key = json.dumps([H["sets"], s["vals"], s["picks"]])
            if key in seen:
                continue
            seen.add(key); rows.append((H["sets"], s["vals"], s["picks"], s.get("orders")))
    W = json.load(gzip.open(wit))["witnesses"]
    args = [rows[w["k"]] + (w,) for w in W]
    c = Counter(rows=len(rows), witnesses=len(W), distinct_rows_covered=len({w["k"] for w in W}))
    with Pool(procs) as pool:
        for r in pool.imap_unordered(check, args, chunksize=200):
            c.update(r)
    print(json.dumps(dict(source="K4.MATCH.RSD.N4 witnesses re-validated", **dict(sorted(c.items())))))


def phantom_random(N, seed):
    """Lemma PHANTOM against the raw threat test on random agents (|R_k| = 3 or 4, strict) and random bundles."""
    import random
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        m = 8; d = rng.choice([3, 4]); R = rng.sample(range(m), d)
        v = [[0] * m]
        for g, x in zip(R, rng.sample(range(1, 60), d)):
            v[0][g] = x
        y = rng.choice(R)
        rest = [g for g in R if g != y]
        tsz = rng.choice([2, 3]) if d == 4 else 2
        T = set(rng.sample(rest, tsz))
        if not val(v, 0, T) > v[0][y]:
            continue
        others = [g for g in range(m) if g not in T]
        X = set(rng.sample(others, rng.randint(1, len(others))))
        c["tests"] += 1
        if phantom_pred(v, 0, T, y, X) != threatened(v, 0, X, val(v, 0, T)):
            c["MISMATCH"] += 1
    print(json.dumps(dict(source=f"Lemma PHANTOM random N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    if sys.argv[1] == "phantom":
        phantom_random(int(sys.argv[2]), int(sys.argv[3]))
    else:
        main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
