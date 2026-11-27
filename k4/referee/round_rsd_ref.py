#!/usr/bin/env python3
"""Referee check of matching's ROUND-RSD (k4/matching.md §6 at 56e64a9f; round_rsd.py and check_rsd.py read, not run
or imported). Own code (cert_ref / oc1hall_ref / rsd_ref / base_ref helpers).

wit MODE: re-validate the ROUND-RSD witnesses (results/k4_matching/round_rsd_*_witnesses.json.gz) against their inputs
(witness k = index into the distinct input rows, in load order). Per round, at the round's start (present agents,
goods, state): every settlement is a reduction step (k present, one good, frozen among the present agents, values a
junk good; P = (k, ...) distinct present agents, each strictly preferring its predecessor's good; T ⊆ (J ∪ S_end) ∩ R_k,
improving); chains vertex-disjoint, T's disjoint; the stored state is all of them applied at once; (L*) at the round's
end (no T threatens any other agent present at the round's start, at its value after the round); after deleting the
settled agents and their T's every present agent holds one good and the state is the SD outcome of some order. Final:
a partition, deleted agents hold exactly their T, present agents keep their good, at most one present agent receives
two or more goods, raw EFX0 in I.

lift MODE: Lemma LIFT* for rounds as a lemma. From each start, every sequence of admissible rounds (<= 2 settlements,
(L*) at the round's end); at every reached state, every extension X of the state to the junk (any assignment to present
agents): if X is EFX0 among the present agents and (Φ) holds (no bundle of X and no T of a LATER round threatens a
deleted k at v_k(T_k)), the whole allocation must be raw EFX0 in I. Mutation 'skip': (L*) is not checked against the
round's other settled agents (the clause "including two settled agents" of the lemma's proof)."""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from oc1hall_ref import threatened
from rsd_ref import sd_sub
from base_ref import settlements

def is_sd(v, present, goods, S):
    return any(all(sd_sub(v, o, present, goods)[a] == next(iter(S[a])) for a in present)
               for o in itertools.permutations(sorted(present)))

def check_wit(args):
    sets, vals, picks, w = args
    c = Counter(); v = mk(sets, vals); n = len(v); m = len(v[0])
    if not any(sd(v, list(o)) == list(picks) for o in itertools.permutations(range(n))):
        c["FAIL_picks"] += 1; return c
    S = [{y} for y in picks]; present = set(range(n)); goods = set(range(m)); deleted = []
    for rd in w["rounds"]:
        J = goods - set().union(*(S[a] for a in present))
        new = [set(s) for s in S]; used_agents = set(); usedT = set(); K = []
        for st in rd["settled"]:
            k, T, P = st["k"], set(st["T"]), st["P"]
            if k not in present or len(S[k]) != 1 or P[0] != k or len(P) < 2 or len(set(P)) != len(P) or any(a not in present for a in P):
                c["FAIL_agents"] += 1; return c
            (g,) = S[k]
            if not any(i != k and v[i][g] > val(v, i, S[i]) for i in present) or not any(v[k][h] > 0 for h in J):
                c["FAIL_not_dangerous"] += 1; return c
            if any(len(S[P[i - 1]]) != 1 or not val(v, P[i], S[P[i - 1]]) > val(v, P[i], S[P[i]]) for i in range(1, len(P))):
                c["FAIL_chain"] += 1; return c
            if not T or not T <= (J | S[P[-1]]) & rel(v, k) or not val(v, k, T) > val(v, k, S[k]):
                c["FAIL_T"] += 1; return c
            if used_agents & set(P) or usedT & T:
                c["FAIL_not_disjoint"] += 1; return c
            used_agents |= set(P); usedT |= T; K.append((k, T))
            for i in range(1, len(P)):
                new[P[i]] = set(S[P[i - 1]])
            new[k] = set(T)
        if any(sorted(new[a]) != sorted(rd["state"][a]) for a in present):
            c["FAIL_state"] += 1; return c
        if any(threatened(v, a, T, val(v, a, new[a])) for k, T in K for a in present if a != k):
            c["FAIL_Lstar_round_end"] += 1; return c
        c[f"round_size_{len(K)}"] += 1
        present -= {k for k, _ in K}; goods -= usedT; deleted += K; S = new
        if any(len(S[a]) != 1 for a in present):
            c["FAIL_not_single"] += 1; return c
        if present and not is_sd(v, present, goods, S):
            c["FAIL_not_SD"] += 1; return c
    X = [set(x) for x in w["alloc"]]
    if sum(map(len, X)) != m or set().union(*X) != set(range(m)):
        c["FAIL_partition"] += 1; return c
    if any(X[k] != T for k, T in deleted) or any(not S[a] <= X[a] for a in present):
        c["FAIL_keeps"] += 1; return c
    if sum(1 for a in present if len(X[a] - S[a]) >= 2) > 1:
        c["FAIL_absorbers"] += 1; return c
    if not efx0(v, X):
        c["FAIL_EFX0"] += 1; return c
    c["valid"] += 1; c[f"rounds_{len(w['rounds'])}"] += 1
    return c

def load_rows(paths):
    rows = []
    for p in paths:
        if p.endswith(".json.gz"):
            d = json.load(gzip.open(p))
            rows += [(H["sets"], s["vals"], s["picks"]) for H in d["hypergraphs"] for s in H["starts"]]
        else:
            f = gzip.open(p, "rt") if p.endswith(".gz") else open(p)
            rows += [(r["sets"], r["vals"], r["picks"]) for r in map(json.loads, (l for l in f if l.strip()))]
    seen = set(); R = []
    for r in rows:
        k = json.dumps([r[0], r[1], list(r[2])])
        if k not in seen:
            seen.add(k); R.append(r)
    return R

def main_wit(witpath, inputs, procs):
    R = load_rows(inputs); W = json.load(gzip.open(witpath))["witnesses"]
    c = Counter(rows=len(R), witnesses=len(W), distinct_rows_covered=len({w["k"] for w in W}))
    with Pool(procs) as pool:
        for r in pool.imap_unordered(check_wit, [R[w["k"]] + (w,) for w in W], chunksize=100):
            c.update(r)
    print(json.dumps(dict(source=f"ROUND-RSD witnesses re-validated: {witpath.rsplit('/', 1)[-1]}", **dict(sorted(c.items())))))

# ---------- LIFT* (rounds) as a lemma ----------
def round_moves(v, S, present, goods, mut):
    sets_ = list(settlements(v, S, present, goods))
    for r in (1, 2):
        for combo in itertools.combinations(sets_, r):
            ags = [a for _, P, _ in combo for a in P]; Ts = [g for _, _, T in combo for g in T]
            if len(ags) != len(set(ags)) or len(Ts) != len(set(Ts)):
                continue
            new = [set(s) for s in S]
            for k, P, T in combo:
                for i in range(1, len(P)):
                    new[P[i]] = set(S[P[i - 1]])
                new[k] = set(T)
            K = {k for k, _, _ in combo}
            def thr(a, T):
                if mut == "skip" and a in K:
                    return False                 # mutation: (L*) not checked against the round's other settled agents
                return threatened(v, a, T, val(v, a, new[a]))
            if any(thr(a, T) for k, _, T in combo for a in present if a != k):
                continue
            pres2 = present - K; goods2 = goods - set(Ts)
            if any(len(new[a]) != 1 for a in pres2) or (pres2 and not is_sd(v, pres2, goods2, new)):
                continue
            yield new, pres2, goods2, [(k, frozenset(T)) for k, _, T in combo]

def lift_start(args):
    sets, vals, picks, mut = args
    v = mk(sets, vals); n = len(v); m = len(v[0]); c = Counter(); seen = set()
    def walk(S, present, goods, rounds_):
        key = (tuple(map(frozenset, S)), frozenset(present), tuple(frozenset(rd) for rd in rounds_))   # history matters for (Φ)
        if key in seen:
            return
        seen.add(key)
        if rounds_:
            J = sorted(goods - set().union(*(S[a] for a in present)))
            pres = sorted(present)
            for f in itertools.product(pres, repeat=len(J)):
                X = [set(s) for s in S]
                for g, a in zip(J, f):
                    X[a].add(g)
                sub = [X[a] for a in pres]
                if not efx0([v[a] for a in pres], sub):
                    continue
                phi = True
                for ri, rd in enumerate(rounds_):
                    for k, T in rd:
                        tk = val(v, k, T)
                        if any(threatened(v, k, X[a], tk) for a in pres):
                            phi = False
                        if any(threatened(v, k, T2, tk) for rd2 in rounds_[ri + 1:] for _, T2 in rd2):
                            phi = False
                if not phi:
                    continue
                c[f"tests_{mut or 'plain'}"] += 1
                c[f"two_settlement_round_present_{mut or 'plain'}"] += any(len(rd) == 2 for rd in rounds_)
                if not efx0(v, X):
                    c[f"LIFT_VIOLATION_{mut or 'plain'}"] += 1
        for new, p2, g2, rd in round_moves(v, S, present, goods, mut):
            walk(new, p2, g2, rounds_ + [rd])
    walk([{y} for y in picks], set(range(n)), set(range(m)), [])
    return c

def main_lift(inputs, N, seed, mut, procs):
    R = load_rows(inputs); rng = random.Random(seed)
    sample = R if N >= len(R) else rng.sample(R, N)
    c = Counter(starts=len(sample))
    with Pool(procs) as pool:
        for r in pool.imap_unordered(lift_start, [s + (mut,) for s in sample], chunksize=4):
            c.update(r)
    print(json.dumps(dict(source=f"LIFT* (rounds) lemma test, N={N} seed={seed} mutation={mut}, inputs {[p.rsplit('/', 1)[-1] for p in inputs]}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    if sys.argv[1] == "wit":
        main_wit(sys.argv[2], sys.argv[3:-1], int(sys.argv[-1]))
    else:   # lift N seed mut|none procs inputs...
        main_lift(sys.argv[6:], int(sys.argv[2]), int(sys.argv[3]), None if sys.argv[4] == "none" else sys.argv[4], int(sys.argv[5]))
