#!/usr/bin/env python3
"""Referee spot check of base-phantom's certified rows (k4/base_phantom.md on proof/k4-base-phantom at 0e6d9abc):
K4.BASE.P1FREE.N4 (from every n = 4 two-move start, the P1-free greedy process never gets stuck) and K4.BASE.DEAD.N4
(the 32,480 dead-end records: reachable by admissible rounds, no lifted completion, no admissible round, the
feasibility flag, an "l alone" phantom on a present agent's base). Own code (cert_ref, oc1hall_ref, rsd_ref, base_ref
helpers); nothing from k4/base_phantom/ is run. Definitions as in base_phantom.md §0: settlements from dangerous
agents (frozen among present agents; phantoms do not count as wanters) along canonical chains, T ⊆ (J ∪ B_end) ∩ R_k
improving (any size); rounds of 1-2 settlements, vertex-disjoint, disjoint T; admissible: (L*) at the round's end, (P2)
toward earlier phantoms, the reduced state a perfect SD outcome (all orders); a lifted completion: one present owner,
every other present agent at most one junk good, phantoms nothing, raw EFX0 in I. P1-free settlement: every good of
R_k - T worth <= v_k(T)."""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, mk
from oc1hall_ref import threatened
from rsd_ref import sd_sub
from base_ref import completion

def settlements(v, S, present, goods):
    J = goods - set().union(*(S[a] for a in present))
    for k in sorted(present):
        if len(S[k]) != 1:
            continue
        (g,) = S[k]
        if not any(i != k and v[i][g] > val(v, i, S[i]) for i in present) or not any(v[k][h] > 0 for h in J):
            continue
        def ext(P):
            for w in sorted(present):
                if w not in P and val(v, w, S[P[-1]]) > val(v, w, S[w]):
                    yield P + [w]
                    yield from ext(P + [w])
        for P in ext([k]):
            pool = sorted((J | S[P[-1]]) & rel(v, k))
            for r in range(1, len(pool) + 1):
                for T in itertools.combinations(pool, r):
                    if val(v, k, T) > val(v, k, S[k]):
                        yield k, tuple(P), frozenset(T)

def p1free(v, k, T):
    tau = val(v, k, T)
    return all(v[k][g] <= tau for g in rel(v, k) - T)

def rounds(v, S, present, goods, phantoms, rule):
    sets_ = [s for s in settlements(v, S, present, goods) if rule == "any" or p1free(v, s[0], s[2])]
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
            if any(threatened(v, a, T, val(v, a, new[a])) for k, _, T in combo for a in present if a != k):
                continue
            if any(threatened(v, f, T, tf) for _, _, T in combo for f, tf in phantoms):
                continue
            K = {k for k, _, _ in combo}; pres2 = present - K; goods2 = goods - set(Ts)
            if any(len(new[a]) != 1 for a in pres2):
                continue
            if pres2 and not any(all(sd_sub(v, o, pres2, goods2)[a] == next(iter(new[a])) for a in pres2)
                                 for o in itertools.permutations(sorted(pres2))):
                continue
            yield combo, new, pres2, goods2, phantoms + [(k, val(v, k, T)) for k, _, T in combo]

def lifted(v, S, present, goods):
    return completion(v, [set(s) for s in S], present, goods, present) is not None

def explore(v, S, present, goods, phantoms, rule, memo):
    key = (tuple(map(frozenset, S)), frozenset(present))
    if key in memo:
        return memo[key]
    memo[key] = True
    if lifted(v, S, present, goods):
        return True
    nxt = list(rounds(v, S, present, goods, phantoms, rule))
    ok = bool(nxt) and all(explore(v, S2, p2, g2, ph2, rule, memo) for _, S2, p2, g2, ph2 in nxt)
    memo[key] = ok
    return ok

def safe_job(args):
    sets, vals, picks = args
    v = mk(sets, vals); n = len(v); m = len(v[0]); S0 = [{y} for y in picks]
    return {r: explore(v, S0, set(range(n)), set(range(m)), [], r, {}) for r in ("P1free", "any")}

def dead_job(rec):
    c = Counter(); v = mk(rec["sets"], rec["vals"]); n = len(v); m = len(v[0])
    S = [{y} for y in rec["picks"]]; present = set(range(n)); goods = set(range(m)); phantoms = []
    for rd in rec["path"]:
        want = sorted((k, tuple(P), tuple(sorted(T))) for k, P, T in rd)
        hit = None
        for combo, S2, p2, g2, ph2 in rounds(v, S, present, goods, phantoms, "any"):
            if sorted((k, P, tuple(sorted(T))) for k, P, T in combo) == want:
                hit = (S2, p2, g2, ph2); break
        if hit is None:
            c["FAIL_path_round_not_admissible"] += 1; return c
        S, present, goods, phantoms = hit
    if sorted(present) != sorted(rec["alive"]) or any(sorted(S[a]) != sorted(rec["B"][a]) for a in range(n)):
        c["FAIL_state"] += 1; return c
    c["state_reached"] += 1
    c["FAIL_has_lifted_completion"] += lifted(v, S, present, goods)
    c["FAIL_has_admissible_round"] += any(True for _ in rounds(v, S, present, goods, phantoms, "any"))
    # feasibility: some allocation of the present goods to the present agents, phantoms keeping T, raw EFX0 in I
    pg = sorted(goods); pa = sorted(present); feas = False
    for f in itertools.product(pa, repeat=len(pg)):
        X = [set(s) if a not in present else set() for a, s in enumerate(S)]
        for g, a in zip(pg, f):
            X[a].add(g)
        if efx0(v, X):
            feas = True; break
    c["feasible_matches_flag"] += feas == rec["feasible"]; c["feasible"] += feas
    la = any(v[k][next(iter(S[a]))] > tk for k, tk in phantoms for a in present
             if len(S[a]) == 1 and next(iter(S[a])) in rel(v, k) - S[k])
    c["l_alone_on_a_base"] += la
    return c

def main(kind, N, seed, procs):
    S_ = "/tmp/claude-0/-home-user-efx0-three-goods/821a7fdf-a86c-53b6-af3e-8e725637f039/scratchpad/bp"
    rng = random.Random(seed); c = Counter()
    if kind == "safe":
        d = json.load(gzip.open(sys.argv[5]))
        rows = list({json.dumps([H["sets"], s["vals"], s["picks"]]): (H["sets"], s["vals"], s["picks"])
                     for H in d["hypergraphs"] for s in H["starts"]}.values())
        sample = rows if N >= len(rows) else rng.sample(rows, N)
        with Pool(procs) as pool:
            for r in pool.imap_unordered(safe_job, sample, chunksize=10):
                c["starts"] += 1; c["P1free_safe"] += r["P1free"]; c["any_safe"] += r["any"]
                c["P1FREE_UNSAFE"] += not r["P1free"]; c["any_unsafe"] += not r["any"]
    else:
        recs = [json.loads(l) for l in gzip.open(sys.argv[5], "rt")]
        sample = recs if N >= len(recs) else rng.sample(recs, N)
        with Pool(procs) as pool:
            for r in pool.imap_unordered(dead_job, sample, chunksize=10):
                c.update(r); c["records"] += 1
    print(json.dumps(dict(source=f"base-phantom {kind} check N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
