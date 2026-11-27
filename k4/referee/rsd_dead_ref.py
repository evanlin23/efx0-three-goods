#!/usr/bin/env python3
"""Referee probe of Conjecture RSD-IND as written (k4/matching.md §6 at 8498cde0): it applies to every perfect SD
start carrying phantom constraints from earlier reduction steps with (L*). Search, on the n = 4 export, for a state
reached by ONE reduction step (canonical chain from a dangerous agent k, improving T ⊆ (J ∪ B_end) ∩ R_k of any size,
(L*), the reduced state an SD outcome of the smaller instance) at which there is neither a completion respecting Φ
(a one-absorber completion with a present owner, k keeping T, raw EFX0 in I) nor a reduction step respecting Φ (its T
does not threaten k). Such a dead end satisfies RSD-IND's hypothesis and violates its conclusion. Own code."""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from oc1hall_ref import threatened
from rsd_ref import sd_sub

def steps(v, S, present, goods):
    """every reduction step at state S of the instance (present agents, goods)."""
    J = goods - set().union(*(S[a] for a in present))
    for k in sorted(present):
        if len(S[k]) != 1:
            continue
        (g,) = S[k]
        if not any(i != k and v[i][g] > val(v, i, S[i]) for i in present) or not any(v[k][h] > 0 for h in J):
            continue
        def ext(P):
            last = P[-1]
            for w in sorted(present):
                if w not in P and len(S[last]) == 1 and val(v, w, S[last]) > val(v, w, S[w]):
                    yield P + [w]
                    yield from ext(P + [w])
        for P in ext([k]):
            pool = (J | S[P[-1]]) & rel(v, k)
            for r in range(1, len(pool) + 1):
                for T in itertools.combinations(sorted(pool), r):
                    T = set(T)
                    if not val(v, k, T) > val(v, k, S[k]):
                        continue
                    new = [set(s) for s in S]
                    for i in range(1, len(P)):
                        new[P[i]] = set(S[P[i - 1]])
                    new[k] = set(T)
                    pres2 = present - {k}; goods2 = goods - T
                    if any(threatened(v, a, T, val(v, a, new[a])) for a in pres2):
                        continue
                    if any(len(new[a]) != 1 for a in pres2):
                        continue
                    if not any(all(sd_sub(v, o, pres2, goods2)[a] == next(iter(new[a])) for a in pres2)
                               for o in itertools.permutations(sorted(pres2))):
                        continue
                    yield k, P, T, new, pres2, goods2

def lifting_completion(v, S, present, goods, deleted):
    n = len(S); J = sorted(goods - set().union(*(S[a] for a in present)))
    pres = sorted(present)
    for owner in pres:
        for f in itertools.product(pres, repeat=len(J)):
            cnt = Counter(f)
            if any(cnt[a] >= 2 for a in pres if a != owner):
                continue
            X = [set(s) for s in S]
            for g, a in zip(J, f):
                X[a].add(g)
            for k, T in deleted:
                X[k] = set(T)
            if efx0(v, X):
                return X
    return None

def probe(args):
    sets, vals, picks = args
    v = mk(sets, vals); n = len(v); m = len(v[0])
    S0 = [{y} for y in picks]; c = Counter(); ex = None
    for k, P, T, S1, pres1, goods1 in steps(v, S0, set(range(n)), set(range(m))):
        c["first_steps"] += 1
        if lifting_completion(v, S1, pres1, goods1, [(k, T)]) is not None:
            c["first_step_then_completion"] += 1; continue
        second = [st for st in steps(v, S1, pres1, goods1) if not threatened(v, k, st[2], val(v, k, T))]
        if not second:
            c["DEAD_END_after_one_step"] += 1
            if ex is None:
                ex = dict(sets=sets, vals=vals, picks=list(picks), k=k, P=P, T=sorted(T), state=[sorted(s) for s in S1])
    return c, ex

def main(path, N, seed, procs):
    E = json.load(gzip.open(path))
    rows = [(H["sets"], s["vals"], s["picks"]) for H in E["hypergraphs"] for s in H["starts"]]
    rng = random.Random(seed)
    sample = rows if N >= len(rows) else rng.sample(rows, N)
    c = Counter(); exs = []
    with Pool(procs) as pool:
        for cc, ee in pool.imap_unordered(probe, sample, chunksize=20):
            c.update(cc); c["starts"] += 1; c["starts_with_a_dead_end"] += cc["DEAD_END_after_one_step"] > 0
            if ee and len(exs) < 2:
                exs.append(ee)
    print(json.dumps(dict(source=f"RSD-IND dead ends after one step, n = 4 export sample N={N} seed={seed}", **dict(sorted(c.items())))))
    for e in exs:
        print("EXAMPLE", json.dumps(e))

if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
