#!/usr/bin/env python3
"""Referee check of matching's base-case result K4.MATCH.RSD.BASE (k4/matching.md §6 and
attempts/k4-matching-rsd-base.md at 56e64a9f): on the 10,109 distinct one-absorber-hard starts with a one-move repair
(results/k4_matching/data/onemove_hard_{multi,hall2071,pw291}.jsonl.gz, read as data), pure reduction with a
completion at once fails at 35 starts with (L*) at each step, and at 6 even with (L*) deferred and deleted agents
receiving junk (smallest ls-alt-rule-n4m7); ROUND-RSD (rounds of <= 2, (L*) at the round's end) fails at the same 35.
Own code only (cert_ref / oc1hall_ref / rsd_ref helpers); nothing from k4/matching or attempts/ is run.

A reduction step at a state S of the current instance (present agents A, goods G; every present agent holds one good):
k in A is dangerous (some other present agent strictly prefers S_k to its own good, and k values a junk good of the
current instance); P = (k, x_1, ..., x_t), t >= 1, distinct present agents, each x_i strictly preferring S_{x_{i-1}} to
S_{x_i}; T ⊆ (J ∪ S_{x_t}) ∩ R_k of any size with v_k(T) > v_k(S_k); optionally (L*): T threatens no other present
agent at its value after P; then k and T are deleted, every present agent must hold one good, and the state must be
the SD outcome of some order of the smaller instance. A round applies 1 or 2 such settlements at once (vertex-disjoint
chains, disjoint T's), (L*) read at the round's end for every agent present at the round's start.
Completion at once: an owner among the allowed agents takes any junk, every other allowed agent at most one junk good;
deleted agents keep their T; raw EFX0 in I. Allowed: the present agents, or (DEADRECV) every agent.
Forms: i = (L*) at the step; ii = (L*) deferred; irecv = (L*) at the step + DEADRECV; iii = deferred + DEADRECV;
R = ROUND-RSD (rounds of <= 2, (L*) at the round's end, allowed = present)."""
import itertools, json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk, complete, oc_depth
from oc1hall_ref import threatened
from rsd_ref import sd_sub

def completion(v, S, present, goods, allowed):
    J = sorted(goods - set().union(*(S[a] for a in present)))
    al = sorted(allowed)
    for o in al:
        others = [a for a in al if a != o]
        def rec(i, X, used):
            if i == len(J):
                return X if efx0(v, X) else None
            g = J[i]
            X[o].add(g); r = rec(i + 1, X, used); X[o].discard(g)
            if r is not None:
                return r
            for a in others:
                if a not in used:
                    X[a].add(g); r = rec(i + 1, X, used | {a}); X[a].discard(g)
                    if r is not None:
                        return r
            return None
        r = rec(0, [set(s) for s in S], frozenset())
        if r is not None:
            return r
    return None

def settlements(v, S, present, goods):
    J = goods - set().union(*(S[a] for a in present))
    for k in sorted(present):
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

def rounds(v, S, present, goods, lstar, rmax):
    sets_ = list(settlements(v, S, present, goods))
    for r in range(1, rmax + 1):
        for combo in itertools.combinations(sets_, r):
            ags = [a for _, P, _ in combo for a in P]
            if len(ags) != len(set(ags)):
                continue
            Ts = [g for _, _, T in combo for g in T]
            if len(Ts) != len(set(Ts)):
                continue
            new = [set(s) for s in S]
            for k, P, T in combo:
                for i in range(1, len(P)):
                    new[P[i]] = set(S[P[i - 1]])
                new[k] = set(T)
            if lstar and any(threatened(v, a, T, val(v, a, new[a])) for k, _, T in combo for a in present if a != k):
                continue
            K = {k for k, _, _ in combo}; pres2 = present - K; goods2 = goods - set(Ts)
            if any(len(new[a]) != 1 for a in pres2):
                continue
            if pres2 and not any(all(sd_sub(v, o, pres2, goods2)[a] == next(iter(new[a])) for a in pres2)
                                 for o in itertools.permutations(sorted(pres2))):
                continue
            yield [tuple(map(frozenset, new)), pres2, goods2, combo]

def solvable(v, S, present, goods, form, memo):
    key = (S, present)
    if key in memo:
        return memo[key]
    lstar = form in ("i", "irecv", "R"); recv = form in ("irecv", "iii"); rmax = 2 if form == "R" else 1
    allowed = set(range(len(v))) if recv else present
    ok = completion(v, [set(s) for s in S], present, goods, allowed) is not None
    if not ok:
        for S2, p2, g2, _ in rounds(v, list(S), present, goods, lstar, rmax):
            if solvable(v, S2, frozenset(p2), frozenset(g2), form, memo):
                ok = True; break
    memo[key] = ok
    return ok

FORMS = ("i", "ii", "irecv", "iii", "R")

def job(row):
    v = mk(row["sets"], row["vals"]); Y = row["picks"]; n = len(v); m = len(v[0])
    out = dict(sd=any(sd(v, list(o)) == list(Y) for o in itertools.permutations(range(n))),
               hard=complete(v, [{y} for y in Y]) is None)
    S0 = tuple(frozenset({y}) for y in Y)
    for f in FORMS:
        out[f] = solvable(v, S0, frozenset(range(n)), frozenset(range(m)), f, {})
    if not out["iii"]:
        out["onemove"] = oc_depth(v, Y, maxd=1) == 1
    return row, out

def key(r):
    return json.dumps([r["sets"], r["vals"], list(r["picks"])])

def main(paths, procs):
    rows = {}; src = {}
    for p in paths:
        tag = p.rsplit("onemove_hard_", 1)[-1].split(".")[0]
        seen = set()
        for line in gzip.open(p, "rt"):
            r = json.loads(line); k = key(r)
            if k in seen:
                continue
            seen.add(k); rows.setdefault(k, r); src.setdefault(k, []).append(tag)
    c = Counter(); fails = {f: [] for f in FORMS}
    with Pool(procs) as pool:
        for r, out in pool.imap_unordered(job, list(rows.values()), chunksize=8):
            k = key(r); c["distinct"] += 1; c["picks_SD"] += out["sd"]; c["hard"] += out["hard"]
            for t in src[k]:
                c[f"{t}_distinct"] += 1
            for f in FORMS:
                if not out[f]:
                    fails[f].append(k)
                    for t in src[k]:
                        c[f"{t}_fail_{f}"] += 1
            if "onemove" in out:
                c["iii_fail_and_one_official_move_repairs"] += out["onemove"]
    for f in FORMS:
        c[f"FAIL_{f}"] = len(fails[f])
    c["iii_fails_subset_of_i_fails"] = set(fails["iii"]) <= set(fails["i"])
    c["R_fails_equal_i_fails"] = set(fails["R"]) == set(fails["i"])
    print(json.dumps(dict(source="pure reduction at the one-move hard starts (the three files; the union is counted as distinct)", **dict(sorted(c.items())))))
    for k in sorted(fails["iii"], key=lambda k: (len(json.loads(k)[0]), 1 + max(max(s) for s in json.loads(k)[0]), k)):
        r = rows[k]
        print("FAILS_iii", r.get("name"), json.dumps(dict(sets=r["sets"], vals=r["vals"], picks=r["picks"])))
    for k in sorted(fails["i"], key=lambda k: (len(json.loads(k)[0]), 1 + max(max(s) for s in json.loads(k)[0]), k))[:3]:
        print("FAILS_i (smallest)", rows[k].get("name"), k)
    json.dump({f: fails[f] for f in FORMS}, open(sys.argv[-1] if sys.argv[-1].endswith(".json") else "/dev/null", "w"))

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.endswith(".json")]
    main(args[:-1], int(args[-1]))
