#!/usr/bin/env python3
"""Referee check of Lemma SDPO (k4/sdc.md §28), Lemma MAXSD (§31, coordinator branch) and Lemma MAX (k4/oc1_hall.md
§19). Written from the text; no shared code.

For random instances (strict values per agent, <= 4 relevant goods; also a ties mutation):
  SDPO:  {SD(pi) : pi an order} == {Pareto-optimal matchings} (matchings: each agent at most one good it values,
         each good at most one agent), by brute force over all matchings.
  MAXSD: some SD outcome is a maximum matching.
  MAX:   at every SD outcome that is a maximum matching, no agent reachable from a pickless agent by an alternating
         path (non-matching edge agent->valued pick, matching edge pick->holder) values a junk good.
"""
import itertools, random, sys, json

def matchings(v):
    n = len(v); m = len(v[0])
    opts = [[None] + [g for g in range(m) if v[i][g] > 0] for i in range(n)]
    for f in itertools.product(*opts):
        gs = [g for g in f if g is not None]
        if len(gs) == len(set(gs)):
            yield f

def sd(v, order):
    m = len(v[0]); G = set(range(m)); Y = [None] * len(v)
    for i in order:
        R = sorted((g for g in G if v[i][g] > 0), key=lambda g: (-v[i][g], g))
        if R:
            Y[i] = R[0]; G.discard(R[0])
    return tuple(Y)

def value(v, i, g):
    return v[i][g] if g is not None else 0

def run(N, nlo, nhi, mlo, mhi, ties, seed):
    rng = random.Random(seed)
    c = dict(instances=0, sdpo_fail=0, sd_not_po=0, po_not_sd=0, maxsd_fail=0, max_starts=0, max_fail=0)
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            k = rng.randint(1, min(4, m))
            goods = rng.sample(range(m), k)
            vals = [rng.randint(1, 3) for _ in goods] if ties else rng.sample(range(1, 30), k)
            for g, x in zip(goods, vals):
                v[i][g] = x
        c["instances"] += 1
        M = list(matchings(v))
        vec = {mu: tuple(value(v, i, mu[i]) for i in range(n)) for mu in M}
        PO = {mu for mu in M if not any(all(a >= b for a, b in zip(vec[nu], vec[mu])) and vec[nu] != vec[mu] for nu in M)}
        SD = {sd(v, o) for o in itertools.permutations(range(n))}
        if SD != PO:
            c["sdpo_fail"] += 1
            c["sd_not_po"] += len(SD - PO); c["po_not_sd"] += len(PO - SD)
            if len(ex) < 3:
                ex.append(("SDPO", v, sorted(SD - PO, key=str)[:2], sorted(PO - SD, key=str)[:2]))
        nu = max(sum(1 for g in mu if g is not None) for mu in M)
        maxSD = [Y for Y in SD if sum(1 for g in Y if g is not None) == nu]
        if not maxSD:
            c["maxsd_fail"] += 1
            if len(ex) < 6:
                ex.append(("MAXSD", v))
        for Y in maxSD:
            c["max_starts"] += 1
            holder = {g: i for i, g in enumerate(Y) if g is not None}
            junk = {g for g in range(m) if g not in holder}
            S = set(i for i in range(n) if Y[i] is None)
            stack = list(S)
            while stack:
                a = stack.pop()
                for g in range(m):
                    if v[a][g] > 0 and g in holder and holder[g] not in S:
                        S.add(holder[g]); stack.append(holder[g])
            if any(v[a][g] > 0 for a in S for g in junk):
                c["max_fail"] += 1
                if len(ex) < 6:
                    ex.append(("MAX", v, Y))
    print(json.dumps(dict(source=f"SDPO/MAXSD/MAX N={N} n={nlo}..{nhi} m={mlo}..{mhi} ties={ties} seed={seed}", **c)))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    a = sys.argv[1:]
    run(int(a[0]), int(a[1]), int(a[2]), int(a[3]), int(a[4]), a[5] == "ties", int(a[6]))
