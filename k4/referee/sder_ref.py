#!/usr/bin/env python3
"""Referee check of Lemma SD-E(round) (K4.MULTI.SDER; k4/oc1max_multi.md §17 on proof/k4-oc1max-multi-2 at
85981d13). Own code (cert_ref / rec_s_ref / rsd_ref helpers). Random strict perfect SD starts; K = one or two frozen
agents with vertex-disjoint PREFIXES of their earliest-wanter chains E(k) (every prefix of length >= 2), pairwise
disjoint improving T_k ⊆ (J ∪ {Y_{z_k}}) ∩ R_k with |T_k| <= 3. Test: (H) (every agent outside K that wants a released
head pick at the picks values its good after the round above it) and the conclusion (the state after the round,
without K and ∪T_k, is the SD outcome of sigma - K). Counted: (H) without the conclusion (must be 0), the conclusion
without (H). Mutation 'anychain': any want-chain prefixes instead of earliest-wanter prefixes."""
import itertools, json, sys, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, rel, sd
from multi_ref import frozen_set
from rsd_ref import sd_sub

def full_E(v, Y, sigma, k):
    n = len(Y); p = [v[i][Y[i]] for i in range(n)]; pos = {a: i for i, a in enumerate(sigma)}
    seq = [k]
    while True:
        W = [a for a in range(n) if a not in seq and v[a][Y[seq[-1]]] > p[a]]
        if not W:
            return seq
        seq.append(min(W, key=lambda a: pos[a]))

def any_chains(v, Y, k):
    n = len(Y); p = [v[i][Y[i]] for i in range(n)]
    out = []
    def rec(seq):
        out.append(list(seq))
        for a in range(n):
            if a not in seq and v[a][Y[seq[-1]]] > p[a]:
                rec(seq + [a])
    rec([k])
    return [s for s in out if len(s) >= 2]

def run(N, seed, mut=None):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        n = rng.randint(4, 6); m = rng.randint(n + 2, n + 4)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.choice([3, 4, 4])), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        sigma = list(range(n)); rng.shuffle(sigma)
        Y = sd(v, sigma)
        if None in Y:
            continue
        J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
        F = frozen_set(v, [{y} for y in Y])
        cand = {}
        for k in F:
            if mut == "anychain":
                cand[k] = any_chains(v, Y, k)
            else:
                E = full_E(v, Y, sigma, k)
                cand[k] = [E[:L] for L in range(2, len(E) + 1)]
        for r in (1, 2):
            for K in itertools.combinations(sorted(F), r):
                for chains in itertools.product(*(cand[k] for k in K)):
                    ags = [a for ch in chains for a in ch]
                    if len(ags) != len(set(ags)):
                        continue
                    pools = [((J | {Y[ch[-1]]}) & rel(v, k)) for k, ch in zip(K, chains)]
                    Topts = [[set(T) for s in (1, 2, 3) for T in itertools.combinations(sorted(pl), s)
                              if val(v, k, set(T)) > p[k]] for k, pl in zip(K, pools)]
                    for Ts in itertools.product(*Topts):
                        if r == 2 and Ts[0] & Ts[1]:
                            continue
                        S = [{y} for y in Y]
                        for k, ch, T in zip(K, chains, Ts):
                            for i in range(1, len(ch)):
                                S[ch[i]] = {Y[ch[i - 1]]}
                            S[k] = set(T)
                        released = [Y[ch[-1]] for ch in chains if not any(Y[ch[-1]] in T for T in Ts)]
                        rest = [a for a in range(n) if a not in K]
                        H = all(not (v[a][g] > p[a]) or val(v, a, S[a]) > v[a][g] for a in rest for g in released)
                        goods = set(range(m)) - set().union(*Ts)
                        sig = [a for a in sigma if a not in K]
                        Ym = sd_sub(v, sig, set(rest), goods)
                        concl = all(len(S[a]) == 1 and Ym[a] == next(iter(S[a])) for a in rest)
                        tag = f"K{r}_"
                        c[tag + "rounds"] += 1; c[tag + "H"] += H; c[tag + "SDE"] += concl
                        c[tag + "H_without_SDE_VIOLATION"] += H and not concl
                        c[tag + "SDE_without_H"] += concl and not H
                        c[tag + "prefix_proper"] += any(len(ch) < len(full_E(v, Y, sigma, k)) for k, ch in zip(K, chains)) if mut is None else 0
    print(json.dumps(dict(source=f"Lemma SD-E(round) N={N} seed={seed} mutation={mut}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else None)
