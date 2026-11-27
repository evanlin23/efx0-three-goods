#!/usr/bin/env python3
"""Referee check of Corollary S^φ(round) (K4.MULTI.SPHIR; k4/oc1max_multi.md §17 on proof/k4-oc1max-multi-2 at
d10b8f20): Theorem S^φ (with (S-φ3)) when the phantoms were settled in ROUNDS. Own code (cert_ref, rec_s_ref,
oc1hall_ref helpers); nothing from k4/oc1max_multi/ is run.

Up to two rounds. A round settles K (|K| <= 2) dangerous agents of the current instance; each k ∈ K takes an
E-prefix P_k (x_l the σ-earliest wanter of Y_{x_{l-1}}, stopped at any head, length >= 2; stopping at a cycle), the
chains vertex-disjoint; T_k ⊆ (J ∪ {Y_{z_k}}) ∩ R_k, 1 <= |T_k| <= 3, improving, pairwise disjoint. Admissible when:
SD-E(round)'s conclusion (the state after the round without K and ∪T_k is SD of σ − K; checked directly);
(L*) at the round's end (no T_k threatens any other current agent at its value after the round, round-mates at
their τ); (P2) the new T_k threaten no earlier phantom at τ_φ; (P3) every released head pick is worth <= τ_φ to every
phantom, the round's included. After every admissible sequence, every Theorem S case (relaxed, longest chain) of the
current instance: hypotheses (S-φ1) W threatens no phantom, (S-φ2) v_φ(B'_r) <= τ_φ, (S-φ3) h = Y_z ⟹ v_φ(Y_z) <= τ_φ;
the full allocation of I0 (phantoms keep T_φ) tested by raw EFX0. Counted: hypotheses without EFX0 (must be 0),
EFX0 without hypotheses; also invariants (P1*) and (P3) re-checked raw at the final state.
Mutation 'noP3': drop (P3) for released picks."""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from multi_ref import frozen_set
from oc1hall_ref import threatened
from rec_s_ref import theorem_s_cases

def e_prefixes(v, Y, sigma, k):
    n = len(Y); p = [v[i][Y[i]] for i in range(n)]; pos = {a: i for i, a in enumerate(sigma)}
    seq = [k]; out = []
    while True:
        W = [a for a in range(n) if a != seq[-1] and v[a][Y[seq[-1]]] > p[a]]
        if not W:
            break
        nxt = min(W, key=lambda a: pos[a])
        if nxt in seq:
            break
        seq = seq + [nxt]; out.append(list(seq))
    return out

def levels(v0, A, G, v, Y, sigma, phantoms, depth, c, mut, hist=()):
    n = len(Y); m = len(v[0])
    if phantoms:
        yield A, G, v, Y, phantoms, hist
    if depth == 0:
        return
    J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, [{y} for y in Y]); D = sorted(d for d in F if any(v[d][g] > 0 for g in J))
    opts = []
    for k in D:
        for P in e_prefixes(v, Y, sigma, k):
            pool = sorted((J | {Y[P[-1]]}) & rel(v, k))
            for s in (1, 2, 3):
                for T in itertools.combinations(pool, s):
                    if val(v, k, T) > p[k]:
                        opts.append((k, P, frozenset(T)))
    for r in (1, 2):
        for combo in itertools.combinations(opts, r):
            ags = [a for _, P, _ in combo for a in P]; Ts = [g for _, _, T in combo for g in T]
            if len(ags) != len(set(ags)) or len(Ts) != len(set(Ts)):
                continue
            new = [{y} for y in Y]
            for k, P, T in combo:
                for i in range(1, len(P)):
                    new[P[i]] = {Y[P[i - 1]]}
                new[k] = set(T)
            K = [k for k, _, _ in combo]
            if any(threatened(v, a, T, val(v, a, new[a])) for k, _, T in combo for a in range(n) if a != k):
                c["round_rejected_Lstar"] += 1; continue
            newph = [(A[k], frozenset(G[g] for g in T), val(v, k, T)) for k, _, T in combo]
            if any(threatened(v0, pa, TI, tau) for pa, _, tau in phantoms for _, TI, _ in newph):
                c["round_rejected_P2"] += 1; continue
            released = [Y[P[-1]] for _, P, _ in combo if not any(Y[P[-1]] in T for _, _, T in combo)]
            allph = phantoms + newph
            if mut != "noP3" and any(v0[pa][G[g]] > tau for pa, _, tau in allph for g in released):
                c["round_rejected_P3"] += 1; continue
            agents = [a for a in range(n) if a not in K]; goods = [g for g in range(m) if g not in set(Ts)]
            gi = {g: i for i, g in enumerate(goods)}
            vm = [[v[a][g] for g in goods] for a in agents]
            Ym = [gi[next(iter(new[a]))] for a in agents]
            sig = [agents.index(a) for a in sigma if a not in K]
            if sd(vm, sig) != Ym:
                c["round_rejected_SD"] += 1; continue
            c[f"rounds_admissible_size_{r}"] += 1
            yield from levels(v0, [A[a] for a in agents], [G[g] for g in goods], vm, Ym, sig, allph, depth - 1, c, mut, hist + (r,))

def check_start(args):
    v0, Y0, orders, mut = args
    c = Counter(); n0 = len(Y0); m0 = len(v0[0])
    for sigma in orders:
        for A, G, v, Y, phantoms, hist in levels(v0, list(range(n0)), list(range(m0)), v0, list(Y0), list(sigma), [], 2, c, mut):
            Jfin = {G[g] for g in set(range(len(v[0]))) - set(Y)}
            for pa, T, tau in phantoms:          # invariants, raw, at the final state of the rounds
                c["P3_raw_fail"] += any(v0[pa][g] > tau for g in Jfin)
                c["P1star_raw_fail"] += any(threatened(v0, A[i], T, v0[A[i]][G[Y[i]]]) for i in range(len(A)))
            nph = "_".join(map(str, hist))
            for kq, sq, h, H0, r, Am in theorem_s_cases(v, Y):
                X = [set() for _ in range(n0)]
                for i, a in enumerate(A):
                    X[a] = {G[g] for g in Am[i]}
                for pa, T, tau in phantoms:
                    X[pa] = set(T)
                W = X[A[kq]]; Br = {G[g] for g in Am[r]} - {G[h]}; z = sq[-1]
                s1 = not any(threatened(v0, pa, W, tau) for pa, _, tau in phantoms)
                s2 = all(val(v0, pa, Br) <= tau for pa, _, tau in phantoms)
                s3 = (h != Y[z]) or all(v0[pa][G[Y[z]]] <= tau for pa, _, tau in phantoms)
                hyp = s1 and s2 and s3; ok = efx0(v0, X)
                tag = f"rounds{nph}_"
                c[tag + "cases"] += 1; c[tag + "hyp"] += hyp; c[tag + "efx0"] += ok
                c[tag + "COROLLARY_VIOLATION_hyp_not_efx0"] += hyp and not ok
                c[tag + "efx0_without_hyp"] += ok and not hyp
                c[tag + "with_a_triple"] += any(len(T) == 3 for _, T, _ in phantoms)
    return c

def load_jsonl(path):
    for line in gzip.open(path, "rt"):
        r = json.loads(line); v = mk(r["sets"], r["vals"]); Y = r["picks"]
        yield v, Y, [o for o in itertools.permutations(range(len(Y))) if sd(v, list(o)) == list(Y)]

def load_export(path, N, seed):
    d = json.load(gzip.open(path)); rows = [(H["sets"], s["vals"], s["picks"]) for H in d["hypergraphs"] for s in H["starts"]]
    rng = random.Random(seed)
    for sets, vals, Y in (rows if N >= len(rows) else rng.sample(rows, N)):
        v = mk(sets, vals)
        yield v, Y, [o for o in itertools.permutations(range(len(Y))) if sd(v, list(o)) == list(Y)]

def rand_starts(N, seed):
    rng = random.Random(seed)
    for _ in range(N):
        n = rng.randint(4, 6); m = rng.randint(n + 2, n + 4)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.choice([3, 4, 4])), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        o = list(range(n)); rng.shuffle(o); Y = sd(v, o)
        if None not in Y:
            yield v, Y, [o]

def main(kind, a, b, mut, procs):
    it = load_jsonl(a) if kind == "jsonl" else load_export(a, int(b), 1) if kind == "export" else rand_starts(int(a), int(b))
    c = Counter()
    with Pool(procs) as pool:
        for cc in pool.imap_unordered(check_start, ((v, Y, o, mut) for v, Y, o in it), chunksize=20):
            c.update(cc); c["starts"] += 1
    print(json.dumps(dict(source=f"Corollary S^phi(round) on {kind} {a.rsplit('/', 1)[-1]} {b} mutation={mut}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], None if sys.argv[4] == "none" else sys.argv[4], int(sys.argv[5]))
