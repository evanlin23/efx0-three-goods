#!/usr/bin/env python3
"""Referee check of Theorem S (K4.MULTI.S; k4/oc1max_multi.md §10, branch proof/k4-oc1max-multi at b107719).
Own code (oc1hall_ref.py / multi_ref.py helpers), raw EFX0; nothing from k4/oc1max_multi/ is run or imported. The
start DATA of K4.MULTI.DATA (results/k4_oc1max_multi/hard2_starts*.jsonl.gz) is read as data only.

Starts: perfect SD starts (every agent with a relevant good picks), hard or not (the theorem does not use hardness):
random instances (<= 4 relevant goods per agent, ties allowed) and the 8,383 K4.MULTI.DATA starts.
For every k in D, every LONGEST canonical chain P = (k, ..., z) from k, every h in J (and h = Y_z, the relaxed form),
W = (J - h) + {Y_z}:
  hypotheses (S-a) v_k(W) > p_k; (S-b) W threatens no d in D - k at p_d; (S-c) W threatens no unfrozen pick holder
  u != z at p_u; (S-d) z values no junk good other than h, or (S-d') W does not threaten z at its value in A.
  For EVERY improving H0 ⊆ W (not only minimal ones): the move is official; B' after P; receiver r = z if z is
  unfrozen at B', else EVERY wanter w of a = Y_{x_{t-1}} at B' (step 1 claims each is off P, unfrozen at the picks,
  a pick holder, unfrozen at B'); A: k takes W, r takes B'_r + h, everyone else keeps B'. Check: A is a partition of
  all goods and raw EFX0.
Also: Lemma HS (any canonical chain; (S1) z unfrozen at B', (S2) z admissible for h against W, (S3) no agent other
than k, z threatened by W at its B' value => A EFX0), and HS-U1 (one unfrozen pick holder => the head of a longest
chain is unfrozen after P, for every improving H0).
Mutations: 'anychain' (every canonical chain, not only longest), 'noSb', 'noSc', 'noSd' (drop the hypothesis).
"""
import itertools, random, sys, json, gzip
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd
from multi_ref import frozen_set, canonical_chains, subsets

def after_chain(Y, seq, H0):
    n = len(Y)
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    B[seq[0]] = set(H0)
    for i in range(1, len(seq)):
        B[seq[i]] = {Y[seq[i - 1]]}
    return B

def analyse(v, Y, c, ex, mut=None, tag="", count_cover=False):
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B)
    p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B)
    D = {d for d in F if any(v[d][g] > 0 for g in J)}
    U = [u for u in range(n) if u not in F and Y[u] is not None]
    cover = {"Sd": False, "Sdp": False, "union": False}
    allch = list(canonical_chains(v, Y, F))
    for k in sorted(D):
        chains = [s for s in allch if s[0] == k]
        if not chains:
            c[tag + "no_chain_from_k_in_D"] += 1
            ex.append(("no chain", v, Y, k))
            continue
        L = max(len(s) for s in chains)
        longest = [s for s in chains if len(s) == L]
        pool = chains if mut == "anychain" else longest
        for seq in pool:
            z = seq[-1]; a = Y[seq[-2]]
            for h in sorted(J) + [Y[z]]:
                relaxed_only = (h == Y[z])
                W = (J | {Y[z]}) - {h}                                  # = (J - h) + {Y_z}; = J when h = Y_z
                Sa = val(v, k, W) > p[k]
                Sb = not any(threatened(v, d, W, p[d]) for d in D if d != k)
                Sc = not any(threatened(v, u, W, p[u]) for u in U if u != z)
                Sd = all(v[z][g] == 0 for g in J if g != h) and not relaxed_only
                if not Sa:
                    continue
                if mut == "noSb":
                    Sb = True
                if mut == "noSc":
                    Sc = True
                if not (Sb and Sc):
                    continue
                imp = [H0 for H0 in subsets(W) if val(v, k, H0) > p[k]]
                # z's frozenness after P must not depend on H0 (k never wants a at B')
                zfr = {z in frozen_set(v, after_chain(Y, seq, H0)) for H0 in imp}
                if len(zfr) != 1:
                    c[tag + "z_frozenness_depends_on_H0"] += 1
                (zf,) = zfr
                zval = v[z][a] + (0 if zf else v[z][h])
                Sdp = not threatened(v, z, W, zval)
                if mut == "noSd":
                    Sd = Sdp = True
                if not (Sd or Sdp):
                    continue
                if seq in longest and mut is None:
                    if Sd:
                        cover["Sd"] = True
                    if Sdp and not relaxed_only:
                        cover["Sdp"] = True
                    if Sdp:
                        cover["union"] = True
                form = "Sd" if Sd else "Sdp"
                for H0 in imp:
                    Bp = after_chain(Y, seq, H0)
                    official = all(v[seq[i]][Y[seq[i - 1]]] > p[seq[i]] for i in range(1, len(seq)))
                    if not official:
                        c[tag + "not_official"] += 1
                    Fp = frozen_set(v, Bp)
                    if z not in Fp:
                        recv = [z]
                    else:
                        recv = [w for w in range(n) if w != z and v[w][a] > val(v, w, Bp[w])]
                        for w in recv:
                            if w in seq or w in F or Y[w] is None or w in Fp or not v[w][a] > p[w]:
                                c[tag + "step1_claim_fail"] += 1
                                ex.append(("step1", v, Y, seq, sorted(H0), w))
                        if not recv:
                            c[tag + "frozen_z_without_wanter"] += 1
                    for r in recv:
                        A = [set(b) for b in Bp]
                        A[k] = set(W)
                        A[r] = Bp[r] | {h}
                        part = sum(len(x) for x in A) == m and set().union(*A) == set(range(m))
                        ok = part and efx0(v, A)
                        key = (tag + form + ("_hYz" if relaxed_only else "") + ("_z" if r == z else "_wanter"))
                        c[key + "_tests"] += 1
                        if not ok:
                            c[key + "_FAIL"] += 1
                            if len(ex) < 8:
                                ex.append((mut, tag, v, Y, seq, h, sorted(H0), r))
    if count_cover:
        for kk, b in cover.items():
            c[tag + "covered_" + kk] += b
    # Lemma HS (any canonical chain, any h in J, any improving H0 ⊆ Pi - h) and HS-U1
    if mut is None:
        for seq in allch:
            k, z = seq[0], seq[-1]; a = Y[seq[-2]]
            if k not in D:
                continue
            Pi = J | {Y[z]}
            for h in sorted(J):
                W = Pi - {h}
                for H0 in subsets(W):
                    if not val(v, k, H0) > p[k]:
                        continue
                    Bp = after_chain(Y, seq, H0)
                    Fp = frozen_set(v, Bp)
                    if len(U) == 1 and len(seq) == max(len(s) for s in allch if s[0] == k):
                        c[tag + "HSU1_tests"] += 1
                        if z in Fp:
                            c[tag + "HSU1_FAIL"] += 1
                    if z in Fp:
                        continue                                            # (S1)
                    bz = v[z][a]
                    S2 = (not threatened(v, z, W, bz)) or (v[z][h] > 0 and not threatened(v, z, W, bz + v[z][h]))
                    S3 = not any(threatened(v, i, W, val(v, i, Bp[i])) for i in range(n) if i not in (k, z))
                    if not (S2 and S3):
                        continue
                    A = [set(b) for b in Bp]; A[k] = set(W); A[z] = Bp[z] | {h}
                    c[tag + "HS_tests"] += 1
                    if not efx0(v, A):
                        c[tag + "HS_FAIL"] += 1
                        ex.append(("HS", v, Y, seq, h, sorted(H0)))

def rand_starts(N, seed):
    rng = random.Random(seed)
    for _ in range(N):
        n = rng.randint(3, 5); m = rng.randint(n + 1, n + 4)
        ties = rng.random() < 0.3
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            gs = rng.sample(range(m), rng.randint(2, min(4, m)))
            xs = [rng.randint(1, 6) for _ in gs] if ties else rng.sample(range(1, 40), len(gs))
            for g, x in zip(gs, xs):
                v[i][g] = x
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:4]:
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen or any(Y[i] is None and any(x > 0 for x in v[i]) for i in range(n)):
                continue
            seen.add(tuple(Y))
            if len(set(range(m)) - set(y for y in Y if y is not None)) > 6:
                continue
            yield v, Y

def data_starts(paths):
    for path in paths:
        for line in gzip.open(path, "rt"):
            d = json.loads(line); I = d["inst"]
            n = len(I["sets"]); m = I["m"]
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(I["sets"][i], I["vals"][i]):
                    v[i][g] = x
            yd = sd(v, d["order"]); Y = [yd[i] for i in range(n)]
            yield d["name"], v, Y, d["picks"]

def main():
    mode = sys.argv[1]
    c = Counter(); ex = []
    if mode == "rand":
        N, seed = int(sys.argv[2]), int(sys.argv[3]); mut = sys.argv[4] if len(sys.argv) > 4 else None
        for v, Y in rand_starts(N, seed):
            c["starts"] += 1
            analyse(v, Y, c, ex, mut)
        src = f"Theorem S, random perfect starts N={N} seed={seed} mutation={mut}"
    else:
        mut = sys.argv[2] if len(sys.argv) > 2 and sys.argv[2] != "-" else None
        for name, v, Y, picks in data_starts(sys.argv[3:]):
            c["starts"] += 1
            if list(Y) != list(picks):
                c["picks_mismatch"] += 1; continue
            if any(Y[i] is None and any(x > 0 for x in v[i]) for i in range(len(Y))):
                c["not_perfect"] += 1
            analyse(v, Y, c, ex, mut, count_cover=True)
        src = f"Theorem S on K4.MULTI.DATA mutation={mut}"
    print(json.dumps(dict(source=src, **dict(sorted(c.items())))))
    for e in ex[:8]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    main()
