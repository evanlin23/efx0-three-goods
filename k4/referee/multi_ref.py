#!/usr/bin/env python3
"""Referee check of Lemma D-red, Proposition T0, Lemma KEEP, Lemma SET and Lemma OWN (k4/oc1max_multi.md §2-§4,
branch proof/k4-oc1max-multi at 6959fc9 / 1ccbb94). Written from the text and the raw EFX0 definition; reuses only my
own helpers (oc1hall_ref.py). No code of k4/oc1max_multi/ is run or imported.

Starts: SD picks of random instances (<= 4 relevant goods per agent, strict values), kept if perfect (every agent with a
relevant good picks), one-absorber-hard (raw brute force, every owner) and |D| >= 2 (T0 is checked at every hard
start). Canonical chains: x_i wants Y_{x_{i-1}} at the picks, the head is unfrozen at the picks, middle agents take no
junk; every improving H0 ⊆ Pi ∩ R_k (Pi = J ∪ {Y_z}).

D-red: parts 1-3 directly; part 4 as "S* owned by k exists (brute) <=> some H ⊆ J' with (H1'') and an SDR of
admissible holders covering the crowded exposed holders"; and "no HEAD, CROWD, DEMAND => S* owned by k" (brute).
KEEP, OWN: whenever the hypotheses hold, brute force for an S* completion with the stated owner in which u takes Y_z.
SET: at every S*-shaped allocation of B' with an allowed owner, no EFX0 violation involves k; and the S* test equals the
S* test of the reduced state (k and H0 deleted).
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd

def frozen_set(v, B):
    n = len(B)
    return {j for j in range(n) if any(i != j and any(v[i][g] > val(v, i, B[i]) for g in B[j]) for i in range(n))}

def holders_of(v, B):
    fr = frozen_set(v, B)
    return [j for j in range(len(B)) if len(B[j]) <= 1 and j not in fr]

def oa_exists(v, B):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    for o in range(n):
        recv = [j for j in range(n) if j != o]
        for f in itertools.product([None] + recv, repeat=len(J)):
            hs = [a for a in f if a is not None]
            if len(hs) != len(set(hs)):
                continue
            X = [set(b) for b in B]
            for g, a in zip(J, f):
                X[o if a is None else a].add(g)
            if efx0(v, X):
                return True
    return False

def sstar_allocs(v, B, o, forced=None):
    """every S*-shaped completion (owner o, holders other than o take <= 1 junk good) — yields X (not EFX0-filtered).
    forced: dict good -> agent that must receive it."""
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    N1 = [h for h in holders_of(v, B) if h != o]
    for f in itertools.product([None] + N1, repeat=len(J)):
        hs = [a for a in f if a is not None]
        if len(hs) != len(set(hs)):
            continue
        if forced and any(f[J.index(g)] != a for g, a in forced.items()):
            continue
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            X[o if a is None else a].add(g)
        yield X

def sstar(v, B, o, forced=None):
    return any(efx0(v, X) for X in sstar_allocs(v, B, o, forced))

def subsets(S):
    S = sorted(S)
    for k in range(len(S) + 1):
        for c in itertools.combinations(S, k):
            yield set(c)

def canonical_chains(v, Y, F):
    """(seq, z): x_i wants Y_{x_{i-1}} at the picks, head unfrozen at the picks."""
    n = len(Y); B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    p = [val(v, i, B[i]) for i in range(n)]
    def ext(seq):
        last = seq[-1]
        for w in range(n):
            if w not in seq and Y[last] is not None and v[w][Y[last]] > p[w]:
                s2 = seq + [w]
                if w not in F:
                    yield s2
                else:
                    yield from ext(s2)
    for k in range(n):
        if k in F:
            yield from ext([k])

MUT = None

def run(N, nlo, nhi, seed):
    rng = random.Random(seed)
    c = {x: 0 for x in ["instances", "perfect", "hard", "hard_D2", "T0_tests", "T0_fail", "T0_improving_fail",
                        "chains", "dred1_fail", "dred2_fail", "dred3_fail", "dred4_tests", "dred4_mismatch",
                        "clean", "clean_fail", "keep_tests", "keep_fail", "keep_zK1_tests", "keep_zK1_fail",
                        "set_tests", "set_alloc_k_violation", "set_mismatch", "own_tests", "own_fail"]}
    ex = []
    for it in range(N):
        n = rng.randint(nlo, nhi)
        kind = it % 4
        if kind >= 2:                      # random 4-sets in m = n + 2 .. n + 3 (densest hard rate)
            m = rng.randint(n + 2, n + 3)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(rng.sample(range(m), 4), rng.sample(range(1, 40), 4)):
                    v[i][g] = x
        elif kind == 0:                    # private good + shared pool
            q = rng.randint(2, 4); m = n + q
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                goods = [i] + rng.sample(range(n, m), rng.randint(2, min(3, q)))
                for g, x in zip(goods, rng.sample(range(1, 40), len(goods))):
                    v[i][g] = x
        else:                              # sparse random
            m = rng.randint(n + 1, n + 4)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                goods = rng.sample(range(m), rng.randint(2, min(4, m)))
                for g, x in zip(goods, rng.sample(range(1, 40), len(goods))):
                    v[i][g] = x
        c["instances"] += 1
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for order in orders[:6]:
            yd = sd(v, order); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen:
                continue
            seen.add(tuple(Y))
            if any(Y[i] is None and any(x > 0 for x in v[i]) for i in range(n)):
                continue
            c["perfect"] += 1
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            J = set(range(m)) - set().union(*B)
            if len(J) > 5 or oa_exists(v, B):
                continue
            c["hard"] += 1
            p = [val(v, i, B[i]) for i in range(n)]
            F = frozen_set(v, B)
            D = {d for d in F if any(v[d][g] > 0 for g in J)}
            DT = {d for d in D if threatened(v, d, J, p[d])}
            U = [z for z in range(n) if z not in F]
            # Proposition T0
            for z in U:
                c["T0_tests"] += 1
                Th = {d for d in D if threatened(v, d, J | B[z], p[d])}
                if not Th:
                    c["T0_fail"] += 1; ex.append(("T0", v, Y, z))
                for kk in Th:
                    if not val(v, kk, (J | B[z]) & rel(v, kk)) > p[kk]:
                        c["T0_improving_fail"] += 1
            if len(D) < 2:
                continue
            c["hard_D2"] += 1
            for seq in canonical_chains(v, Y, F):
                k, z = seq[0], seq[-1]
                if k not in D:
                    continue
                Pi = J | {Y[z]}
                Theta = {d for d in D if threatened(v, d, Pi, p[d])}
                for H0 in subsets(Pi & rel(v, k)):
                    if not val(v, k, H0) > p[k]:
                        continue
                    c["chains"] += 1
                    Bp = [set(b) for b in B]
                    Bp[k] = set(H0)
                    for i in range(1, len(seq)):
                        Bp[seq[i]] = {Y[seq[i - 1]]}
                    Jp = Pi - H0
                    vp = [val(v, i, Bp[i]) for i in range(n)]
                    Fp = frozen_set(v, Bp)
                    hold = holders_of(v, Bp)
                    # part 1: nobody but k wants a good of Pi; k wants no good of J'
                    if any(v[i][g] > vp[i] for i in range(n) if i != k for g in Pi) or any(v[k][g] > vp[k] for g in Jp):
                        c["dred1_fail"] += 1; ex.append(("dred1", v, Y, seq, sorted(H0)))
                    # part 2
                    bad2 = any(q != k and q not in F and q != z for q in Fp)
                    for q in Fp:
                        if q == k:
                            continue
                        if (q in F and q not in D) or (q in D and q not in Theta and q != k):
                            if threatened(v, q, Pi, vp[q]):
                                bad2 = True
                    if bad2:
                        c["dred2_fail"] += 1; ex.append(("dred2", v, Y, seq, sorted(H0)))
                    N1 = [u for u in hold if u != k]
                    crowded = {u for u in N1 if len(H0 & rel(v, u)) >= 2 and val(v, u, H0) > vp[u]}
                    wants_H0 = {u for u in N1 if any(v[u][g] > vp[u] for g in H0)}
                    # part 3 and part 4 for every H ⊆ J'
                    exists4 = False
                    for H in subsets(Jp):
                        X = Pi - H
                        E = [u for u in N1 if threatened(v, u, X, vp[u])]
                        for u in E:
                            ok = (u == z) or (u not in seq and u not in F) or (u in D and u != k and u not in Fp)
                            nonmov = (u in wants_H0) or (len(H0 & rel(v, u)) >= 2 and val(v, u, H0 & rel(v, u)) > vp[u])
                            if not ok or nonmov != (u in crowded):
                                c["dred3_fail"] += 1; ex.append(("dred3", v, Y, seq, sorted(H0), sorted(H), u))
                        h1 = not any(threatened(v, q, X, vp[q]) for q in (D - {k}) | {z} if q in Fp)
                        if not h1:
                            continue
                        Hl = sorted(H)
                        def adm(u, h):
                            return (u not in E) or (v[u][h] > 0 and not threatened(v, u, X, vp[u] + v[u][h]))
                        must = [u for u in E if u in crowded]
                        for img in itertools.permutations(N1, len(Hl)):
                            if all(adm(u, h) for u, h in zip(img, Hl)) and all(u in img for u in must):
                                exists4 = True
                                break
                        if exists4:
                            break
                    brute = sstar(v, Bp, k)
                    c["dred4_tests"] += 1
                    if brute != exists4:
                        c["dred4_mismatch"] += 1; ex.append(("dred4", v, Y, seq, sorted(H0), brute, exists4))
                    head = z in Fp and threatened(v, z, Pi, vp[z])
                    crowd = bool(crowded)
                    demand = any(d in Fp and threatened(v, d, Pi, vp[d]) for d in D - {k})
                    if MUT == "noDEMAND":
                        demand = False
                    if MUT == "noCROWD":
                        crowd = False
                    if MUT == "noHEAD":
                        head = False
                    if not (head or crowd or demand):
                        c["clean"] += 1
                        if not brute:
                            c["clean_fail"] += 1; ex.append(("clean", v, Y, seq, sorted(H0)))
                    # KEEP: H0 ⊆ J
                    if Y[z] not in H0:
                        K2 = not any(len(H0 & rel(v, u)) >= 2 and val(v, u, H0) > vp[u] for u in hold)
                        K3 = not any(q in Fp and threatened(v, q, J, vp[q]) for q in (DT - {k}) | {z})
                        for u in N1:
                            K1 = (not threatened(v, u, J, vp[u])) or (v[u][Y[z]] > 0 and not threatened(v, u, J, vp[u] + v[u][Y[z]]))
                            if u == z and z not in Fp:
                                c["keep_zK1_tests"] += 1
                                if not K1:
                                    c["keep_zK1_fail"] += 1; ex.append(("keepz", v, Y, seq, sorted(H0)))
                            if K1 and (K2 or MUT == "noK2") and (K3 or MUT == "noK3"):
                                c["keep_tests"] += 1
                                if not sstar(v, Bp, k, forced={Y[z]: u}):
                                    c["keep_fail"] += 1; ex.append(("keep", v, Y, seq, sorted(H0), u))
                    # SET and OWN: H0 a junk pair
                    if len(H0) == 2 and H0 <= J:
                        x1 = seq[1]
                        for o in range(n):
                            if o in (k, x1):
                                continue
                            if not any(v[k][g] > vp[k] for g in Bp[o]):
                                c["set_tests"] += 1
                                found = False
                                for X in sstar_allocs(v, Bp, o):
                                    if X[k] != H0:
                                        c["set_alloc_k_violation"] += 1
                                    # violations involving k
                                    vk = any(i != k and threatened(v, i, X[k], val(v, i, X[i])) for i in range(n)) or \
                                        any(j != k and len(X[j]) >= 2 and threatened(v, k, X[j], val(v, k, X[k])) for j in range(n))
                                    if vk:
                                        c["set_alloc_k_violation"] += 1; ex.append(("set_k", v, Y, seq, sorted(H0), o))
                                    if efx0(v, X):
                                        found = True
                                # reduced state: delete k and H0
                                keep_ag = [i for i in range(n) if i != k]
                                goods = [g for g in range(m) if g not in H0]
                                vr = [[v[i][g] for g in goods] for i in keep_ag]
                                Br = [{goods.index(g) for g in Bp[i]} for i in keep_ag]
                                hold_r = [keep_ag.index(h) for h in hold if h != k]
                                orr = keep_ag.index(o)
                                Jr = sorted(set(range(len(goods))) - set().union(*Br))
                                N1r = [h for h in hold_r if h != orr]
                                red = False
                                for f in itertools.product([None] + N1r, repeat=len(Jr)):
                                    hs = [a for a in f if a is not None]
                                    if len(hs) != len(set(hs)):
                                        continue
                                    Xr = [set(b) for b in Br]
                                    for g, a in zip(Jr, f):
                                        Xr[orr if a is None else a].add(g)
                                    if efx0(vr, Xr):
                                        red = True
                                        break
                                if red != found:
                                    c["set_mismatch"] += 1; ex.append(("set", v, Y, seq, sorted(H0), o, found, red))
                            # OWN
                            W2 = len(Bp[o]) <= 1 and o not in Fp and not any(v[q][g] > 0 for g in Bp[o] for q in Fp | {k})
                            if not W2:
                                continue
                            Wb = Bp[o] | (J - H0)
                            W1 = not any(d in Fp and threatened(v, d, Wb, vp[d]) for d in DT - {k})
                            if not W1 and MUT != "noW1":
                                continue
                            if z in Fp and threatened(v, z, Wb, vp[z]):
                                continue
                            for u in hold:
                                if u == o:
                                    continue
                                if (not threatened(v, u, Wb, vp[u])) or (v[u][Y[z]] > 0 and not threatened(v, u, Wb, vp[u] + v[u][Y[z]])):
                                    c["own_tests"] += 1
                                    if not sstar(v, Bp, o, forced={Y[z]: u}):
                                        c["own_fail"] += 1; ex.append(("own", v, Y, seq, sorted(H0), o, u))
    print(json.dumps(dict(source=f"D-red/T0/KEEP/SET/OWN N={N} n={nlo}..{nhi} seed={seed} mutation={MUT}", **c)))
    for e in ex[:6]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    if len(sys.argv) > 5:
        MUT = sys.argv[5]
    a = list(map(int, sys.argv[1:5]))
    run(*a)
