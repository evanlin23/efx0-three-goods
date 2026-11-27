#!/usr/bin/env python3
"""Referee check of k4/oc1_hall.md §21-§22 (branch claude/k4-oc1-hall at a14932d): Lemma D1-chain, Proposition 3',
Lemma D1-red, Lemma D1-C0, Proposition D1-C' (|D| = 1), and the §22 counterexamples cex1, cex2 and the TTC n = 5
instance. Own code (helpers from oc1hall_ref.py and multi_ref.py), raw EFX0, no code of k4/oc1_hall/.

Starts: SD picks of random instances (<= 4 relevant goods per agent, strict values), one-absorber-hard (raw brute force,
every owner), D = {k}. Perfect and non-perfect starts both (D1-chain's second part needs a maximum matching).
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd, improving_chains
from multi_ref import frozen_set, holders_of, oa_exists, sstar, subsets, canonical_chains

def nu(v):
    """maximum matching agents x relevant goods (augmenting paths)."""
    n = len(v); m = len(v[0]); match = {}
    def aug(i, seen):
        for g in range(m):
            if v[i][g] > 0 and g not in seen:
                seen.add(g)
                if g not in match or aug(match[g], seen):
                    match[g] = i
                    return True
        return False
    return sum(1 for i in range(n) if aug(i, set()))

def minimal_improving(v, k, pool, p):
    out = []
    for S in subsets(pool & rel(v, k)):
        if val(v, k, S) > p and not any(val(v, k, S - {g}) > p for g in S):
            out.append(S)
    return out

def check_start(v, Y, c, ex):
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B)
    p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B)
    D = {d for d in F if any(v[d][g] > 0 for g in J)}
    if len(D) != 1:
        return
    (k,) = D
    c["hard_D1"] += 1
    maxm = sum(1 for y in Y if y is not None) == nu(v)
    U = [z for z in range(n) if z not in F]
    # Proposition 3'
    for z in U:
        c["p3_tests"] += 1
        if not val(v, k, (J | B[z]) & rel(v, k)) > p[k]:
            c["p3_fail"] += 1; ex.append(("P3'", v, Y, z))
    # Lemma D1-C0 (a), (b)
    for z in U:
        Pi = J | B[z]
        cand = [u for u in range(n) if u not in (k, z) and u not in F and any(v[u][g] > 0 for g in Pi)]
        fav = {}
        for u in cand:
            c["c0a_tests"] += 1
            if Y[u] is None or len(Pi & rel(v, u)) > 3:
                c["c0a_fail"] += 1; ex.append(("C0a-size", v, Y, z, u)); continue
            b = max(Pi & rel(v, u), key=lambda g: v[u][g])
            fav[u] = b
            for S in subsets(Pi - {b}):
                if threatened(v, u, S, p[u] + v[u][b]):
                    c["c0a_fail"] += 1; ex.append(("C0a", v, Y, z, u, sorted(S)))
        for r in range(1, len(cand) + 1):
            for U2 in itertools.combinations([u for u in cand if u in fav and fav[u] in J], r):
                bs = [fav[u] for u in U2]
                if len(set(bs)) < len(bs):
                    continue
                c["c0b_tests"] += 1
                if not val(v, k, (Pi & rel(v, k)) - set(bs)) > p[k]:
                    c["c0b_fail"] += 1; ex.append(("C0b", v, Y, z, U2))
    # Lemma D1-chain
    chains = list(canonical_chains(v, Y, F))
    mine = [s for s in chains if s[0] == k]
    c["chain_tests"] += 1
    if not mine:
        c["chain_exist_fail"] += 1; ex.append(("D1-chain", v, Y))
    if maxm:
        c["chain_maxm_starts"] += 1
        if any(Y[s[-1]] is None for s in mine):
            c["chain_maxm_fail"] += 1; ex.append(("D1-chain-max", v, Y))
    for seq in mine:
        z = seq[-1]; a = Y[seq[-2]]
        Pi = J | B[z]
        # second wanters of a off P at the picks
        second = [w for w in range(n) if w not in seq and v[w][a] > p[w]]
        for H0 in subsets(Pi & rel(v, k)):
            if not val(v, k, H0) > p[k]:
                continue
            c["red_chains"] += 1
            Bp = [set(b) for b in B]; Bp[k] = set(H0)
            for i in range(1, len(seq)):
                Bp[seq[i]] = {Y[seq[i - 1]]}
            Jp = Pi - H0
            vp = [val(v, i, Bp[i]) for i in range(n)]
            Fp = frozen_set(v, Bp); hold = holders_of(v, Bp)
            # part 1
            if any(v[i][g] > vp[i] for i in range(n) if i != k for g in Pi) or any(v[k][g] > vp[k] for g in Jp):
                c["red1_fail"] += 1; ex.append(("red1", v, Y, seq, sorted(H0)))
            # part 2
            bad = any(q != k and q not in F and q != z for q in Fp)
            bad |= any(q in F and q != k and any(threatened(v, q, S, vp[q]) for S in subsets(Pi)) for q in Fp)
            if z in Fp and not second:
                bad = True
            if any(v[k][Y[seq[i]]] > vp[k] for i in range(len(seq) - 1)):
                bad = True
            if bad:
                c["red2_fail"] += 1; ex.append(("red2", v, Y, seq, sorted(H0)))
            # part 3, 4
            N1 = [u for u in hold if u != k]
            crowded = {u for u in N1 if len(H0 & rel(v, u)) >= 2 and val(v, u, H0 & rel(v, u)) > vp[u]}
            exists4 = False
            for H in subsets(Jp):
                X = Pi - H
                E = [u for u in N1 if threatened(v, u, X, vp[u])]
                for u in E:
                    if not (u == z or (u not in seq and u not in F)):
                        c["red3_fail"] += 1; ex.append(("red3", v, Y, seq, sorted(H0), u))
                h1 = not (z in Fp and threatened(v, z, X, vp[z]))
                if not h1 or exists4:
                    continue
                Hl = sorted(H)
                must = [u for u in E if u in crowded]
                def adm(u, h):
                    return (u not in E) or (v[u][h] > 0 and not threatened(v, u, X, vp[u] + v[u][h]))
                for img in itertools.permutations(N1, len(Hl)):
                    if all(adm(u, h) for u, h in zip(img, Hl)) and all(u in img for u in must):
                        exists4 = True
                        break
            brute = sstar(v, Bp, k)
            c["red4_tests"] += 1
            if brute != exists4:
                c["red4_mismatch"] += 1; ex.append(("red4", v, Y, seq, sorted(H0), brute, exists4))
            head = z in Fp and threatened(v, z, Pi, vp[z])
            if not head and not crowded:
                c["red_clean"] += 1
                if not brute:
                    c["red_clean_fail"] += 1; ex.append(("clean", v, Y, seq, sorted(H0)))
        # Proposition D1-C'
        zfrozen = bool(second)   # x_t frozen at B' iff a has a second wanter off P (Lemma D1-red 2, checked above)
        head = zfrozen and threatened(v, z, Pi, v[z][a])
        if head:
            continue
        Pk = Pi & rel(v, k)
        Up = [u for u in range(n) if u not in seq and u not in F and len(Pk & rel(v, u)) >= 2]
        favs = {u: max(Pi & rel(v, u), key=lambda g: v[u][g]) for u in Up}
        if len(set(favs.values())) < len(favs) or any(b not in J for b in favs.values()):
            continue
        c["cp_chains"] += 1
        avoid = Pk - set(favs.values())
        mins = minimal_improving(v, k, avoid, p[k])
        if not mins:
            c["cp_exist_fail"] += 1; ex.append(("C'-exist", v, Y, seq)); continue
        for H0 in mins:
            hz = Y[z] is not None and Y[z] in H0
            Bp = [set(b) for b in B]; Bp[k] = set(H0)
            for i in range(1, len(seq)):
                Bp[seq[i]] = {Y[seq[i - 1]]}
            vz = val(v, z, Bp[z])
            crowd_head = z in holders_of(v, Bp) and len(H0 & rel(v, z)) >= 2 and val(v, z, H0 & rel(v, z)) > vz
            if hz and crowd_head:
                continue
            c["cp_tests"] += 1
            if not sstar(v, Bp, k):
                c["cp_fail"] += 1; ex.append(("C'", v, Y, seq, sorted(H0)))

def run(N, nlo, nhi, seed):
    rng = random.Random(seed)
    c = {x: 0 for x in ["instances", "starts", "hard", "hard_D1", "p3_tests", "p3_fail", "c0a_tests", "c0a_fail",
                        "c0b_tests", "c0b_fail", "chain_tests", "chain_exist_fail", "chain_maxm_starts", "chain_maxm_fail",
                        "red_chains", "red1_fail", "red2_fail", "red3_fail", "red4_tests", "red4_mismatch", "red_clean",
                        "red_clean_fail", "cp_chains", "cp_exist_fail", "cp_tests", "cp_fail"]}
    ex = []
    for it in range(N):
        n = rng.randint(nlo, nhi)
        if it % 3:
            m = rng.randint(n + 2, n + 3)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(rng.sample(range(m), 4), rng.sample(range(1, 40), 4)):
                    v[i][g] = x
        else:
            m = rng.randint(n + 1, n + 4)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                goods = rng.sample(range(m), rng.randint(1, min(4, m)))
                for g, x in zip(goods, rng.sample(range(1, 40), len(goods))):
                    v[i][g] = x
        c["instances"] += 1
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for order in orders[:6]:
            yd = sd(v, order); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen:
                continue
            seen.add(tuple(Y)); c["starts"] += 1
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            if len(set(range(m)) - set().union(*B)) > 5 or oa_exists(v, B):
                continue
            c["hard"] += 1
            check_start(v, Y, c, ex)
    print(json.dumps(dict(source=f"Hall §21 N={N} n={nlo}..{nhi} seed={seed}", **c)))
    for e in ex[:6]:
        print("EXAMPLE", e)

CEX = [   # §22, data as printed (sets, values in set order, order)
    ("cex1", [[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]], [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]],
     (0, 3, 2, 1), (1, 2, 5, 6)),
    ("cex2", [[0, 4, 5, 6], [1, 2, 3, 5], [1, 3, 5, 6], [2, 4, 6]], [[2, 3, 10, 6], [3, 10, 6, 8], [5, 3, 7, 6], [4, 3, 2]],
     (3, 1, 2, 0), (4, 5, 6, 2)),
    ("ttc-n5", [[0, 4, 5, 6], [2, 3, 4, 6], [0, 1, 5, 6], [2, 4, 5, 6], [0, 1, 7, 8]],
     [[3, 2, 10, 6], [4, 1, 6, 8], [2, 8, 5, 4], [5, 4, 8, 2], [7, 8, 2, 4]], (1, 3, 4, 2, 0), (4, 6, 0, 5, 1)),
]

def additions(v, B, J):
    """t = 0 moves: one agent adds a nonempty H ⊆ J ∩ R_x to its base (not an official move of k4/sdc.md §29; extra)."""
    for x in range(len(B)):
        for H in subsets(J & rel(v, x)):
            if H:
                c = [set(b) for b in B]; c[x] |= H
                yield c

def cex():
    for name, sets, vals, order, picks in CEX:
        n = len(sets); m = 1 + max(max(s) for s in sets)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(sets[i], vals[i]):
                v[i][g] = x
        strict = all(len(set(x for x in row if x > 0)) == sum(1 for x in row if x > 0) for row in v)
        yd = sd(v, order); Y = [yd[i] for i in range(n)]
        B = [{y} for y in Y]; J = set(range(m)) - set(Y)
        F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
        one = list(improving_chains(v, B, J))
        one_ok = sum(1 for s in one if oa_exists(v, s))
        add_ok = sum(1 for s in additions(v, B, J) if oa_exists(v, s))
        two_ok = 0
        for s in one:
            Js = set(range(m)) - set().union(*s)
            for s2 in improving_chains(v, s, Js):
                if oa_exists(v, s2):
                    two_ok += 1
                    break
        print(json.dumps(dict(case=name, strict=strict, picks=Y, picks_as_printed=list(Y) == list(picks), junk=sorted(J),
                              F=sorted(F), D=sorted(D), perfect=all(y is not None for y in Y), nu=nu(v),
                              hard=not oa_exists(v, B), one_chain_states=len(one), one_chain_complete=one_ok,
                              t0_additions_complete=add_ok, first_chains_with_a_repairing_second_chain=two_ok)))

if __name__ == "__main__":
    if sys.argv[1] == "cex":
        cex()
    else:
        run(*map(int, sys.argv[1:5]))
