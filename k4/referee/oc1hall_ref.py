#!/usr/bin/env python3
"""Referee check of Lemma 2, Lemma 2*, Corollary 2.1, Proposition 3 and Theorem F1_1 (k4/oc1_hall.md §4-§6,
branch claude/k4-oc1-hall). Written from the text; shares no code with k4/oc1_hall/ or k4/sdc/.

States: serial-dictatorship picks of random instances with <= 4 relevant goods per agent (additive, ties allowed),
and the states one random improving chain (k4/sdc.md §29) reaches from them.

For every state and every owner o:
  * brute force: does an S* completion with owner o exist (one owner; each holder other than o -- an agent with at
    most one base good that nobody else wants -- takes at most one junk good; everyone else takes nothing; raw EFX0)?
  * Lemma 2 (when (G1), (G2), (G5'), (H3) hold): some H ⊆ J with (H1) and |H| + theta(H) - nu(H) <= |N1|;
  * Lemma 2* (when (G1), (G2) hold): some H with (H1) and an SDR of admissible holders covering every non-movable
    exposed holder;
  * Corollary 2.1: (H2) <=> an SDR of H into admissible holders exists.
For every start with exactly one frozen agent x, one wanter w, n >= 3 (Theorem F1_1): Proposition 3's owner, case
(B2) (every owner outside {x, w} after a pair swap), (B3a) (owner w after the swap to L_x), (B3b) (every owner outside
{x, i}) are each checked by brute force, and the theorem's conclusion as a whole.
"""
import itertools, random, sys, json

def val(v, i, S):
    return sum(v[i][g] for g in S)

def threatened(v, i, S, t):
    tot = val(v, i, S)
    return any(tot - v[i][h] > t for h in S)

def efx0(v, X):
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2 and threatened(v, i, X[j], t):
                return False
    return True

def rel(v, i):
    return {g for g in range(len(v[i])) if v[i][g] > 0}

def sd(v, order):
    m = len(v[0]); G = set(range(m)); Y = {}
    for i in order:
        R = sorted((g for g in G if v[i][g] > 0), key=lambda g: (-v[i][g], g))
        Y[i] = R[0] if R else None
        if R:
            G.discard(R[0])
    return Y

def wants(v, i, g, B):
    return g not in B[i] and v[i][g] > val(v, i, B[i])

def classify(v, B):
    """holders (<= 1 base good nobody else wants), others."""
    n = len(B)
    holders = []
    for j in range(n):
        if len(B[j]) <= 1 and not any(i != j and any(wants(v, i, g, B) for g in B[j]) for i in range(n)):
            holders.append(j)
    return holders

def sstar_brute(v, B, J, o, holders):
    N1 = [h for h in holders if h != o]
    J = sorted(J)
    for f in itertools.product([None] + N1, repeat=len(J)):
        used = [a for a in f if a is not None]
        if len(used) != len(set(used)):
            continue
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            X[o if a is None else a].add(g)
        if efx0(v, X):
            return True
    return False

def max_matching(adj):
    """adj: dict left -> set of right; returns size of max matching (small, augmenting paths)."""
    match = {}
    def aug(u, seen):
        for w in adj[u]:
            if w in seen:
                continue
            seen.add(w)
            if w not in match or aug(match[w], seen):
                match[w] = u
                return True
        return False
    return sum(1 for u in adj if aug(u, set()))

def sdr_covering(H, N1, adm, must):
    """is there an injective map H -> N1 with h -> u only if adm(u, h), whose image contains `must`?"""
    H = list(H)
    for perm in itertools.permutations(N1, len(H)) if len(H) <= len(N1) else []:
        if all(adm(u, h) for h, u in zip(H, perm)) and set(must) <= set(perm):
            return True
    return False

def lemma2_tests(v, B, J, o, holders, cnt, ex, tag):
    n = len(B)
    N1 = [h for h in holders if h != o]
    Q = [q for q in range(n) if q not in N1 and q != o]
    Wo = set(B[o]) | set(J)
    base = [val(v, i, B[i]) for i in range(n)]
    G1 = not any(threatened(v, i, B[q], base[i]) for q in Q for i in range(n) if i != q and len(B[q]) >= 2)
    G2 = not any(v[i][g] > base[i] for g in J for i in range(n))
    G5 = not any(wants(v, i, g, B) for i in N1 for g in B[o])
    H3 = all(len(set(B[o]) & rel(v, i)) <= 1 or val(v, i, set(B[o]) & rel(v, i)) <= base[i] for i in N1)
    brute = sstar_brute(v, B, J, o, holders)
    cnt["owner_tests"] += 1
    if not (G1 and G2):
        return brute
    def exposed(H):
        S = Wo - set(H)
        return [u for u in N1 if threatened(v, u, S, base[u])]
    lem2 = lem2s = False; cor_bad = 0
    for k in range(len(J) + 1):
        for H in itertools.combinations(sorted(J), k):
            S = Wo - set(H)
            if any(threatened(v, q, S, base[q]) for q in Q):
                continue  # (H1)
            E = exposed(H)
            def adm(u, h):
                if u not in E:
                    return True
                return v[u][h] > 0 and not threatened(v, u, S, base[u] + v[u][h])
            adjE = {u: {h for h in H if adm(u, h)} for u in E}
            nu = max_matching(adjE)
            H2 = len(H) + len(E) - nu <= len(N1)
            sdr = sdr_covering(H, N1, adm, [])
            if H2 != sdr:
                cor_bad += 1
            if H2:
                lem2 = True
            nonmov = [u for u in E if any(wants(v, u, g, B) for g in B[o]) or
                      (len(set(B[o]) & rel(v, u)) >= 2 and val(v, u, set(B[o]) & rel(v, u)) > base[u])]
            if sdr_covering(H, N1, adm, nonmov):
                lem2s = True
    cnt["cor21_tests"] += 1
    if cor_bad:
        cnt["cor21_mismatch"] += 1
    cnt["lemma2star_tests"] += 1
    if lem2s != brute:
        cnt["lemma2star_mismatch"] += 1
        if len(ex) < 6:
            ex.append(("lemma2*", tag, v, [sorted(b) for b in B], o, brute, lem2s))
    if G5 and H3:
        cnt["lemma2_tests"] += 1
        if lem2 != brute:
            cnt["lemma2_mismatch"] += 1
            if len(ex) < 6:
                ex.append(("lemma2", tag, v, [sorted(b) for b in B], o, brute, lem2))
    return brute

def improving_chains(v, B, J):
    n = len(B)
    def subsets(S):
        S = sorted(S)
        for k in range(len(S) + 1):
            for c in itertools.combinations(S, k):
                yield set(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            def rec(i, used, nb):
                if i > t:
                    pool = ((set(J) - used) | set(B[seq[-1]])) & rel(v, seq[0])
                    for H0 in subsets(pool):
                        if H0 and val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            c = list(nb); c[seq[0]] = set(H0); yield c
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((set(J) - used) & rel(v, xi)):
                    if val(v, xi, set(B[pr]) | Hi) > val(v, xi, B[xi]):
                        c = list(nb); c[xi] = set(B[pr]) | Hi
                        yield from rec(i + 1, used | Hi, c)
            yield from rec(1, set(), [set(b) for b in B])

def f1_tests(v, Y, cnt, ex):
    n = len(v); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    picks = {g for g in Y.values() if g is not None}
    J = set(range(m)) - picks
    frozen = [j for j in range(n) if B[j] and any(i != j and wants(v, i, Y[j], B) for i in range(n))]
    if len(frozen) != 1 or n < 3:
        return
    x = frozen[0]; a = Y[x]
    W = [i for i in range(n) if i != x and wants(v, i, a, B)]
    if len(W) != 1:
        return
    w = W[0]; px = v[x][a]
    cnt["f1_starts"] += 1
    holders = classify(v, B)
    def has(Bs, o):
        held = set().union(*Bs); Js = set(range(m)) - held
        return sstar_brute(v, Bs, Js, o, classify(v, Bs))
    # Proposition 3
    prop3 = [o for o in range(n) if o != x and val(v, x, (J | B[o]) & rel(v, x)) <= px]
    for o in prop3:
        cnt["prop3_owner_tests"] += 1
        if not has(B, o):
            cnt["prop3_fail"] += 1
            if len(ex) < 6:
                ex.append(("prop3", v, dict(Y), o))
    conclusion = any(has(B, o) for o in range(n))
    I = (J | B[w]) & rel(v, x)
    def swap(H0):
        Bs = [set(b) for b in B]; Bs[w] = {a}; Bs[x] = set(H0); return Bs
    if not prop3:
        pairs = [set(p) for p in itertools.combinations(sorted(I), 2) if val(v, x, p) > px]
        if pairs:
            cnt["B2"] += 1
            for H0 in pairs:
                Bs = swap(H0)
                for o in range(n):
                    if o in (x, w):
                        continue
                    cnt["B2_owner_tests"] += 1
                    if not has(Bs, o):
                        cnt["B2_fail"] += 1
                        if len(ex) < 6:
                            ex.append(("B2", v, dict(Y), sorted(H0), o))
        else:
            Lx = rel(v, x) - {a}
            if I != Lx or len(Lx) != 3:
                cnt["B3_shape_violation"] += 1
            crowded = [i for i in range(n) if i != x and threatened(v, i, Lx, v[i][Y[i]] if Y[i] is not None else 0)]
            if not crowded:
                cnt["B3a"] += 1
                if not has(swap(Lx), w):
                    cnt["B3a_fail"] += 1
                    if len(ex) < 6:
                        ex.append(("B3a", v, dict(Y)))
            else:
                cnt["B3b"] += 1
                for i in crowded:
                    for o in range(n):
                        if o in (x, i):
                            continue
                        cnt["B3b_owner_tests"] += 1
                        if not has(B, o):
                            cnt["B3b_fail"] += 1
                            if len(ex) < 6:
                                ex.append(("B3b", v, dict(Y), i, o))
    if not conclusion:
        ok = False
        for H0 in (set(c) for k in range(1, len(I) + 1) for c in itertools.combinations(sorted(I), k)):
            if val(v, x, H0) > px and any(has(swap(H0), o) for o in range(n)):
                ok = True; break
        if not ok:
            cnt["f1_theorem_fail"] += 1
            if len(ex) < 6:
                ex.append(("F1_1", v, dict(Y)))

def rand_inst(rng, n, m, ties, pool=None):
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        k = rng.randint(2, min(4, m))
        R = rng.sample(range(m) if pool is None else pool, k)
        for g in R:
            v[i][g] = rng.randint(1, 4 if ties else 30)
    return v

def run(N, nlo, nhi, mlo, mhi, ties, seed, chains_per=2):
    rng = random.Random(seed)
    cnt = {k: 0 for k in ["starts", "states", "owner_tests", "lemma2_tests", "lemma2_mismatch", "lemma2star_tests",
                          "lemma2star_mismatch", "cor21_tests", "cor21_mismatch", "f1_starts", "prop3_owner_tests",
                          "prop3_fail", "B2", "B2_owner_tests", "B2_fail", "B3a", "B3a_fail", "B3b", "B3b_owner_tests",
                          "B3b_fail", "B3_shape_violation", "f1_theorem_fail"]}
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        v = rand_inst(rng, n, m, ties)
        seen = set()
        orders = list(itertools.permutations(range(n)))
        rng.shuffle(orders)
        for order in orders[:6]:
            Y = sd(v, order)
            key = tuple(Y[i] for i in range(n))
            if key in seen:
                continue
            seen.add(key); cnt["starts"] += 1
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            J = set(range(m)) - set().union(*B)
            states = [(B, J, "picks")]
            chs = list(itertools.islice(improving_chains(v, B, J), 200))
            for c in rng.sample(chs, min(chains_per, len(chs))):
                Jc = set(range(m)) - set().union(*c)
                states.append((c, Jc, "chain"))
            for Bs, Js, tag in states:
                if len(Js) > 6:
                    continue
                cnt["states"] += 1
                hs = classify(v, Bs)
                for o in range(n):
                    lemma2_tests(v, Bs, Js, o, hs, cnt, ex, tag)
            f1_tests(v, Y, cnt, ex)
    print(json.dumps(dict(source=f"oc1_hall N={N} n={nlo}..{nhi} m={mlo}..{mhi} ties={ties} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

def run_f1(N, nlo, nhi, mlo, mhi, ties, seed):
    """targeted: instances built to have one frozen agent with one wanter (shared top), many orders."""
    rng = random.Random(seed)
    cnt = {k: 0 for k in ["starts", "f1_starts", "prop3_owner_tests", "prop3_fail", "B2", "B2_owner_tests", "B2_fail",
                          "B3a", "B3a_fail", "B3b", "B3b_owner_tests", "B3b_fail", "B3_shape_violation",
                          "f1_theorem_fail"]}
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        v = rand_inst(rng, n, m, ties)
        # x = 0 and w = 1 share top good 0; x has three lower goods worth little each but much together sometimes
        v[0] = [0] * m; v[1][0] = max(v[1]) + rng.randint(1, 5)
        lower = rng.sample(range(1, m), 3)
        top = rng.randint(10, 30)
        for g in lower:
            v[0][g] = rng.randint(max(1, top // 4), top - 1)
        v[0][0] = top
        for order in itertools.permutations(range(n)):
            Y = sd(v, order); cnt["starts"] += 1
            f1_tests(v, Y, cnt, ex)
    print(json.dumps(dict(source=f"F1_1 targeted N={N} n={nlo}..{nhi} m={mlo}..{mhi} ties={ties} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "run":
        run(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), a[6] == "ties", int(a[7]))
    elif a[0] == "f1":
        run_f1(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), a[6] == "ties", int(a[7]))

def run_f1b3(N, nlo, nhi, ties, seed):
    """targeted at cases (B3a), (B3b): x = 0 with top 0 and three lower goods 1, 2, 3 that are junk and satisfy
    b + c <= a < b + c + d; w = 1 wants good 0; other agents get private tops and sometimes two of x's lower goods."""
    rng = random.Random(seed)
    cnt = {k: 0 for k in ["starts", "f1_starts", "prop3_owner_tests", "prop3_fail", "B2", "B2_owner_tests", "B2_fail",
                          "B3a", "B3a_fail", "B3b", "B3b_owner_tests", "B3b_fail", "B3_shape_violation",
                          "f1_theorem_fail"]}
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = 4 + n + rng.randint(0, 3)
        v = [[0] * m for _ in range(n)]
        while True:
            b, c, d = sorted([rng.randint(1, 12) for _ in range(3)], reverse=True)
            a = rng.randint(max(b, b + c), b + c + d - 1) if b + c < b + c + d - 1 else None
            if a is not None and a >= b and b + c <= a < b + c + d:
                break
        v[0][0], v[0][1], v[0][2], v[0][3] = a, b, c, d
        # w: top good 0, second its own good 4 (+ maybe junk)
        v[1][0] = rng.randint(5, 20); v[1][4] = rng.randint(1, v[1][0] - 1 if v[1][0] > 1 else 1)
        if rng.random() < 0.5:
            v[1][rng.choice([1, 2, 3])] = rng.randint(1, max(1, v[1][4] - 1)) if v[1][4] > 1 else 0
        for i in range(2, n):
            own = 4 + i
            v[i][own] = rng.randint(3, 15)
            if rng.random() < 0.7:
                g, g2 = rng.sample([1, 2, 3], 2)
                v[i][g] = rng.randint(1, max(1, v[i][own] - 1)); v[i][g2] = rng.randint(1, max(1, v[i][own] - 1))
            if rng.random() < 0.3 and own + 1 < m:
                v[i][own + 1] = rng.randint(1, v[i][own])
        for order in itertools.permutations(range(n)):
            Y = sd(v, order); cnt["starts"] += 1
            f1_tests(v, Y, cnt, ex)
    print(json.dumps(dict(source=f"F1_1 (B3-targeted) N={N} n={nlo}..{nhi} ties={ties} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__" and sys.argv[1] == "f1b3":
    run_f1b3(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] == "ties", int(sys.argv[6]))
