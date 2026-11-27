#!/usr/bin/env python3
"""Referee check of Lemma M and Lemma EX (k4/matching.md §1, §3, branch proof/k4-matching at 2c0198e).
Written from the text; reuses only my own helpers from oc1hall_ref.py (no code of k4/matching/).

Lemma M: at states with (G1), (G2), for every owner o and d = 0, 1, 2: "an S* completion with owner o and d dummy
slots exists" (brute force: every junk good to o, to a holder other than o (<= 1 each), or to a dummy (<= d goods),
raw EFX0) <=> "some H ⊆ J with (H1) has a matching in Gamma(H) covering E(H) with >= |H| - d edges".

Lemma EX: at perfect starts (every agent with a relevant good holds a pick), for every official chain (t >= 1; the end
unfrozen at Y or its pick inside H0), every owner o and every H ⊆ J': whenever (G1'), (1') and (2) hold, the proof's
allocation (o takes X, matched holders their goods, the other goods of H to Ext, one each) must be EFX0 and S*-shaped.
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd, wants, classify, max_matching, improving_chains

def matching_covering(Egoods_adj, must, H):
    """max matching size in the bipartite graph holders x H with adjacency adj[u] (goods), required to cover `must`;
    returns (exists_cover, max_size_with_cover)."""
    holders = list(Egoods_adj)
    best = -1
    # brute force over injective partial maps (small sizes)
    H = list(H)
    def rec(i, used, size, covered):
        nonlocal best
        if i == len(holders):
            if must <= covered:
                best = max(best, size)
            return
        u = holders[i]
        rec(i + 1, used, size, covered)
        for h in Egoods_adj[u]:
            if h not in used:
                rec(i + 1, used | {h}, size + 1, covered | {u})
    rec(0, frozenset(), 0, frozenset())
    return best >= 0, best

def lemmaM_state(v, B, J, o, d, holders):
    n = len(B)
    N1 = [h for h in holders if h != o]
    Q = [q for q in range(n) if q not in N1 and q != o]
    base = [val(v, i, B[i]) for i in range(n)]
    # brute force S* with d dummies
    Jl = sorted(J)
    brute = False
    for f in itertools.product(["o", "d"] + N1, repeat=len(Jl)):
        hs = [a for a in f if a not in ("o", "d")]
        if len(hs) != len(set(hs)) or sum(1 for a in f if a == "d") > d:
            continue
        X = [set(b) for b in B]
        for g, a in zip(Jl, f):
            if a == "o":
                X[o].add(g)
            elif a != "d":
                X[a].add(g)
        if efx0(v, X):
            brute = True
            break
    # formula
    Wo = set(B[o]) | set(J)
    formula = False
    for k in range(len(Jl) + 1):
        for H in itertools.combinations(Jl, k):
            Xh = Wo - set(H)
            if any(threatened(v, q, Xh, base[q]) for q in Q):
                continue
            E = {u for u in N1 if threatened(v, u, Xh, base[u])}
            adj = {u: [h for h in H if (u not in E) or (v[u][h] > 0 and not threatened(v, u, Xh, base[u] + v[u][h]))]
                   for u in N1}
            ok, size = matching_covering(adj, E, H)
            if ok and size >= len(H) - d:
                formula = True
                break
        if formula:
            break
    return brute, formula

def chains_official(v, Y, m):
    """official chains t >= 1 at the picks Y (list of goods or None): yields (seq, H list, H0)."""
    n = len(Y)
    J = set(range(m)) - {y for y in Y if y is not None}
    R = [rel(v, i) for i in range(n)]
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    frozen = {j for j in range(n) if Y[j] is not None and any(i != j and v[i][Y[j]] > val(v, i, B[i]) for i in range(n))}
    def subsets(S):
        S = sorted(S)
        for k in range(len(S) + 1):
            for c in itertools.combinations(S, k):
                yield set(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            if any(Y[x] is None for x in seq[:-1]):
                continue  # passed bases nonempty
            def rec(i, used, Hs):
                if i > t:
                    end = seq[-1]
                    pool = ((J - used) | B[end]) & R[seq[0]]
                    for H0 in subsets(pool):
                        if val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            if end in frozen and not (B[end] and B[end] <= H0):
                                continue
                            yield seq, Hs, H0
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((J - used) & R[xi]):
                    if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                        yield from rec(i + 1, used | Hi, Hs + [Hi])
            yield from rec(1, set(), [])

def lemmaEX_start(v, Y, m, cnt, ex, mut=None, rng=None):
    n = len(Y)
    J = set(range(m)) - {y for y in Y if y is not None}
    BY = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    pick = [val(v, i, BY[i]) for i in range(n)]
    F = {j for j in range(n) if Y[j] is not None and any(i != j and v[i][Y[j]] > pick[i] for i in range(n))}
    holdersY = [i for i in range(n) if i not in F]  # at a perfect start every agent holds <= 1 good
    for seq, Hs, H0 in chains_official(v, Y, m):
        Bp = [set(b) for b in BY]
        for i in range(1, len(seq)):
            Bp[seq[i]] = BY[seq[i - 1]] | Hs[i - 1]
        Bp[seq[0]] = set(H0)
        Jp = set(range(m)) - set().union(*Bp)
        valp = [val(v, i, Bp[i]) for i in range(n)]
        P = set(seq)
        Fp = {j for j in range(n) if any(i != j and any(v[i][g] > valp[i] for g in Bp[j] if g not in Bp[i]) for i in range(n))
              and len(Bp[j]) == 1}
        for o in range(n):
            # (G1'): no multi-good B'_j, j != o, threatens anyone at B' values
            if mut != "noG1" and any(len(Bp[j]) >= 2 and threatened(v, i, Bp[j], valp[i])
                                     for j in range(n) if j != o for i in range(n) if i != j):
                continue
            N = [u for u in holdersY if u not in P and u != o]
            Ext = [j for j in ((F | P) if mut == "extP" else (F | {seq[-1]})) if j != o and len(Bp[j]) == 1 and j not in Fp]
            s = len(Ext) + (1 if mut == "s+1" else 0)
            Jl = sorted(Jp)
            for k in range(len(Jl) + 1):
                for H in itertools.combinations(Jl, k):
                    Xo = set(Bp[o]) | (Jp - set(H))
                    # (1')
                    if mut != "no1F" and any(threatened(v, f, Xo, pick[f]) for f in F if f not in P and f != o):
                        continue
                    if mut != "no1P" and any(threatened(v, x, Xo, valp[x]) for x in P if x != o):
                        continue
                    E = {u for u in N if threatened(v, u, Xo, pick[u])}
                    adj = {u: [h for h in H if (u not in E) or (v[u][h] > 0 and not threatened(v, u, Xo, pick[u] + v[u][h]))] for u in N}
                    # every matching covering E with >= |H| - s edges; the rest of H to Ext in a random order
                    any_hyp = False
                    for combo in itertools.product(*[[None] + adj[u] for u in N]):
                        gs = [g for g in combo if g is not None]
                        if len(gs) != len(set(gs)) or any(combo[N.index(u)] is None for u in E):
                            continue
                        if len(gs) < len(H) - s:
                            continue
                        any_hyp = True
                        cnt["ex_tests"] += 1
                        X = [set(b) for b in Bp]
                        X[o] = set(Xo)
                        for u, g in zip(N, combo):
                            if g is not None:
                                X[u].add(g)
                        rest = [h for h in H if h not in gs]
                        ext = list(Ext)
                        if rng:
                            rng.shuffle(ext)
                        if len(rest) > len(ext):      # only under the s+1 mutation
                            X[o] |= set(rest[len(ext):]); rest = rest[:len(ext)]
                        for h, j in zip(rest, ext):
                            X[j].add(h)
                        shape = all(len(X[j] - Bp[j]) <= 1 for j in range(n) if j != o) and \
                            all(not (X[j] - Bp[j]) for j in range(n) if j != o and j not in N and j not in Ext)
                        if not efx0(v, X) or set().union(*X) != set(range(m)) or not shape:
                            cnt["ex_fail"] += 1
                            if len(ex) < 5:
                                ex.append(("EX", mut, v, Y, seq, sorted(H0), o, H, combo))
                    if any_hyp:
                        cnt["ex_hyp"] += 1

def gen(rng, nlo, nhi, mlo, mhi, kind):
    n = rng.randint(nlo, nhi)
    if kind == "pool":         # one private good each plus a shared pool (the K4.MC2-like design), some overlap
        q = rng.randint(2, 4)
        m = n + q
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            v[i][i] = rng.randint(1, 12)
            pool = rng.sample(range(n, m), rng.randint(min(2, q), min(3, q)))
            for g in pool:
                v[i][g] = rng.randint(1, 12)
        return v, m
    m = rng.randint(mlo, mhi)
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        k = rng.randint(1, min(4, m))
        for g, x in zip(rng.sample(range(m), k), (rng.sample(range(1, 30), k) if kind == "generic" else
                                                    [rng.randint(1, 4) for _ in range(k)])):
            v[i][g] = x
    return v, m

def G1G2(v, B, J, holders):
    n = len(B); base = [val(v, i, B[i]) for i in range(n)]
    if any(j not in holders and len(B[j]) >= 2 and threatened(v, i, B[j], base[i]) for j in range(n) for i in range(n) if i != j):
        return False
    return not any(v[i][g] > base[i] for g in J for i in range(n))

def run(N, nlo, nhi, mlo, mhi, seed, mut=None):
    rng = random.Random(seed)
    cnt = dict(instances=0, starts=0, M_tests=0, M_tests_after_chain=0, M_mismatch=0, M_brute_true=0,
               perfect_starts=0, ex_hyp=0, ex_tests=0, ex_fail=0)
    ex = []
    for it in range(N):
        kind = ("pool", "generic", "ties")[it % 3]
        v, m = gen(rng, nlo, nhi, mlo, mhi, kind)
        n = len(v)
        cnt["instances"] += 1
        orders = list(itertools.permutations(range(n)))
        rng.shuffle(orders)
        seen = set()
        for order in orders[:4]:
            yd = sd(v, order); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen:
                continue
            seen.add(tuple(Y))
            cnt["starts"] += 1
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            J = set(range(m)) - set().union(*B)
            if mut is None and len(J) <= 5:
                states = [B]
                chs = list(improving_chains(v, B, J))
                rng.shuffle(chs)
                for c in chs[:3]:
                    Jc = set(range(m)) - set().union(*c)
                    if len(Jc) <= 5:
                        states.append(c)
                for si, St in enumerate(states):
                    Js = set(range(m)) - set().union(*St)
                    hs = classify(v, St)
                    if not G1G2(v, St, Js, hs):
                        continue
                    for o in range(n):
                        for d in (0, 1, 2):
                            cnt["M_tests"] += 1
                            if si:
                                cnt["M_tests_after_chain"] += 1
                            b, f = lemmaM_state(v, St, Js, o, d, hs)
                            cnt["M_brute_true"] += b
                            if b != f:
                                cnt["M_mismatch"] += 1
                                if len(ex) < 5:
                                    ex.append(("M", v, [sorted(x) for x in St], o, d, b, f))
            if all(Y[i] is not None for i in range(n) if any(x > 0 for x in v[i])) and len(J) <= 4:
                cnt["perfect_starts"] += 1
                lemmaEX_start(v, Y, m, cnt, ex, mut=mut, rng=rng)
    print(json.dumps(dict(source=f"Lemma M / Lemma EX N={N} n={nlo}..{nhi} m={mlo}..{mhi} seed={seed} mutation={mut}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

def oa_def(v, B, o, dmax=4, shape="oa"):
    """least d such that B has a one-absorber (shape 'oa': every other agent <= 1 junk good) or S* completion with
    owner o and d dummy slots; brute force, raw EFX0."""
    n = len(B); m = len(v[0])
    J = sorted(set(range(m)) - set().union(*B))
    recv = [j for j in range(n) if j != o] if shape == "oa" else [j for j in classify(v, B) if j != o]
    for d in range(dmax + 1):
        for f in itertools.product(["o", "d"] + recv, repeat=len(J)):
            hs = [a for a in f if a not in ("o", "d")]
            if len(hs) != len(set(hs)) or sum(1 for a in f if a == "d") > d:
                continue
            X = [set(b) for b in B]
            for g, a in zip(J, f):
                if a == "o":
                    X[o].add(g)
                elif a != "d":
                    X[a].add(g)
            if efx0(v, X):
                return d
    return None

CASES = [   # instance data as printed in attempts/k4-matching-deficiency.md (sets, values in set order, picks)
    ("gap-ivsetting-n3-m6-n3c23", [[0, 3, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [[1, 6, 4, 8], [2, 5, 4, 8], [3, 6, 5, 7]], (4, 3, 5)),
    ("r36", [[0, 2, 4, 5], [1, 3, 4, 5], [3, 4, 5]], [[2, 4, 8, 7], [8, 10, 3, 4], [4, 3, 2]], (4, 3, 5)),
    ("PW5", [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
     [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]], (0, 1, 2, 3, 4)),
    ("RD5", [[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
     [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]], (1, 3, 4, 2)),
]

def cases():
    for name, sets, vals, Y in CASES:
        n = len(sets); m = 1 + max(max(s) for s in sets)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(sets[i], vals[i]):
                v[i][g] = x
        B = [{g} for g in Y]
        J = set(range(m)) - set(Y)
        isSD = any([sd(v, o)[i] for i in range(n)] == list(Y) for o in itertools.permutations(range(n)))
        per_owner = {o: oa_def(v, B, o) for o in range(n)}
        per_owner_s = {o: oa_def(v, B, o, shape="sstar") for o in range(n)}
        after = []
        for c in improving_chains(v, B, J):
            after.append(min(x for x in (oa_def(v, c, o, dmax=2) for o in range(n)) if x is not None)
                         if any(oa_def(v, c, o, dmax=2) is not None for o in range(n)) else 99)
        print(json.dumps(dict(case=name, picks=list(Y), is_SD_order=isSD, junk=sorted(J),
                              deficiency_oa_per_owner=per_owner, deficiency_sstar_per_owner=per_owner_s,
                              chains=len(after), least_oa_deficiency_after_one_chain=min(after),
                              repairing_chains=sum(1 for x in after if x == 0))))

if __name__ == "__main__":
    if sys.argv[1] == "cases":
        cases()
    else:
        a = list(map(int, sys.argv[1:7]))
        run(*a, mut=(sys.argv[7] if len(sys.argv) > 7 else None))
