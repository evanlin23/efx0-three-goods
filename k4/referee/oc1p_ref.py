#!/usr/bin/env python3
"""Referee replay of K4.SDC.OC1PMAX (k4/sdc.md §31 at origin/main 9cb9a45; OC1' from kgen/rounds.md §4.6). Own code
(cert_ref.py helpers: §29 official moves, one-absorber completion, raw EFX0); nothing from k4/sdc/ or kgen/rounds/ is
run or imported. The certifier's n = 4 export is read as data only.

OC1' move (written from kgen/rounds.md §1 and §4.6): an addition (one agent adds a nonempty set of junk), or a chain
x0, ..., xt (t >= 1, distinct agents, passers' bases nonempty): x_i (1 <= i <= t) takes B_{x_{i-1}} + H_i, where
H_i ⊆ J for the end x_t and H_i ⊆ J ∪ B_{x_t} for non-end agents (the OC1' widening); x0 takes H0 ⊆ J ∪ B_{x_t};
H sets disjoint; every chain agent strictly gains; the rest of B_{x_t} becomes junk. H sets lie inside the taker's
relevant goods ('strict' generator), or may be any goods ('wide' generator, a superset, for the negative claim).
Completion: one absorber (at most one agent receives two or more goods beyond its base), raw EFX0.

  cex  : the n = 5 instance 5_pure idx 164: core conditions (K4.CORE), strict types, connectivity, the SD picks of the
         three listed orders, maximum matching, OC1 fails at the picks; every OC1' move state (strict and wide
         generators) has no one-absorber completion; the EFX0 allocations that value-dominate the picks; two
         sequential official moves repair (OC2); the stated one-round repair (ring 0<->1 with junk 0, 1 and ring 3<->4
         with junk 6) is EFX0.
  n4   : the certifier's n = 4 export of the 112,880 OC1^max-failing starts (or a sample): OC1' holds (some strict-
         generator move state has a one-absorber completion), and the picks are the SD picks of a stored order.
"""
import itertools, json, gzip, sys, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, nu, complete, subsets, moves, oc_depth, mk

def oc1p_moves(v, B, wide=False):
    n = len(B); m = len(v[0]); J = set(range(m)) - set().union(*B)
    R = [set(range(m)) if wide else rel(v, i) for i in range(n)]
    for x in range(n):
        for H in subsets(J & R[x]):
            if H and val(v, x, B[x] | H) > val(v, x, B[x]):
                c = [set(b) for b in B]; c[x] |= H; yield c
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            if any(not B[x] for x in seq[:-1]):
                continue
            E = B[seq[-1]]
            def rec(i, used, nb):
                if i > t:
                    for H0 in subsets(((J | E) - used) & R[seq[0]]):
                        if H0 and val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            c = [set(b) for b in nb]; c[seq[0]] = set(H0); yield c
                    return
                xi, pr = seq[i], seq[i - 1]
                pool = (J if i == t else (J | E)) - used - B[pr]
                for Hi in subsets(pool & R[xi]):
                    if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                        c = [set(b) for b in nb]; c[xi] = B[pr] | Hi
                        yield from rec(i + 1, used | Hi, c)
            yield from rec(1, set(), [set(b) for b in B])

def uniq(states):
    u = {}
    for c in states:
        u[tuple(frozenset(b) for b in c)] = c
    return list(u.values())

def core_check(v):
    n = len(v); m = len(v[0])
    R = [rel(v, i) for i in range(n)]
    deg = Counter(g for i in range(n) for g in R[i])
    out = {}
    for i in range(n):
        xs = sorted((v[i][g] for g in R[i]), reverse=True)
        priv = [g for g in R[i] if deg[g] == 1]
        ok = len(R[i]) in (3, 4) and xs[0] < sum(xs[1:])
        ok &= len(priv) <= (1 if len(R[i]) == 3 else 2)
        if len(priv) == 2:
            others = [g for g in R[i] if g not in priv]
            ok &= sum(v[i][g] for g in priv) < sum(v[i][g] for g in others)
        # strict type: no two disjoint nonempty subsets of R_i with equal value
        gs = sorted(R[i])
        strict = True
        for S in subsets(gs):
            for T in subsets(set(gs) - S):
                if S and T and val(v, i, S) == val(v, i, T):
                    strict = False
        out[i] = dict(goods=len(R[i]), balanced_privates_ok=bool(ok), strict=strict, private=priv)
    # connectivity of the agent-good incidence graph
    seen = {0}; stack = [0]
    while stack:
        a = stack.pop()
        for b in range(n):
            if b not in seen and R[a] & R[b]:
                seen.add(b); stack.append(b)
    return out, len(seen) == n, all(deg[g] >= 1 for g in range(m))

def run_cex():
    sets = [[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]]
    vals = [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]
    v = mk(sets, vals); n = len(v); m = len(v[0])
    agents, conn, allrel = core_check(v)
    print(json.dumps(dict(instance="5_pure idx 164", n=n, m=m, agents=agents, connected=conn, every_good_relevant=allrel)))
    picks = {o: sd(v, list(o)) for o in [(1, 4, 2, 0, 3), (4, 1, 2, 0, 3), (4, 2, 1, 0, 3)]}
    print(json.dumps(dict(sd_picks={str(o): p for o, p in picks.items()}, nu=nu(v))))
    allorders = Counter(tuple(sd(v, list(o))) for o in itertools.permutations(range(n)))
    print(json.dumps(dict(orders_giving_7_2_3_5_4=allorders[(7, 2, 3, 5, 4)])))
    Y = [7, 2, 3, 5, 4]; B = [{y} for y in Y]
    print(json.dumps(dict(one_absorber_completion_at_picks=complete(v, B) is not None)))
    for wide in (False, True):
        st = uniq(oc1p_moves(v, B, wide))
        good = [s for s in st if complete(v, s) is not None]
        print(json.dumps(dict(generator="wide" if wide else "strict", oc1p_move_states=len(st),
                              states_with_one_absorber_completion=len(good))))
    st29 = moves(v, B)
    print(json.dumps(dict(sec29_official_move_states=len(st29),
                          sec29_states_with_completion=sum(complete(v, s) is not None for s in st29))))
    # EFX0 allocations that value-dominate the picks
    p = [v[i][Y[i]] for i in range(n)]
    md = []
    for f in itertools.product(range(n), repeat=m):
        X = [set() for _ in range(n)]
        for g, a in enumerate(f):
            X[a].add(g)
        if all(val(v, i, X[i]) >= p[i] for i in range(n)) and efx0(v, X):
            md.append([sorted(x) for x in X])
    swap01 = sum(1 for X in md if 2 in X[0] and 7 in X[1] and 1 in X[1])
    up3 = sum(1 for X in md if (4 in X[3] or 3 in X[3]))
    print(json.dumps(dict(md_efx0_allocations=len(md), with_0_getting_2_and_1_getting_7_and_1=swap01,
                          with_agent3_getting_4_or_3=up3, examples=md[:9])))
    print(json.dumps(dict(oc_depth_sec29=oc_depth(v, Y, 2))))
    # two sequential OC1' moves
    two = 0
    for s1 in uniq(oc1p_moves(v, B)):
        for s2 in uniq(oc1p_moves(v, s1)):
            if complete(v, s2) is not None:
                two += 1; break
    print(json.dumps(dict(first_OC1p_moves_after_which_a_second_OC1p_move_repairs=two)))
    # the stated one-round repair: ring 0<->1 with junk 0 and 1, ring 3<->4 with junk 6
    # (0 takes y1 = 2 plus junk 0; 1 takes y0 = 7 plus junk 1; 3 takes y4 = 4; 4 takes y3 = 5 plus junk 6)
    R2 = [{2, 0}, {7, 1}, {3}, {4}, {5, 6}]
    print(json.dumps(dict(one_round_state=[sorted(b) for b in R2], completion=str(complete(v, R2)),
                          gains=[val(v, i, R2[i]) > p[i] for i in range(n)])))

def check_start(args):
    sets, vals, picks, orders = args
    v = mk(sets, vals); B = [{y} for y in picks]
    sdok = any(sd(v, list(o)) == list(picks) for o in orders)
    for s in oc1p_moves(v, B):
        if complete(v, s) is not None:
            return sdok, True
    return sdok, False

def run_n4(path, N, seed, procs):
    d = json.load(gzip.open(path))
    allst = [(H["sets"], s["vals"], s["picks"], s["orders"]) for H in d["hypergraphs"] for s in H["starts"]]
    rng = random.Random(seed)
    todo = allst if N >= len(allst) else rng.sample(allst, N)
    from multiprocessing import Pool
    c = Counter(); bad = []
    with Pool(procs) as pool:
        for (sdok, ok), a in zip(pool.imap(check_start, todo, chunksize=50), todo):
            c["checked"] += 1; c["picks_are_SD"] += sdok; c["OC1p_holds"] += ok
            if not ok and len(bad) < 5:
                bad.append(a)
    print(json.dumps(dict(source=f"OC1' on the certifier's n = 4 export, N={N} seed={seed}", exported=len(allst), **c)))
    for b in bad:
        print("FAIL", b)

if __name__ == "__main__":
    if sys.argv[1] == "cex":
        run_cex()
    else:
        run_n4(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
