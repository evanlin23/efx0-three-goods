#!/usr/bin/env python3
"""Referee check of kgen-n3's Proposition A and Lemmas G6, G7 (kgen/n3.md §15.17-§15.18 on claude/kgen-n3 at 0bfe9933)
at k = 3 (DE's core case: every agent values three goods a > b > c with a < b + c). Own code. Restricted to perfect
SD drafts where no LB upgrade applies (no b-holder whose c is junk), so the draft is P itself and (UT) holds trivially.
Setting: T = {t} (one non-pair-holder whose good nobody wants), |E_t| >= 2 (E_t: agents x != t holding exactly a_x with
b_x, c_x ∈ J ∪ {Y_t}). For every k ∈ E_t with (α) π_x != π_k and (β) a common good g of the sets π_x - π_k: the Rule E
chain from k (σ = the SD order, then with t moved last for G6) ends at t; the rotation's P' is valid; the completion
"g to a terminal of P', J' - g to k" is raw EFX0 (for some / every terminal). G6: with t last, t is the only wanter in
P of the good it receives, and a terminal of P'. G7: every y ∈ E'_t is of kind (a), (b) or (c)."""
import itertools, json, sys, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import efx0

def run(N, seed):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        n = rng.randint(3, 7); m = rng.randint(n + 2, 2 * n)
        v = [[0] * m for _ in range(n)]; rank = []
        for a in range(n):
            gs = rng.sample(range(m), 3)
            while True:
                x = sorted(rng.sample(range(2, 60), 3), reverse=True)
                if x[0] < x[1] + x[2]:
                    break
            for g, val_ in zip(gs, x):
                v[a][g] = val_
            rank.append(gs)                    # a, b, c
        if any(all(v[a][g] == 0 for a in range(n)) for g in range(m)):
            continue                           # cores: every good valued by someone
        sig = list(range(n)); rng.shuffle(sig)
        free = set(range(m)); Y = {}
        for a in sig:
            R = [g for g in rank[a] if g in free]
            if not R:
                break
            g = max(R, key=lambda g: v[a][g]); Y[a] = g; free.discard(g)
        if len(Y) < n:
            continue                           # perfect drafts only
        J = set(free)
        # no upgrade possible: no b-holder whose c is junk
        if any(Y[a] == rank[a][1] and rank[a][2] in J for a in range(n)):
            continue
        hold = {a: {Y[a]} for a in range(n)}; U = set()
        def val(a, S): return sum(v[a][g] for g in S)
        def wants(w, g, H, U): return w not in U and v[w][g] > val(w, H[w])
        def terminals(H, U):
            return [a for a in range(n) if a not in U and not any(w != a and wants(w, next(iter(H[a])), H, U) for w in range(n))]
        T = terminals(hold, U)
        if len(T) != 1:
            continue
        t = T[0]; W = J | {Y[t]}
        Et = [x for x in range(n) if x != t and Y[x] == rank[x][0] and {rank[x][1], rank[x][2]} <= W]
        if len(Et) < 2:
            continue
        c["one_terminal_drafts_Et_ge_2"] += 1
        pi = {x: {rank[x][1], rank[x][2]} for x in Et}
        for k in Et:
            others = [x for x in Et if x != k]
            if any(pi[x] == pi[k] for x in others):
                continue
            common = set.intersection(*[pi[x] - pi[k] for x in others])
            if not common:
                continue
            for order_kind in ("sigma", "t_last"):
                sg = sig if order_kind == "sigma" else [a for a in sig if a != t] + [t]
                pos = {a: i for i, a in enumerate(sg)}
                chain = [k]
                while chain[-1] != t:
                    gcur = Y[chain[-1]]
                    ws = [w for w in range(n) if w != chain[-1] and wants(w, gcur, hold, U)]
                    if not ws:
                        break
                    nxt = min(ws, key=lambda w: pos[w])
                    if nxt in chain:
                        c["FAIL_chain_cycle"] += 1; break
                    chain.append(nxt)
                if chain[-1] != t:
                    c["FAIL_chain_not_ending_at_t"] += 1; continue
                c[f"cases_{order_kind}"] += 1
                H2 = {a: set(hold[a]) for a in range(n)}
                for i in range(1, len(chain)):
                    H2[chain[i]] = {Y[chain[i - 1]]}
                H2[k] = set(pi[k]); U2 = {k}
                J2 = W - pi[k]
                # validity: every wanted good held alone
                valid = all(len(H2[a]) == 1 for a in range(n) for w in range(n)
                            if a != w and a not in U2 and any(wants(w, gg, H2, U2) for gg in H2[a]))
                valid &= not any(wants(w, gg, H2, U2) for w in range(n) for gg in H2[k])
                c[f"P2_valid_{order_kind}"] += valid
                T2 = terminals(H2, U2)
                c[f"T2_nonempty_{order_kind}"] += bool(T2)
                if order_kind == "sigma":
                    g = min(common)
                    oks = []
                    for tau in T2:
                        X = [set(H2[a]) for a in range(n)]
                        X[tau].add(g); X[k] |= (J2 - {g})
                        oks.append(efx0(v, X) and sum(map(len, X)) == m)
                    c["PROPA_some_terminal_works"] += any(oks); c["PROPA_every_terminal_works"] += all(oks) and bool(oks)
                    c["PROPA_VIOLATION_no_terminal_works"] += not any(oks)
                else:
                    gt = Y[chain[-2]]
                    only = all(w == t for w in range(n) if wants(w, gt, hold, U))
                    c["G6_t_only_wanter"] += only; c["G6_FAIL"] += (not only) or (t not in T2)
                    Ept = [y for y in range(n) if y != t and y not in U2 and len(H2[y]) == 1 and next(iter(H2[y])) == rank[y][0]
                           and {rank[y][1], rank[y][2]} <= J2 | H2[t]]
                    for y in Ept:
                        py = {rank[y][1], rank[y][2]}
                        ka = y in Et and not (py & pi[k])
                        kb = y not in chain and y not in Et and gt in py and (py - {gt}) <= J2
                        kc = len(chain) >= 2 and y == chain[-2] and gt in py and (py - {gt}) <= J2
                        c["G7_tests"] += 1; c["G7_FAIL"] += not (ka or kb or kc)
    print(json.dumps(dict(source=f"Proposition A / G6 / G7 at k = 3, no-upgrade perfect drafts, N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
