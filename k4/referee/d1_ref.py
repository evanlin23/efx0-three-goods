#!/usr/bin/env python3
"""Referee check of Theorem D1-C (k4/d1.md §3) and Proposition D1-H3 (§6), branch proof/k4-d1 at a9232a0.
Own code (oc1hall_ref.py / multi_ref.py helpers), raw EFX0. Nothing from k4/d1/ is run or imported.

Part 1. SD starts (any order, maximum matching or not) of random instances with <= 4 relevant goods per agent and every
good relevant to someone, D = {k}:
  * at hard starts: every canonical chain from k without HEAD has some H0 in M (inclusion-minimal improving subsets of
    P_k) with an S* completion owned by k (brute force);  -- the theorem
  * Lemma C3 and Lemma HC at hard starts (a crowded head with y_z in H0 forces U = empty; a crowded head has an option);
  * at every start (hard or not): Tool T (whenever (i), (ii) hold for an unfrozen owner o and |H| <= 2, the picks have
    an S* completion with owner o), Lemma O(b), and Lemma HC's allocation A (whenever its case hypotheses hold, A is
    an EFX0 one-absorber completion of the picks).
Part 2. Proposition D1-H3 on random three-agent K4.MC2 cores (3-4 goods each, strictly balanced, <= 1 private good,
  ties allowed or not): at every hard start with D = {k}, k the only frozen agent, both other agents wanting a = Y_k and
  every canonical chain having HEAD, some canonical chain with a minimal H0 repairs (S* owned by k).
Part 3. The named instances: D1H-X, the outside-MC2 example of §6 and the tied model on D1H-X's structure.
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd
from multi_ref import frozen_set, holders_of, oa_exists, sstar, subsets, canonical_chains

def robust(v, i, yi_val, h, Q):
    return yi_val + v[i][h] >= val(v, i, set(Q) - {h})

def minimal_improving(v, k, P, p):
    out = []
    for S in subsets(P):
        if S and val(v, k, S) > p and not any(val(v, k, S - {g}) > p for g in S):
            out.append(S)
    return out

def state_after(B, seq, H0, Y):
    Bp = [set(b) for b in B]; Bp[seq[0]] = set(H0)
    for i in range(1, len(seq)):
        Bp[seq[i]] = {Y[seq[i - 1]]}
    return Bp

def tool_T(v, Y, B, J, F, k, c, ex):
    """every unfrozen owner o and H ⊆ J, |H| <= 2, with (i) and (ii): S* with owner o must exist."""
    n = len(Y); p = [val(v, i, B[i]) for i in range(n)]
    for o in range(n):
        if o in F:
            continue
        Wo = J | B[o]
        for r in (0, 1, 2):
            for H in itertools.combinations(sorted(J), r):
                H = set(H)
                if threatened(v, k, Wo - H, p[k]):
                    continue
                # distinct helpers: unfrozen agents != o with a pick, valuing h, h robust in Wo ∩ R_i
                cand = {h: [i for i in range(n) if i != o and i not in F and Y[i] is not None and v[i][h] > 0
                            and robust(v, i, p[i], h, Wo & rel(v, i))] for h in H}
                Hl = sorted(H)
                ok = any(len(set(a)) == len(a) for a in itertools.product(*[cand[h] for h in Hl])) if Hl else True
                if not ok:
                    continue
                c["toolT_tests"] += 1
                if not sstar(v, B, o):
                    c["toolT_fail"] += 1; ex.append(("ToolT", v, Y, o, Hl))

def check_start(v, Y, c, ex, hard):
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B)
    p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B)
    D = {d for d in F if any(v[d][g] > 0 for g in J)}
    if len(D) != 1:
        return
    (k,) = D
    c["hard_D1" if hard else "easy_D1"] += 1
    tool_T(v, Y, B, J, F, k, c, ex)
    for seq in canonical_chains(v, Y, F):
        if seq[0] != k:
            continue
        z = seq[-1]; a = Y[seq[-2]]; x = seq[-2]
        Pi = J | B[z]; Pk = Pi & rel(v, k)
        second = [w for w in range(n) if w not in seq and v[w][a] > p[w]]
        head = bool(second) and threatened(v, z, Pi, v[z][a])
        if head:
            continue
        U = [u for u in range(n) if u not in seq and u not in F]
        M = minimal_improving(v, k, Pk, p[k])
        if hard:
            c["chains_noHEAD"] += 1
            good = False
            for H0 in M:
                Bp = state_after(B, seq, H0, Y)
                crowded_any = any(len(H0 & rel(v, u)) >= 2 and val(v, u, H0 & rel(v, u)) > val(v, u, Bp[u])
                                  for u in holders_of(v, Bp) if u != k)
                c["crowd_H0" if crowded_any else "clean_H0"] += 1
                if sstar(v, Bp, k):
                    good = True
            if not good:
                c["D1C_fail"] += 1; ex.append(("D1-C", v, Y, seq))
        # lemma-level checks for every H0 in M
        for H0 in M:
            Bp = state_after(B, seq, H0, Y)
            hold = holders_of(v, Bp)
            if z not in hold:
                continue
            zc = len(H0 & rel(v, z)) >= 2 and val(v, z, H0 & rel(v, z)) > v[z][a]
            if not zc:
                continue
            yz = Y[z]
            Qz = Pi & rel(v, z)
            if yz is None or yz not in H0:
                c["O_b_tests"] += 1
                if yz is None or not robust(v, z, v[z][a], yz, Qz):
                    c["O_b_fail"] += 1; ex.append(("O(b)", v, Y, seq, sorted(H0)))
                continue
            if hard:
                c["C3_tests"] += 1
                if U:
                    c["C3_fail"] += 1; ex.append(("C3", v, Y, seq, sorted(H0)))
            if U:
                continue
            g = next(iter(sorted((H0 & rel(v, z) & J))), None)
            if g is None:
                continue
            others = Qz - {yz, g}
            e = next(iter(others), None)
            if e is not None and e in H0:
                continue
            has_opt = e is not None and robust(v, z, v[z][a], e, Qz)
            if hard:
                c["HC_tests"] += 1
                if not has_opt:
                    c["HC_fail"] += 1; ex.append(("HC", v, Y, seq, sorted(H0)))
            if not has_opt:
                # Lemma HC's allocation A: x takes {a} ∪ (J - g), z takes {y_z, g}
                A = [set(b) for b in B]
                A[x] = {a} | (J - {g}); A[z] = {yz, g}
                c["HC_A_tests"] += 1
                if not (efx0(v, A) and set().union(*A) == set(range(m))):
                    c["HC_A_fail"] += 1; ex.append(("HC-A", v, Y, seq, sorted(H0)))

def rand_inst(rng, n):
    if rng.random() < 0.6:     # denser: random 4-sets in m = n + 2 .. n + 3
        while True:
            m = rng.randint(n + 2, n + 3)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(rng.sample(range(m), rng.choice([3, 4])), rng.sample(range(1, 40), 4)):
                    v[i][g] = x
            if all(any(v[i][g] > 0 for i in range(n)) for g in range(m)):
                return v
    while True:
        m = rng.randint(n + 1, n + 4)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.randint(2, min(4, m))), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        if all(any(v[i][g] > 0 for i in range(n)) for g in range(m)):
            return v

def part1(N, nlo, nhi, seed):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); v = rand_inst(rng, n)
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:6]:
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen:
                continue
            seen.add(tuple(Y))
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            if len(set(range(len(v[0]))) - set().union(*B)) > 5:
                continue
            c["starts"] += 1
            check_start(v, Y, c, ex, hard=not oa_exists(v, B))
    print(json.dumps(dict(source=f"D1-C part 1 N={N} n={nlo}..{nhi} seed={seed}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

def mc2_inst(rng, ties):
    while True:
        m = rng.randint(4, 8)
        sets = [sorted(rng.sample(range(m), rng.choice([3, 4]))) for _ in range(3)]
        if not all(any(g in s for s in sets) for g in range(m)):
            continue
        if any(sum(1 for g in s if sum(1 for t in sets if g in t) == 1) > 1 for s in sets):
            continue
        v = [[0] * m for _ in range(3)]
        ok = True
        for i, s in enumerate(sets):
            xs = [rng.randint(1, 12) for _ in s] if ties else rng.sample(range(1, 30), len(s))
            if 2 * max(xs) >= sum(xs):
                ok = False; break
            for g, x in zip(s, xs):
                v[i][g] = x
        if ok:
            return v

def part2(N, seed, ties):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    for _ in range(N):
        v = mc2_inst(rng, ties)
        n = 3; m = len(v[0])
        seen = set()
        for o in itertools.permutations(range(n)):
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen or any(y is None for y in Y):
                continue
            seen.add(tuple(Y))
            B = [{y} for y in Y]; J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
            F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
            if len(F) != 1 or len(D) != 1:
                continue
            (k,) = D
            others = [i for i in range(n) if i != k]
            if not all(v[i][Y[k]] > p[i] for i in others):
                continue
            if oa_exists(v, B):
                continue
            chains = [s for s in canonical_chains(v, Y, F) if s[0] == k]
            allhead = True
            for seq in chains:
                z = seq[-1]; a = Y[seq[-2]]
                second = [w for w in range(n) if w not in seq and v[w][a] > p[w]]
                if not (second and threatened(v, z, J | B[z], v[z][a])):
                    allhead = False
            if not allhead:
                continue
            c["core3_allHEAD_hard"] += 1
            good = any(sstar(v, state_after(B, seq, H0, Y), k)
                       for seq in chains for H0 in minimal_improving(v, k, (J | B[seq[-1]]) & rel(v, k), p[k]))
            if not good:
                c["D1H3_fail"] += 1; ex.append(("D1-H3", v, Y))
    print(json.dumps(dict(source=f"D1-H3 sample N={N} seed={seed} ties={ties}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

def mk(sets, vals):
    m = 1 + max(max(s) for s in sets)
    v = [[0] * m for _ in sets]
    for i, (s, x) in enumerate(zip(sets, vals)):
        for g, a in zip(s, x):
            v[i][g] = a
    return v

def ed_chains_repair(v, Y, k):
    """all chains from k (t >= 1, any H_i ⊆ J inside R, H0 ⊆ J ∪ B_xt), S* owned by k after it?"""
    from oc1hall_ref import improving_chains
    n = len(Y); B = [{y} for y in Y]; J = set(range(len(v[0]))) - set(Y)
    res = []
    for st in improving_chains(v, B, J):
        if st[k] != B[k] and sstar(v, st, k):
            res.append([sorted(b) for b in st])
    return res

def part3():
    cases = [("D1H-X", [[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]], [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29]], (0, 1, 2)),
             ("outside-MC2 strict", [[0, 3, 4], [0, 1, 5, 6], [0, 2, 7, 8]], [[4, 3, 2], [8, 4, 3, 2], [8, 4, 3, 2]], None),
             ("D1H-X structure, tied", [[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]], [[2, 2, 1, 2], [5, 2, 2, 2], [5, 2, 2, 2]], None)]
    for name, sets, vals, order in cases:
        v = mk(sets, vals); n = 3; m = len(v[0])
        orders = [order] if order else list(itertools.permutations(range(n)))
        for o in orders:
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            B = [{y} for y in Y]; J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
            F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
            if len(D) != 1:
                continue
            (k,) = D
            hard = not oa_exists(v, B)
            chains = [s for s in canonical_chains(v, Y, F) if s[0] == k]
            canon_ok = any(sstar(v, state_after(B, s, H0, Y), k) for s in chains
                           for H0 in minimal_improving(v, k, (J | B[s[-1]]) & rel(v, k), p[k]))
            # head + one junk good: z takes {a, h}
            hj_ok = False
            for s in chains:
                z = s[-1]
                for h in J & rel(v, z):
                    for H0 in minimal_improving(v, k, ((J - {h}) | B[z]) & rel(v, k), p[k]):
                        st = state_after(B, s, H0, Y); st[z] = {Y[s[-2]], h}
                        if sstar(v, st, k):
                            hj_ok = True
            ed = ed_chains_repair(v, Y, k)
            print(json.dumps(dict(case=name, order=list(o), picks=Y, k=k, frozen=sorted(F), hard=hard,
                                  canonical_chains=[list(s) for s in chains], canonical_repair=canon_ok,
                                  head_junk_repair=hj_ok, any_chain_repairs_owner_k=len(ed), example=ed[:1])))
            if order is None:
                pass

def core_inst(rng, ties):
    """the three-agent core configuration built directly (agents k = 0, z = 1, w = 2; goods a = 0, y_z = 1, y_w = 2,
    the rest junk), K4.MC2 conditions enforced; the SD order (0, 1, 2) must give picks (0, 1, 2)."""
    while True:
        m = rng.randint(5, 8)
        others = list(range(3, m))
        sk = {0} | set(rng.sample([1, 2] + others, rng.choice([2, 3])))
        sz = {0, 1} | set(rng.sample([2] + others, rng.choice([1, 2])))
        sw = {0, 2} | set(rng.sample([1] + others, rng.choice([1, 2])))
        sets = [sorted(sk), sorted(sz), sorted(sw)]
        if not all(any(g in t for t in sets) for g in range(m)):
            continue
        if any(sum(1 for g in t if sum(1 for u in sets if g in u) == 1) > 1 for t in sets):
            continue
        v = [[0] * m for _ in range(3)]
        bad = False
        for i, t in enumerate(sets):
            xs = [rng.randint(1, 12) for _ in t] if ties else rng.sample(range(1, 40), len(t))
            if 2 * max(xs) >= sum(xs):
                bad = True; break
            for g, x in zip(t, xs):
                v[i][g] = x
        if bad:
            continue
        if sd(v, (0, 1, 2)) != {0: 0, 1: 1, 2: 2}:
            continue
        return v

def part2c(N, seed, ties):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    for _ in range(N):
        v = core_inst(rng, ties); n = 3; m = len(v[0])
        Y = [0, 1, 2]; B = [{y} for y in Y]; J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
        F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
        c["cores"] += 1
        if F != {0} or D != {0} or not (v[1][0] > p[1] and v[2][0] > p[2]):
            continue
        c["config"] += 1
        chains = [s for s in canonical_chains(v, Y, F) if s[0] == 0]
        allhead = all(any(w not in s and v[w][Y[s[-2]]] > p[w] for w in range(n)) and
                      threatened(v, s[-1], J | B[s[-1]], v[s[-1]][Y[s[-2]]]) for s in chains)
        if not allhead:
            continue
        c["allHEAD"] += 1
        if oa_exists(v, B):
            continue
        c["allHEAD_hard"] += 1
        good = any(sstar(v, state_after(B, seq, H0, Y), 0)
                   for seq in chains for H0 in minimal_improving(v, 0, (J | B[seq[-1]]) & rel(v, 0), p[0]))
        if not good:
            c["D1H3_fail"] += 1
            if len(ex) < 6:
                ex.append(("D1-H3", v))
    print(json.dumps(dict(source=f"D1-H3 targeted three-agent cores N={N} seed={seed} ties={ties}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

def tied_all_orders():
    """the tied model on D1H-X's structure, under every tie-breaking: any SD outcome (each agent takes some top good)."""
    sets = [[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]]; vals = [[2, 2, 1, 2], [5, 2, 2, 2], [5, 2, 2, 2]]
    v = mk(sets, vals); n = 3; m = len(v[0])
    outs = set()
    for o in itertools.permutations(range(n)):
        def rec(i, taken, Y):
            if i == n:
                outs.add(tuple(Y)); return
            a = o[i]
            avail = [g for g in range(m) if g not in taken and v[a][g] > 0]
            if not avail:
                Y2 = list(Y); rec(i + 1, taken, Y2); return
            top = max(v[a][g] for g in avail)
            for g in avail:
                if v[a][g] == top:
                    Y2 = list(Y); Y2[a] = g; rec(i + 1, taken | {g}, Y2)
        rec(0, set(), [None] * n)
    res = []
    for Y in sorted(outs, key=str):
        if any(y is None for y in Y):
            continue
        B = [{y} for y in Y]; J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
        F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
        if len(D) != 1 or oa_exists(v, B):
            continue
        (k,) = D
        chains = [s for s in canonical_chains(v, list(Y), F) if s[0] == k]
        canon = any(sstar(v, state_after(B, s, H0, list(Y)), k) for s in chains
                    for H0 in minimal_improving(v, k, (J | B[s[-1]]) & rel(v, k), p[k]))
        res.append(dict(picks=list(Y), k=k, chains=[list(s) for s in chains], canonical_repair=canon,
                        any_chain_owner_k=len(ed_chains_repair(v, list(Y), k))))
    print(json.dumps(dict(case="D1H-X structure, tied, every tie-breaking", hard_D1_starts=res)))

def qualifies_core(v):
    n = 3; m = len(v[0]); Y = [0, 1, 2]
    if any(v[i][Y[i]] <= 0 for i in range(n)) or sd(v, (0, 1, 2)) != {0: 0, 1: 1, 2: 2}:
        return None
    for i in range(n):
        xs = [x for x in v[i] if x > 0]
        if 2 * max(xs) >= sum(xs):
            return None
    B = [{y} for y in Y]; J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    if F != {0} or D != {0} or not (v[1][0] > p[1] and v[2][0] > p[2]):
        return None
    chains = [s for s in canonical_chains(v, Y, F) if s[0] == 0]
    if not all(any(w not in s and v[w][Y[s[-2]]] > p[w] for w in range(n)) and
               threatened(v, s[-1], J | B[s[-1]], v[s[-1]][Y[s[-2]]]) for s in chains):
        return None
    if oa_exists(v, B):
        return None
    return chains, B, J, p

def part2w(N, seed, ties, steps=400):
    """targeted cores, then value walks (+-1..3 on one relevant value; sets and MC2 conditions kept) from every
    qualifying profile; D1-H3 tested at every distinct qualifying profile visited."""
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []; seen = set()
    for _ in range(N):
        v = core_inst(rng, ties)
        q = qualifies_core(v)
        if not q:
            continue
        c["seeds"] += 1
        cur = [row[:] for row in v]
        for st in range(steps):
            key = tuple(map(tuple, cur))
            q = qualifies_core(cur)
            if q and key not in seen:
                seen.add(key)
                chains, B, J, p = q
                c["profiles"] += 1
                good = any(sstar(cur, state_after(B, seq, H0, [0, 1, 2]), 0)
                           for seq in chains for H0 in minimal_improving(cur, 0, (J | B[seq[-1]]) & rel(cur, 0), p[0]))
                if not good:
                    c["D1H3_fail"] += 1
                    if len(ex) < 6:
                        ex.append(("D1-H3", cur))
            nxt = [row[:] for row in cur]
            i = rng.randrange(3); gs = [g for g in range(len(cur[0])) if cur[i][g] > 0]
            g = rng.choice(gs); nxt[i][g] = max(1, nxt[i][g] + rng.choice([-3, -2, -1, 1, 2, 3]))
            if not ties and len(set(x for x in nxt[i] if x > 0)) < len(gs):
                continue
            if qualifies_core(nxt):
                cur = nxt
    print(json.dumps(dict(source=f"D1-H3 targeted cores + walks N={N} seed={seed} ties={ties}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

def crowd_case(v, Y):
    """(hard D1 start) list of no-HEAD canonical chains from k having a minimal H0 that crowds a holder."""
    n = len(Y); m = len(v[0])
    B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    J = set(range(m)) - set().union(*B); p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    if len(D) != 1:
        return False
    (k,) = D
    for seq in canonical_chains(v, Y, F):
        if seq[0] != k:
            continue
        z = seq[-1]; a = Y[seq[-2]]; Pi = J | B[z]
        if any(w not in seq and v[w][a] > p[w] for w in range(n)) and threatened(v, z, Pi, v[z][a]):
            continue
        for H0 in minimal_improving(v, k, Pi & rel(v, k), p[k]):
            Bp = state_after(B, seq, H0, Y)
            if any(len(H0 & rel(v, u)) >= 2 and val(v, u, H0 & rel(v, u)) > val(v, u, Bp[u])
                   for u in holders_of(v, Bp) if u != k):
                return True
    return False

def part1w(N, nlo, nhi, seed, steps=300):
    """random instances; from every hard D = {k} start with a CROWD (no-HEAD chain, crowding minimal H0), a value walk
    (same order, +-1..3 on one relevant value, every good kept relevant) that stays at hard D1 starts with CROWD;
    check_start at every distinct visited profile."""
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []; seen = set()
    for _ in range(N):
        n = rng.randint(nlo, nhi); v = rand_inst(rng, n)
        for o in itertools.permutations(range(n)):
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            B = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
            if len(set(range(len(v[0]))) - set().union(*B)) > 5 or oa_exists(v, B) or not crowd_case(v, Y):
                continue
            c["seeds"] += 1
            cur = [row[:] for row in v]
            for st in range(steps):
                key = (tuple(map(tuple, cur)), o)
                yd = sd(cur, o); Yc = [yd[i] for i in range(n)]
                Bc = [({Yc[i]} if Yc[i] is not None else set()) for i in range(n)]
                if key not in seen and not oa_exists(cur, Bc) and crowd_case(cur, Yc):
                    seen.add(key); c["walk_profiles"] += 1
                    check_start(cur, Yc, c, ex, hard=True)
                nxt = [row[:] for row in cur]
                i = rng.randrange(n); gs = [g for g in range(len(cur[0])) if cur[i][g] > 0]
                g = rng.choice(gs); nxt[i][g] = max(1, nxt[i][g] + rng.choice([-3, -2, -1, 1, 2, 3]))
                yd = sd(nxt, o); Yn = [yd[i] for i in range(n)]
                Bn = [({Yn[i]} if Yn[i] is not None else set()) for i in range(n)]
                if len(set(range(len(v[0]))) - set().union(*Bn)) <= 5 and not oa_exists(nxt, Bn) and crowd_case(nxt, Yn):
                    cur = nxt
            break
    print(json.dumps(dict(source=f"D1-C CROWD walks N={N} n={nlo}..{nhi} seed={seed}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    if sys.argv[1] == "p1":
        part1(*map(int, sys.argv[2:6]))
    elif sys.argv[1] == "p2c":
        part2c(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == "ties")
    elif sys.argv[1] == "p2w":
        part2w(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == "ties")
    elif sys.argv[1] == "p1w":
        part1w(*map(int, sys.argv[2:6]))
    elif sys.argv[1] == "tied":
        tied_all_orders()
    elif sys.argv[1] == "p2":
        part2(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == "ties")
    else:
        part3()
