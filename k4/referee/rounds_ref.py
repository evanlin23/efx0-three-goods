#!/usr/bin/env python3
"""Referee check of Lemma R1 and the starved-agent certificate (kgen/rounds.md §1, §3, branch proof/kgen-rounds at
a33b135). Own code; nothing from kgen/rounds/ is run or imported. Raw EFX0 (= EFX here: values are positive).

Rounds are enumerated forward from the definitions (k4/sdc.md §29, k4/ksens.md §6): vertex-disjoint chains x0..xt
(t >= 0) with pairwise disjoint junk sets; x_i (i >= 1) takes y_{x_{i-1}} ∪ H_i (H_i ⊆ J); x0 takes H0 ⊆ J ∪ {y_{xt}}
(t >= 1) or adds H0 ⊆ J to its pick (t = 0); strict gains; the rest of y_{xt} becomes junk. A base tuple completes if
some EFX allocation contains every base (free); one-absorber: also at most one agent holds >= 2 goods outside its base.

1. Lemma R1 on every (round, completion) pair of random positive instances.
2. The certificate's consequence on the same data: if every MD EFX allocation has a starved agent, no round completes.
3. RD5+ (eps = 1 and 99), C4G and the two-type instance of §3: all EFX allocations, the MD ones, starvation in each;
   one round fails by forward enumeration (independent of the certificate); the printed two-round repair of RD5+.
"""
import itertools, random, sys, json

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx(v, X):
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2:
                tot = val(v, i, X[j])
                if any(tot - v[i][h] > t for h in X[j]):
                    return False
    return True

def sd(v, order):
    m = len(v[0]); G = set(range(m)); y = {}
    for i in order:
        g = max(sorted(G), key=lambda g: (v[i][g], -g))
        y[i] = g; G.discard(g)
    return [y[i] for i in range(len(v))]

def all_efx(v):
    n = len(v); m = len(v[0]); out = []
    for f in itertools.product(range(n), repeat=m):
        X = [frozenset(g for g in range(m) if f[g] == i) for i in range(n)]
        if efx(v, X):
            out.append(X)
    return out

def subsets(S):
    S = sorted(S)
    for k in range(len(S) + 1):
        for c in itertools.combinations(S, k):
            yield frozenset(c)

def rounds(v, y):
    """every base tuple reachable by one round (including the empty round) from the picks y."""
    n = len(y); m = len(v[0]); J = frozenset(range(m)) - frozenset(y)
    py = [v[i][y[i]] for i in range(n)]
    out = set()
    def chains(free_agents, free_junk):
        """yield (agents used, junk used, {agent: base})"""
        for x0 in free_agents:
            # t = 0
            for H0 in subsets(free_junk):
                if H0:
                    yield {x0}, H0, {x0: frozenset({y[x0]}) | H0}
            # t >= 1
            def ext(seq, used_junk, bases):
                last = seq[-1]
                for w in free_agents:
                    if w in seq:
                        continue
                    for Hw in subsets(free_junk - used_junk):
                        nb = frozenset({y[last]}) | Hw
                        if val(v, w, nb) > py[w]:
                            b2 = dict(bases); b2[w] = nb
                            s2 = seq + [w]; uj = used_junk | Hw
                            for H0 in subsets((free_junk - uj) | {y[w]}):
                                if val(v, x0, H0) > py[x0]:
                                    b3 = dict(b2); b3[x0] = H0
                                    yield set(s2), uj | (H0 - {y[w]}), b3
                            yield from ext(s2, uj, b2)
            yield from ext([x0], frozenset(), {})
    def rec(free_agents, free_junk, bases):
        out.add(tuple(bases.get(i, frozenset({y[i]})) for i in range(n)))
        if not free_agents:
            return
        lo = min(free_agents)
        # either lo is on no chain, or lo is on some chain (as any member); to avoid blow-up, branch on chains containing lo
        rec(free_agents - {lo}, free_junk, bases)
        for ag, ju, b in chains(free_agents, free_junk):
            if lo in ag:
                nb = dict(bases); nb.update(b)
                rec(free_agents - ag, free_junk - ju, nb)
    rec(frozenset(range(n)), J, {})
    return out

def completions(EF, B):
    return [X for X in EF if all(B[i] <= X[i] for i in range(len(B)))]

def one_abs(X, B):
    return sum(1 for i in range(len(B)) if len(X[i] - B[i]) >= 2) <= 1

def starved(v, y, X, a):
    if y[a] in X[a]:
        return False
    J = set(range(len(v[0]))) - set(y)
    foreign = [g for g in X[a] if g in y and g != y[a]]
    junk = [g for g in X[a] if g in J]
    best = max([val(v, a, junk)] + [val(v, a, [f] + junk) for f in foreign])
    return best <= v[a][y[a]]

def analyse_start(v, y, EF, c, ex, tag):
    n = len(v)
    py = [v[i][y[i]] for i in range(n)]
    md = [X for X in EF if all(val(v, i, X[i]) >= py[i] for i in range(n))]
    cert = bool(md) and all(any(starved(v, y, X, a) for a in range(n)) for X in md)
    R = rounds(v, y)
    reach_free = reach_one = False
    for B in R:
        for X in completions(EF, B):
            reach_free = True
            c["r1_pairs"] += 1
            ok = all(val(v, i, X[i]) >= py[i] and (y[i] in X[i] or val(v, i, X[i]) > py[i]) for i in range(n))
            ok &= all(sum(1 for g in B[i] if g in y and g != y[i]) <= 1 for i in range(n))
            if not ok:
                c["r1_fail"] += 1; ex.append(("R1", tag, v, y))
            if one_abs(X, B):
                reach_one = True
    c["starts"] += 1
    c["cert_starts"] += cert
    if cert and reach_free:
        c["cert_fail"] += 1; ex.append(("cert", tag, v, y))
    return dict(md=len(md), cert=cert, rounds=len(R), one_round_free=reach_free, one_round_one_absorber=reach_one)

def run(N, nlo, nhi, seed):
    rng = random.Random(seed)
    c = dict(instances=0, starts=0, r1_pairs=0, r1_fail=0, cert_starts=0, cert_fail=0)
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(n + 1, 7 if n == 3 else 6)
        v = [[rng.randint(1, 30) for _ in range(m)] for _ in range(n)]
        c["instances"] += 1
        EF = all_efx(v)
        seen = set()
        for order in itertools.permutations(range(n)):
            y = sd(v, order)
            if tuple(y) in seen:
                continue
            seen.add(tuple(y))
            analyse_start(v, y, EF, c, ex, "random")
    print(json.dumps(dict(source=f"R1 + certificate, random positive N={N} n={nlo}..{nhi} seed={seed}", **c)))
    for e in ex[:5]:
        print("EXAMPLE", e)

def rounds_from(v, B):
    """every base tuple reachable by one round from arbitrary bases B (x_i takes the whole B_{x_{i-1}} plus junk)."""
    n = len(B); m = len(v[0]); J = frozenset(range(m)) - frozenset().union(*B)
    pv = [val(v, i, B[i]) for i in range(n)]
    out = set()
    def chains(free_agents, free_junk):
        for x0 in free_agents:
            for H0 in subsets(free_junk):
                if H0:
                    yield {x0}, H0, {x0: B[x0] | H0}
            def ext(seq, used_junk, bases):
                last = seq[-1]
                if not B[last]:
                    return
                for w in free_agents:
                    if w in seq:
                        continue
                    for Hw in subsets(free_junk - used_junk):
                        nb = B[last] | Hw
                        if val(v, w, nb) > pv[w]:
                            b2 = dict(bases); b2[w] = nb
                            s2 = seq + [w]; uj = used_junk | Hw
                            for H0 in subsets((free_junk - uj) | B[w]):
                                if val(v, x0, H0) > pv[x0]:
                                    b3 = dict(b2); b3[x0] = H0
                                    yield set(s2), uj | (H0 - B[w]), b3
                            yield from ext(s2, uj, b2)
            yield from ext([x0], frozenset(), {})
    def rec(free_agents, free_junk, bases):
        out.add(tuple(bases.get(i, B[i]) for i in range(n)))
        if not free_agents:
            return
        lo = min(free_agents)
        rec(free_agents - {lo}, free_junk, bases)
        for ag, ju, b in chains(free_agents, free_junk):
            if lo in ag:
                nb = dict(bases); nb.update(b)
                rec(free_agents - ag, free_junk - ju, nb)
    rec(frozenset(range(n)), J, {})
    return out

def two_rounds(v, y, EF):
    n = len(v); B0 = tuple(frozenset({y[i]}) for i in range(n))
    R1 = rounds_from(v, B0)
    good = 0
    for B1 in R1:
        if any(completions(EF, B2) for B2 in rounds_from(v, B1)):
            good += 1
    return len(R1), good

def named():
    E = 1
    def rd5plus(eps):
        return [[2600, 5700, eps, 4400, 2300, 3300, eps], [eps, 1200, 1100, 600, eps, eps, eps],
                [eps, 900, 800, 600, 100, eps, eps], [3600, eps, 5300, eps, eps, 4700, 400]]
    cases = [("RD5+ eps=1", rd5plus(1), (0, 3, 1, 2), [1, 2, 3, 4]),
             ("RD5+ eps=99", rd5plus(99), (0, 3, 1, 2), [1, 2, 3, 4]),
             ("C4G", [[304, 35, 1, 2864, 610, 2535, 950], [432, 643, 29, 1067, 71, 2469, 764],
                      [90, 582, 165, 1265, 981, 2483, 1970], [434, 642, 29, 1068, 69, 2467, 764]], (2, 1, 3, 0), [6, 3, 4, 5]),
             ("two-types", [[144, 1429, 2963, 2918, 1039, 1633, 2640]] * 2 + [[173, 23, 8993, 6979, 1816, 929, 2941]] * 2,
              (0, 1, 2, 3), None)]
    for name, v, order, printed in cases:
        y = sd(v, order)
        EF = all_efx(v)
        c = dict(instances=0, starts=0, r1_pairs=0, r1_fail=0, cert_starts=0, cert_fail=0)
        res = analyse_start(v, y, EF, c, [], name)
        n = len(v); py = [v[i][y[i]] for i in range(n)]
        md = [X for X in EF if all(val(v, i, X[i]) >= py[i] for i in range(n))]
        st = sorted({a for X in md for a in range(n) if starved(v, y, X, a)})
        others = {}
        seen = {tuple(y)}
        for o in itertools.permutations(range(n)):
            y2 = sd(v, o)
            if tuple(y2) in seen:
                continue
            seen.add(tuple(y2))
            py2 = [v[i][y2[i]] for i in range(n)]
            ext = any(all(frozenset({y2[i]}) <= X[i] for i in range(n)) for X in EF)
            one = ext or any(completions(EF, B) for B in rounds(v, y2))
            others[str(y2)] = "extend" if ext else ("one round" if one else "FAILS one round")
        out = dict(case=name, picks=y, efx_allocations=len(EF), md_allocations=len(md),
                   md_bundles=[[sorted(b) for b in X] for X in md], starved_agents=st, **res,
                   other_starts=others)
        y0 = tuple(frozenset({y[i]}) for i in range(n))
        out["one_round_states_general"] = len(rounds_from(v, y0))
        out["rounds_agree"] = rounds_from(v, y0) == rounds(v, y)
        r1n, r1good = two_rounds(v, y, EF)
        out["two_rounds"] = dict(first_round_states=r1n, first_rounds_with_a_completing_second_round=r1good)
        if name.startswith("RD5+"):
            # the printed two-round repair
            J = set(range(7)) - set(y)
            B1 = [frozenset({1, 6}), frozenset({3}), frozenset({4}), frozenset({0, 5})]  # 3 -> 1 with H0 = {0,5}; 0 adds 6
            ok1 = (val(v, 3, {0, 5}) > v[3][2] and v[1][2] > v[1][3] and val(v, 0, {1, 6}) > v[0][1])
            B1 = [frozenset({1, 6}), frozenset({2}), frozenset({4}), frozenset({0, 5})]
            # round 2: ring 0 -> 2: agent 2 takes 1 from 0's base {1, 6}; agent 0 takes 2's pick 4 plus released 3
            J1 = {3}
            B2 = [frozenset({3, 4}), frozenset({2}), frozenset({1}), frozenset({0, 5})]
            ok2 = val(v, 2, {1}) > val(v, 2, B1[2]) and val(v, 0, {3, 4}) > val(v, 0, B1[0])
            Xf = [frozenset({3, 4, 6}), frozenset({2}), frozenset({1}), frozenset({0, 5})]
            printed_B1 = (frozenset({1, 6}), frozenset({2}), frozenset({4}), frozenset({0, 5}))
            R2 = rounds_from(v, printed_B1)
            ring = (frozenset({3, 4}), frozenset({2}), frozenset({1, 6}), frozenset({0, 5}))   # x1 = 2 takes all of {1, 6}
            corr_B1 = (frozenset({1}), frozenset({2}), frozenset({4}), frozenset({0, 5}))     # without the t = 0 addition
            corr_B2 = (frozenset({3, 4}), frozenset({2}), frozenset({1}), frozenset({0, 5}))
            out["two_round_repair"] = dict(
                printed_round1_reachable=printed_B1 in rounds_from(v, y0),
                printed_round2_under_chain_rule=ring in R2, printed_round2_state_completes=bool(completions(EF, ring)),
                printed_final_contains_chain_rule_bases=all(ring[i] <= Xf[i] for i in range(4)),
                printed_final_efx=efx(v, Xf),
                corrected_round1_reachable=corr_B1 in rounds_from(v, y0),
                corrected_round2_reachable=corr_B2 in rounds_from(v, corr_B1),
                corrected_completes_with_printed_final=all(corr_B2[i] <= Xf[i] for i in range(4)) and efx(v, Xf))
        print(json.dumps(out))

if __name__ == "__main__":
    if sys.argv[1] == "named":
        named()
    else:
        run(*map(int, sys.argv[1:5]))
