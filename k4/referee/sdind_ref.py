#!/usr/bin/env python3
"""Referee check of Lemmas D, F, S, U, BOTH-TP and Corollary TP (k4/sd_induct.md §1, §3, §5, branch
claude/k4-sd-induct). Written from the text; shares no code with k4/sdind/ or k4/sdc/.

Random additive instances with <= 4 relevant goods per agent (strict values), random orders.
  D: deleting any agent u with its pick, SD(pi - u) gives the same picks and the same junk.
  S: for every one-absorber completion (every agent but o holds its pick plus <= 1 junk good), raw EFX0 <=> (S1)&(S2).
  TP: when every pick-frozen agent is alone (and o is not pick-frozen), raw EFX0 <=> (S1).
  F: for an agent f whose pick is its top among the goods present, and every one-absorber completion X of the others
     that is EFX0: X + (f -> {Y_f}) is EFX0 <=> f is not threatened by X_o.
  U: in the same setting with f threatened, f takes its best junk good g of X_o; check items 1-3, separately for f
     unfrozen and f frozen (the statement has no 'unfrozen' hypothesis).
  BOTH-TP: for a both agent u and every TP-shaped EFX0 one-absorber completion X' of I - u - Y_u, the construction
     (add u alone; if threatened, u takes its best junk good of X_o) is EFX0 and TP-shaped.
"""
import itertools, random, sys, json

def val(v, i, S):
    return sum(v[i][g] for g in S)

def thr(v, i, B, t):
    tot = val(v, i, B)
    return len(B) >= 1 and any(tot - v[i][h] > t for h in B)

def efx0(v, X, agents):
    for i in agents:
        t = val(v, i, X[i])
        for j in agents:
            if i != j and len(X[j]) >= 2 and thr(v, i, X[j], t):
                return False
    return True

def sd(v, order, goods):
    G = set(goods); Y = {}
    for i in order:
        R = sorted((g for g in G if v[i][g] > 0), key=lambda g: (-v[i][g], g))
        Y[i] = R[0] if R else None
        if R:
            G.discard(R[0])
    return Y, G

def completions(agents, Y, J, o):
    """all one-absorber completions with absorber o: each other agent gets <= 1 junk good."""
    J = sorted(J); others = [a for a in agents if a != o]
    for f in itertools.product([None] + others, repeat=len(J)):
        used = [a for a in f if a is not None]
        if len(used) != len(set(used)):
            continue
        X = {a: ({Y[a]} if Y[a] is not None else set()) for a in agents}
        for g, a in zip(J, f):
            X[o if a is None else a].add(g)
        yield X

def frozen(v, Y, agents):
    return {j for j in agents if Y[j] is not None and any(i != j and v[i][Y[j]] > (v[i][Y[i]] if Y[i] is not None else 0) for i in agents)}

def run(N, nlo, nhi, mlo, mhi, seed):
    rng = random.Random(seed)
    c = {k: 0 for k in ["instances", "D_tests", "D_fail", "S_tests", "S_fail", "TP_tests", "TP_fail", "F_tests", "F_fail",
                        "U_tests_unfrozen", "U1_fail", "U2_fail", "U3_fail_unfrozen", "U_tests_frozen",
                        "U3_fail_frozen", "BOTH_tests", "BOTH_fail"]}
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            vals = rng.sample(range(1, 40), min(4, m))
            for g, x in zip(rng.sample(range(m), rng.randint(2, min(4, m))), vals):
                v[i][g] = x
        c["instances"] += 1
        order = list(range(n)); rng.shuffle(order)
        agents = list(range(n))
        Y, J = sd(v, order, range(m))
        # Lemma D
        for u in agents:
            c["D_tests"] += 1
            goods = [g for g in range(m) if g != Y[u]]
            Y2, J2 = sd(v, [a for a in order if a != u], goods)
            if any(Y2[a] != Y[a] for a in agents if a != u) or J2 != J:
                c["D_fail"] += 1
        if len(J) > 5:
            continue
        Fz = frozen(v, Y, agents)
        # Lemma S and Corollary TP, every absorber
        for o in agents:
            for X in completions(agents, Y, J, o):
                c["S_tests"] += 1
                raw = efx0(v, X, agents)
                S1 = not any(thr(v, i, X[o], val(v, i, X[i])) for i in agents if i != o and len(X[o]) >= 2)
                S2 = all(v[i][Y[j]] <= val(v, i, X[i]) for j in agents if j != o and Y[j] is not None and len(X[j]) == 2
                         for i in agents if i != j)
                if raw != (S1 and S2):
                    c["S_fail"] += 1
                    if len(ex) < 6:
                        ex.append(("S", v, order, o, {k: sorted(s) for k, s in X.items()}))
                if all(len(X[j]) == 1 for j in Fz if j != o) and o not in Fz:
                    c["TP_tests"] += 1
                    if raw != S1:
                        c["TP_fail"] += 1
        # Lemmas F and U: f = an agent whose pick is its top among goods present (insertable first)
        for f in agents:
            if Y[f] is None:
                continue
            Rf = [g for g in range(m) if v[f][g] > 0]
            if any(v[f][g] > v[f][Y[f]] for g in Rf):
                continue
            rest = [a for a in agents if a != f]
            Yr = {a: Y[a] for a in rest}
            fz_f = any(v[i][Y[f]] > (v[i][Y[i]] if Y[i] is not None else 0) for i in rest)
            for o in rest:
                for X in completions(rest, Yr, J, o):
                    if not efx0(v, X, rest):
                        continue
                    c["F_tests"] += 1
                    X2 = dict(X); X2[f] = {Y[f]}
                    raw = efx0(v, X2, agents)
                    t = len(X[o]) >= 2 and thr(v, f, X[o], v[f][Y[f]])
                    if raw != (not t):
                        c["F_fail"] += 1
                        if len(ex) < 6:
                            ex.append(("F", v, order, f, o))
                    if not t:
                        continue
                    junk_in = [g for g in X[o] if g in J and v[f][g] > 0]
                    g = max(junk_in, key=lambda h: (v[f][h], -h))
                    X3 = {a: set(s) for a, s in X.items()}; X3[o] = X[o] - {g}; X3[f] = {Y[f], g}
                    tf = val(v, f, X3[f])
                    u1 = not any(len(X3[j]) >= 2 and thr(v, f, X3[j], tf) for j in rest)
                    u2 = all(not thr(v, i, X3[f], val(v, i, X3[i])) or v[i][Y[f]] > val(v, i, X3[i]) for i in rest)
                    newly = [i for i in rest if any(len(X3[j]) >= 2 and thr(v, i, X3[j], val(v, i, X3[i]))
                                                    for j in agents if j != i)]
                    u3 = all(i == o for i in newly)
                    if o in newly:
                        # o only by a two-good bundle {Y_j, g_j} with v_o(Y_j) > v_o(X_o - g)
                        u3 = u3 and all(not (len(X3[j]) >= 2 and thr(v, o, X3[j], val(v, o, X3[o]))) or
                                        (len(X3[j]) == 2 and v[o][Y[j]] > val(v, o, X3[o])) for j in agents if j != o)
                    key = "frozen" if fz_f else "unfrozen"
                    c["U_tests_" + key] += 1
                    if not u1:
                        c["U1_fail"] += 1
                    if not u2:
                        c["U2_fail"] += 1
                    if not u3:
                        c["U3_fail_" + key] += 1
                        if len(ex) < 6 and key == "unfrozen":
                            ex.append(("U3 unfrozen", v, order, f, o))
        # BOTH-TP
        for u in agents:
            if Y[u] is None or u in Fz:
                continue
            if any(v[u][g] > v[u][Y[u]] for g in range(m)):
                continue
            rest = [a for a in agents if a != u]
            Yr = {a: Y[a] for a in rest}
            Fr = frozen(v, Yr, rest)
            for o in rest:
                if o in Fr:
                    continue
                for X in completions(rest, Yr, J, o):
                    if any(len(X[j]) != 1 for j in Fr) or not efx0(v, X, rest):
                        continue
                    c["BOTH_tests"] += 1
                    X2 = {a: set(s) for a, s in X.items()}; X2[u] = {Y[u]}
                    if len(X[o]) >= 2 and thr(v, u, X[o], v[u][Y[u]]):
                        junk_in = [g for g in X[o] if g in J and v[u][g] > 0]
                        g = max(junk_in, key=lambda h: (v[u][h], -h))
                        X2[o] = X[o] - {g}; X2[u] = {Y[u], g}
                    ok = efx0(v, X2, agents) and all(len(X2[j]) == 1 for j in frozen(v, Y, agents))
                    if not ok:
                        c["BOTH_fail"] += 1
                        if len(ex) < 6:
                            ex.append(("BOTH", v, order, u, o))
    print(json.dumps(dict(source=f"sd_induct N={N} n={nlo}..{nhi} m={mlo}..{mhi} seed={seed}", **c)))
    for e in ex:
        print("EXAMPLE", e)

def u_counterexample():
    """Lemma U without 'f unfrozen': agents f = 0, i = 1, o = 2; goods a = 0, y_i = 1, y_o = 2, b = 3, c = 4."""
    v = [[10, 0, 0, 6, 5], [5, 3, 0, 0, 0], [0, 0, 4, 0, 0]]
    order = [0, 1, 2]
    Y, J = sd(v, order, range(5))
    X = {1: {1}, 2: {2, 3, 4}}
    ok_rest = efx0(v, X, [1, 2])
    t = thr(v, 0, X[2], v[0][0])
    X3 = {0: {0, 3}, 1: {1}, 2: {2, 4}}
    i_thr = thr(v, 1, X3[0], val(v, 1, X3[1]))
    print(json.dumps(dict(source="Lemma U item 3 without 'unfrozen'", picks=Y, junk=sorted(J), completion_of_others_EFX0=ok_rest,
                          f_threatened=t, after_move={k: sorted(s) for k, s in X3.items()},
                          old_agent_1_threatened_by_f=i_thr, agent_1_wants_a=v[1][0] > v[1][1])))

if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "run":
        run(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), int(a[6]))
    elif a[0] == "ucex":
        u_counterexample()

def prtp_run(N, nlo, nhi, mlo, mhi, seed):
    """Theorem PR-TP: reverse-order insertion keeping pick-frozen agents junk-free; after every step whose agent is
    unthreatened or pick-unfrozen, the partial allocation must be EFX0 and prefix-robust."""
    rng = random.Random(seed)
    c = dict(instances=0, runs=0, steps=0, steps_unfrozen_threatened=0, steps_frozen_unthreatened=0,
             step_fail=0, stopped_at_threatened_frozen=0)
    ex = []
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            vals = rng.sample(range(1, 40), min(4, m))
            for g, x in zip(rng.sample(range(m), rng.randint(2, min(4, m))), vals):
                v[i][g] = x
        c["instances"] += 1
        for _r in range(4):
            order = list(range(n)); rng.shuffle(order)
            Y, J = sd(v, order, range(m))
            Fz = frozen(v, Y, list(range(n)))
            o = order[-1]
            if o in Fz:
                continue
            c["runs"] += 1
            X = {o: ({Y[o]} if Y[o] is not None else set()) | set(J)}
            junk_of = {}
            present = [o]
            for k in range(n - 2, -1, -1):
                f = order[k]
                present_new = [f] + present
                Xn = {a: set(s) for a, s in X.items()}; Xn[f] = {Y[f]} if Y[f] is not None else set()
                t = len(X[o]) >= 2 and thr(v, f, X[o], val(v, f, Xn[f]))
                frozen_now = f in frozen(v, Y, present_new)
                if t:
                    if frozen_now:
                        c["stopped_at_threatened_frozen"] += 1
                        break
                    jin = [g for g in X[o] if g in J and v[f][g] > 0]
                    g = max(jin, key=lambda h: (v[f][h], -h))
                    Xn[o] = X[o] - {g}; Xn[f].add(g); junk_of[f] = g
                    c["steps_unfrozen_threatened"] += 1
                elif frozen_now:
                    c["steps_frozen_unthreatened"] += 1
                c["steps"] += 1
                # EFX0 and PR on the present agents, order restricted to them
                sub = order[k:]
                ok = efx0(v, Xn, present_new)
                for idx in range(len(sub) - 1):
                    a = sub[idx]
                    B = set(Xn[o]) | {junk_of[b] for b in sub[:idx] if b in junk_of}
                    if len(B) >= 2 and thr(v, a, B, val(v, a, Xn[a])):
                        ok = False
                if not ok:
                    c["step_fail"] += 1
                    if len(ex) < 5:
                        ex.append(("PR-TP", v, order, k))
                    break
                X = Xn; present = present_new
    print(json.dumps(dict(source=f"PR-TP N={N} n={nlo}..{nhi} m={mlo}..{mhi} seed={seed}", **c)))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__" and sys.argv[1] == "prtp":
    prtp_run(*map(int, sys.argv[2:8]))
