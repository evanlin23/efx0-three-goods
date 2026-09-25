"""Independent construction of the cores H_t of k4/c4.md section 7, and checks of Task 1.

Written from the prose of c4.md section 7 and the definitions of k4/SCOUT.md (K4.CORE) and
lean/EFX/K4Reduction.lean (IsCore4), lean/EFX/K4Ties.lean (Strict). No code of the author is used.
"""
import itertools
import sys


def build_H(t):
    """Return (agent_names, good_names, v) with v[i][g] a nonnegative int.

    Agents in index order: l, then per gadget j: x_{j,1}, x_{j,2}, x_{j,3}, y_j.
    Goods: g_1..g_t, z, u, u', then a_{j,i}, b_{j,i}, c_{j,i}. (Good order only matters for ties, and every
    agent's relevant values are distinct, so it does not matter.)
    """
    goods = [f"g{j}" for j in range(1, t + 1)] + ["z", "u", "u'"]
    for j in range(1, t + 1):
        for i in range(1, 4):
            goods += [f"a{j}{i}", f"b{j}{i}", f"c{j}{i}"]
    gi = {g: k for k, g in enumerate(goods)}
    agents = ["l"]
    vals = [{"g1": 8, "z": 6, "u": 5, "u'": 4}]
    for j in range(1, t + 1):
        for i in range(1, 4):
            agents.append(f"x{j}{i}")
            vals.append({f"a{j}{i}": 8, f"b{j}{i}": 6, f"c{j}{i}": 4, f"g{j}": 3})
        e = f"g{j + 1}" if j < t else "z"
        agents.append(f"y{j}")
        vals.append({f"a{j}1": 8, f"a{j}2": 6, f"a{j}3": 4, e: 3})
    v = [[0] * len(goods) for _ in agents]
    for a, d in enumerate(vals):
        for g, x in d.items():
            v[a][gi[g]] = x
    assert len(agents) == 4 * t + 1 and len(goods) == 10 * t + 3
    return agents, goods, v


def is_core4(v, verbose=False):
    """IsCore4 of K4Reduction.lean plus connectivity and strictness. Returns list of failures."""
    n, m = len(v), len(v[0])
    R = [[g for g in range(m) if v[i][g] > 0] for i in range(n)]
    fails = []
    if n < 2:
        fails.append("n<2")
    for i in range(n):
        d = len(R[i])
        if d not in (3, 4):
            fails.append(f"agent {i}: {d} goods")
        tot = sum(v[i])
        for g in range(m):
            if not 2 * v[i][g] < tot:
                fails.append(f"agent {i}: not strictly balanced at good {g}")
        priv = [g for g in R[i] if all(v[j][g] == 0 for j in range(n) if j != i)]
        shared = [g for g in R[i] if g not in priv]
        if len(priv) + 2 > d:
            fails.append(f"agent {i}: {len(priv)} private goods of {d}")
        if len(priv) == 2 and not sum(v[i][g] for g in priv) < sum(v[i][g] for g in shared):
            fails.append(f"agent {i}: p+q >= s+t")
        # strict (Lean Strict): disjoint S, T with equal value => value 0. Over R_i: disjoint nonempty subsets
        # have different values.
        for mask_s in range(1, 1 << d):
            for mask_t in range(1, 1 << d):
                if mask_s & mask_t:
                    continue
                vs = sum(v[i][R[i][k]] for k in range(d) if mask_s >> k & 1)
                vt = sum(v[i][R[i][k]] for k in range(d) if mask_t >> k & 1)
                if vs == vt:
                    fails.append(f"agent {i}: tie {mask_s} {mask_t}")
    for g in range(m):
        if all(v[i][g] == 0 for i in range(n)):
            fails.append(f"good {g} irrelevant")
    # connectivity of agents through goods (union-find)
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in range(m):
        hold = [i for i in range(n) if v[i][g] > 0]
        for a in hold[1:]:
            par[f(a)] = f(hold[0])
    if len({f(i) for i in range(n)}) != 1:
        fails.append("not connected")
    return fails


def efx0_raw(v, X, n):
    """Raw EFX0: for i != j and every g in X_j, v_i(X_i) >= v_i(X_j minus g). X[g] = owner agent."""
    m = len(X)
    bund = [[g for g in range(m) if X[g] == i] for i in range(n)]
    bad = []
    for i in range(n):
        vi = sum(v[i][g] for g in bund[i])
        for j in range(n):
            if i == j:
                continue
            for g in bund[j]:
                if vi < sum(v[i][h] for h in bund[j] if h != g):
                    bad.append((i, j, g))
    return bad, bund


def explicit_alloc(t, agents, goods):
    """c4.md section 7: y_j gets {a_j1}; x_j1 gets {b_j1, c_j1}; x_j2, x_j3 get their {a, b}; l gets the rest."""
    ai = {a: k for k, a in enumerate(agents)}
    X = [0] * len(goods)  # l by default
    for gk, g in enumerate(goods):
        if g[0] in "abc" and len(g) == 3:
            j, i = g[1], g[2]
            if g[0] == "a":
                X[gk] = ai[f"y{j}"] if i == "1" else ai[f"x{j}{i}"]
            elif g[0] == "b":
                X[gk] = ai[f"x{j}{i}"]
            else:  # c
                X[gk] = ai[f"x{j}{i}"] if i == "1" else ai["l"]
    return X


if __name__ == "__main__":
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    ok_all = True
    for t in range(1, T + 1):
        agents, goods, v = build_H(t)
        n, m = len(agents), len(goods)
        fails = is_core4(v)
        X = explicit_alloc(t, agents, goods)
        bad, bund = efx0_raw(v, X, n)
        big = [i for i in range(n) if len(bund[i]) > 2]
        # 4-good agents, private goods summary
        R = [[g for g in range(m) if v[i][g] > 0] for i in range(n)]
        n4 = sum(1 for i in range(n) if len(R[i]) == 4)
        print(f"t={t}: n={n} m={m} (4t+1={4*t+1}, 10t+3={10*t+3}) 4-good agents={n4} m<=3n:{m <= 3*n} "
              f"core-failures={fails} | explicit allocation: EFX0 violations={len(bad)} "
              f"bundles>2 goods: {[agents[i] for i in big]} sizes={[len(bund[i]) for i in big]} "
              f"all goods allocated={sum(len(b) for b in bund) == m}")
        ok_all &= (not fails) and (not bad) and len(big) <= 1
    print("ALL OK" if ok_all else "FAILURES")
