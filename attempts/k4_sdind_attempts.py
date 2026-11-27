"""Independent replay of the failures recorded in attempts/k4-sdind-*.md (workstream proof/k4-sd-induct).

Pure Python, itertools only; no code shared with k4/sdind or k4/sdc.  Raw EFX0: v_i(X_i) >= v_i(X_j minus g) for all
i != j and g in X_j.  Serial dictatorship: each agent in turn takes its most valuable remaining relevant good, ties
by the smaller good index.

    python3 attempts/k4_sdind_attempts.py both1 every bothfree ab1"""
import sys, itertools


def sd(sets, vals, order, m):
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    left = set(range(m)); Y = [None] * len(sets)
    for i in order:
        av = [g for g in sets[i] if g in left and v[i][g] > 0]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); Y[i] = g; left.discard(g)
    return Y


def efx0(v, B):
    n = len(B)
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in B[i])
        for j in range(n):
            if i == j or not B[j]: continue
            vs = [v[i].get(g, 0) for g in B[j]]
            if sum(vs) - min(vs) > own: return False
    return True


def completions(sets, vals, Y, m, agents=None, maxabs=1):
    """EFX0 completions of the picks Y (restricted to `agents`; the others are deleted with their picks); junk =
    goods picked by nobody; at most maxabs agents with >= 2 junk goods (None: no limit)"""
    n = len(sets); agents = list(range(n)) if agents is None else list(agents)
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    J = [g for g in range(m) if g not in Y]
    out = []
    for a in itertools.product(agents, repeat=len(J)):
        cnt = {i: sum(1 for k in a if k == i) for i in agents}
        if maxabs is not None and sum(1 for i in agents if cnt[i] >= 2) > maxabs: continue
        B = {i: ([Y[i]] if Y[i] is not None else []) for i in agents}
        for g, k in zip(J, a): B[k].append(g)
        vv = [v[i] for i in agents]; BB = [B[i] for i in agents]
        if efx0(vv, BB): out.append(dict(zip(J, a)))
    return out


def both1():
    print('== both1: Lemma BOTH for one-absorber completions fails (r1179, n = 4, m = 9)')
    sets = [[0, 3, 6, 7], [1, 4, 6, 7], [2, 5, 8], [3, 4, 5, 8]]
    vals = [[8, 1, 6, 4], [4, 8, 3, 2], [4, 2, 3], [5, 8, 6, 4]]
    m = 9
    for order in itertools.permutations(range(4)):
        Y = sd(sets, vals, list(order), m)
        if Y == [0, 1, 2, 4]: break
    print('picks', Y, 'from order', order)
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    u = 0
    top = max(sets[u], key=lambda h: (v[u][h], -h))
    wanters = [i for i in range(4) if i != u and v[i].get(Y[u], 0) > v[i].get(Y[i], 0)]
    print('agent 0 holds its top:', Y[u] == top, '; agents wanting its pick:', wanters)
    sub = completions(sets, vals, Y, m, agents=[1, 2, 3], maxabs=1)
    full1 = completions(sets, vals, Y, m, maxabs=1)
    full = completions(sets, vals, Y, m, maxabs=None)
    print('one-absorber completions of the picks without agent 0 (agents 1, 2, 3):', len(sub), sub[:3])
    print('one-absorber completions of the picks of I:', len(full1))
    print('free completions of the picks of I:', len(full), full[:2])
    assert Y == [0, 1, 2, 4] and Y[u] == top and not wanters and len(sub) == 8 and len(full1) == 0 and len(full) == 36
    print('confirmed')


def every():
    print('== every: deleting the last / first agent, a completion of the sub-instance may be far from every completion of I')
    # Q2 (k4/sdc nof_var.SPECIAL), picks of order (0, 2, 3, 1) ... use the start printed by e1_delete.py
    sets = [[0, 1, 3, 4], [2, 3, 6, 7], [2, 5, 7], [4, 5, 6, 7]]
    vals = [[2, 3, 10, 6], [2, 8, 3, 4], [2, 4, 3], [4, 8, 2, 3]]
    m = 8
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    for order in itertools.permutations(range(4)):
        Y = sd(sets, vals, list(order), m)
        if Y == [3, 6, 7, 5]: break
    print('picks', Y, 'from order', order)
    u = 1   # nobody wants agent 1's pick (it can be last)
    wanters = [i for i in range(4) if i != u and v[i].get(Y[u], 0) > v[i].get(Y[i], 0)]
    print('agents wanting the pick of agent 1:', wanters)
    full = completions(sets, vals, Y, m, maxabs=1)
    sub = completions(sets, vals, Y, m, agents=[0, 2, 3], maxabs=1)
    J = sorted(full[0].keys()) if full else []
    worst = 0
    for x in sub:
        d = min(sum(1 for g in J if x[g] != X[g]) for X in full)
        worst = max(worst, d)
    print('one-absorber completions of I:', len(full), '; of I - 1 - Y_1:', len(sub), '; worst distance', worst)
    assert not wanters and worst == 4
    print('confirmed')


def bothfree():
    print('== bothfree: Lemma BOTH for free completions fails (log174, n = 3, m = 7)')
    sets = [[0, 3, 2, 5], [0, 2, 1, 6], [2, 3, 4, 0]]
    vals = [[10, 24, 19, 31], [35, 43, 33, 40], [65, 27, 15, 24]]
    m = 7
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    for order in itertools.permutations(range(3)):
        Y = sd(sets, vals, list(order), m)
        if Y == [5, 2, 3]: break
    print('picks', Y, 'from order', order)
    u = 0
    top = max(sets[u], key=lambda h: (v[u][h], -h))
    others = [i for i in range(3) if i != u and v[i].get(Y[u], 0) > 0]
    print('agent 0 holds its top:', Y[u] == top, '; other agents valuing it at all:', others)
    sub = completions(sets, vals, Y, m, agents=[1, 2], maxabs=None)
    full = completions(sets, vals, Y, m, maxabs=None)
    print('free completions of the picks without agent 0:', len(sub), sub)
    print('free completions of the picks of I:', len(full))
    assert Y == [5, 2, 3] and Y[u] == top and not others and len(sub) > 0 and len(full) == 0
    print('confirmed')


def ab1():
    print('== ab1: Conjecture AB1 fails when no absorber is needed (climb instance, n = 4, m = 7)')
    sets = [[0, 2, 3, 6], [1, 4, 5, 6], [3, 4, 5, 6], [4, 5, 6]]
    vals = [[6, 4, 8, 5], [8, 3, 4, 6], [10, 6, 7, 2], [2, 4, 3]]
    m = 7; n = 4
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    target = [3, 1, 4, 5]
    orders = [o for o in itertools.permutations(range(n)) if sd(sets, vals, list(o), m) == target]
    Y = target
    full = completions(sets, vals, Y, m, maxabs=1)
    J = sorted(full[0].keys())
    absorbers = set(tuple(i for i in range(n) if sum(1 for g in J if X[g] == i) >= 2) for X in full)
    wanted = [[i for i in range(n) if i != j and v[i].get(Y[j], 0) > v[i].get(Y[i], 0)] for j in range(n)]
    print('picks', Y, 'orders producing them', orders)
    print('one-absorber completions', full, '; agents holding >= 2 junk goods in them:', absorbers)
    o = 2
    print('agent 2 wanted by:', wanted[2])
    def path_ok(pi):
        seq = list(pi)[::-1]
        levels = [completions(sets, vals, Y, m, agents=seq[:k], maxabs=1) for k in range(1, n + 1)]
        R = levels[0]
        for L in levels[1:]:
            R = [X for X in L if any(sum(1 for g in J if X[g] != P[g]) <= 1 for P in R)]
            if not R: return False
        return True
    res = {pi: path_ok(pi) for pi in orders}
    print('orders with agent 2 last:', {pi: r for pi, r in res.items() if pi[-1] == o})
    print('orders with another last agent that work:', [pi for pi, r in res.items() if pi[-1] != o and r])
    assert absorbers == {()} and not wanted[2] and not any(r for pi, r in res.items() if pi[-1] == o)
    assert any(r for pi, r in res.items() if pi[-1] != o)
    print('confirmed: no order with agent 2 last works; some order with another last agent does')


if __name__ == '__main__':
    for a in sys.argv[1:]:
        {'both1': both1, 'every': every, 'bothfree': bothfree, 'ab1': ab1}[a]()
