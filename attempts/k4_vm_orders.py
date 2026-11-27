"""Replay for attempts/k4-vm-orders.md (definitions only; shares no code with k4/vm/): induct-g-r2 (n = 3, m = 5).
Lists every SD outcome with its rank vector; checks that the leximin-rank ("fair") outcomes and V-M's rank-greedy
outcomes extend to no EFX0 allocation, while the outcomes where agent 0 picks last extend.
    python3 attempts/k4_vm_orders.py"""
import itertools
sets = [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]]
vals = [[5, 3, 7, 6], [2, 3, 4], [2, 3, 4]]
n, m = 3, 5
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
val = lambda i, B: sum(v[i].get(g, 0) for g in B)
efx0 = lambda X: all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
                     for i in range(n) for j in range(n))
sols = [X for own in itertools.product(range(n), repeat=m) for X in [[[g for g in range(m) if own[g] == i] for i in range(n)]] if efx0(X)]
rank = [sorted(S, key=lambda g: -v[i][g]) for i, S in enumerate(sets)]


def sd(order):
    left = set(range(m)); Y = [None] * n
    for i in order:
        av = [g for g in rank[i] if g in left]
        if av:
            Y[i] = av[0]; left.discard(av[0])
    return tuple(Y)


outs = {}
for o in itertools.permutations(range(n)):
    outs.setdefault(sd(o), []).append(o)
fair = lambda Y: tuple([rank[i].index(Y[i]) + 1 if Y[i] is not None else 5 for i in range(n)].count(k) for k in (5, 4, 3, 2))
best = min(fair(Y) for Y in outs)
for Y, os_ in sorted(outs.items()):
    ext = any(all(Y[i] in X[i] for i in range(n)) for X in sols)
    print(Y, 'ranks', [rank[i].index(Y[i]) + 1 for i in range(n)], 'fair-best' if fair(Y) == best else '', 'extends' if ext else '-', 'orders', os_)
    assert ext == (os_[0][-1] == 0)            # extends exactly when agent 0 picks last
    if fair(Y) == best:
        assert not ext
# V-M's rank-greedy matchings: nobody is strong; step 1 gives 3 to agent 0 and 4 to agent 1 or 2; the other takes 2
for Y in [(3, 4, 2), (3, 2, 4)]:
    assert Y in outs and not any(all(Y[i] in X[i] for i in range(n)) for X in sols)
print('OK')
