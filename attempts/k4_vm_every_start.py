"""Replay for attempts/k4-vm-every-start.md (definitions only; shares no code with k4/vm/): r4253, Y = SD(3,2,1,0).
Checks that no EFX0 allocation contains Y, that 8 value-dominate it, and that each of them gives 6 to agent 0 and 4
to agent 1 (so reaching one from Y moves goods around a three-agent cycle).
    python3 attempts/k4_vm_every_start.py"""
import itertools
sets = [[0, 2, 5, 6], [1, 4, 6], [2, 3, 4, 5], [3, 4, 5, 6]]
vals = [[2, 4, 10, 7], [2, 4, 3], [4, 5, 8, 2], [2, 6, 10, 7]]
n, m = 4, 7
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
val = lambda i, B: sum(v[i].get(g, 0) for g in B)
efx0 = lambda X: all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
                     for i in range(n) for j in range(n))
left = set(range(m)); Y = [None] * n
for i in (3, 2, 1, 0):
    g = max((g for g in sets[i] if g in left), key=lambda g: v[i][g]); Y[i] = g; left.discard(g)
assert Y == [2, 6, 4, 5]
sols = [X for own in itertools.product(range(n), repeat=m) for X in [[[g for g in range(m) if own[g] == i] for i in range(n)]] if efx0(X)]
ext = [X for X in sols if all(Y[i] in X[i] for i in range(n))]
dom = [X for X in sols if all(val(i, X[i]) >= v[i][Y[i]] for i in range(n))]
print(len(sols), 'EFX0 allocations;', len(ext), 'contain Y;', len(dom), 'value-dominate Y')
assert len(sols) == 23 and not ext and len(dom) == 8
assert all(6 in X[0] and 4 in X[1] for X in dom)
print('OK')
