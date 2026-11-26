"""Replay for attempts/k4-vm-deterministic.md (definitions only; shares no code with k4/vm/): the n = 2, m = 5 trap
of VM-LL (gen:5525).  After V-M both agents hold their tops ({4}, {2}).  Agent 0's upgrade {4} -> {0, 1} keeps EFX0,
and afterwards each of the pool goods 3, 4 has a safe place on its own (so the one-good lookahead accepts the move),
but no placement of both exists (and no further upgrade exists); an EFX0 allocation exists.
    python3 attempts/k4_vm_deterministic.py"""
import itertools
v = [{3: 15, 0: 8, 4: 19, 1: 18}, {2: 14, 1: 13, 0: 8}]
n, m = 2, 5
val = lambda i, B: sum(v[i].get(g, 0) for g in B)
efx0 = lambda X: all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
                     for i in range(n) for j in range(n))
assert max(v[0], key=v[0].get) == 4 and max(v[1], key=v[1].get) == 2        # distinct tops: V-M gives ({4}, {2})
X = [[0, 1], [2]]                                                            # agent 0's upgrade: 8 + 18 = 26 > 19
assert efx0(X) and val(0, [0, 1]) > v[0][4]
safe = lambda X, s, g: efx0([b + [g] if k == s else b for k, b in enumerate(X)])
assert [s for s in range(n) if safe(X, s, 3)] == [1] and [s for s in range(n) if safe(X, s, 4)] == [1]
for X2 in ([[0, 1], [2, 3]], [[0, 1], [2, 4]]):
    rest = 4 if 3 in X2[1] else 3
    assert efx0(X2) and not any(safe(X2, s, rest) for s in range(n))
sols = [Y for own in itertools.product(range(n), repeat=m) for Y in [[[g for g in range(m) if own[g] == i] for i in range(n)]] if efx0(Y)]
print('EFX0 allocations:', sols)
assert sols
print('OK: the one-good lookahead accepts an upgrade after which the pool cannot be placed')
