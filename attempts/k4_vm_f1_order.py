"""Replay for attempts/k4-vm-f1-order.md, from the definitions only (shares no code with k4/vm/).
Two agents, distinct tops; goods a0 = 0, a1 = 1, g = 2, p = 3, q = 4.  Checks: holding the tops, placing p with agent 0
and q with agent 1 is EFX0-safe, after which g has no safe place (and no envy cycle exists); an EFX0 allocation exists.
    python3 attempts/k4_vm_f1_order.py"""
v = [{0: 10, 1: 9, 2: 8, 3: 1}, {1: 10, 0: 9, 2: 8, 4: 1}]
n = 2


def val(i, B):
    return sum(v[i].get(g, 0) for g in B)


def efx0(X):
    return all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
               for i in range(n) for j in range(n))


X = [[0], [1]]
assert efx0(X)
X = [[0, 3], [1]]; assert efx0(X)            # p to agent 0
X = [[0, 3], [1, 4]]; assert efx0(X)         # q to agent 1
assert not any(val(i, X[1 - i]) > val(i, X[i]) for i in range(n))        # nobody envies: no cycle to rotate
stuck = [s for s in range(n) if efx0([b + [2] if k == s else b for k, b in enumerate(X)])]
print('safe places for g from', X, ':', stuck)
assert stuck == []
assert efx0([[0, 2], [1, 3, 4]])
print('OK: F1 can get stuck with distinct tops; ({a0, g}, {a1, p, q}) is EFX0')
