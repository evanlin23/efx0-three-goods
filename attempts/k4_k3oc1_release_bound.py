"""Independent replay (no repository code, raw EFX0 definition, values 10 > 8 > 7) of the counterexample to the release
bound (R) of k4/k3_oc1.md §12.1, in attempts/k4-k3oc1-release-bound.md.

Instance: an n = 7, m = 12 ledger core (results/certs_7_12.json.gz), agents a > b > c:
  0: 0 > 5 > 7   1: 3 > 2 > 8   2: 2 > 6 > 9   3: 3 > 10 > 6   4: 4 > 11 > 5   5: 0 > 1 > 5   6: 6 > 4 > 1
Order (0, 3, 1, 2, 4, 6, 5).  Checks: (1) the picks have no one-absorber completion; (2) omega = |J| - |T| = 4;
(3) the two rotations into the terminal 5 (its exposed agents 0 and 4 along their earliest-wanter chains) each leave
omega' = 2 after LB's upgrades, so neither gives the no-owner completion (R) predicts; (4) each still has a
one-absorber completion.
    python3 attempts/k4_k3oc1_release_bound.py"""
import itertools
SETS = [[0, 5, 7], [3, 2, 8], [2, 6, 9], [3, 10, 6], [4, 11, 5], [0, 1, 5], [6, 4, 1]]
ORDER = (0, 3, 1, 2, 4, 6, 5)
n, m = 7, 12
v = [{s[0]: 10, s[1]: 8, s[2]: 7} for s in SETS]
val = lambda i, S: sum(v[i].get(g, 0) for g in S)
rank = lambda i, g: SETS[i].index(g)

def efx0(X):
    return all(val(i, set(X[j]) - {h}) <= val(i, X[i]) for i in range(n) for j in range(n) if i != j for h in X[j])

def completion(X0):
    J = [g for g in range(m) if not any(g in b for b in X0)]
    for asg in itertools.product(range(n), repeat=len(J)):
        if sum(1 for a in range(n) if asg.count(a) >= 2) > 1: continue
        X = [list(X0[a]) + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]
        if efx0(X): return X
    return None

def wanted(X, g, holder):
    """some agent other than the holder, not holding its pair, ranks g above its holding"""
    return any(x != holder and len(X[x]) == 1 and g in SETS[x] and rank(x, g) < rank(x, X[x][0]) for x in range(n))

def omega(X):
    """|J| - |T| after LB's upgrades (a b-holder whose b nobody wants takes its junk c)"""
    X = [list(b) for b in X]
    while True:
        J = [g for g in range(m) if not any(g in b for b in X)]
        up = [x for x in range(n) if len(X[x]) == 1 and X[x][0] == SETS[x][1] and SETS[x][2] in J and not wanted(X, X[x][0], x)]
        if not up: break
        X[up[0]].append(SETS[up[0]][2])
    J = [g for g in range(m) if not any(g in b for b in X)]
    T = [x for x in range(n) if len(X[x]) == 1 and not wanted(X, X[x][0], x)]
    return len(J) - len(T), X

taken = set(); Y = [None] * n
for i in ORDER:
    Y[i] = max((g for g in SETS[i] if g not in taken), key=lambda g: v[i][g]); taken.add(Y[i])
picks = [[g] for g in Y]
om, _ = omega(picks)
print('picks', Y, 'junk', [g for g in range(m) if g not in taken], 'omega', om)
print('(1) one-absorber completion of the picks:', completion(picks))
for chain in ([0, 5], [4, 6, 5]):
    X = [list(b) for b in picks]; k = chain[0]
    for i in range(len(chain) - 1, 0, -1): X[chain[i]] = [Y[chain[i - 1]]]
    X[k] = [SETS[k][1], SETS[k][2]]
    for a in range(n):
        if a != k: X[a] = [g for g in X[a] if g not in X[k]]
    assert all(val(a, X[a]) > val(a, picks[a]) for a in chain)
    om2, Xu = omega(X)
    print('(3) rotation %s: bases %s, omega\' after upgrades %d' % (chain, Xu, om2))
    print('(4)     one-absorber completion:', completion(Xu))
