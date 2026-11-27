"""Replay for attempts/k4-vm-completion.md, from the definitions only (shares no code with k4/vm/).

Instance core4:1615 (a random strict profile of a certified connected k = 4 core, n = 4, m = 8).  Checks:
  1. the EFX0 allocations (brute force over all 4^8 allocations); the V-M matching ({7},{3},{5},{4}) extends;
  2. V-M's Phases I-III by hand (asserted): agent 3 is the only strong agent and takes 4; agents 0 and 1 both claim 7;
     the loser takes its 2nd choice; agent 2 takes its 3rd (5); Phase III gives agent 2 its 4th (6) first (safe),
     then the loser its 4th choice (its 3rd is gone);
  3. from both Phase-III states, every sequence of EFX0-safe single-good placements (any order, any safe recipient)
     gets stuck, and no reachable state has an envy cycle, so rotations never apply.
    python3 attempts/k4_vm_completion.py"""
import itertools

sets = [[0, 2, 5, 7], [1, 3, 6, 7], [4, 5, 6, 7], [4, 5, 6, 7]]
vals = [[6, 4, 5, 8], [4, 6, 5, 8], [10, 4, 3, 8], [8, 2, 4, 3]]
n, m = 4, 8
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]


def val(i, B):
    return sum(v[i].get(g, 0) for g in B)


def efx0(X):
    return all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
               for i in range(n) for j in range(n))


sols = [X for own in itertools.product(range(n), repeat=m)
        for X in [[[g for g in range(m) if own[g] == i] for i in range(n)]] if efx0(X)]
Y = [[7], [3], [5], [4]]
ext = [X for X in sols if all(set(Y[i]) <= set(X[i]) for i in range(n))]
print(len(sols), 'EFX0 allocations; extensions of', Y, ':', ext)
assert ext

rank = [sorted(S, key=lambda g: -v[i][g]) for i, S in enumerate(sets)]
assert [i for i in range(n) if v[i][rank[i][0]] > v[i][rank[i][1]] + v[i][rank[i][2]]] == [3]
assert rank[3][0] == 4 and rank[0][0] == rank[1][0] == 7 and rank[2][0] == 4 and rank[2][1] == 7
assert rank[0][1] == 0 and rank[1][1] == 3 and rank[2][2] == 5          # step 2: the loser's 2nd; step 3: agent 2's 3rd
assert rank[2][3] == 6 and rank[1][2] == 6 and rank[0][2] == 5          # Phase III: 6 is agent 2's 4th and agent 1's 3rd
starts = [[[7], [3, 1], [5, 6], [4]], [[0, 2], [7], [5, 6], [4]]]   # agent 1 / agent 0 wins good 7
for X in starts:
    assert efx0(X)


def envy_cycle(X):
    E = {i: [j for j in range(n) if j != i and val(i, X[j]) > val(i, X[i])] for i in range(n)}
    for c in itertools.permutations(range(n)):
        for k in range(2, n + 1):
            if all(c[(t + 1) % k] in E[c[t]] for t in range(k)):
                return True
    return False


def search(X, pool):
    assert not envy_cycle(X), X
    if not pool:
        return True
    for g in pool:
        for s in range(n):
            Z = [list(b) for b in X]; Z[s].append(g)
            if efx0(Z) and search(Z, [h for h in pool if h != g]):
                return True
    return False


for X in starts:
    pool = [g for g in range(m) if not any(g in b for b in X)]
    ok = search(X, pool)
    print('from', X, 'pool', pool, ': some safe placement sequence completes?', ok)
    assert not ok
print('OK: V-M with F1-F3 (and rotation) cannot complete, although the matching extends')
