"""Replay for attempts/k4-vm-skeleton.md, from the definitions only (shares no code with k4/vm/).

Instance c4-exposure-nonleader-n3m5 (screen set; a connected k = 4 core).  Checks:
  1. the four EFX0 allocations (brute force over all 3^5 allocations, raw EFX0 definition);
  2. Viswanathan-Mehta's Phase I-II matchings: A is empty; step 1 gives good 3 to agent 0 (its first choice, nobody
     else's) and good 4 to agent 1 or agent 2; the other one has its 2nd choice 3 taken and gets its 3rd choice 2;
  3. no EFX0 allocation contains either matching (in fact none gives good 3 to agent 0).
    python3 attempts/k4_vm_skeleton.py"""
import itertools

sets = [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]]
vals = [[3, 6, 8, 4], [2, 3, 4], [2, 3, 4]]
n, m = 3, 5
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]


def val(i, B):
    return sum(v[i].get(g, 0) for g in B)


def efx0(X):
    for i in range(n):
        for j in range(n):
            if i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]):
                return False
    return True


sols = []
for own in itertools.product(range(n), repeat=m):
    X = [[g for g in range(m) if own[g] == i] for i in range(n)]
    if efx0(X):
        sols.append(X)
print('EFX0 allocations:', sols)
assert len(sols) == 4 and all(3 not in X[0] for X in sols)

# Viswanathan-Mehta, Phases I-II (rankings by value; all values distinct within an agent)
rank = [sorted(S, key=lambda g: -v[i][g]) for i, S in enumerate(sets)]
A = [i for i in range(n) if v[i][rank[i][0]] > v[i][rank[i][1]] + v[i][rank[i][2]]]
assert A == []
assert [r[0] for r in rank] == [3, 4, 4]          # step 1: good 3 has the single claimant 0; good 4 has 1 and 2
assert rank[1][1] == rank[2][1] == 3 and rank[1][2] == rank[2][2] == 2
matchings = [[[3], [4], [2]], [[3], [2], [4]]]
for Y in matchings:
    ext = [X for X in sols if all(set(Y[i]) <= set(X[i]) for i in range(n))]
    print('matching', Y, 'extensions:', ext)
    assert not ext
print('OK: no Phase I-II matching of V-M extends to an EFX0 allocation')
