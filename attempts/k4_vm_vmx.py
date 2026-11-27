"""Replay for attempts/k4-vm-vmx.md, from the definitions only (shares no code with k4/vm/).

Instance: a strict profile of a certified connected k = 4 core, n = 3, m = 6 (found by k4/vm/vmx_climb.py).
Checks:
  1. brute force: 10 EFX0 allocations, none gives good 5 to agent 0;
  2. V-M: agent 0 is the only strongly-top agent (8 > 4 + 3), so Phase I gives it good 5; Phase II gives agent 1 and
     agent 2 goods 3 and 2 (or 1 and 3); Phase III with the EFX0 filter F2 gives the N3 agent its 4th choice (good 4);
  3. from both post-Phase-III states, a breadth-first search over a SUPERSET of VMx's moves (any envy-cycle rotation,
     any EFX0-safe placement of a pool good, any upgrade of a single good y to S within the pool with v(S) > v(y),
     any two-agent exchange with pool goods where both gain), keeping only partial EFX0 states, reaches no complete
     allocation.
    python3 attempts/k4_vm_vmx.py"""
import itertools
from collections import deque

sets = [[0, 1, 2, 5], [1, 3, 4, 5], [2, 3, 4, 5]]
vals = [[4, 3, 2, 8], [4, 7, 2, 8], [4, 8, 3, 10]]
n, m = 3, 6
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
val = lambda i, B: sum(v[i].get(g, 0) for g in B)


def efx0(X):
    return all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
               for i in range(n) for j in range(n))


sols = [X for own in itertools.product(range(n), repeat=m) for X in [[[g for g in range(m) if own[g] == i] for i in range(n)]] if efx0(X)]
print(len(sols), 'EFX0 allocations; any with good 5 at agent 0:', any(5 in X[0] for X in sols))
assert len(sols) == 10 and not any(5 in X[0] for X in sols)

rank = [sorted(S, key=lambda g: -v[i][g]) for i, S in enumerate(sets)]
strong = [i for i in range(n) if v[i][rank[i][0]] > v[i][rank[i][1]] + v[i][rank[i][2]]]
assert strong == [0] and rank[0][0] == 5                          # Phase I: good 5 to agent 0
assert rank[1][:3] == [5, 3, 1] and rank[2][:3] == [5, 3, 2]       # step 1: both tops gone; step 2: both claim 3
# the winner of 3 is in N2; the loser takes its 3rd choice at step 3 (1 for agent 1, 2 for agent 2) and is in N3
starts = []
for w, l in ((1, 2), (2, 1)):
    X = [[5], [], []]; X[w] = [3]; X[l] = [rank[l][2]]
    # Phase III (a): the N3 agent l gets its 4th choice if unassigned and EFX0-safe
    d = rank[l][3]
    Z = [list(b) for b in X]; Z[l] = Z[l] + [d]
    if efx0(Z): X = Z
    # (b): the N2 agent w gets its 3rd choice if unassigned and safe; (c) else its 4th
    held = set(g for b in X for g in b)
    for g in (rank[w][2], rank[w][3]):
        if g not in held:
            Z = [list(b) for b in X]; Z[w] = Z[w] + [g]
            if efx0(Z):
                X = Z; break
    starts.append(X)
print('post-Phase-III states:', starts)
assert sorted(map(str, starts)) == sorted(map(str, [[[5], [3], [2, 4]], [[5], [1, 4], [3]]]))


def key(X):
    return tuple(tuple(sorted(b)) for b in X)


def moves(X):
    held = set(g for b in X for g in b); pool = [g for g in range(m) if g not in held]
    out = []
    E = {i: [j for j in range(n) if j != i and val(i, X[j]) > val(i, X[i])] for i in range(n)}
    for k in range(2, n + 1):                                        # rotations along envy cycles
        for c in itertools.permutations(range(n), k):
            if c[0] == min(c) and all(c[(t + 1) % k] in E[c[t]] for t in range(k)):
                Y = [list(b) for b in X]
                for t in range(k):
                    Y[c[t]] = list(X[c[(t + 1) % k]])
                out.append(Y)
    for g in pool:                                                   # safe placements
        for s in range(n):
            Y = [list(b) for b in X]; Y[s].append(g); out.append(Y)
    for i in range(n):                                               # upgrades and exchanges of a single good
        if len(X[i]) != 1:
            continue
        y = X[i][0]
        mine = [g for g in pool if g in v[i]]
        for r in range(1, len(mine) + 1):
            for S in itertools.combinations(mine, r):
                if val(i, S) > val(i, [y]):
                    Y = [list(b) for b in X]; Y[i] = list(S); out.append(Y)
        for j in range(n):
            if j == i:
                continue
            for z in X[j]:
                Bj = [h for h in X[j] if h != z] + [y]
                if val(j, Bj) <= val(j, X[j]):
                    continue
                for r in range(0, len(mine) + 1):
                    for S in itertools.combinations(mine, r):
                        Bi = [z] + list(S)
                        if val(i, Bi) > val(i, [y]):
                            Y = [list(b) for b in X]; Y[i] = Bi; Y[j] = Bj; out.append(Y)
    return [Y for Y in out if efx0(Y)]


for X0 in starts:
    seen = {key(X0)}; q = deque([X0]); complete = False
    while q:
        X = q.popleft()
        if sum(len(b) for b in X) == m:
            complete = True; break
        for Y in moves(X):
            k = key(Y)
            if k not in seen:
                seen.add(k); q.append(Y)
    print('from', X0, ': states reached', len(seen), '; complete EFX0 reached:', complete)
    assert not complete
print('OK: VMx (and every superset of its moves above) is stuck from every V-M start')
