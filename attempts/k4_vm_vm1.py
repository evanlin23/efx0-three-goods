"""Replay for attempts/k4-vm-vm1.md, from the definitions only (shares no code with k4/vm/).

Instance: a strict connected k = 4 core (n = 3, m = 7) found by k4/vm/vmx2_climb.py --obj=vm1.  Checks:
  1. 20 EFX0 allocations exist (brute force);
  2. V-M's matchings, by hand: agent 2 is the only strongly-top agent (10 > 6 + 3) and takes good 1 (also the top of
     agents 0 and 1); agents 0 and 1 then both claim good 4 (their 2nd); the loser takes its 3rd choice;
  3. NARROW moves (an exchange hands the taker i a good z that i values): from both matchings, and from every state one
     narrow move away (any upgrade of a single good y to a pool set S with v(S) > v(y); any two-agent exchange with
     pool goods, z valued by i, both gain; the state stays EFX0), no sequence of EFX0-safe placements and envy-cycle
     rotations reaches a complete allocation (exhaustive search);
  4. FREE moves (z may be worthless to i): some state one move away IS completed that way, e.g. agent 2 gives its
     top 1 to agent 1 and takes agent 1's good 6 (worthless to agent 2) plus the pool goods {2, 3, 5}.
    python3 attempts/k4_vm_vm1.py"""
import itertools

sets = [[0, 5, 1, 4], [1, 6, 4], [2, 3, 1, 5]]
vals = [[4, 1, 8, 6], [4, 2, 3], [6, 3, 10, 2]]
n, m = 3, 7
v = [dict(zip(S, W)) for S, W in zip(sets, vals)]
val = lambda i, B: sum(v[i].get(g, 0) for g in B)


def efx0(X):
    return all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
               for i in range(n) for j in range(n))


sols = [X for own in itertools.product(range(n), repeat=m) for X in [[[g for g in range(m) if own[g] == i] for i in range(n)]] if efx0(X)]
print(len(sols), 'EFX0 allocations')
assert len(sols) == 20

rank = [sorted(S, key=lambda g: -v[i][g]) for i, S in enumerate(sets)]
assert [i for i in range(n) if v[i][rank[i][0]] > v[i][rank[i][1]] + v[i][rank[i][2]]] == [2] and rank[2][0] == 1
assert rank[0][0] == rank[1][0] == 1 and rank[0][1] == rank[1][1] == 4
matchings = [[[4], [rank[1][2]], [1]], [[rank[0][2]], [4], [1]]]
print('V-M matchings:', matchings)
assert matchings == [[[4], [6], [1]], [[0], [4], [1]]]


def pool_of(X):
    held = set(g for b in X for g in b)
    return [g for g in range(m) if g not in held]


def rotations(X):
    E = {i: [j for j in range(n) if j != i and val(i, X[j]) > val(i, X[i])] for i in range(n)}
    out = []
    for k in range(2, n + 1):
        for c in itertools.permutations(range(n), k):
            if c[0] == min(c) and all(c[(t + 1) % k] in E[c[t]] for t in range(k)):
                Y = [list(b) for b in X]
                for t in range(k):
                    Y[c[t]] = list(X[c[(t + 1) % k]])
                out.append(Y)
    return out


def one_moves(X, free):
    pool = pool_of(X); out = []
    for i in range(n):
        if len(X[i]) != 1:
            continue
        y = X[i][0]; mine = [g for g in pool if g in v[i]]
        for r in range(1, len(mine) + 1):
            for S in itertools.combinations(mine, r):
                if val(i, S) > val(i, [y]):
                    Y = [list(b) for b in X]; Y[i] = list(S); out.append(Y)
        for j in range(n):
            if j == i:
                continue
            for z in X[j]:
                if not free and z not in v[i]:
                    continue
                Bj = [h for h in X[j] if h != z] + [y]
                if val(j, Bj) <= val(j, X[j]):
                    continue
                for r in range(0, len(mine) + 1):
                    for S in itertools.combinations(mine, r):
                        if val(i, [z] + list(S)) > val(i, [y]):
                            Y = [list(b) for b in X]; Y[i] = [z] + list(S); Y[j] = Bj; out.append(Y)
    return [Y for Y in out if efx0(Y)]


key = lambda X: tuple(tuple(sorted(b)) for b in X)


def placeable(X0):
    """exhaustive: some sequence of safe placements and rotations completes X0"""
    seen = {key(X0)}; stack = [X0]
    while stack:
        X = stack.pop()
        pool = pool_of(X)
        if not pool:
            return True
        nxt = rotations(X)
        for g in pool:
            for s in range(n):
                Y = [list(b) for b in X]; Y[s].append(g)
                if efx0(Y):
                    nxt.append(Y)
        for Y in nxt:
            if key(Y) not in seen:
                seen.add(key(Y)); stack.append(Y)
    return False


def states_within_one(free):
    out = []
    for Y in matchings:
        assert efx0(Y)
        out.append((0, Y))
        for R in rotations(Y):
            out.append((0, R))
        for Z in one_moves(Y, free):
            out.append((1, Z))
        for R in rotations(Y):
            for Z in one_moves(R, free):
                out.append((1, Z))
    return out


narrow = states_within_one(False)
print('narrow: states within one move:', len(narrow))
for d, Z in narrow:
    assert not placeable(Z), (d, Z)
print('OK (narrow): no V-M matching, and no state one narrow move away, can be completed')
free = states_within_one(True)
good = [Z for d, Z in free if placeable(Z)]
print('free: states within one move:', len(free), '; completable:', good)
assert [[4], [1], [6, 2, 3, 5]] in good
print('OK (free): one unrestricted exchange makes the pool placeable')
