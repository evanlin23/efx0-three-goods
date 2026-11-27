"""Replay for attempts/k4-vm-vm1-k7.md, from the definitions only (shares no code with k4/vm/).

Instance PW(2,3,6)#0 (k = 7; the family of k4/ksens.md on claude/k4-ksens): n = 5, m = 11.  Checks:
  1. V-M's Phases I-II, by a direct rank-greedy implementation over every tie resolution: 4 matchings;
  2. a SUPERSET of VM1's moves from each matching (rotations first or not; any upgrade of a single good y to a pool
     set S with v(S) > v(y); any two-agent exchange, i taking any good z of j plus a pool set S, both gaining; the
     state stays EFX0): no state within one move is completed by EFX0-safe placements and envy-cycle rotations
     (exhaustive memoized search);
  3. with two moves some state is (the completion found is printed and re-checked).
    python3 attempts/k4_vm_vm1_pw.py"""
import itertools

sets = [[0, 5, 6, 7, 8, 9, 10], [1, 5, 6, 7, 8, 9, 10], [0, 1, 2], [0, 1, 3], [0, 1, 4]]
vals = [[100, 90, 82, 61, 66, 77, 54], [100, 95, 62, 83, 92, 93, 78], [94, 60, 40], [98, 65, 54], [98, 83, 56]]
n, m = 5, 11
v = [dict(zip(S, W)) for S, W in zip(sets, vals)]
val = lambda i, B: sum(v[i].get(g, 0) for g in B)


def efx0(X):
    return all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
               for i in range(n) for j in range(n))


rank = [sorted(S, key=lambda g: (-v[i][g], g)) for i, S in enumerate(sets)]


def vm_matchings():
    """Phase I (agents whose top beats their 2nd + 3rd) then Phase II (k-th choices, k = 1.. 7), every claimant choice"""
    A = [i for i in range(n) if v[i][rank[i][0]] > sum(v[i][g] for g in rank[i][1:3])]
    out = []
    def steps(Y, remaining, avail, ks):
        if not ks:
            out.append([list(b) for b in Y]); return
        k = ks[0]; claim = {}
        for i in sorted(remaining):
            if len(rank[i]) >= k and rank[i][k - 1] in avail:
                claim.setdefault(rank[i][k - 1], []).append(i)
        goods = sorted(claim)
        for pick in itertools.product(*[claim[g] for g in goods]):
            Z = [list(b) for b in Y]; rem = set(remaining); av = set(avail)
            for g, i in zip(goods, pick):
                Z[i] = [g]; rem.discard(i); av.discard(g)
            steps(Z, rem, av, ks[1:])
    # Phase I
    claimI = {}
    for i in A:
        claimI.setdefault(rank[i][0], []).append(i)
    goods = sorted(claimI)
    for pick in itertools.product(*[claimI[g] for g in goods]):
        Y = [[] for _ in range(n)]; rem = set(range(n)); av = set(range(m))
        for g, i in zip(goods, pick):
            Y[i] = [g]; rem.discard(i); av.discard(g)
        steps(Y, rem, av, list(range(1, 1 + max(map(len, sets)))))
    res = []
    for Y in out:
        if Y not in res: res.append(Y)
    return res


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


def moves(X):
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
    seen = {key(X0)}; stack = [X0]
    while stack:
        X = stack.pop()
        pool = pool_of(X)
        if not pool:
            return X
        nxt = rotations(X)
        for g in pool:
            for s in range(n):
                Y = [list(b) for b in X]; Y[s].append(g)
                if efx0(Y):
                    nxt.append(Y)
        for Y in nxt:
            if key(Y) not in seen:
                seen.add(key(Y)); stack.append(Y)
    return None


def closure_rot(X):
    """X and every state reachable from X by rotations alone"""
    seen = {key(X)}; out = [X]; k = 0
    while k < len(out):
        for Y in rotations(out[k]):
            if key(Y) not in seen:
                seen.add(key(Y)); out.append(Y)
        k += 1
    return out


Ms = vm_matchings()
print('V-M matchings:', Ms)
assert len(Ms) == 4
level0 = [Z for Y in Ms for Z in closure_rot(Y)]
level1 = [W for Z in level0 for Y in moves(Z) for W in closure_rot(Y)]
print('states with no move:', len(level0), '; within one move:', len(level1))
for Z in level0 + level1:
    assert placeable(Z) is None, Z
print('OK: no state within one move completes (superset of VM1)')
for Z in level1:
    for Y in moves(Z):
        X = placeable(Y)
        if X is not None:
            assert efx0(X) and sorted(g for b in X for g in b) == list(range(m))
            print('two moves suffice, e.g.', X)
            raise SystemExit(0)
print('no completion with two moves either')
