"""Replay for attempts/k4-vm-vm1-core.md, from the definitions only (shares no code with k4/vm/ or k4/c4_verify_H/;
adapted from attempts/k4_vm_vm1_noncore.py).  For each instance below:
  0. it is a connected k = 4 core, by a direct check of IsCore4 (LEDGER K4.CORE: (C1) 3 <= |R_i| <= 4; (C2)
     2 v_i(g) < v_i(M); (C3) |P_i| + 2 <= |R_i|; (C4) |P_i| = 2 => v_i(P_i) < v_i(S_i); (C5) every good relevant),
     strictness (disjoint nonempty subsets of R_i have different values) and connectivity;
  1. V-M's Phases I-II, by a direct rank-greedy implementation over every tie resolution;
  2. a SUPERSET of VM1's moves from each matching (rotations first or not; any upgrade of a single good y to a pool
     set S with v(S) > v(y); any two-agent exchange, i taking any good z of j plus a pool set S, both gaining; the
     state stays EFX0): no state within one move is completed by EFX0-safe placements and envy-cycle rotations
     (exhaustive memoized search);
  3. with two moves some state is, or else with three (the completion found is printed and re-checked).
A failed placement search proves every state it reached unplaceable, so failures are memoized across searches.
Instances: C0..C4, the five cores found by k4/vm/vm1_core_repair.py (results/k4_vm/vm1_core_repair.log), walking
from the near-core failure K4-cut of attempts/k4-vm-vm1-noncore.md.  C0 (n = 5, m = 8) is the smallest.
    python3 attempts/k4_vm_vm1_core.py [NAME ...]"""
import itertools, sys

INST = {
    'C0': ([[3, 6, 2, 4], [7, 0, 4], [1, 3, 2, 0], [7, 4, 2, 3], [7, 6, 5, 4]],
           [[25, 5, 15, 26], [17, 30, 23], [6, 15, 30, 25], [14, 9, 24, 3], [11, 15, 8, 30]], 8),
    'C1': ([[4, 1, 0, 5], [2, 0, 3, 6], [8, 4, 2, 0], [0, 4, 2, 5], [3, 7, 6, 5]],
           [[23, 21, 1, 25], [13, 28, 1, 18], [20, 25, 30, 29], [6, 8, 30, 18], [11, 15, 8, 30]], 9),
    'C2': ([[4, 2, 9, 5], [3, 1, 0, 8], [7, 4, 3, 1], [6, 1, 3, 7], [8, 9, 6, 5]],
           [[25, 5, 15, 26], [14, 24, 4, 9], [20, 25, 30, 29], [11, 8, 29, 14], [11, 15, 8, 30]], 10),
    'C3': ([[5, 2, 1, 6], [0, 1, 3], [2, 5, 3, 1], [7, 5, 3, 4], [4, 8, 7, 6]],
           [[25, 5, 15, 26], [19, 27, 17], [20, 25, 30, 29], [10, 4, 17, 5], [11, 15, 8, 30]], 9),
    'C4': ([[5, 3, 0, 6], [2, 1, 3], [2, 5, 3, 1], [7, 8, 3, 1], [4, 8, 7, 6]],
           [[21, 2, 10, 27], [26, 30, 24], [20, 23, 26, 24], [12, 9, 30, 11], [3, 8, 9, 19]], 9),
}


def is_core(sets, vals, m):
    """IsCore4 + strictness + connectivity, from the definitions"""
    n = len(sets); vv = [dict(zip(S, W)) for S, W in zip(sets, vals)]
    R = [[g for g in S if vv[i][g] > 0] for i, S in enumerate(sets)]
    if n < 2: return False
    for i in range(n):
        d = len(R[i]); tot = sum(vv[i][g] for g in R[i])
        if not 3 <= d <= 4: return False                                       # C1
        if any(not 2 * vv[i][g] < tot for g in R[i]): return False             # C2
        P = [g for g in R[i] if all(g not in R[j] for j in range(n) if j != i)]
        Sh = [g for g in R[i] if g not in P]
        if len(P) + 2 > d: return False                                        # C3
        if len(P) == 2 and not sum(vv[i][g] for g in P) < sum(vv[i][g] for g in Sh): return False   # C4
        for a in range(1, 1 << d):                                             # strict
            for b in range(1, 1 << d):
                if a & b: continue
                if sum(vv[i][R[i][t]] for t in range(d) if a >> t & 1) == sum(vv[i][R[i][t]] for t in range(d) if b >> t & 1):
                    return False
    if any(all(g not in R[i] for i in range(n)) for g in range(m)): return False   # C5
    comp = {0}; changed = True                                                 # connected through shared goods
    while changed:
        changed = False
        for i in range(n):
            if i not in comp and any(set(R[i]) & set(R[j]) for j in comp):
                comp.add(i); changed = True
    return len(comp) == n


def load(name):
    global sets, vals, n, m, v, rank, FAILED
    sets, vals, m = INST[name]; n = len(sets)
    v = [dict(zip(S, W)) for S, W in zip(sets, vals)]
    rank = [sorted(S, key=lambda g: (-v[i][g], g)) for i, S in enumerate(sets)]
    FAILED = set()


val = lambda i, B: sum(v[i].get(g, 0) for g in B)


def efx0(X):
    return all(not (i != j and any(val(i, [h for h in X[j] if h != g]) > val(i, X[i]) for g in X[j]))
               for i in range(n) for j in range(n))




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
    if key(X0) in FAILED:
        return None
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
            if key(Y) not in seen and key(Y) not in FAILED:
                seen.add(key(Y)); stack.append(Y)
    FAILED.update(seen)
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




def nextlevel(L):
    seen = set(); out = []
    for Z in L:
        for Y in moves(Z):
            for W in closure_rot(Y):
                if key(W) not in seen:
                    seen.add(key(W)); out.append(W)
    return out


def main(name):
    load(name)
    print("==", name, flush=True)
    assert is_core(sets, vals, m), name
    print('connected k = 4 core: yes', flush=True)
    Ms = vm_matchings()
    print('V-M matchings:', Ms, flush=True)


    level0 = [Z for Y in Ms for Z in closure_rot(Y)]
    level1 = nextlevel(level0)
    print('states with no move:', len(level0), '; within one move:', len(level1), flush=True)
    for Z in level0 + level1:
        assert placeable(Z) is None, Z
    print('OK: no state within one move completes (superset of VM1)', flush=True)
    level2 = nextlevel(level1)
    for Z in level2:
        X = placeable(Z)
        if X is not None:
            assert efx0(X) and sorted(g for b in X for g in b) == list(range(m))
            print('two moves suffice, e.g.', X)
            return
    print('no completion with two moves (%d states); trying three' % len(level2), flush=True)
    for Z in level2:
        for Y in moves(Z):
            X = placeable(Y)
            if X is not None:
                assert efx0(X) and sorted(g for b in X for g in b) == list(range(m))
                print('three moves suffice, e.g.', X)
                return
    print('no completion with three moves either')


if __name__ == '__main__':
    for name in (sys.argv[1:] or list(INST)):
        main(name)
