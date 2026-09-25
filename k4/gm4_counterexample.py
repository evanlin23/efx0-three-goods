"""Independent brute-force check of the counterexamples to conjecture GM4 (k4/gm4.md §2).  Plain Python, raw
definitions only; shares no code with gm4_explore.c, gm4_fast.c or gm4_analyze.py.

For each instance (explicit integer values; every agent's subset sums on its relevant goods are distinct):
  1. it is a k = 4 core: every agent has 3 or 4 relevant goods, is strictly balanced (top < sum of the others), has at
     most d - 2 private goods (two only with p + q < s + t), every good is relevant to someone, and the core is
     connected;
  2. the stated partial allocation Y is junk-free and EFX0: v_i(Y_i) >= v_i(Y_j - {g}) for all i != j, g in Y_j
     (every good may be removed, including goods worth 0 to i);
  3. Y maximizes the level sum  sum_i #{T subset R_i : v_i(T) < v_i(Y_i)}  over ALL junk-free EFX0 partial
     allocations (every good to the pool or to one of its valuers: all of them are enumerated);
  4. [GM4] no placement of the pool: no assignment of the pool goods to agents (any agents, valued or not) gives a
     complete EFX0 allocation containing Y (so in particular no junk placement);
  5. [dead end] no complete EFX0 allocation X has v_i(X_i) >= v_i(Y_i) for every i (all n^m allocations);
  6. it lists every level-sum maximum and says which admit a placement, and counts the complete EFX0 allocations.
Exit status 0 iff every claim holds for every instance.
Usage: python3 k4/gm4_counterexample.py
"""
import itertools, sys

# (goods of agent i with values), stated maximum Y (list of bundles), label
INSTANCES = [
    ("A: pure n=4, m=7",
     [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 2, 3: 7, 5: 8, 6: 4}, {3: 6, 4: 3, 5: 4, 6: 8}],
     [{0, 2}, {1, 4}, {5}, {6}]),
    ("B: pure n=4, m=7",
     [{0: 4, 2: 2, 5: 8, 6: 5}, {1: 3, 4: 6, 5: 8, 6: 10}, {2: 4, 3: 5, 4: 2, 6: 8}, {3: 5, 4: 4, 5: 8, 6: 2}],
     [{0, 2}, {1, 4}, {6}, {5}]),
    ("C: pure n=4, m=7",
     [{0: 2, 2: 4, 5: 8, 6: 3}, {1: 2, 2: 4, 3: 7, 6: 10}, {1: 1, 4: 6, 5: 4, 6: 8}, {3: 8, 4: 6, 5: 10, 6: 3}],
     [{0, 2}, {6}, {1, 4}, {5}]),
    ("D: pure n=4, m=7",
     [{0: 10, 2: 7, 4: 2, 5: 6}, {0: 8, 3: 4, 4: 1, 6: 6}, {1: 1, 2: 4, 5: 8, 6: 6}, {1: 3, 3: 6, 5: 10, 6: 2}],
     [{2, 4}, {0}, {5}, {1, 3}]),
]

def v(vals, i, S):
    return sum(vals[i].get(g, 0) for g in S)

def efx0(vals, X):
    n = len(X)
    for i in range(n):
        own = v(vals, i, X[i])
        for j in range(n):
            if j == i: continue
            for g in X[j]:
                if v(vals, i, X[j] - {g}) > own: return False
    return True

def level(vals, i, S):
    R = sorted(vals[i])
    x = v(vals, i, S)
    return sum(1 for k in range(len(R) + 1) for T in itertools.combinations(R, k) if v(vals, i, T) < x)

def check(label, vals, Y):
    n = len(vals); m = 1 + max(g for d in vals for g in d)
    Y = [set(b) for b in Y]
    ok = True
    def claim(c, text):
        nonlocal ok
        print(f"  [{'ok' if c else 'FAILED'}] {text}")
        ok &= bool(c)
    print(label)
    R = [set(d) for d in vals]
    deg = [sum(g in R[i] for i in range(n)) for g in range(m)]
    core = all(len(R[i]) in (3, 4) for i in range(n)) and all(d >= 1 for d in deg)
    for i in range(n):
        top = max(vals[i].values()); core &= top < sum(vals[i].values()) - top
        sums = [v(vals, i, T) for k in range(1, len(R[i]) + 1) for T in itertools.combinations(sorted(R[i]), k)]
        core &= len(set(sums)) == len(sums)
        priv = [g for g in R[i] if deg[g] == 1]
        core &= len(priv) <= len(R[i]) - 2
        if len(priv) == 2: core &= v(vals, i, priv) < v(vals, i, R[i] - set(priv))
    seen, todo = {0}, [0]                       # connectivity of the agent-good incidence graph
    while todo:
        a = todo.pop()
        for b in range(n):
            if b not in seen and R[a] & R[b]: seen.add(b); todo.append(b)
    core &= len(seen) == n
    claim(core, "k = 4 core (degrees 3-4, strictly balanced, strict, private-good rule, every good valued, connected)")
    claim(all(Y[i] <= R[i] for i in range(n)) and efx0(vals, Y), "Y is junk-free and EFX0")
    U = set(range(m)) - set().union(*Y)
    ly = sum(level(vals, i, Y[i]) for i in range(n))
    best, maxima = -1, []
    for owners in itertools.product(*[[None] + [i for i in range(n) if g in R[i]] for g in range(m)]):
        X = [set() for _ in range(n)]
        for g, i in enumerate(owners):
            if i is not None: X[i].add(g)
        if not efx0(vals, X): continue
        s = sum(level(vals, i, X[i]) for i in range(n))
        if s > best: best, maxima = s, []
        if s == best: maxima.append(X)
    claim(ly == best and Y in maxima, f"Y maximizes the level sum over all junk-free EFX0 partial allocations ({ly} = {best})")
    def placeable(Z):
        P = sorted(set(range(m)) - set().union(*Z))
        for asg in itertools.product(range(n), repeat=len(P)):
            X = [set(b) for b in Z]
            for u, j in zip(P, asg): X[j].add(u)
            if efx0(vals, X): return True
        return False
    claim(U and not placeable(Y), f"pool {sorted(U)} is nonempty and no assignment of it to any agents is EFX0 (GM4 fails)")
    comp = []
    for owners in itertools.product(range(n), repeat=m):
        X = [set(g for g in range(m) if owners[g] == i) for i in range(n)]
        if efx0(vals, X): comp.append(X)
    dom = [X for X in comp if all(v(vals, i, X[i]) >= v(vals, i, Y[i]) for i in range(n))]
    claim(not dom, f"dead end: none of the {len(comp)} complete EFX0 allocations gives every agent at least v_i(Y_i)")
    print(f"  level-sum maxima: {len(maxima)}; with a placement: {sum(placeable(Z) for Z in maxima)}")
    for Z in maxima:
        print(f"    {[sorted(b) for b in Z]} pool {sorted(set(range(m)) - set().union(*Z))} placement: {placeable(Z)}")
    bestc = max(sum(level(vals, i, X[i] & R[i]) for i in range(n)) for X in comp)
    print(f"  largest level sum of a complete EFX0 allocation: {bestc} (maximum over partial ones: {best})")
    return ok

if __name__ == '__main__':
    allok = True
    for label, vals, Y in INSTANCES:
        allok &= check(label, vals, Y)
    print("ALL CLAIMS HOLD" if allok else "SOME CLAIM FAILED")
    sys.exit(0 if allok else 1)
