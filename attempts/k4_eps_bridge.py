"""The epsilon bridge from EFX to EFX0 (attempts/k4-eps-bridge.md): on V-M's smallest EFX0 failure (k4/vm.md §5.3,
n = 2, m = 3), list by brute force (1) the EFX0 allocations of v, (2) the ordinary EFX allocations of v, (3) the
ordinary EFX allocations of v^eps (every good outside R_i valued eps by i) for eps = 1e-3, 1e-6.  Shows that EFX for
v^eps (small eps) picks out exactly EFX0 allocations of v (here with the junk-count tie-break), and that v^eps is not
4-limited (every agent values all goods), so Theorem VM does not apply to it.
    python3 attempts/k4_eps_bridge.py"""
import itertools

V = [{0: 19, 1: 14}, {0: 17, 2: 7}]; n, m = 2, 3


def val(v, S): return sum(v.get(g, 0) for g in S)


def ok(vs, X, zero_counts):   # zero_counts: removal of a zero-valued good counts (EFX0) or not (EFX)
    for i in range(n):
        for j in range(n):
            if i == j: continue
            for g in X[j]:
                if not zero_counts and vs[i].get(g, 0) == 0: continue
                if val(vs[i], [h for h in X[j] if h != g]) > val(vs[i], X[i]) + 1e-12: return False
    return True


allocs = []
for lab in itertools.product(range(n), repeat=m):
    allocs.append(tuple(tuple(g for g in range(m) if lab[g] == i) for i in range(n)))
print('EFX0 for v      :', [X for X in allocs if ok(V, X, True)])
print('EFX  for v      :', [X for X in allocs if ok(V, X, False)])
for eps in (1e-3, 1e-6):
    Ve = [{g: V[i].get(g, eps) for g in range(m)} for i in range(n)]
    print('EFX  for v^%g :' % eps, [X for X in allocs if ok(Ve, X, False)],
          '| relevant goods per agent under v^eps:', [len(Ve[i]) for i in range(n)])
