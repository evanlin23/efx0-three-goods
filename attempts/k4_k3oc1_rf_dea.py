"""Independent replay (no repository code, raw EFX0, the instances' own values) for attempts/k4-k3oc1-rf-dea.md:
receiver-first (Conjecture RF, k4/sdc.md §31) does not restore the k = 3 fact (DE-a) that only an agent giving up
its top good takes junk in a repairing move.

For each instance: the failing order o, its receiver u (last picker), the RF order (u, o - u) and its picks Y';
(1) Y' has no one-absorber EFX0 completion; (2) every improving chain from Y' (official rule of k4/sdc.md §29: x0 takes
H0, plus goods of x_t's base when t >= 1; x_i takes x_{i-1}'s base plus H_i; every agent on it gains; a chain never
hands on an empty base), and whether a one-absorber completion exists after it; (3) among the repairing chains, how
many satisfy (DE-a): every agent that takes a junk good held its top good before the chain.
    python3 attempts/k4_k3oc1_rf_dea.py"""
import itertools

INSTANCES = [
    ('(1, 3) class, 5_pure#778: every repairing chain violates (DE-a)',
     [[0, 2, 6, 7], [1, 5, 6, 8], [2, 5, 6, 7], [3, 4, 5, 8], [3, 4, 7, 8]],
     [[2, 4, 5, 8], [1, 6, 4, 8], [1, 6, 4, 8], [3, 5, 6, 7], [6, 3, 10, 8]], (0, 4, 3, 1, 2)),
    ('(1, 3) class, 5_pure#778, other values: a (DE-a) repair exists',
     [[0, 2, 6, 7], [1, 5, 6, 8], [2, 5, 6, 7], [3, 4, 5, 8], [3, 4, 7, 8]],
     [[2, 4, 5, 8], [3, 8, 4, 10], [2, 6, 3, 10], [4, 5, 6, 8], [6, 3, 4, 8]], (0, 4, 3, 1, 2)),
]

def run(name, SETS, VALS, ORDER):
    n = len(SETS); m = 1 + max(max(s) for s in SETS)
    v = [dict(zip(s, x)) for s, x in zip(SETS, VALS)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    top = [max(s, key=lambda g: v[i][g]) for i, s in enumerate(SETS)]
    def sd(order):
        taken = set(); Y = [None] * n
        for i in order:
            av = [g for g in SETS[i] if g not in taken]
            if av: Y[i] = max(av, key=lambda g: v[i][g]); taken.add(Y[i])
        return Y
    def efx0(X):
        return all(val(i, set(X[j]) - {h}) <= val(i, X[i]) for i in range(n) for j in range(n) if i != j for h in X[j])
    def completes(base):
        B = [[g for g in range(m) if base[g] == a] for a in range(n)]
        J = [g for g in range(m) if base[g] < 0]
        for asg in itertools.product(range(n), repeat=len(J)):
            if sum(1 for a in range(n) if asg.count(a) >= 2) > 1: continue
            if efx0([B[a] + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]): return True
        return False
    def chains(base):
        B = [[g for g in range(m) if base[g] == a] for a in range(n)]; J = [g for g in range(m) if base[g] < 0]
        subsets = lambda xs: [S for r in range(len(xs) + 1) for S in itertools.combinations(xs, r)]
        out = []
        for t in range(n):
            for path in itertools.permutations(range(n), t + 1):
                x0, xt = path[0], path[-1]
                if any(not B[a] for a in path[:-1]): continue
                for Hs in itertools.product(*[subsets([g for g in J if g in v[a]]) for a in path]):
                    if len(set(g for H in Hs for g in H)) != sum(len(H) for H in Hs): continue
                    for Hx in (subsets([g for g in B[xt] if g in v[x0]]) if t > 0 else [()]):
                        new0 = (B[x0] if t == 0 else []) + list(Hs[0]) + list(Hx)
                        if not Hs[0] and not Hx: continue
                        if val(x0, new0) <= val(x0, B[x0]): continue
                        nb = list(base)
                        if t > 0:
                            for g in B[xt]: nb[g] = -1
                        ok = True
                        for s in range(1, t + 1):
                            new = B[path[s - 1]] + list(Hs[s])
                            if val(path[s], new) <= val(path[s], B[path[s]]): ok = False; break
                            for g in new: nb[g] = path[s]
                        if not ok: continue
                        for g in new0: nb[g] = x0
                        junk_takers = [a for a, H in zip(path, Hs) if H]
                        dea = all(B[a] == [top[a]] for a in junk_takers)
                        out.append((tuple(nb), path, Hs, dea))
        return out
    Y = sd(ORDER); u = ORDER[-1]
    assert not any(v[j].get(Y[u], 0) > v[j][Y[j]] for j in range(n) if j != u), 'u is not a receiver'
    Y2 = sd((u,) + tuple(a for a in ORDER if a != u))
    base = tuple(next((a for a in range(n) if Y2[a] == g), -1) for g in range(m))
    print('==', name, '| order', ORDER, 'picks', Y, '| receiver', u, '| RF picks', Y2, 'junk', [g for g in range(m) if base[g] < 0])
    print('   (1) one-absorber completion at the RF picks:', completes(base))
    ch = chains(base); rep = [c for c in ch if completes(c[0])]
    print('   (2) improving chains: %d; repairing: %d' % (len(ch), len(rep)))
    print('   (3) repairing chains satisfying (DE-a): %d' % sum(1 for c in rep if c[3]))
    for nb, path, Hs, dea in rep[:3]:
        print('       e.g. path %s, junk taken %s, mover ranks %s' % (path, Hs, [sorted(SETS[a], key=lambda g: -v[a][g]).index(Y2[a]) for a in path]))

for inst in INSTANCES: run(*inst)
