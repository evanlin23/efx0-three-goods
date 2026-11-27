"""Replay of attempts/k4-k3oc1-junk-shape.md and attempts/k4-k3oc1-validity.md, independent of k4/ code (brute
force over every improving chain and every one-absorber placement of the junk, raw EFX0 definition, no SAT).
  nsw-local-n3m5 (n = 3, m = 5), order (1, 0, 2): every repairing chain gives junk to an agent that does not hold
      its top (agent 0 trades its second good 4 for {1, 3}), which never helps at k = 3;
  T3 (n = 3, m = 6), order (0, 2, 1): every repairing chain leaves agent 1's top 4 in a two-good bundle (not valid);
      the completion compensates agent 1 with the junk good 3.
    python3 attempts/k4_k3oc1_lift.py"""
import itertools
INSTANCES = {
    'nsw-local-n3m5': ([[0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4]], [[8, 4, 5, 6], [10, 3, 4, 8], [2, 3, 4, 8]], 5, (1, 0, 2)),
    'T3': ([[5, 0, 4, 2], [3, 1, 4], [4, 1, 3, 0]], [[1, 38, 36, 6], [12, 22, 30], [28, 20, 12, 38]], 6, (0, 2, 1)),
}
val = lambda i, S: sum(v[i].get(g, 0) for g in S)

def efx0(X):
    for i in range(n):
        for j in range(n):
            if i != j and any(val(i, set(X[j]) - {h}) > val(i, X[i]) for h in X[j]): return False
    return True

def one_absorber_completions(base):
    """complete EFX0 allocations keeping every base, at most one agent receiving two or more unallocated goods"""
    J = [g for g in range(m) if base[g] < 0]
    for asg in itertools.product(range(n), repeat=len(J)):
        cnt = [asg.count(a) for a in range(n)]
        if sum(1 for c in cnt if c >= 2) > 1: continue
        X = [[g for g in range(m) if base[g] == a] + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]
        if efx0(X): yield X

def valid(base):
    B = [[g for g in range(m) if base[g] == a] for a in range(n)]
    for i in range(n):
        for g in sets[i]:
            if g in B[i] or v[i][g] <= val(i, B[i]): continue
            a = base[g]
            if a < 0 or len(B[a]) != 1: return False
    return True

def chains(base, record):
    """every improving chain of k4/sdc.md §29 (t = 0 included), by brute force over paths and sets"""
    B = [[g for g in range(m) if base[g] == a] for a in range(n)]; J = [g for g in range(m) if base[g] < 0]
    subsets = lambda xs: (S for r in range(len(xs) + 1) for S in itertools.combinations(xs, r))
    out = set()
    for t in range(n):
        for path in itertools.permutations(range(n), t + 1):
            x0, xt = path[0], path[-1]
            for Hs in itertools.product(*[list(subsets(J)) for _ in path]):
                if len(set(g for H in Hs for g in H)) != sum(len(H) for H in Hs): continue
                extra0 = [] if t == 0 else list(B[xt])
                for H0x in subsets(extra0):
                    new0 = (B[x0] if t == 0 else []) + list(Hs[0]) + list(H0x)
                    if not Hs[0] and not H0x: continue
                    if val(x0, new0) <= val(x0, B[x0]): continue
                    ok = True; nb = list(base)
                    if t > 0:
                        for g in B[xt]: nb[g] = -1
                    for s in range(1, t + 1):
                        new = B[path[s - 1]] + list(Hs[s])
                        if val(path[s], new) <= val(path[s], B[path[s]]): ok = False; break
                        for g in new: nb[g] = path[s]
                    if not ok: continue
                    for g in new0: nb[g] = x0
                    out.add(tuple(nb)); record.setdefault(tuple(nb), []).append((path, Hs, H0x))
    return out

for name, (sets, vals, m, order) in INSTANCES.items():
    n = len(sets); v = [dict(zip(st, x)) for st, x in zip(sets, vals)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    top = [max(st, key=lambda g: v[i][g]) for i, st in enumerate(sets)]
    taken = set(); Y = [None] * n
    for i in order:
        av = [g for g in sets[i] if g not in taken]
        if av: Y[i] = max(av, key=lambda g: v[i][g]); taken.add(Y[i])
    base = tuple(next((a for a in range(n) if Y[a] == g), -1) for g in range(m))
    print('===', name, 'order', order, 'picks', Y, 'junk', [g for g in range(m) if base[g] < 0])
    print('picks have a one-absorber completion:', any(True for _ in one_absorber_completions(base)))
    rec = {}; ch = chains(base, rec); rep = [b for b in ch if any(True for _ in one_absorber_completions(b))]
    print('improving chains:', len(ch), '; with a one-absorber completion:', len(rep))
    for b in rep:
        descs = rec[b]
        tops_only = any(all(not H or [g for g in range(m) if base[g] == path[s]] == [top[path[s]]] for s, H in enumerate(Hs)) and
                        (not H0x or [g for g in range(m) if base[g] == path[0]] == [top[path[0]]]) for path, Hs, H0x in descs)
        print('  repairing result', [[g for g in range(m) if b[g] == a] for a in range(n)], '| valid', valid(b),
              '| some description gives junk only to top-holders', tops_only, '| completion', next(one_absorber_completions(b)))
