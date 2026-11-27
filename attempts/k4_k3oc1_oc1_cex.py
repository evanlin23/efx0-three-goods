"""Independent replay (no repository code, no SAT, raw EFX0 definition, explicit values) of the counterexample to
Conjecture OC1 of k4/sdc.md §29 in attempts/k4-k3oc1-oc1-counterexample.md.

Instance (k = 3: every agent values exactly three goods, strictly balanced): goods 0..8,
  agent 0 values goods 0, 1, 2 at 10, 8, 7     agent 1 values goods 0, 1, 2 at 10, 8, 7
  agent 2 values goods 0, 3, 4 at 10, 8, 7     agent 3 values goods 1, 5, 6 at 10, 8, 7
  agent 4 values goods 2, 7, 8 at 10, 8, 7
Order (2, 3, 4, 0, 1): picks 0, 1, 2 for agents 2, 3, 4; agents 0 and 1 get nothing; goods 3..8 are unpicked.
Two notions of chain: "no glue" (as k4/sdc/de_free.py, which produced all of §29's evidence: a chain stops at an
agent holding nothing, as Draft and Exchange's chains do) and "glue" (the literal text of §29: an agent holding
nothing may pass on its empty base, so the next agent takes only junk and a second chain starts there).
Checks: (1) the picks have no one-absorber completion; (2) no chain without glue gives one, while chains with glue do;
(3) with the free completion (any number of absorbers) one chain without glue suffices; (4) two chains without glue
suffice for the one-absorber completion.
    python3 attempts/k4_k3oc1_oc1_cex.py"""
import itertools
SETS = [[0, 1, 2], [0, 1, 2], [0, 3, 4], [1, 5, 6], [2, 7, 8]]
VALS = [[10, 8, 7]] * 5
ORDER = (2, 3, 4, 0, 1)
n, m = len(SETS), 9
v = [dict(zip(s, x)) for s, x in zip(SETS, VALS)]
val = lambda i, S: sum(v[i].get(g, 0) for g in S)
assert all(x[0] < x[1] + x[2] for x in VALS)

def efx0(X):
    return all(val(i, set(X[j]) - {h}) <= val(i, X[i]) for i in range(n) for j in range(n) if i != j for h in X[j])

def completions(base, absorbers_max):
    J = [g for g in range(m) if base[g] < 0]
    for asg in itertools.product(range(n), repeat=len(J)):
        if sum(1 for a in range(n) if asg.count(a) >= 2) > absorbers_max: continue
        X = [[g for g in range(m) if base[g] == a] + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]
        if efx0(X): return X
    return None

def chains(base, glue=True):
    """every improving chain x0..xt: x0 takes H0 (from J, and for t >= 1 also from x_t's base) in addition to its base
    (t = 0) or in place of it (t >= 1); x_i (i >= 1) takes x_{i-1}'s base plus H_i from J; every agent on it gains;
    the rest of x_t's base becomes unallocated.  The sets H lie inside the receivers' relevant goods (k4/sdc.md §29)."""
    B = [[g for g in range(m) if base[g] == a] for a in range(n)]; J = [g for g in range(m) if base[g] < 0]
    subsets = lambda xs: [S for r in range(len(xs) + 1) for S in itertools.combinations(xs, r)]
    out = set()
    for t in range(n):
        for path in itertools.permutations(range(n), t + 1):
            x0, xt = path[0], path[-1]
            if not glue and any(not B[a] for a in path[:-1]): continue   # de_free.py: a chain ends at an empty-handed agent
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
                    out.add(tuple(nb))
    return out

taken = set(); Y = [None] * n
for i in ORDER:
    av = [g for g in SETS[i] if g not in taken]
    if av: Y[i] = max(av, key=lambda g: v[i][g]); taken.add(Y[i])
base = tuple(next((a for a in range(n) if Y[a] == g), -1) for g in range(m))
print('picks', Y, 'unallocated', [g for g in range(m) if base[g] < 0])
print('(1) one-absorber completion of the picks:', completions(base, 1))
for glue in (False, True):
    ch = chains(base, glue)
    rep1 = [b for b in ch if completions(b, 1) is not None]
    print('(2) glue %s: improving chains %d; after which a one-absorber completion exists: %d' % (glue, len(ch), len(rep1)))
    if rep1: print('    e.g. bases', [[g for g in range(m) if rep1[0][g] == a] for a in range(n)])
ch = chains(base, False)
repF = [b for b in ch if completions(b, n) is not None]
print('(3) no glue: chains after which a completion with any number of absorbers exists:', len(repF))
if repF:
    b = repF[0]; print('    e.g. bases', [[g for g in range(m) if b[g] == a] for a in range(n)], 'completion', completions(b, n))
two = next((b2 for b in ch for b2 in chains(b, False) if completions(b2, 1) is not None), None)
print('(4) two chains reach a one-absorber completion:', two is not None,
      '' if two is None else [[g for g in range(m) if two[g] == a] for a in range(n)])
