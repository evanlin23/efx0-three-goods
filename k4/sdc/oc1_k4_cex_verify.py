"""Coordinator's independent replay (2026-11-26) of the claimed OC1 counterexample at k = 4 (TTC session).  Own code, raw
definitions, no SAT.  Moves (k4/sdc.md §29): improving chains x0..xt with disjoint H's inside receivers' relevant
goods; t = 0: x0 adds junk H0 to its base; t >= 1: x0 takes H0 (from J and B_{xt}), x_i takes B_{x_{i-1}} + H_i (H_i
from J), rest of B_{xt} becomes junk; every mover strictly gains.  Rings: w0 -> ... -> w_{r-1} -> w0, each takes its
predecessor's base plus junk, all strictly gain.  No caps on set sizes."""
import itertools, sys
PERMISSIVE = 'permissive' in sys.argv   # allow handing on an empty base (= disjoint chains glued through pickless agents)
sets = [[0,2,3,1],[1,4,5,9],[1,2,0,8],[1,6,7,8],[3,6,9],[1,3,6,9]]
vals = [[2,7,8,3],[3,6,4,9],[12,2,4,8],[12,6,3,4],[7,2,10],[7,8,4,1]]
n = len(sets); m = 1 + max(max(s) for s in sets)
v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
V = lambda i, S: sum(v[i].get(g, 0) for g in S)
R = [set(s) for s in sets]
# serial dictatorship, order 0..n-1 (ties impossible: strict values per agent)
taken = set(); picks = []
for i in range(n):
    av = [g for g in R[i] if g not in taken]
    if av:
        g = max(av, key=lambda g: v[i][g]); picks.append(g); taken.add(g)
    else: picks.append(None)
print('m', m, 'picks', picks)
def efx0(B):
    for i in range(n):
        own = V(i, B[i])
        for j in range(n):
            if j != i:
                for h in B[j]:
                    if V(i, [g for g in B[j] if g != h]) > own: return False
    return True
def completions(base, maxabs=None):
    """all junk placements (keep bases); return list of absorber counts of EFX0 completions"""
    J = [g for g in range(m) if all(g not in b for b in base)]
    out = []
    for asg in itertools.product(range(n), repeat=len(J)):
        cnt = [0] * n
        for a in asg: cnt[a] += 1
        nab = sum(c >= 2 for c in cnt)
        if maxabs is not None and nab > maxabs: continue
        B = [list(b) for b in base]
        for g, a in zip(J, asg): B[a].append(g)
        if efx0(B): out.append((nab, tuple(asg)))
    return out
base0 = [[p] if p is not None else [] for p in picks]
J0 = [g for g in range(m) if g not in taken]
print('junk', J0)
allc = completions(base0)
print('free completions of the picks:', len(allc), '| absorber counts:', sorted(set(c for c, _ in allc)))
print('one-absorber completions of the picks:', sum(1 for c, _ in allc if c <= 1))
def subsets(xs):
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)
def moves(base):
    J = [g for g in range(m) if all(g not in b for b in base)]
    res = set()
    # t = 0: add junk
    for x in range(n):
        for H in subsets([g for g in J if g in R[x]]):
            if H and V(x, base[x] + list(H)) > V(x, base[x]):
                nb = [list(b) for b in base]; nb[x] = base[x] + list(H); res.add(tuple(tuple(sorted(b)) for b in nb))
    # chains t >= 1
    def ext(path, used, assign):
        xt = path[-1]
        if len(path) >= 2:
            pool = [g for g in J if g not in used and g in R[path[0]]] + [g for g in base[xt] if g in R[path[0]]]
            for H0 in subsets(pool):
                if H0 and V(path[0], H0) > V(path[0], base[path[0]]):
                    nb = [list(b) for b in base]
                    nb[path[0]] = list(H0)
                    for i in range(1, len(path)):
                        nb[path[i]] = list(base[path[i - 1]]) + list(assign[i])
                    # leftover of B_{xt} not in H0 becomes junk (already excluded by reassigning xt's base)
                    res.add(tuple(tuple(sorted(b)) for b in nb))
        if len(path) >= n or (not base[xt] and not PERMISSIVE): return
        for y in range(n):
            if y in path: continue
            for H in subsets([g for g in J if g not in used and g in R[y]]):
                if V(y, list(base[xt]) + list(H)) > V(y, base[y]):
                    ext(path + [y], used | set(H), {**assign, len(path): H})
    for x in range(n): ext([x], frozenset(), {})
    # rings
    for r in range(2, n + 1):
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc): continue
            def ring(i, used, assign):
                if i == r:
                    nb = [list(b) for b in base]
                    for t in range(r):
                        w = cyc[t]; pred = cyc[t - 1]
                        nb[w] = list(base[pred]) + list(assign[t])
                    res.add(tuple(tuple(sorted(b)) for b in nb)); return
                w = cyc[i]; pred = cyc[i - 1]
                if not base[pred] and not PERMISSIVE: return
                for H in subsets([g for g in J if g not in used and g in R[w]]):
                    if V(w, list(base[pred]) + list(H)) > V(w, base[w]):
                        ring(i + 1, used | set(H), {**assign, i: H})
            ring(0, frozenset(), {})
    return res
M = moves(base0)
print('distinct states after one improving move:', len(M))
good = 0
for st in M:
    if any(c <= 1 for c, _ in completions([list(b) for b in st], maxabs=1)): good += 1
print('states with a one-absorber completion:', good)
print('OC1 at this start:', 'HOLDS' if allc and min(c for c, _ in allc) <= 1 or good else 'FAILS')
