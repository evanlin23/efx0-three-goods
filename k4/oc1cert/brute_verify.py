"""Brute-force verification of an OC1^max candidate failure from the raw definitions (no repository code).
Checks: strictness, balance, SD orders giving the picks, maximum matching, then every complete allocation for EFX0,
and every one-move state (additions, chains, rings; official rules) for a one-absorber completion; also the free
completion (any number of absorbers)."""
import itertools, json, sys, collections

def run(sets, vals, picks):
    n = len(sets); m = 1 + max(max(s) for s in sets)
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]; R = [set(s) for s in sets]
    V = lambda i, S: sum(v[i].get(g, 0) for g in S)
    # strict + balanced
    for i, s in enumerate(sets):
        for A in range(1, 1 << len(s)):
            for B in range(1, 1 << len(s)):
                if A & B: continue
                a = sum(vals[i][p] for p in range(len(s)) if A >> p & 1); b = sum(vals[i][p] for p in range(len(s)) if B >> p & 1)
                assert A == B or a != b, ('not strict', i)
        assert 2 * max(vals[i]) < sum(vals[i]), ('not balanced', i)
    # SD orders
    def sd(o):
        taken = set(); Y = [None] * n
        for i in o:
            av = [g for g in sets[i] if g not in taken]
            if av: g = max(av, key=lambda g: v[i][g]); Y[i] = g; taken.add(g)
        return tuple(Y)
    orders = [o for o in itertools.permutations(range(n)) if sd(o) == tuple(picks)]
    # maximum matching size by brute force
    best = 0
    for choice in itertools.product(*[list(s) + [None] for s in sets]):
        c = [g for g in choice if g is not None]
        if len(c) == len(set(c)): best = max(best, len(c))
    npk = sum(p is not None for p in picks)
    # EFX0 allocations
    def efx0(B):
        for i in range(n):
            own = V(i, B[i])
            for j in range(n):
                if j == i: continue
                for h in B[j]:
                    if V(i, [g for g in B[j] if g != h]) > own: return False
        return True
    EF = []
    for X in itertools.product(range(n), repeat=m):
        B = [[g for g in range(m) if X[g] == a] for a in range(n)]
        if efx0(B): EF.append(X)
    base = [[p] if p is not None else [] for p in picks]
    # states: picks + one official move
    def states(base):
        held = {g for b in base for g in b}; J = [g for g in range(m) if g not in held]
        out = []
        sub = lambda xs: itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))
        for x in range(n):
            for H in sub([g for g in J if g in R[x]]):
                if H: nb = [list(b) for b in base]; nb[x] = base[x] + list(H); out.append(('add', nb))
        def ext(path, used, Hs):
            xt = path[-1]
            if len(path) >= 2:
                x0 = path[0]
                for H0 in sub([g for g in J if g not in used and g in R[x0]] + [g for g in base[xt] if g in R[x0]]):
                    if H0 and V(x0, H0) > V(x0, base[x0]):
                        nb = [list(b) for b in base]; nb[x0] = list(H0)
                        for t in range(1, len(path)): nb[path[t]] = base[path[t - 1]] + list(Hs[t])
                        out.append(('chain', nb))
            if len(path) >= n or not base[xt]: return
            for y in range(n):
                if y in path: continue
                for H in sub([g for g in J if g not in used and g in R[y]]):
                    if V(y, base[xt] + list(H)) > V(y, base[y]): ext(path + [y], used | set(H), Hs + [H])
        for x in range(n): ext([x], frozenset(), [()])
        for r in range(2, n + 1):
            for cyc in itertools.permutations(range(n), r):
                if cyc[0] != min(cyc): continue
                def ring(i, used, Hs):
                    if i == r:
                        nb = [list(b) for b in base]
                        for t in range(r): nb[cyc[t]] = base[cyc[t - 1]] + list(Hs[t])
                        out.append(('ring', nb)); return
                    w, pred = cyc[i], cyc[i - 1]
                    if not base[pred]: return
                    for H in sub([g for g in J if g not in used and g in R[w]]):
                        if V(w, base[pred] + list(H)) > V(w, base[w]): ring(i + 1, used | set(H), Hs + [H])
                ring(0, frozenset(), [])
        return out
    def completes(nb, X, absorbers):
        inb = {g: a for a, b in enumerate(nb) for g in b}
        if len(inb) != sum(len(b) for b in nb): return False
        if any(X[g] != a for g, a in inb.items()): return False
        cnt = collections.Counter(X[g] for g in range(m) if g not in inb)
        return absorbers is None or sum(c >= 2 for c in cnt.values()) <= absorbers
    sts = [('picks', base)] + states(base)
    res = {}
    for A in (1, None):
        res['one-absorber' if A == 1 else 'free'] = sorted(set(k for k, nb in sts if any(completes(nb, X, A) for X in EF)))
    return {'n': n, 'm': m, 'orders giving the picks': len(orders), 'example order': orders[0] if orders else None,
            'picks': npk, 'max matching (brute force)': best, 'EFX0 allocations': len(EF),
            'one-move states': len(sts) - 1,
            'states with a completion (kinds)': res,
            'picks complete one-absorber': any(completes(base, X, 1) for X in EF)}

if __name__ == '__main__':
    for line in sys.stdin:
        if not line.strip(): continue
        d = json.loads(line)
        print(json.dumps(d), '\n ->', json.dumps(run(d['sets'], d['vals'], d['picks'])), flush=True)
