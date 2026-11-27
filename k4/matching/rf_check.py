"""Independent checker for receiver-first (RF) claims at a start (second checker for twin_hunt.py; K4.SDC.RF).
Self-contained: raw definitions only; it imports nothing from k4/ (the official moves are enumerated here as in
check_rec.py, following k4/sdc.md §29: junk grabs, chains from any agent whose agents take relevant junk, rings).

For an instance and a start P it decides, by brute force:
  - OC1 at a pick vector: a one-absorber completion at the picks, or after one official move (raw EFX0);
  - nu (maximum matching size), and whether P is a maximum-matching SD outcome;
  - the receivers of P, and for each receiver u every u-first order's pick vector: maximum or not, OC1 or not.

    python3 k4/matching/rf_check.py FILE.jsonl      (rows: sets, vals, start; e.g. FAIL lines of twin_hunt.py)"""
import sys, json, itertools, collections


class Inst:
    def __init__(self, sets, vals):
        self.n = len(sets); self.m = 1 + max(max(s) for s in sets)
        self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]; self.R = [set(s) for s in sets]

    def V(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def efx0(self, X):
        for i in range(self.n):
            own = self.V(i, X[i])
            for j in range(self.n):
                if j != i and X[j] and self.V(i, X[j]) - min(self.v[i].get(g, 0) for g in X[j]) > own: return False
        return True

    def sd(self, order):
        taken = set(); Y = [None] * self.n
        for i in order:
            av = [g for g in self.R[i] if g not in taken]
            if av: g = max(av, key=lambda h: (self.v[i][h], -h)); Y[i] = g; taken.add(g)
        return tuple(Y)


def nu(I):
    """Maximum matching size of the agent / relevant-good graph (brute force)."""
    def rec(i, taken):
        if i == I.n: return 0
        return max([rec(i + 1, taken)] + [1 + rec(i + 1, taken | {g}) for g in I.R[i] if g not in taken])
    return rec(0, frozenset())


def sub(xs): return itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))


def one_absorber(I, B):
    J = [g for g in range(I.m) if all(g not in b for b in B)]
    for o in range(I.n):
        others = [u for u in range(I.n) if u != o]
        for lab in itertools.product([o] + others, repeat=len(J)):
            if any(lab.count(u) > 1 for u in others): continue
            X = [list(b) for b in B]
            for g, a in zip(J, lab): X[a].append(g)
            if I.efx0(X): return True
    return False


def moves(I, B):
    n = I.n; J = [g for g in range(I.m) if all(g not in b for b in B)]; out = set()
    key = lambda nb: tuple(tuple(sorted(b)) for b in nb)
    for x in range(n):
        for H in sub([g for g in J if g in I.R[x]]):
            if H: nb = [list(b) for b in B]; nb[x] = list(B[x]) + list(H); out.add(key(nb))

    def ext(path, used, asg):
        xt = path[-1]
        if len(path) >= 2:
            pool = [g for g in J if g not in used and g in I.R[path[0]]] + [g for g in B[xt] if g in I.R[path[0]]]
            for H0 in sub(pool):
                if H0 and I.V(path[0], H0) > I.V(path[0], B[path[0]]):
                    nb = [list(b) for b in B]; nb[path[0]] = list(H0)
                    for i in range(1, len(path)): nb[path[i]] = list(B[path[i - 1]]) + list(asg[i])
                    out.add(key(nb))
        if len(path) >= n or not B[xt]: return
        for y in range(n):
            if y in path: continue
            for H in sub([g for g in J if g not in used and g in I.R[y]]):
                if I.V(y, list(B[xt]) + list(H)) > I.V(y, B[y]): ext(path + [y], used | set(H), {**asg, len(path): H})
    for x in range(n): ext([x], frozenset(), {})
    for r in range(2, n + 1):
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc): continue

            def ring(i, used, asg):
                if i == r:
                    nb = [list(b) for b in B]
                    for t in range(r): nb[cyc[t]] = list(B[cyc[t - 1]]) + list(asg[t])
                    out.add(key(nb)); return
                w, pred = cyc[i], cyc[i - 1]
                if not B[pred]: return
                for H in sub([g for g in J if g not in used and g in I.R[w]]):
                    if I.V(w, list(B[pred]) + list(H)) > I.V(w, B[w]): ring(i + 1, used | set(H), {**asg, i: H})
            ring(0, frozenset(), {})
    return [list(map(list, s)) for s in out]


def oc1(I, P):
    B = [[g] if g is not None else [] for g in P]
    return one_absorber(I, B) or any(one_absorber(I, s) for s in moves(I, B))


def report(sets, vals, start):
    I = Inst(sets, vals); n = I.n; N = nu(I); P = tuple(start)
    orders = [o for o in itertools.permutations(range(n)) if I.sd(o) == P]
    out = {'nu': N, 'start is an SD outcome': bool(orders), 'start is maximum': sum(x is not None for x in P) == N,
           'OC1 at the start': oc1(I, P)}
    rec = [u for u in range(n) if P[u] is not None and all(I.v[i].get(P[u], 0) <= I.v[i].get(P[i], 0) for i in range(n) if i != u)]
    out['receivers'] = rec; out['per receiver'] = {}
    for u in rec:
        vecs = {}
        for rest in itertools.permutations([i for i in range(n) if i != u]):
            p = I.sd((u,) + rest)
            if p not in vecs: vecs[p] = (sum(x is not None for x in p) == N)
        res = {json.dumps(list(p)): oc1(I, p) for p, mx in vecs.items() if mx}
        out['per receiver'][u] = {'u-first maximum vectors': len(res), 'with OC1': sum(res.values()),
                                  'every-form': bool(res) and all(res.values()), 'RF-exists': any(res.values()), 'detail': res}
    return out


if __name__ == '__main__':
    print('$ python3 k4/matching/rf_check.py', *sys.argv[1:])
    for l in open(sys.argv[1]):
        l = l.strip()
        if not l: continue
        if l.startswith('FAIL '): l = l[5:]
        r = json.loads(l)
        print(json.dumps({'sets': r['sets'], 'vals': r['vals'], 'start': r['start']}))
        print('   ', json.dumps(report(r['sets'], r['vals'], r['start'])))
