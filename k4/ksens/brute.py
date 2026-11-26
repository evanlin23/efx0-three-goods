"""Brute-force checker for SD-C, MD, OC, OC1 and one-absorber completions, written from the definitions only (no SAT,
no sdclib, no ocsat): k4/ksens.md.  For small instances (n^m up to a few million allocations).

- EFX0 (raw definition): for all i != j and every g in X_j, v_i(X_i) >= v_i(X_j minus g); computed as
  v_i(X_i) >= v_i(X_j) - min_{g in X_j} v_i(g) for nonempty X_j (the removal of the least valuable good is the worst
  case), vectorized over every complete allocation with numpy.
- serial dictatorship: own implementation (ties by smaller good index).
- improving chains: enumerated by depth-first search from the definition in k4/sdc.md §29, no bound on set sizes;
  an agent with an empty base may pass it on (as in ocsat.py).
- completion: a complete EFX0 allocation containing every new base; with A absorbers at most A agents hold two or more
  goods outside their base.

    python3 k4/ksens/brute.py '[[sets], [vals]]' [m] [order]   # every order (or the given one)
"""
import sys, json, itertools
import numpy as np


class Inst:
    def __init__(self, sets, vals, m=None):
        self.sets = [list(s) for s in sets]; self.n = len(sets)
        self.m = m or 1 + max(max(s) for s in sets if s)
        self.V = np.zeros((self.n, self.m), dtype=np.int64)
        for i, (s, v) in enumerate(zip(sets, vals)):
            for g, x in zip(s, v): self.V[i, g] = x
        self._all = None

    def val(self, i, S):
        return int(sum(self.V[i, g] for g in S))

    def efx0_list(self):
        """every complete EFX0 allocation, as an (N, m) array of owners"""
        if self._all is not None: return self._all
        n, m, V = self.n, self.m, self.V
        out = []; total = n ** m; CH = 1 << 18
        for lo in range(0, total, CH):
            idx = np.arange(lo, min(total, lo + CH), dtype=np.int64)
            own = np.empty((len(idx), m), dtype=np.int8); t = idx.copy()
            for g in range(m): own[:, g] = t % n; t //= n
            ok = np.ones(len(idx), dtype=bool)
            mine = np.zeros((len(idx), n), dtype=np.int64)
            for i in range(n): mine[:, i] = ((own == i) * V[i]).sum(1)
            for j in range(n):
                mask = own == j; nonempty = mask.any(1)
                for i in range(n):
                    if i == j: continue
                    tot = (mask * V[i]).sum(1)
                    mn = np.where(mask, V[i], np.iinfo(np.int64).max).min(1)
                    worst = np.where(nonempty, tot - mn, 0)
                    ok &= mine[:, i] >= worst
            out.append(own[ok])
        self._all = np.concatenate(out) if out else np.zeros((0, m), dtype=np.int8)
        return self._all

    def sd(self, order):
        left = set(range(self.m)); Y = [None] * self.n
        for i in order:
            av = [g for g in self.sets[i] if g in left and self.V[i, g] > 0]
            if av:
                g = sorted(av, key=lambda h: (-self.V[i, h], h))[0]; Y[i] = g; left.discard(g)
        return Y

    def chains(self, base):
        """every state (tuple of new bases, as frozensets) one improving chain reaches, t >= 0"""
        n = self.n; J = [g for g in range(self.m) if not any(g in b for b in base)]
        R = [set(g for g in s if self.V[i, g] > 0) for i, s in enumerate(self.sets)]
        out = set()

        def subsets(xs):
            for r in range(1, len(xs) + 1):
                yield from itertools.combinations(xs, r)

        def dfs(path, used, newb):
            # close the chain at path[-1]
            x0, xt = path[0], path[-1]
            pool = [g for g in J if g not in used and g in R[x0]]
            if len(path) > 1: pool += [g for g in base[xt] if g in R[x0]]
            for H0 in subsets(pool):
                nb0 = (set(base[x0]) if len(path) == 1 else set()) | set(H0)
                if self.val(x0, nb0) <= self.val(x0, base[x0]): continue
                st = dict(newb); st[x0] = frozenset(nb0)
                out.add(tuple(st.get(i, frozenset(base[i])) for i in range(n)))
            # extend: y takes base[xt] plus H from J
            for y in range(n):
                if y in path: continue
                free = [g for g in J if g not in used and g in R[y]]
                for r in range(0, len(free) + 1):
                    for H in itertools.combinations(free, r):
                        nby = set(base[xt]) | set(H)
                        if self.val(y, nby) <= self.val(y, base[y]): continue
                        nn = dict(newb); nn[y] = frozenset(nby)
                        dfs(path + [y], used | set(H), nn)

        for x in range(n): dfs([x], frozenset(), {})
        return out

    def rounds(self, base):
        """every state (tuple of new bases) one round reaches: any set of vertex-disjoint improving chains (each as in
        chains()), with pairwise disjoint junk sets, each head taking only junk and goods of its own chain's end, all
        applied at once (k4/ksens.md §6); includes the empty round"""
        n = self.n; J = frozenset(g for g in range(self.m) if not any(g in b for b in base))
        R = [set(g for g in s if self.V[i, g] > 0) for i, s in enumerate(self.sets)]
        def subsets(xs, lo=0):
            for r in range(lo, len(xs) + 1):
                yield from itertools.combinations(xs, r)
        def chain_list(avail, availJ):
            res = []
            def dfs(path, used, newb):
                x0, xt = path[0], path[-1]
                pool = sorted(g for g in availJ if g not in used and g in R[x0])
                if len(path) > 1: pool += [g for g in base[xt] if g in R[x0]]
                for H0 in subsets(pool, 1):
                    nb0 = (set(base[x0]) if len(path) == 1 else set()) | set(H0)
                    if self.val(x0, nb0) <= self.val(x0, base[x0]): continue
                    st = dict(newb); st[x0] = frozenset(nb0)
                    res.append((frozenset(path), st, used | (set(H0) & availJ)))
                for y in avail:
                    if y in path: continue
                    free = sorted(g for g in availJ if g not in used and g in R[y])
                    for H in subsets(free):
                        nby = set(base[xt]) | set(H)
                        if self.val(y, nby) <= self.val(y, base[y]): continue
                        nn = dict(newb); nn[y] = frozenset(nby)
                        dfs(path + [y], used | set(H), nn)
            for x in avail: dfs([x], frozenset(), {})
            return res
        out = set()
        def rec(avail, availJ, cur, last):
            out.add(tuple(cur.get(i, frozenset(base[i])) for i in range(n)))
            for agents, st, used in chain_list(avail, availJ):
                if min(agents) <= last: continue
                rec(avail - agents, availJ - used, {**cur, **st}, min(agents))
        rec(frozenset(range(n)), J, {}, -1)
        return out

    def completes(self, bases, A=None):
        """some complete EFX0 allocation keeps every base (and has at most A absorbers)"""
        L = self.efx0_list()
        ok = np.ones(len(L), dtype=bool)
        for i, b in enumerate(bases):
            for g in b: ok &= L[:, g] == i
        if not ok.any(): return False
        if A is None: return True
        L = L[ok]; inb = np.zeros(self.m, dtype=bool)
        for b in bases:
            for g in b: inb[g] = True
        big = np.zeros(len(L), dtype=np.int64)
        for i in range(self.n):
            big += (((L == i) & ~inb).sum(1) >= 2)
        return bool((big <= A).any())

    def completes_bt(self, bases, A=None):
        """the same question as completes(), by backtracking over the placement of the goods outside the bases
        (raw EFX0 definition, no enumeration of all n^m allocations); pruning: a pair (i, j) is dead when
        v_i(X_j) - min_{g in X_j} v_i(g) already exceeds v_i(X_i) plus everything i could still receive"""
        n, m, V = self.n, self.m, self.V
        X = [set(b) for b in bases]; inb = set(g for b in bases for g in b)
        J = [g for g in range(m) if g not in inb]
        junk = [0] * n
        def worst(i, j):
            if not X[j]: return 0
            vs = [int(V[i, g]) for g in X[j]]
            return sum(vs) - min(vs)
        def ok_final():
            for i in range(n):
                vi = self.val(i, X[i])
                for j in range(n):
                    if j != i and worst(i, j) > vi: return False
            return True
        def rec(k, rest_val):
            # rest_val[i]: value to i of the junk not yet placed
            for i in range(n):
                cap = self.val(i, X[i]) + rest_val[i]
                for j in range(n):
                    if j != i and worst(i, j) > cap: return False
            if k == len(J): return ok_final()
            g = J[k]; nrest = [rest_val[i] - int(V[i, g]) for i in range(n)]
            for a in range(n):
                if A is not None and junk[a] == 1 and sum(1 for b in range(n) if junk[b] >= 2) >= A: continue
                X[a].add(g); junk[a] += 1
                if rec(k + 1, nrest): X[a].discard(g); junk[a] -= 1; return True
                X[a].discard(g); junk[a] -= 1
            return False
        return rec(0, [sum(int(V[i, g]) for g in J) for i in range(n)])

    def dominated(self, Y):
        L = self.efx0_list(); ok = np.ones(len(L), dtype=bool)
        for i, g in enumerate(Y):
            t = self.V[i, g] if g is not None else 0
            ok &= ((L == i) * self.V[i]).sum(1) >= t
        return bool(ok.any())


def report(sets, vals, m=None, orders=None, A=1):
    I = Inst(sets, vals, m); out = {}
    for o in (orders if orders is not None else itertools.permutations(range(I.n))):
        Y = tuple(I.sd(o))
        if Y in out: continue
        base = [frozenset([g]) if g is not None else frozenset() for g in Y]
        r = {'order': tuple(o), 'md': I.dominated(Y), 'ext': I.completes(base), 'ext1': I.completes(base, A)}
        ch = I.chains(base) if not (r['ext'] and r['ext1']) else set()
        r['oc'] = r['ext'] or any(I.completes(s) for s in ch)
        r['oc1'] = r['ext1'] or any(I.completes(s, A) for s in ch)
        out[Y] = r
    return out, I


if __name__ == '__main__':
    sets, vals = json.loads(sys.argv[1])[:2]
    m = int(sys.argv[2]) if len(sys.argv) > 2 else None
    orders = [tuple(json.loads(sys.argv[3]))] if len(sys.argv) > 3 else None
    res, I = report(sets, vals, m, orders)
    print('EFX0 allocations', len(I.efx0_list()))
    for Y, r in res.items(): print(Y, r)
    print('SD-C', any(r['ext'] for r in res.values()), 'MD', all(r['md'] for r in res.values()),
          'OC', all(r['oc'] for r in res.values()), 'OC1', all(r['oc1'] for r in res.values()))
