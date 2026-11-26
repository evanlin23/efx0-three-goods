"""One SAT call per start for SD-C, MD, OC and OC1 at any k (k4/ksens.md).

Instance: sets[i] (agent i's relevant goods), vals[i] (values, same order), m goods; any number of relevant goods per
agent.  The EFX0 clauses are sdclib's (k4/sdc/sdclib.py, Enc); everything else is written here from the definitions of
k4/sdc.md §2, §28, §29:

- start: the serial-dictatorship picks Y = SD(pi) of an order pi (ties by good index, as sdc_orders.sd);
- bases: agent i's base is {Y_i} (empty if it picked nothing); J = the goods nobody picked (junk);
- improving chain: distinct agents x_0, ..., x_t (t >= 0), disjoint H_0 inside J + B_{x_t} (t >= 1) or J (t = 0),
  H_i inside J (i >= 1), each H_i inside R_{x_i}; x_0's new base is H_0 (t >= 1) or B_{x_0} + H_0 (t = 0), x_i's new
  base is B_{x_{i-1}} + H_i, and every agent of the chain strictly gains; the rest of B_{x_t} becomes junk;
- completion: a complete EFX0 allocation X with every new base inside its holder's bundle; 'free' (any junk anywhere)
  or with at most A absorbers (agents holding two or more goods outside their base).

One solver per instance holds the EFX0 clauses; each start adds its chain clauses under an activation literal, so the
solver keeps what it learned across starts.  Unlike k4/sdc/de_free.py, set sizes are not bounded (no DF_HMAX/DF_BMAX),
and an agent with an empty base may pass it on (both allowed by the definition); EMPTY_PASS = False restores de_free's
restriction.

    python3 k4/ksens/ocsat.py '[[sets], [vals]]'        # report SD-C, MD, OC, OC1 on every order
"""
import sys, json, itertools
import _paths
from sdclib import Enc
from pysat.solvers import Cadical153

EMPTY_PASS = True


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


def sd(sets, vals, order, m):
    """serial-dictatorship picks (None = nothing left), ties broken by smaller good index"""
    left = set(range(m)); Y = [None] * len(sets)
    for i in order:
        av = [(vals[i][k], -g, g) for k, g in enumerate(sets[i]) if g in left]
        if av:
            g = max(av)[2]; Y[i] = g; left.discard(g)
    return Y


def starts(sets, vals, m, orders=None):
    """distinct pick vectors over all orders (or the given ones): dict picks -> first order giving them"""
    n = len(sets); res = {}
    for o in (orders if orders is not None else itertools.permutations(range(n))):
        Y = tuple(sd(sets, vals, o, m))
        res.setdefault(Y, tuple(o))
    return res


class OC:
    def __init__(self, sets, vals, m):
        self.sets, self.vals, self.m = sets, vals, m
        self.E = E = Enc(sets, vals, m)
        self.n = E.n; self.top = E.top
        self.S = Cadical153(bootstrap_with=E.cl)
        for g in range(m): self.S.add_clause([-E.x[g][E.n]])     # complete
        self.calls = 0

    def new(self):
        self.top += 1; return self.top

    def v(self, i, S):
        return sum(self.E.v[i].get(g, 0) for g in S)

    def close(self):
        self.S.delete()

    # ------------------------------------------------------------------ per-start clause group
    def group(self, base, chain='any', A=None, md=False):
        """add the clauses of one question under a fresh activation literal; returns (act, nb) with nb[(g, i)] the
        new-base variables.  base: list of goods per agent (the start).  chain: 'none' | 'any' | 'need' (exactly one
        chain, possibly t = 0).  A: None (free completion) or the absorber bound.  md: add value domination of the
        start (v_i(X_i) >= v_i(base_i)) instead of keeping bases (then chain must be 'none')."""
        E = self.E; n, m = self.n, self.m; act = self.new(); cl = []
        add = lambda c: cl.append(c + [-act])
        if md:
            for i in range(n):
                t = self.v(i, base[i])
                add([y for S, y in E.y[i].items() if self.v(i, S) >= t])
            for c in cl: self.S.add_clause(c)
            return act, {}
        owner = [-1] * m
        for i in range(n):
            for g in base[i]: owner[g] = i
        R = [set(s) for s in self.sets]
        on = [self.new() for _ in range(n)]; st = [self.new() for _ in range(n)]; en = [self.new() for _ in range(n)]
        s = [[self.new() if j != i else None for j in range(n)] for i in range(n)]
        pos = [[self.new() for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if j == i: continue
                add([-s[i][j], on[i]]); add([-s[i][j], on[j]]); add([-s[i][j], -pos[i][n - 1]])
                if not base[i] and not EMPTY_PASS: add([-s[i][j]])
                for p in range(n - 1): add([-s[i][j], -pos[i][p], pos[j][p + 1]])
            succ = [s[i][j] for j in range(n) if j != i]; pred = [s[j][i] for j in range(n) if j != i]
            for a, b in itertools.combinations(succ, 2): add([-a, -b])
            for a, b in itertools.combinations(pred, 2): add([-a, -b])
            add([-st[i], on[i]]); add([-en[i], on[i]])
            for l in pred: add([-st[i], -l])
            for l in succ: add([-en[i], -l])
            add([-on[i], st[i]] + pred); add([-on[i], en[i]] + succ)
            add([-on[i]] + pos[i]); add([-st[i], pos[i][0]])
            for a, b in itertools.combinations(pos[i], 2): add([-a, -b])
        for a, b in itertools.combinations(st, 2): add([-a, -b])
        if chain == 'none':
            for i in range(n): add([-on[i]])
        elif chain == 'need':
            add(list(on))
        nb = {}
        for g in range(m):
            j = owner[g]
            for i in range(n):
                if j < 0 and g not in R[i]: continue
                nb[(g, i)] = l = self.new(); add([-l, E.x[g][i]])
                if j < 0:
                    add([-l, on[i]])
                elif i == j:
                    add([on[j], l]); add([-st[j], -en[j], l]); add([-l, -on[j], st[j]]); add([-l, -on[j], en[j]])
                else:
                    add([-s[j][i], l])
                    if g in R[i]:
                        add([-l, s[j][i], st[i]]); add([-l, s[j][i], en[j]]); add([-l, s[j][i], -st[j]])
                    else:
                        add([-l, s[j][i]])
        # improvement of every chain agent
        for i in range(n):
            t = self.v(i, base[i]); zs = []
            for S in subsets(sorted(R[i])):
                if self.v(i, S) <= t or any((g, i) not in nb for g in S): continue
                z = self.new(); zs.append(z)
                for g in R[i]:
                    if (g, i) in nb: add([-z, nb[(g, i)] if g in S else -nb[(g, i)]])
            add([-on[i]] + zs)
        # absorbers
        if A is not None:
            bigs = []
            for i in range(n):
                b = self.new(); bigs.append(b)
                jk = [(g, nb.get((g, i))) for g in range(m)]
                for (g, a), (h, c) in itertools.combinations(jk, 2):
                    c1 = [-E.x[g][i], -E.x[h][i], b]
                    if a: c1.append(a)
                    if c: c1.append(c)
                    add(c1)
            if A == 0:
                for b in bigs: add([-b])
            else:
                aux = []                                   # sequential counter: at most A of bigs
                prev = None
                for k, b in enumerate(bigs):
                    row = [self.new() for _ in range(A)]
                    add([-b, row[0]])
                    if prev is not None:
                        for r in range(A):
                            add([-prev[r], row[r]])
                        for r in range(1, A):
                            add([-b, -prev[r - 1], row[r]])
                        add([-b, -prev[A - 1]])
                    prev = row
        for c in cl: self.S.add_clause(c)
        return act, nb

    def retire(self, act):
        self.S.add_clause([-act])

    def holds(self, base, chain='any', A=None, md=False, model=False):
        act, nb = self.group(base, chain, A, md)
        self.calls += 1
        ok = self.S.solve(assumptions=[act])
        res = ok
        if ok and model:
            mdl = set(l for l in self.S.get_model() if l > 0)
            X = [[g for g in range(self.m) if self.E.x[g][i] in mdl] for i in range(self.n)]
            newb = [[g for g in range(self.m) if (g, i) in nb and nb[(g, i)] in mdl] for i in range(self.n)]
            res = (X, newb)
        self.retire(act)
        return res

    def count(self, base, chain='need', A=None, cap=20):
        """number of distinct new-base vectors (states one chain reaches) that have a completion, up to cap"""
        act, nb = self.group(base, chain, A)
        keys = sorted(nb); lits = [nb[k] for k in keys]; c = 0
        while c < cap:
            self.calls += 1
            if not self.S.solve(assumptions=[act]): break
            mdl = set(l for l in self.S.get_model() if l > 0)
            self.S.add_clause([-act] + [-l if l in mdl else l for l in lits]); c += 1
        self.retire(act)
        return c


def bases_of(Y, n):
    return [[g] if g is not None else [] for g in Y]


def report(sets, vals, m=None, orders=None, A=1):
    """per distinct start: md, sdc (picks extend), oc (free, <= 1 chain), oc1 (A absorbers, <= 1 chain)"""
    m = m or 1 + max(max(s) for s in sets)
    O = OC(sets, vals, m); out = {}
    for Y, o in starts(sets, vals, m, orders).items():
        b = bases_of(Y, len(sets))
        r = {'order': o}
        r['md'] = O.holds(b, md=True)
        r['ext'] = O.holds(b, chain='none')
        r['oc'] = r['ext'] or O.holds(b, chain='need')
        r['ext1'] = O.holds(b, chain='none', A=A)
        r['oc1'] = r['ext1'] or O.holds(b, chain='need', A=A)
        out[Y] = r
    O.close()
    return out


if __name__ == '__main__':
    sets, vals = json.loads(sys.argv[1])[:2]
    res = report(sets, vals)
    for Y, r in res.items(): print(Y, r)
    print('SD-C', any(r['ext'] for r in res.values()), 'MD', all(r['md'] for r in res.values()),
          'OC', all(r['oc'] for r in res.values()), 'OC1', all(r['oc1'] for r in res.values()))
