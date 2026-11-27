"""c improving chains applied one after another, then a completion, in one SAT call (k4/ksens.md §4).

Layer t (t = 1..c) is one chain of k4/sdc.md §29 applied to the bases left by layer t - 1 (layer 0 = the start); a
layer may be empty, so 'at most c chains'.  Bases of layers >= 1 are variables ob[t][(g, i)].  Each layer's chain:
on/st/en/succ/position variables as in ocsat.py; x_i (i >= 1) takes the whole previous base of x_{i-1} plus junk it
values; x_0 takes junk and goods of x_t's base it values (t >= 1) or adds junk to its own base (t = 0); every chain agent
strictly gains (compared through subset indicator variables of the old and new base); the rest of x_t's base becomes
junk.  The completion: a complete EFX0 allocation (sdclib's clauses) containing the last layer's bases, free or with at
most A absorbers.  Written separately from ocsat.py's single-chain encoding, so the two cross-check each other at c = 1.

    python3 k4/ksens/ocseq.py '[[sets], [vals]]' ORDER C [A]
holds(..., multi=True): c rounds of vertex-disjoint chains instead of c chains (k4/ksens.md §6)."""
import sys, json, itertools
import _paths
from sdclib import Enc
from pysat.solvers import Cadical153
import ocsat


class Seq:
    def __init__(self, sets, vals, m):
        self.sets, self.vals, self.m = sets, vals, m
        self.E = E = Enc(sets, vals, m); self.n = E.n; self.top = E.top
        self.S = Cadical153(bootstrap_with=E.cl)
        for g in range(m): self.S.add_clause([-E.x[g][E.n]])
        self.R = [sorted(s) for s in sets]

    def new(self):
        self.top += 1; return self.top

    def v(self, i, S):
        return sum(self.E.v[i].get(g, 0) for g in S)

    def close(self):
        self.S.delete()

    def subset_vars(self, add, own, i):
        """exact indicators z[S] <-> (base of i inside R_i equals S); own(g, i) is a literal, True or False"""
        z = {}
        for S in ocsat.subsets(self.R[i]):
            lits = []; ok = True
            for g in self.R[i]:
                l = own(g, i)
                want = g in S
                if l is True or l is False:
                    if l != want: ok = False; break
                else:
                    lits.append(l if want else -l)
            if not ok: continue
            if not lits: z[S] = True; continue
            y = self.new(); z[S] = y
            for l in lits: add([-y, l])
            add([y] + [-l for l in lits])
        return z

    def layer(self, add, own, multi=False):
        """one (possibly empty) chain applied to the bases own(g, i), or with multi one round of vertex-disjoint
        chains (each head taking only from its own chain's end); returns the new-base function"""
        n, m = self.n, self.m; R = [set(r) for r in self.R]
        def lit(x):    # normalize own() output
            return x
        on = [self.new() for _ in range(n)]; st = [self.new() for _ in range(n)]; en = [self.new() for _ in range(n)]
        s = [[self.new() if j != i else None for j in range(n)] for i in range(n)]
        pos = [[self.new() for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if j == i: continue
                add([-s[i][j], on[i]]); add([-s[i][j], on[j]]); add([-s[i][j], -pos[i][n - 1]])
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
        root = None
        if not multi:
            for a, b in itertools.combinations(st, 2): add([-a, -b])
        else:      # root[i][a]: agent i lies on the chain that starts at a
            root = [[self.new() for a in range(n)] for i in range(n)]
            for i in range(n):
                add([-st[i], root[i][i]]); add([-on[i]] + root[i])
                for a, b in itertools.combinations(root[i], 2): add([-a, -b])
                for a in range(n):
                    add([-root[i][a], on[i]]); add([-root[i][a], st[a]])
                    for j in range(n):
                        if j != i: add([-s[i][j], -root[i][a], root[j][a]])
        # junk indicator of each good before the layer
        junk = {}
        for g in range(m):
            ls = [own(g, i) for i in range(n)]
            if any(l is True for l in ls): junk[g] = False; continue
            vs = [l for l in ls if l is not False]
            if not vs: junk[g] = True; continue
            jv = self.new(); junk[g] = jv
            for l in vs: add([-jv, -l])
            add([jv] + vs)
        nb = {}
        def cl_with(c, *ls):
            """add clause c extended by literals ls; True kills the clause, False drops the literal"""
            out = list(c)
            for l in ls:
                if l is True: return
                if l is False: continue
                out.append(l)
            add(out)
        for g in range(m):
            for i in range(n):
                b = self.new(); nb[(g, i)] = b
                # allowed reasons for b: (A) g in own base of i and (i off chain or i alone on its chain);
                # (B) g in base of j and s[j][i]; (C) g junk, i on chain, g in R_i;
                # (D) g in base of j, j = end with predecessor, i = start, g in R_i
                rs = []
                rA = self.new(); rs.append(rA)
                cl_with([-rA], own(g, i))
                add([-rA, -on[i], st[i]]); add([-rA, -on[i], en[i]])
                for j in range(n):
                    if j == i: continue
                    rB = self.new(); rs.append(rB)
                    cl_with([-rB], own(g, j)); add([-rB, s[j][i]])
                    if g in R[i]:
                        rD = self.new(); rs.append(rD)
                        cl_with([-rD], own(g, j)); add([-rD, en[j]]); add([-rD, -st[j]]); add([-rD, st[i]])
                        if root is not None: add([-rD, root[j][i]])
                if g in R[i]:
                    rC = self.new(); rs.append(rC)
                    cl_with([-rC], junk[g]); add([-rC, on[i]])
                add([-b] + rs)
                # forced: g stays with i when i is off the chain or alone; g passes along s[i][j]
                cl_with([on[i], b], -own(g, i) if own(g, i) not in (True, False) else (not own(g, i)))
                cl_with([-st[i], -en[i], b], -own(g, i) if own(g, i) not in (True, False) else (not own(g, i)))
                for j in range(n):
                    if j != i:
                        o = own(g, j)
                        cl_with([-s[j][i], b], -o if o not in (True, False) else (not o))
        for g in range(m):          # every good in at most one new base (only the last layer is tied to the allocation)
            for i in range(n):
                for j in range(i + 1, n): add([-nb[(g, i)], -nb[(g, j)]])
        newown = lambda g, i: nb[(g, i)]
        # strict gain of every chain agent
        for i in range(n):
            z0 = self.subset_vars(add, own, i); z1 = self.subset_vars(add, newown, i)
            for T, y in z0.items():
                tv = self.v(i, T)
                better = [l for S, l in z1.items() if self.v(i, S) > tv]
                if any(l is True for l in better): continue
                c = [-on[i]] + [l for l in better if l is not False]
                if y is not True: c.append(-y)
                add(c)
        return newown

    def holds(self, base, c, A=None, model=False, multi=False, cap=None):
        """some state c chains (or c rounds) reach has a completion; cap: instead count the distinct completed final
        allocations, up to cap (blocking clauses on the allocation variables)"""
        act = self.new(); cl = []
        add = lambda c_: cl.append(c_ + [-act])
        owner = {}
        for i, b in enumerate(base):
            for g in b: owner[g] = i
        own = lambda g, i, _o=owner: (_o.get(g) == i)
        for t in range(c): own = self.layer(add, own, multi)
        E = self.E
        for g in range(self.m):
            for i in range(self.n):
                l = own(g, i)
                if l is True: add([E.x[g][i]])
                elif l is not False: add([-l, E.x[g][i]])
        if A is not None:
            bigs = []
            for i in range(self.n):
                b = self.new(); bigs.append(b)
                for g, h in itertools.combinations(range(self.m), 2):
                    c1 = [-E.x[g][i], -E.x[h][i], b]
                    for q in (g, h):
                        l = own(q, i)
                        if l is True: c1 = None; break
                        if l is not False: c1.append(l)
                    if c1: add(c1)
            if A == 0:
                for b in bigs: add([-b])
            else:
                for comb in itertools.combinations(bigs, A + 1): add([-x for x in comb])
        for c_ in cl: self.S.add_clause(c_)
        if cap is not None:
            xs = [E.x[g][i] for g in range(self.m) for i in range(self.n)]; cnt = 0
            while cnt < cap and self.S.solve(assumptions=[act]):
                mdl = set(l for l in self.S.get_model() if l > 0)
                self.S.add_clause([-act] + [-l for l in xs if l in mdl]); cnt += 1
            self.S.add_clause([-act]); return cnt
        ok = self.S.solve(assumptions=[act])
        res = ok
        if ok and model:
            mdl = set(l for l in self.S.get_model() if l > 0)
            res = [[g for g in range(self.m) if E.x[g][i] in mdl] for i in range(self.n)]
        self.S.add_clause([-act])
        return res


def least(sets, vals, m, order, cmax, A=None):
    Q = Seq(sets, vals, m); Y = ocsat.sd(sets, vals, order, m); b = ocsat.bases_of(Y, len(sets))
    for c in range(cmax + 1):
        if Q.holds(b, c, A): Q.close(); return c
    Q.close(); return None


if __name__ == '__main__':
    sets, vals = json.loads(sys.argv[1])[:2]; order = tuple(json.loads(sys.argv[2])); C = int(sys.argv[3])
    A = int(sys.argv[4]) if len(sys.argv) > 4 else None
    m = 1 + max(max(s) for s in sets)
    print('least number of chains (at most %d tried):' % C, least(sets, vals, m, order, C, A))
