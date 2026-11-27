"""Conjecture RF (receiver first; k4/sdc.md §31 end, on main) for EVERY strict profile of one hypergraph, by ordinal
CEGAR (k4/ksens.md §8; an extension of kcegar.py).

RF for a hypergraph: for every strict profile, every maximum-matching SD start Y where OC1 fails (no one-absorber
completion at the picks, nor after one improving chain, official rule), and every receiver u of Y (an agent with a pick
that no other agent values above its own pick; an agent without a pick prefers every good it values), every order with
u first whose SD picks Z form a maximum matching satisfies OC1.

Outer SAT: kcegar's variables for Y (comparison bits, picks, a strict total order, |Y| = nu), a second copy for Z (picks
p2, order before2, |Z| = nu), and a one-hot receiver u with
  - u holds a pick in Y, and for every other agent j valuing Y_u: j holds a pick h with v_j(h) > v_j(Y_u);
  - u is first in Z's order (before2(u, j) for all j; the SD clauses then give Z_u = u's top good).
Inner (no SAT): kcegar's one-chain repair search, first at Y, then at Z.  A repair witness (picks, comparisons) is added
as a cut on Y's pick variables AND on Z's (a repair of given bases under given comparisons does not depend on which
order produced them).  UNSAT = 'certified' (RF holds for every strict profile); otherwise a FAIL (profile, Y, Z, u),
re-checked by brute force from the definitions (rf_replay.py's oc1).

--any-receiver: drop the receiver constraint (u any agent with a pick in Y).  Not RF; a weaker-premise control that
must fail where some non-receiver-first order fails, to show the FAIL path works.

    python3 k4/ksens/rfcegar.py '[[sets]]' [--grid6=FILE --exact6] [--any-receiver]"""
import sys, json, itertools, time
import _paths
import kcegar
from pysat.card import CardEnc, EncType


class RF(kcegar.Cegar):
    def __init__(self, sets, any_receiver=False, **kw):
        super().__init__(sets, D=1, require_max=True, **kw)
        n = self.n; v = self.pool.id
        self.p2 = [{g: v(('p2', i, g)) for g in self.R[i]} for i in range(n)]
        self.none2 = [v(('none2', i)) for i in range(n)]
        for i in range(n): self._exactly_one(list(self.p2[i].values()) + [self.none2[i]])
        for g in range(self.m):
            lits = [self.p2[i][g] for i in range(n) if g in self.p2[i]]
            for a, b in itertools.combinations(lits, 2): self.S.add_clause([-a, -b])
        enc = CardEnc.equals(lits=[-x for x in self.none2], bound=self.nu, vpool=self.pool, encoding=EncType.seqcounter)
        for c in enc.clauses: self.S.add_clause(c)
        self.bf2 = {(a, b): v(('bf2', a, b)) for a, b in itertools.combinations(range(n), 2)}
        for a, b, c in itertools.permutations(range(n), 3):
            self.S.add_clause([-self.before2(a, b), -self.before2(b, c), self.before2(a, c)])
        self._sd(self.p2, self.none2, self.before2)
        # the receiver u
        self.u = [v(('u', i)) for i in range(n)]; self._exactly_one(self.u)
        for i in range(n):
            self.S.add_clause([-self.u[i], -self.none[i]])
            for j in range(n):
                if j != i: self.S.add_clause([-self.u[i], self.before2(i, j)])
            if any_receiver: continue
            for j in range(n):
                if j == i: continue
                for g in self.R[i]:
                    if g not in self.p[j]: continue          # j does not value g
                    self.S.add_clause([-self.u[i], -self.p[i][g], -self.none[j]])
                    for h in self.R[j]:
                        if h != g: self.S.add_clause([-self.u[i], -self.p[i][g], -self.p[j][h], self.cmp(j, (h,), (g,))])

    def before2(self, a, b):
        return self.bf2[(a, b)] if a < b else -self.bf2[(b, a)]

    def _sd(self, p, none, before):
        """kcegar's SD clauses for a pick system: every good i prefers to its pick (every good of R_i when i has none)
        is picked by an agent before i"""
        n = self.n
        for i in range(n):
            for h in self.R[i]:
                for g in self.R[i]:
                    if g == h: continue
                    c = self.cmp(i, (g,), (h,))
                    hold = [p[j][g] for j in range(n) if j != i and g in p[j]]
                    self.S.add_clause([-p[i][h], -c] + hold)
                    for j in range(n):
                        if j != i and g in p[j]: self.S.add_clause([-p[i][h], -c, -p[j][g], before(j, i)])
            for g in self.R[i]:
                hold = [p[j][g] for j in range(n) if j != i and g in p[j]]
                self.S.add_clause([-none[i]] + hold)
                for j in range(n):
                    if j != i and g in p[j]: self.S.add_clause([-none[i], -p[j][g], before(j, i)])

    def _cut(self, Y, Q):
        comps = [-self.cmp(i, a, b) for i, a, b in set((i, frozenset(a), frozenset(b)) for i, a, b in Q)]
        for p, none in ((self.p, self.none), (self.p2, self.none2)):
            cl = [-p[i][Y[i]] if Y[i] is not None else -none[i] for i in range(self.n)] + comps
            self.S.add_clause([l for l in cl if l != -self.TRUE])

    def run(self, time_limit=None, verbose=False):
        t0 = time.time()
        while True:
            if time_limit and time.time() - t0 > time_limit: return 'timeout', None
            if not self.S.solve(): return 'certified', None
            mdl = set(l for l in self.S.get_model() if l > 0)
            ty = self.realize(mdl)
            if ty is None: continue
            self.iters += 1
            Y = tuple(next((g for g, x in self.p[i].items() if x in mdl), None) for i in range(self.n))
            Z = tuple(next((g for g, x in self.p2[i].items() if x in mdl), None) for i in range(self.n))
            u = next(i for i in range(self.n) if self.u[i] in mdl)
            vals = [ty[i] if self.LP[i] or self.G[i] else self.T[i][ty[i]] for i in range(self.n)]
            Q = self.inner(vals, Y)
            if Q is not None: self._cut(Y, Q); self.kinds['Y repaired'] += 1; continue
            Q = self.inner(vals, Z)
            if Q is not None: self._cut(Z, Q); self.kinds['Z repaired'] += 1; continue
            return 'FAIL', (vals, Y, Z, u)


def recheck(R, vals, Y, Z, u, any_receiver=False):
    """brute force from the definitions: Y and Z are maximum-matching SD starts, Z from an order with u first, u a
    receiver of Y (unless any_receiver), and OC1 fails at both"""
    import brute, rf_replay
    from maxmatch import nu
    n = len(R); m = 1 + max(max(s) for s in R); vl = [[vals[i][g] for g in R[i]] for i in range(n)]
    I = brute.Inst(R, vl, m); v = nu(R, vl); val = lambda i, g: vals[i].get(g, 0)
    sdY = [o for o in itertools.permutations(range(n)) if tuple(I.sd(o)) == tuple(Y)]
    sdZ = [o for o in itertools.permutations(range(n)) if o[0] == u and tuple(I.sd(o)) == tuple(Z)]
    rec = Y[u] is not None and not any(j != u and val(j, Y[u]) > (val(j, Y[j]) if Y[j] is not None else 0) for j in range(n))
    return {'vals': vl, 'Y': list(Y), 'Z': list(Z), 'u': u, 'Y is an SD start': bool(sdY), 'Z from a u-first order': bool(sdZ),
            'maximum matchings': sum(g is not None for g in Y) == v == sum(g is not None for g in Z),
            'u a receiver of Y': rec, 'OC1 at Y': rf_replay.oc1(I, Y, n), 'OC1 at Z': rf_replay.oc1(I, Z, n)}


if __name__ == '__main__':
    sets = json.loads(sys.argv[1]); ar = '--any-receiver' in sys.argv
    C = RF(sets, any_receiver=ar, grid6=next((a[8:] for a in sys.argv if a.startswith('--grid6=')), None),
           grid_exact='--exact6' in sys.argv)
    t0 = time.time(); r, w = C.run()
    print(r, 'iterations', C.iters, dict(C.kinds), '%.1f s' % (time.time() - t0))
    if w: print(json.dumps(recheck(C.R, *w, any_receiver=ar)))
