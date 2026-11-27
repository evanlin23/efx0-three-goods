"""Conjecture RKMAX (rank-maximal start; k4/sdc.md §31 end, ledger K4.SDC.RKMAX, coordinator's branch) for EVERY strict
profile of one hypergraph, by ordinal CEGAR (k4/ksens.md §8; an extension of kcegar.py).

RKMAX: every maximum-matching SD pick vector Y whose rank signature sigma(Y) = (#rank 1, ..., #rank k) is
lexicographically maximal among the maximum-matching SD vectors satisfies OC1 (one-absorber completion at the picks or
after one improving chain, official rule).  rank_i = 1 + the number of i's relevant goods valued above its pick; agents
without a pick are not counted.

Outer SAT: kcegar's (bits, a maximum-matching SD start Y).  After each model, sigma-maximality of Y is checked in Python
over all n! orders under the model's singleton ranking.  If some order pi gives a maximum-matching vector Z with
sigma(Z) > sigma(Y), the cut is
    not(Y) or not(the singleton comparisons that fix SD(pi) = Z and the ranks of Y's and Z's picks)
(valid: every profile with those comparisons has SD(pi) = Z and the same ranks).  Otherwise kcegar's one-chain repair
search runs at Y; a repair witness is a cut; no repair = FAIL (a sigma-maximal maximum-matching start where OC1 fails),
re-checked by brute force (rf_replay.oc1).  --tops: sigma = (#rank 1) only, which the coordinator found fails at
k = 4 (a control for the FAIL path).

RKMAX can only fail where OC1^max fails, so at n = 3, k <= 5 only the 13 hypergraphs of kcegar_k5_n3_D1.log matter.

    python3 k4/ksens/rkcegar.py '[[sets]]'"""
import sys, json, itertools, time
import _paths
import kcegar


def sd_vals(R, vals, order):
    taken = set(); Y = [None] * len(R)
    for i in order:
        av = [g for g in R[i] if g not in taken]
        if av: g = max(av, key=lambda h: vals[i][h]); Y[i] = g; taken.add(g)
    return tuple(Y)


def sigma(R, vals, Y, k):
    s = [0] * k
    for i, g in enumerate(Y):
        if g is None: continue
        r = sum(1 for h in R[i] if vals[i][h] > vals[i][g])
        if r < k: s[r] += 1
    return tuple(s)


class RK(kcegar.Cegar):
    def __init__(self, sets, tops_only=False, **kw):
        super().__init__(sets, D=1, require_max=True, **kw)
        self.k = 1 if tops_only else max(len(r) for r in self.R)   # tops_only: sigma = (#rank 1,), a control

    def explain(self, vals, Y, order, Z):
        """the singleton literals (as in this profile) that fix SD(order) = Z and the ranks of Y's and Z's picks"""
        lits = set(); taken = set()
        for i in order:
            if Z[i] is None: continue
            for g in self.R[i]:
                if g != Z[i] and g not in taken: lits.add(self.cmp(i, (Z[i],), (g,)))
            taken.add(Z[i])
        for W in (Y, Z):
            for i, g in enumerate(W):
                if g is None: continue
                for h in self.R[i]:
                    if h != g: lits.add(self.cmp(i, (h,), (g,)) if vals[i][h] > vals[i][g] else self.cmp(i, (g,), (h,)))
        return lits

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
            vals = [ty[i] if self.LP[i] or self.G[i] else self.T[i][ty[i]] for i in range(self.n)]
            sY = sigma(self.R, vals, Y, self.k); best = None
            for o in itertools.permutations(range(self.n)):
                Z = sd_vals(self.R, vals, o)
                if sum(g is not None for g in Z) != self.nu: continue
                sZ = sigma(self.R, vals, Z, self.k)
                if sZ > sY and (best is None or sZ > best[0]): best = (sZ, o, Z)
            if best is not None:
                cl = [-self.p[i][Y[i]] if Y[i] is not None else -self.none[i] for i in range(self.n)]
                cl += [-l for l in self.explain(vals, Y, best[1], best[2])]
                self.S.add_clause([l for l in cl if l != -self.TRUE]); self.kinds['not sigma-maximal'] += 1; continue
            Q = self.inner(vals, Y)
            if Q is None: return 'FAIL', (vals, Y)
            cl = [-self.p[i][Y[i]] if Y[i] is not None else -self.none[i] for i in range(self.n)]
            cl += [-self.cmp(i, a, b) for i, a, b in set((i, frozenset(a), frozenset(b)) for i, a, b in Q)]
            self.S.add_clause([l for l in cl if l != -self.TRUE]); self.kinds['repaired'] += 1


def recheck(R, vals, Y):
    import brute, rf_replay
    from maxmatch import nu
    n = len(R); m = 1 + max(max(s) for s in R); vl = [[vals[i][g] for g in R[i]] for i in range(n)]
    I = brute.Inst(R, vl, m); v = nu(R, vl); k = max(map(len, R))
    vecs = set(tuple(I.sd(o)) for o in itertools.permutations(range(n)))
    mx = [Z for Z in vecs if sum(g is not None for g in Z) == v]
    top = max(sigma(R, vals, Z, k) for Z in mx)
    return {'vals': vl, 'Y': list(Y), 'Y an SD vector': tuple(Y) in vecs, 'Y maximum': tuple(Y) in mx,
            'sigma(Y)': sigma(R, vals, Y, k), 'max sigma': top, 'OC1 at Y': rf_replay.oc1(I, Y, n)}


if __name__ == '__main__':
    sets = json.loads(sys.argv[1]); C = RK(sets, tops_only='--tops' in sys.argv); t0 = time.time(); r, w = C.run()
    print(r, 'iterations', C.iters, dict(C.kinds), '%.1f s' % (time.time() - t0))
    if w: print(json.dumps(recheck(C.R, *w)))
