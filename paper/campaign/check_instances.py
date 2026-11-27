"""Independent re-check of the instances printed in paper/campaign/draft.md (Appendix C).

Written by the paper/campaign session from the draft's own tables and definitions (draft §2.4); it imports nothing from
the repository and uses no SAT.  Every claim marked with a dagger in the draft is re-checked here from the printed data,
so a transcription error in the draft would show up as a failed assertion.

Method.  For an instance, enumerate every complete EFX0 allocation once (backtracking over goods; prune when a threat
toward some bundle already exceeds what the threatened agent could still reach).  A state reached from SD picks by one
move (addition, improving chain, ring; draft §2.4) has a completion X iff X satisfies the placement and gain conditions
of that move with the largest possible junk sets H (Lemma R of kgen/n3.md §2: enlarging H by goods its receiver values
keeps the gains and only shrinks the goods outside the bases).  So every claim "no state one move reaches has a
(one-absorber / free) EFX0 completion" is a check over the list of EFX0 allocations.

    python3 paper/campaign/check_instances.py            # all checks (about a minute)
    python3 paper/campaign/check_instances.py quick      # skip B< (n = 6, m = 10), the slowest
"""
import itertools
import random
import sys
import time


class Inst:
    def __init__(self, vals, m=None):
        self.v = [dict(d) for d in vals]
        self.n = len(vals)
        self.m = m if m is not None else 1 + max(g for d in vals for g in d)
        self.R = [set(g for g, x in d.items() if x > 0) for d in self.v]

    def val(self, i, S):
        return sum(self.v[i].get(g, 0) for g in S)

    def efx0(self, X, pool_ok=True):
        """Raw EFX0 over the bundles X (a list of sets); goods not in any bundle are ignored (partial allocation)."""
        for i in range(self.n):
            own = self.val(i, X[i])
            for j in range(self.n):
                if i != j and X[j]:
                    if self.val(i, X[j]) - min(self.v[i].get(h, 0) for h in X[j]) > own:
                        return False
        return True

    def sd(self, order):
        taken, picks = set(), [None] * self.n
        for i in order:
            best = None
            for g in sorted(self.R[i]):
                if g not in taken and (best is None or self.v[i][g] > self.v[i][best]):
                    best = g
            picks[i] = best
            if best is not None:
                taken.add(best)
        return tuple(picks)

    def all_efx0(self):
        """Every complete EFX0 allocation, as a tuple owner[g]."""
        n, m, v = self.n, self.m, self.v
        goods = sorted(range(m), key=lambda g: -max(v[i].get(g, 0) for i in range(n)))
        val = [[0] * n for _ in range(n)]          # val[i][j] = v_i(X_j)
        mn = [[None] * n for _ in range(n)]        # mn[i][j] = min_{g in X_j} v_i(g), None if X_j empty
        rem = [sum(v[i].get(g, 0) for g in range(m)) for i in range(n)]
        owner = [None] * m
        out = []

        def ok():
            for i in range(n):
                cap = val[i][i] + rem[i]
                for j in range(n):
                    if j != i and mn[i][j] is not None and val[i][j] - mn[i][j] > cap:
                        return False
            return True

        def rec(k):
            if k == m:
                out.append(tuple(owner))
                return
            g = goods[k]
            for a in range(n):
                saved = [(i, val[i][a], mn[i][a]) for i in range(n)]
                for i in range(n):
                    x = v[i].get(g, 0)
                    val[i][a] += x
                    mn[i][a] = x if mn[i][a] is None else min(mn[i][a], x)
                    rem[i] -= x
                owner[g] = a
                if ok():
                    rec(k + 1)
                for i, a1, a2 in saved:
                    val[i][a] = a1
                    mn[i][a] = a2
                    rem[i] += v[i].get(g, 0)
                owner[g] = None

        rec(0)
        return out

    def bundles(self, owner):
        X = [set() for _ in range(self.n)]
        for g, a in enumerate(owner):
            X[a].add(g)
        return X

    # ---- moves from SD picks (draft §2.4), checked against a complete allocation X ----
    def structures(self, picks, glued=False):
        """Every one-move structure: ('pick',), ('add', x), ('chain', path), ('ring', cycle).  With glued=True a
        chain may also pass an empty base (the literal wording of k4/sdc.md §29; not a move of draft §2.4)."""
        n = self.n
        yield ('pick',)
        for x in range(n):
            if picks[x] is not None:
                yield ('add', x)
        for L in range(2, n + 1):
            for path in itertools.permutations(range(n), L):
                if glued or all(picks[a] is not None for a in path[:-1]):   # passed bases are nonempty
                    yield ('chain', path)
                if path[0] == min(path) and all(picks[a] is not None for a in path):
                    yield ('ring', path)

    def fits(self, picks, X, st, one_absorber):
        """Does X complete the state reached from picks by structure st (largest junk sets)?"""
        n, v, R = self.n, self.v, self.R
        J = set(range(self.m)) - set(p for p in picks if p is not None)
        base = [set() if p is None else {p} for p in picks]
        kind = st[0]
        on = set()
        if kind == 'add':
            x = st[1]
            H = X[x] & J & R[x]
            if not H:
                return False
            base[x] = {picks[x]} | H
            on = {x}
        elif kind == 'chain':
            path = st[1]
            x0, xt = path[0], path[-1]
            pool0 = J | ({picks[xt]} if picks[xt] is not None else set())
            H0 = X[x0] & pool0 & R[x0]
            if not self.val(x0, H0) > self.val(x0, base[x0]):
                return False
            newb = {x0: H0}
            for a, b in zip(path, path[1:]):
                if not base[a] <= X[b]:
                    return False
                Hb = X[b] & J & R[b]
                if not self.val(b, base[a] | Hb) > self.val(b, base[b]):
                    return False
                newb[b] = base[a] | Hb
            for a, B in newb.items():
                base[a] = B
            on = set(path)
        elif kind == 'ring':
            cyc = st[1]
            newb = {}
            for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                if picks[a] not in X[b]:
                    return False
                Hb = X[b] & J & R[b]
                if not self.val(b, {picks[a]} | Hb) > self.val(b, base[b]):
                    return False
                newb[b] = {picks[a]} | Hb
            for a, B in newb.items():
                base[a] = B
            on = set(cyc)
        for a in range(n):
            if a not in on and picks[a] is not None and picks[a] not in X[a]:
                return False
            if not base[a] <= X[a]:
                return False
        if one_absorber:
            if sum(1 for a in range(n) if len(X[a] - base[a]) >= 2) > 1:
                return False
        return True

    def verdict(self, picks, allocs, one_absorber, kinds=('pick', 'add', 'chain', 'ring'), glued=False):
        """'picks' if the picks complete, 'move' if one move repairs, 'fails' otherwise."""
        Xs = [self.bundles(o) for o in allocs]
        sts = [st for st in self.structures(picks, glued) if st[0] in kinds]
        if any(self.fits(picks, X, ('pick',), one_absorber) for X in Xs):
            return 'picks'
        if any(self.fits(picks, X, st, one_absorber) for X in Xs for st in sts if st[0] != 'pick'):
            return 'move'
        return 'fails'

    # ---- core conditions (draft §2.2) ----
    def core_failures(self):
        f = []
        n = self.n
        for i in range(n):
            Ri, tot = self.R[i], self.val(i, self.R[i])
            P = [g for g in Ri if all(g not in self.R[j] for j in range(n) if j != i)]
            S = [g for g in Ri if g not in P]
            if not 3 <= len(Ri) <= 4: f.append('C1 %d' % i)
            if any(2 * self.v[i][g] >= tot for g in Ri): f.append('C2 %d' % i)
            if len(P) + 2 > len(Ri): f.append('C3 %d' % i)
            if len(P) == 2 and not self.val(i, P) < self.val(i, S): f.append('C4 %d' % i)
            sums = {}
            for r in range(1, len(Ri) + 1):
                for T in itertools.combinations(sorted(Ri), r):
                    sums.setdefault(self.val(i, T), []).append(set(T))
            if any(not (a & b) for L in sums.values() for a, b in itertools.combinations(L, 2)):
                f.append('tie %d' % i)
        if set().union(*self.R) != set(range(self.m)): f.append('C5')
        comp, grow = {0}, True
        while grow:
            grow = False
            for j in range(n):
                if j not in comp and any(self.R[j] & self.R[i] for i in comp):
                    comp.add(j); grow = True
        if len(comp) < n: f.append('disconnected')
        return f

    def private(self):
        return {i: sorted(g for g in self.R[i] if all(g not in self.R[j] for j in range(self.n) if j != i))
                for i in range(self.n)}

    def nu(self):
        """Maximum matching size of the incidence graph (augmenting paths)."""
        match = {}

        def aug(i, seen):
            for g in self.R[i]:
                if g not in seen:
                    seen.add(g)
                    if g not in match or aug(match[g], seen):
                        match[g] = i
                        return True
            return False
        return sum(1 for i in range(self.n) if aug(i, set()))


def from_sets(sets, vals):
    return Inst([dict(zip(s, x)) for s, x in zip(sets, vals)])


def report(name, ok, detail=''):
    print('%-62s %s %s' % (name, 'OK' if ok else 'FAILED', detail))
    if not ok:
        report.failed += 1
report.failed = 0


# ---------------------------------------------------------------------------------------------------------------
def check_pareto_stuck(name, I, X, out_good, n_complete):
    """Props 7.1, 7.2: X is partial EFX0; out_good cannot be added; no partial EFX0 allocation dominates X; every
    complete EFX0 allocation leaves some agent below its value in X; the number of complete ones."""
    n, m = I.n, I.m
    uX = [I.val(i, X[i]) for i in range(n)]
    report(name + ': X is partial EFX0', I.efx0(X))
    fits = []
    for a in range(n):
        Y = [set(b) for b in X]; Y[a].add(out_good)
        fits.append(I.efx0(Y))
    report(name + ': the left-out good fits in no bundle', not any(fits))
    dom, complete, complete_below = 0, 0, 0
    for asg in itertools.product(range(n + 1), repeat=m):     # n = pool
        Y = [set() for _ in range(n)]
        for g, a in enumerate(asg):
            if a < n: Y[a].add(g)
        if not I.efx0(Y):
            continue
        u = [I.val(i, Y[i]) for i in range(n)]
        alloc = sum(len(b) for b in Y)
        if all(u[i] >= uX[i] for i in range(n)) and (any(u[i] > uX[i] for i in range(n)) or alloc > m - 1):
            dom += 1
        if alloc == m:
            complete += 1
            if any(u[i] < uX[i] for i in range(n)):
                complete_below += 1
    report(name + ': no partial EFX0 allocation dominates X', dom == 0, '(dominating: %d)' % dom)
    report(name + ': complete EFX0 allocations, each below X for someone', complete == n_complete == complete_below,
           '(%d complete, %d below)' % (complete, complete_below))


def check_two_agent_construction(trials=20000, seed=1):
    """Theorem 3.4 as transcribed in the draft: steps 0-2, LPT cut (Fact 3.1), Lemma 3.2, Tops Lemma; EFX0 and shape."""
    rnd = random.Random(seed)

    def favourite(v, goods):
        best = None
        for g in sorted(goods):
            if v[g] > 0 and (best is None or v[g] > v[best]):
                best = g
        return best

    def lpt(v, goods):
        P, Q = [], []
        for g in sorted(goods, key=lambda g: (-v[g], g)):
            (P if sum(v[h] for h in P) <= sum(v[h] for h in Q) else Q).append(g)
        return P, Q

    def efx0_2(v, X):
        for i in (0, 1):
            j = 1 - i
            if X[j] and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > sum(v[i][g] for g in X[i]):
                return False
        return True

    def construct(va, vb, M):
        ya = favourite(va, M)
        if ya is None:
            return (set(), set(M)), 'D'
        if all(vb[g] == 0 for g in M):
            return (set(M), set()), 'D'
        yb = favourite(vb, [g for g in M if g != ya])
        if yb is None:
            if va[ya] >= sum(va[g] for g in M if g != ya):
                return ({ya}, set(M) - {ya}), 'D'
            return (set(M) - {ya}, {ya}), 'D'
        if vb[ya] > vb[yb]:
            P, Q = lpt(vb, M)
            assert ya in P and yb in Q
            Xa, Xb = (set(P), set(Q)) if sum(va[g] for g in P) >= sum(va[g] for g in Q) else (set(Q), set(P))
        else:
            J = [g for g in M if g not in (ya, yb)]
            P, Q = lpt(vb, J)
            Xa, Xb = (set(P), set(Q)) if sum(va[g] for g in P) >= sum(va[g] for g in Q) else (set(Q), set(P))
            Xa.add(ya); Xb.add(yb)
        W = {g for g in Xa if va[g] == 0}
        Xa -= W; Xb |= W                                        # Lemma 3.2
        if ya in Xa and yb in Xb:
            J = set(M) - {ya, yb}
            assert Xa - {ya} <= J and all(va[g] > 0 for g in Xa - {ya})
            return (Xa, Xb), 'A1'
        assert ya in Xb and vb[ya] > vb[yb] and sum(va[g] for g in Xa) > va[ya]
        assert Xa <= set(M) - {ya} and all(va[g] > 0 for g in Xa)
        return (Xa, Xb), 'B'

    shapes = {}
    bad = 0
    for t in range(trials):
        m = rnd.randint(1, 12)
        kind = t % 4
        def draw():
            if kind == 0: return rnd.randint(1, 100)
            if kind == 1: return rnd.randint(0, 3)
            if kind == 2: return rnd.choice([0, 0, rnd.randint(1, 20)])
            return rnd.choice([0, 5, 5, 7])
        va = [draw() for _ in range(m)]; vb = [draw() for _ in range(m)]
        for (v1, v2) in ((va, vb), (vb, va)):                 # both orders
            X, s = construct(v1, v2, list(range(m)))
            shapes[s] = shapes.get(s, 0) + 1
            if not (efx0_2([v1, v2], X) and X[0] | X[1] == set(range(m)) and not (X[0] & X[1])):
                bad += 1
    report('Theorem 3.4 construction: EFX0, complete, shape (A1/B/D), %d starts' % (2 * trials), bad == 0,
           str(sorted(shapes.items())))


def main(quick=False):
    t0 = time.time()
    print('# paper/campaign/check_instances.py: independent checks of the draft\'s printed instances')
    check_two_agent_construction()

    # Prop 4.5 (CH-F, k = 4): the stranded state
    V4 = [{0: 20, 6: 21, 8: 40}, {0: 12, 7: 16, 9: 27}, {2: 20, 6: 21, 10: 40}, {2: 12, 7: 13, 11: 24},
          {4: 20, 6: 21, 12: 40}, {4: 9, 7: 10, 13: 18}, {0: 2, 1: 1, 12: 7, 13: 4}, {2: 2, 3: 1, 8: 5, 9: 4},
          {4: 2, 5: 1, 10: 8, 11: 4}]
    X4 = [{8}, {9}, {10}, {11}, {12}, {13}, {0, 1}, {2, 3}, {4, 5}]
    I = Inst(V4, 14)
    ok = (all(len(I.R[i]) <= 4 for i in range(I.n)) and I.efx0(X4)
          and all(I.val(i, {6, 7}) <= I.val(i, X4[i]) for i in range(I.n))
          and sum(I.val(i, X4[i]) for i in range(I.n)) == 198 and set().union(*X4) == set(range(14)) - {6, 7})
    report('Prop 4.5 (CH-F, k = 4): state EFX0, strong charity, total 198', ok)

    # Prop 7.1 (GM4-E)
    I = Inst([{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}])
    report('Prop 7.1 (GM4-E): strict connected k = 4 core', I.core_failures() == [], str(I.core_failures()))
    check_pareto_stuck('Prop 7.1 (GM4-E)', I, [{0, 4}, {1, 3}, {2}, {5}], 6, 15)

    # Prop 7.2 (S'(2, 3))
    I = Inst([{5: 10, 0: 6, 4: 6}, {6: 10, 2: 6, 4: 6}, {6: 5, 0: 2, 1: 2}, {5: 5, 2: 2, 3: 2}])
    report("Prop 7.2 (S'(2,3)): every agent values exactly three goods", all(len(R) == 3 for R in I.R))
    check_pareto_stuck("Prop 7.2 (S'(2,3))", I, [{5}, {6}, {0, 1}, {2, 3}], 4, 58)

    # Prop 7.3 (b): the MC2-class core
    I = from_sets([[0, 3, 6, 8], [1, 4, 7, 6], [2, 5, 8, 7], [0, 1, 2], [0, 1, 2]],
                  [[10, 6, 5, 7], [10, 6, 5, 7], [10, 6, 5, 7], [4, 3, 2], [2, 4, 3]])
    pv = I.private()
    report('Prop 7.3(b): strict connected core, MC2 class (<= 1 private good each)',
           I.core_failures() == [] and all(len(p) <= 1 for p in pv.values()), str(pv))
    allocs = I.all_efx0()
    picks = I.sd(range(5))
    report('Prop 7.3(b): order 0..4 picks (0, 1, 2, -, -)', picks == (0, 1, 2, None, None))
    report('Prop 7.3(b): no free completion at the picks or after one move',
           I.verdict(picks, allocs, one_absorber=False) == 'fails', '(%d EFX0 allocations)' % len(allocs))
    nu = I.nu()
    cnt = {}
    for o in itertools.permutations(range(5)):
        p = I.sd(o)
        key = ('max' if sum(x is not None for x in p) == nu else 'non-max', I.verdict(p, allocs, False))
        cnt[key] = cnt.get(key, 0) + 1
    report('Prop 7.3(b): OC fails for 12 of 120 orders; all 50 max orders complete at picks',
           cnt.get(('non-max', 'fails'), 0) == 12 and cnt.get(('max', 'picks'), 0) == 50
           and sum(c for (k, _), c in cnt.items() if k == 'max') == 50, str(sorted(cnt.items())))

    # Prop 7.5 (PW5)
    I = from_sets([[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
                  [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]])
    allocs = I.all_efx0()
    picks = I.sd(range(5))
    report('Prop 7.5 (PW5): 5-limited; order x1,x2,x3,w1,w2 picks every agent',
           all(len(R) <= 5 for R in I.R) and picks == (0, 1, 2, 3, 4) and I.nu() == 5)
    report('Prop 7.5 (PW5): 186 complete EFX0 allocations', len(allocs) == 186, '(%d)' % len(allocs))
    report('Prop 7.5 (PW5): no free completion at the picks or after one move (incl. rings)',
           I.verdict(picks, allocs, one_absorber=False) == 'fails')
    fail_orders = sum(1 for o in itertools.permutations(range(5)) if I.verdict(I.sd(o), allocs, False) == 'fails')
    report('Prop 7.5 (PW5): the failing start comes from exactly 12 orders', fail_orders == 12, '(%d)' % fail_orders)

    # Prop 7.7 (RD5): one round fails, two sequential chains repair; free and one-absorber
    I = Inst([{1: 57, 3: 44, 5: 33, 0: 26, 4: 24}, {1: 12, 2: 11, 3: 6}, {1: 9, 2: 8, 3: 6, 4: 1},
              {2: 53, 5: 47, 0: 36, 6: 4}])
    allocs = I.all_efx0()
    picks = I.sd([0, 3, 1, 2])
    report('Prop 7.8 (RD5): order (0,3,1,2) picks 1,2,3,4 for agents 0,3,1,2; junk {0,5,6}',
           picks == (1, 3, 4, 2) and I.nu() == 4)
    report('Prop 7.8 (RD5): no completion (free) at the picks or after one move',
           I.verdict(picks, allocs, one_absorber=False) == 'fails', '(%d EFX0 allocations)' % len(allocs))
    report('Prop 7.8 (RD5): one round fails (free completion)', not round_fits(I, picks, allocs, False))
    report('Prop 7.8 (RD5): two sequential chains repair (one absorber)', two_chains_fit(I, picks, allocs))

    # Remark in 7.2: k = 3 outside cores
    I = Inst([{0: 10, 1: 8, 2: 7}, {0: 10, 1: 8, 2: 7}, {0: 10, 3: 8, 4: 7}, {1: 10, 5: 8, 6: 7}, {2: 10, 7: 8, 8: 7}])
    allocs = I.all_efx0()
    picks = I.sd([2, 3, 4, 0, 1])
    no_empty = I.verdict(picks, allocs, one_absorber=True, kinds=('pick', 'chain')) == 'fails'
    report('Remark §7.2 (k = 3): picks (-, -, 0, 1, 2); no one-absorber completion at the picks or after a chain',
           picks == (None, None, 0, 1, 2) and no_empty)
    report('Remark §7.2 (k = 3): no one-absorber completion after any addition or ring either',
           I.verdict(picks, allocs, one_absorber=True) == 'fails')
    report('Remark §7.2 (k = 3): one chain passing an empty base repairs (one absorber)',
           I.verdict(picks, allocs, one_absorber=True, kinds=('pick', 'chain'), glued=True) == 'move')
    report('Remark §7.2 (k = 3): under the free completion the picks already extend',
           I.verdict(picks, allocs, one_absorber=False, kinds=('pick',)) == 'picks'
           and I.efx0([{3, 5, 7}, {4, 6, 8}, {0}, {1}, {2}]))

    # §8: the k = 3 "no repair" instance and DT5
    I = Inst([{0: 12, 1: 13, 2: 3}, {1: 19, 2: 2, 3: 5}])
    allocs = I.all_efx0()
    picks = I.sd([0, 1])
    report('§8 (k = 3): picks (1, 3) do not extend; one chain repairs',
           picks == (1, 3) and I.verdict(picks, allocs, False) == 'move')
    I = Inst([{0: 100, 2: 91, 3: 92, 4: 93, 5: 94}, {1: 100, 2: 94, 3: 93, 4: 92, 5: 91}])
    allocs = I.all_efx0()
    picks = I.sd([0, 1])
    report('§8 (DT5): distinct tops, but the picks have no one-absorber completion',
           picks == (0, 1) and I.verdict(picks, allocs, True, kinds=('pick',)) == 'fails'
           and I.verdict(picks, allocs, False, kinds=('pick',)) == 'picks')

    # Prop 7.4: OC1^max fails at k = 4 (two n = 4 cores)
    for name, sets, vals, order, n_eff, n_vec in [
            ('instance 1', [[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]],
             [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]], (0, 3, 2, 1), 14, 7),
            ('instance 2', [[0, 4, 5, 6], [1, 2, 3, 5], [1, 3, 5, 6], [2, 4, 6]],
             [[2, 3, 10, 6], [3, 10, 6, 8], [5, 3, 7, 6], [4, 3, 2]], (3, 1, 2, 0), 24, 6)]:
        I = from_sets(sets, vals)
        allocs = I.all_efx0()
        picks = I.sd(order)
        tag = 'Prop 7.4 (%s)' % name
        report(tag + ': strict connected MC2-class core; every agent picks (nu = 4)',
               I.core_failures() == [] and all(len(q) <= 1 for q in I.private().values())
               and None not in picks and I.nu() == 4, str(picks))
        report(tag + ': %d EFX0 allocations; no free completion at picks or after one move' % n_eff,
               len(allocs) == n_eff and I.verdict(picks, allocs, one_absorber=False) == 'fails', '(%d)' % len(allocs))
        report(tag + ': one round fails, free (two methods)',
               not round_fits(I, picks, allocs, False) and not forward_round(I, picks, allocs, False))
        report(tag + ': two sequential chains repair (one absorber)', two_chains_fit(I, picks, allocs))
        vecs = {}
        for o in itertools.permutations(range(4)):
            q = I.sd(o)
            if sum(x is not None for x in q) == I.nu():
                vecs.setdefault(q, []).append(o)
        res = sorted(I.verdict(q, allocs, True) for q in vecs)
        report(tag + ': %d max pick vectors, 4 complete at the picks, 1 fails' % n_vec,
               len(vecs) == n_vec and res.count('picks') == 4 and res.count('fails') == 1, str(res))
        report(tag + ': some R1-priority order gives the failing picks',
               any(r1_priority(I, o) for o in vecs[picks]), str([o for o in vecs[picks] if r1_priority(I, o)]))

    # Remark in 7.5: RD5+ (ROUND+, every value positive)
    I = Inst([dict(enumerate(r)) for r in [[2600, 5700, 1, 4400, 2300, 3300, 1], [1, 1200, 1100, 600, 1, 1, 1],
                                           [1, 900, 800, 600, 100, 1, 1], [3600, 1, 5300, 1, 1, 4700, 400]]], 7)
    allocs = I.all_efx0()
    picks = I.sd([0, 3, 1, 2])
    report('Remark §7.5 (RD5+): one round fails (free, two methods); two sequential chains repair',
           not round_fits(I, picks, allocs, False) and not forward_round(I, picks, allocs, False)
           and two_chains_fit(I, picks, allocs), str(picks))
    # §8 / §7.3: the round methods agree on the known cases (PW5 repaired by one round, RD5 not)
    Ipw = from_sets([[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
                    [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]])
    apw = Ipw.all_efx0(); ppw = Ipw.sd(range(5))
    Ird = Inst([{1: 57, 3: 44, 5: 33, 0: 26, 4: 24}, {1: 12, 2: 11, 3: 6}, {1: 9, 2: 8, 3: 6, 4: 1},
                {2: 53, 5: 47, 0: 36, 6: 4}])
    ard = Ird.all_efx0(); prd = Ird.sd([0, 3, 1, 2])
    report('round methods agree on PW5 (one round repairs) and RD5 (it does not)',
           round_fits(Ipw, ppw, apw, True) and forward_round(Ipw, ppw, apw, True)
           and not round_fits(Ird, prd, ard, False) and not forward_round(Ird, prd, ard, False))

    # §12.5 (a): Conjecture W fails at n = 2
    I = Inst([{0: 40, 1: 10, 2: 11, 3: 12}, {0: 70, 4: 10, 5: 40, 6: 11}])
    start = (2, 0, 0, 0, 1, 1, 1)       # good 0 pooled (holder 2 = pool), {1, 2, 3} | {4, 5, 6}
    report('§12.5 (W): the state is partial EFX0; two moves never improve; three moves do',
           I.efx0([{1, 2, 3}, {4, 5, 6}]) and welfare_lemma_radius(I, start, 3) == 3)

    # Prop 7.3 (a): B<
    sets = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
    vals = [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]
    I = from_sets(sets, vals)
    picks = I.sd(range(6))
    report('Prop 7.3(a) (B<): strict connected core; order 0..5 picks (3, 9, 1, 6, -, -)',
           I.core_failures() == [] and picks == (3, 9, 1, 6, None, None), str(I.private()))
    report('Prop 7.3(a) (B<): the printed allocation is EFX0',
           I.efx0([{3}, {9}, {1}, {6}, {2, 4, 7}, {0, 5, 8}]))
    if not quick:
        allocs = I.all_efx0()
        report('Prop 7.3(a) (B<): no one-absorber completion at the picks or after one move',
               I.verdict(picks, allocs, one_absorber=True) == 'fails', '(%d EFX0 allocations)' % len(allocs))
        I2 = from_sets(sets, [vals[0], vals[1], [28, 4, 16, 19]] + vals[3:])
        allocs2 = I2.all_efx0()
        report('Prop 7.3(a) (B>): the same', I2.core_failures() == [] and
               I2.verdict(I2.sd(range(6)), allocs2, one_absorber=True) == 'fails')
        cnt = {}
        for o in itertools.permutations(range(6)):
            p = I.sd(o)
            cnt[p] = cnt.get(p, 0) + 1
        fails = sum(c for p, c in cnt.items() if I.verdict(p, allocs, True) == 'fails')
        report('Prop 7.3(a) (B<): OC1 fails for exactly 24 of the 720 orders', fails == 24, '(%d)' % fails)
    check_programme()
    check_monotone_s3()
    check_revision5()
    check_revision6()
    print('# %d failed; %.0f s' % (report.failed, time.time() - t0))
    return report.failed


def chains_of(I, picks):
    for st in I.structures(picks):
        if st[0] in ('add', 'chain'):
            yield st


def round_fits(I, picks, allocs, one_absorber):
    """One round (draft §2.4): vertex-disjoint chains (additions allowed), each head taking from J and its own end.
    Brute force over sets of disjoint structures; small n only."""
    sts = list(chains_of(I, picks))
    agents_of = lambda st: {st[1]} if st[0] == 'add' else set(st[1])
    rounds = [[]]
    for st in sts:
        rounds += [r + [st] for r in rounds if all(not (agents_of(st) & agents_of(s)) for s in r)]
    Xs = [I.bundles(o) for o in allocs]
    for r in rounds:
        on = set().union(*[agents_of(st) for st in r]) if r else set()
        for X in Xs:
            if all(picks[a] is None or picks[a] in X[a] for a in range(I.n) if a not in on) and \
                    combined_ok(I, picks, X, r, one_absorber):
                return True
    return False


def combined_ok(I, picks, X, r, one_absorber):
    """Placement and gains of every chain of the round at once, and the absorber count."""
    J = set(range(I.m)) - set(p for p in picks if p is not None)
    base = [set() if p is None else {p} for p in picks]
    for st in r:
        if st[0] == 'add':
            x = st[1]
            H = X[x] & J & I.R[x]
            if not H or picks[x] not in X[x]:
                return False
            base[x] = {picks[x]} | H
        else:
            path = st[1]
            x0, xt = path[0], path[-1]
            pool0 = J | ({picks[xt]} if picks[xt] is not None else set())
            H0 = X[x0] & pool0 & I.R[x0]
            if not I.val(x0, H0) > I.val(x0, {picks[x0]}):
                return False
            nb = {x0: H0}
            for a, b in zip(path, path[1:]):
                if picks[a] not in X[b]:
                    return False
                Hb = X[b] & J & I.R[b]
                if not I.val(b, {picks[a]} | Hb) > I.val(b, base[b]):
                    return False
                nb[b] = {picks[a]} | Hb
            for a, B in nb.items():
                base[a] = B
    if not all(base[a] <= X[a] for a in range(I.n)):
        return False
    if one_absorber and sum(1 for a in range(I.n) if len(X[a] - base[a]) >= 2) > 1:
        return False
    return True


def chain_states(I, B, prime=False):
    """Every official improving chain (draft §2.4) from the state B (a tuple of frozensets): yields (path, B').
    With prime=True, the OC1' move of kgen/rounds.md §4.6: non-end chain agents may also take goods of the end's base."""
    J = set(range(I.m)) - set().union(*B)
    n = I.n

    def extend(path, k, nb, used):
        if k == len(path):
            NB = list(B)
            for a, S in nb.items():
                NB[a] = S
            yield path, tuple(NB)
            return
        a, b = path[k - 1], path[k]
        extra = set(B[path[-1]]) if (prime and k < len(path) - 1) else set()
        cand = sorted(((J | extra) - used) & I.R[b])
        for r in range(0, len(cand) + 1):
            for H in itertools.combinations(cand, r):
                S = set(B[a]) | set(H)
                if I.val(b, S) > I.val(b, B[b]):
                    nb2 = dict(nb); nb2[b] = frozenset(S)
                    yield from extend(path, k + 1, nb2, used | set(H))
    for L in range(2, n + 1):
        for path in itertools.permutations(range(n), L):
            if not all(B[a] for a in path[:-1]):
                continue
            x0, xt = path[0], path[-1]
            cand0 = sorted((J | B[xt]) & I.R[x0])
            for r0 in range(1, len(cand0) + 1):
                for H0 in itertools.combinations(cand0, r0):
                    H0 = set(H0)
                    if not I.val(x0, H0) > I.val(x0, B[x0]):
                        continue
                    yield from extend(path, 1, {x0: frozenset(H0)}, set(H0))


def apply_chain(I, B, path, H):
    """Apply the chain path at state B with junk sets H[0] (for x0, may include B[x_t]) and H[i] (for x_i).
    Returns the new state, or None if the chain is not an official improving chain."""
    J = set(range(I.m)) - set().union(*B)
    x0, xt = path[0], path[-1]
    if not all(B[a] for a in path[:-1]):
        return None
    if not set(H[0]) <= (J | B[xt]) & I.R[x0] or not I.val(x0, H[0]) > I.val(x0, B[x0]):
        return None
    used = set(H[0])
    NB = list(B)
    NB[x0] = frozenset(H[0])
    for i in range(1, len(path)):
        a, b = path[i - 1], path[i]
        Hi = set(H[i])
        if not Hi <= (J & I.R[b]) or Hi & used:
            return None
        used |= Hi
        S = set(B[a]) | Hi
        if not I.val(b, S) > I.val(b, B[b]):
            return None
        NB[b] = frozenset(S)
    return tuple(NB)


def two_chains_fit(I, picks, allocs):
    """Some chain, then some chain from the resulting bases, gives bases with a one-absorber completion.
    States are enumerated explicitly (bases as sets), small n only."""
    start = tuple(frozenset() if p is None else frozenset({p}) for p in picks)

    def moves(B):
        for _, NB in chain_states(I, B):
            yield NB

    Xs = [I.bundles(o) for o in allocs]

    def completes(B):
        for X in Xs:
            if all(B[a] <= X[a] for a in range(I.n)) and \
                    sum(1 for a in range(I.n) if len(X[a] - B[a]) >= 2) <= 1:
                return True
        return False
    seen = set()
    for B1 in moves(start):
        if B1 in seen:
            continue
        seen.add(B1)
        for B2 in moves(B1):
            if completes(B2):
                return True
    return False


def forward_round(I, picks, allocs, one_absorber):
    """Second, independent method for one round: enumerate explicit rounds (disjoint chains and additions, every choice
    of junk sets), build the bases, and test the list of EFX0 allocations for a completion."""
    n = I.n
    J = set(range(I.m)) - set(p for p in picks if p is not None)
    B = [frozenset() if p is None else frozenset({p}) for p in picks]
    Xs = [I.bundles(o) for o in allocs]

    def completes(nb):
        return any(all(nb[a] <= X[a] for a in range(n)) and
                   (not one_absorber or sum(1 for a in range(n) if len(X[a] - nb[a]) >= 2) <= 1) for X in Xs)
    paths = [path for L in range(1, n + 1) for path in itertools.permutations(range(n), L)
             if (L == 1 and B[path[0]]) or (L > 1 and all(B[a] for a in path[:-1]))]

    def ext(path, k, nb, used):
        if k == len(path):
            yield nb, used
            return
        a, b = path[k - 1], path[k]
        cand = sorted((J - used) & I.R[b])
        for r in range(0, len(cand) + 1):
            for H in itertools.combinations(cand, r):
                S = B[a] | frozenset(H)
                if I.val(b, S) > I.val(b, B[b]):
                    nb2 = dict(nb); nb2[b] = S
                    yield from ext(path, k + 1, nb2, used | set(H))

    def results(path, used):
        if len(path) == 1:
            x = path[0]
            cand = sorted((J - used) & I.R[x])
            for r in range(1, len(cand) + 1):
                for H in itertools.combinations(cand, r):
                    yield {x: B[x] | frozenset(H)}, used | set(H)
            return
        x0, xt = path[0], path[-1]
        cand0 = sorted(((J - used) | B[xt]) & I.R[x0])
        for r in range(1, len(cand0) + 1):
            for H0 in itertools.combinations(cand0, r):
                if I.val(x0, H0) > I.val(x0, B[x0]):
                    yield from ext(path, 1, {x0: frozenset(H0)}, used | (set(H0) & J))

    def rec(start, usedagents, nb, usedj):
        base = list(B)
        for a, S in nb.items():
            base[a] = S
        if completes(base):
            return True
        for idx in range(start, len(paths)):
            path = paths[idx]
            if set(path) & usedagents:
                continue
            for nbc, uj in results(path, usedj):
                d = dict(nb); d.update(nbc)
                if rec(idx + 1, usedagents | set(path), d, uj):
                    return True
        return False
    return rec(0, set(), {}, set())


def r1_priority(I, order):
    """R1 priority (k4/sdc.md §2): whenever some unprocessed agent has lost a good, the next agent is such an agent."""
    taken, P = set(), I.sd(order)
    for k, i in enumerate(order):
        lost = [a for a in order[k:] if I.R[a] & taken]
        if lost and i not in lost:
            return False
        if P[i] is not None:
            taken.add(P[i])
    return True


def welfare_lemma_radius(I, start, maxd):
    """Conjecture W (k4/haxell.md §6), n = 2: the least number of moves (give one good to the other agent; swap the
    holders of two goods, the pool counting as a holder; rotate the bundles) after which a partial EFX0 allocation with
    a smaller pool, or the same pool and larger welfare, is reached; None if more than maxd."""
    POOL = I.n
    bund = lambda s: [{g for g in range(I.m) if s[g] == a} for a in range(I.n)]
    wel = lambda s: sum(I.val(i, B) for i, B in enumerate(bund(s)))
    pool = lambda s: sum(1 for x in s if x == POOL)

    def moves(s):
        out = set()
        for g in range(I.m):
            for a in range(I.n):
                if s[g] != a:
                    t = list(s); t[g] = a; out.add(tuple(t))
        for g, h in itertools.combinations(range(I.m), 2):
            if s[g] != s[h]:
                t = list(s); t[g], t[h] = s[h], s[g]; out.add(tuple(t))
        if I.n == 2:
            out.add(tuple({0: 1, 1: 0, POOL: POOL}[x] for x in s))
        return out
    good = lambda t: I.efx0(bund(t)) and (pool(t) < pool(start) or (pool(t) == pool(start) and wel(t) > wel(start)))
    seen, lvl = {start}, {start}
    for d in range(1, maxd + 1):
        nxt = set()
        for st in lvl:
            nxt |= moves(st)
        nxt -= seen; seen |= nxt; lvl = nxt
        if any(good(t) for t in seen):
            return d
    return None




# ---------------- §11 (the k = 4 programme), §7.5 (RD5+ repair), §9.4 (Lemma 9.6) ----------------

def frozen_sets(I, picks):
    """(F, D, U): frozen agents, dangerous ones (frozen and valuing junk), receivers (unfrozen pick holders)."""
    n = I.n
    J = set(range(I.m)) - set(p for p in picks if p is not None)
    F = {j for j in range(n) if picks[j] is not None and any(
        i != j and picks[j] in I.R[i] and I.v[i][picks[j]] > (I.v[i].get(picks[i], 0) if picks[i] is not None else 0)
        for i in range(n))}
    D = {j for j in F if J & I.R[j]}
    U = {j for j in range(n) if picks[j] is not None and j not in F}
    return F, D, U, J


def one_absorber_complete(I, B, Xs):
    return any(all(B[a] <= X[a] for a in range(I.n)) and
               sum(1 for a in range(I.n) if len(X[a] - B[a]) >= 2) <= 1 for X in Xs)


def check_programme():
    # Corollary 11.2 (Lemma T6's certificate) on both n = 4 instances of Prop 7.4
    for name, sets, vals, order, n_dom, agent in [
            ('instance 1', [[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]],
             [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]], (0, 3, 2, 1), 6, 0),
            ('instance 2', [[0, 4, 5, 6], [1, 2, 3, 5], [1, 3, 5, 6], [2, 4, 6]],
             [[2, 3, 10, 6], [3, 10, 6, 8], [5, 3, 7, 6], [4, 3, 2]], (3, 1, 2, 0), None, None)]:
        I = from_sets(sets, vals)
        picks = I.sd(order)
        J = set(range(I.m)) - set(picks)
        p = [I.v[i][picks[i]] for i in range(I.n)]
        dom = [X for X in (I.bundles(o) for o in I.all_efx0()) if all(I.val(i, X[i]) >= p[i] for i in range(I.n))]

        def blocked(X, i):
            fp = [picks[j] for j in range(I.n) if j != i and picks[j] in X[i]]
            if len(fp) >= 3:
                return True
            jr = I.val(i, J & I.R[i])
            return len(fp) == 2 and all(I.val(i, {f}) + jr <= p[i] for f in fp)
        ok = all(any(blocked(X, i) for i in range(I.n)) for X in dom)
        detail = '(%d dominating)' % len(dom)
        if n_dom is not None:
            ok = ok and len(dom) == n_dom and all({2, 5} <= X[agent] and blocked(X, agent) for X in dom)
        report('Cor 11.2 (T6 certificate), Prop 7.4 %s: every value-dominating EFX0 allocation has a blocked agent'
               % name, ok, detail)

    # §11.9 item 4: LIFT-SHAPE+ / SHARE2 (ii) fail at n = 5 (5_pure idx 164, k4/matching.md §6)
    I = from_sets([[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]],
                  [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]])
    allocs = I.all_efx0()
    Xs = [I.bundles(o) for o in allocs]
    picks = I.sd((1, 4, 2, 0, 3))
    F, D, U, J = frozen_sets(I, picks)
    report('§11.9 (n = 5 start): strict connected core; picks (7, 2, 3, 5, 4); one receiver 3; D = {0, 1, 2, 4}',
           I.core_failures() == [] and picks == (7, 2, 3, 5, 4) and U == {3} and D == {0, 1, 2, 4},
           str((picks, sorted(U), sorted(D), I.core_failures())))
    report('§11.9 (n = 5 start): no free completion at the picks or after one move (OC1^max fails at n = 5)',
           I.verdict(picks, allocs, one_absorber=False) == 'fails', '(%d EFX0 allocations)' % len(allocs))
    report('§11.9 (n = 5 start): two chains repair; [[2],[1,7,0],[5,6],[3],[4]] is EFX0',
           two_chains_fit(I, picks, allocs) and I.efx0([{2}, {1, 7, 0}, {5, 6}, {3}, {4}]))
    start = tuple(frozenset({q}) for q in picks)
    z, fav = 3, 4
    bad = 0; firsts = 0
    for P1, B1 in chain_states(I, start):
        if P1[-1] != z:
            continue
        firsts += 1
        for P2, B2 in chain_states(I, B1):
            if P2[-1] == z and fav in B2[z] and one_absorber_complete(I, B2, Xs):
                bad += 1
    report('§11.9 (n = 5 start): after no chain ending at z = 3 does a second chain ending at z with good 4 complete',
           firsts > 0 and bad == 0, '(%d first chains end at z)' % firsts)
    # leaf 5d: OC1' (non-end chain agents may also take the end's pick) fails at the same start, even with free
    # completions; additions and rings are covered by verdict() above
    Xall = Xs
    free_ok = any(all(B1[a] <= X[a] for a in range(I.n)) for _, B1 in chain_states(I, start, prime=True) for X in Xall)
    n_prime = sum(1 for _ in chain_states(I, start, prime=True))
    report("§11.8 leaf 5d (OC1'): no OC1' chain state of the n = 5 start has a free completion",
           not free_ok, '(%d OC1\' chain states)' % n_prime)

    # §11.9 item 1: S2-X (proof/k4-d1), the facts this checker can test
    I = from_sets([[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7], [8, 6, 7, 3]],
                  [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29], [14, 11, 1, 7]])
    allocs = I.all_efx0()
    Xs = [I.bundles(o) for o in allocs]
    picks = I.sd((0, 1, 2, 3))
    F, D, U, J = frozen_sets(I, picks)
    wanters7 = {i for i in range(I.n) if i != 0 and 7 in I.R[i] and I.v[i][7] > I.v[i][picks[i]]}
    hard = not any(I.fits(picks, X, ('pick',), True) for X in Xs)
    chain02 = any(I.fits(picks, X, ('chain', (0, 2)), True) for X in Xs)
    report('§11.9 (S2-X): core; picks (7, 6, 2, 8); D = {0}; 7 wanted by 1 and 2; 3 unfrozen, values junk 3; hard; '
           'chain (0, 2) repairs',
           I.core_failures() == [] and picks == (7, 6, 2, 8) and D == {0} and wanters7 == {1, 2}
           and 3 in U and 3 in (J & I.R[3]) and hard and chain02)

    # §11.9 item 3: the smallest R2-M test (n = 3)
    I = from_sets([[0, 1, 2, 3], [0, 1, 4, 5], [2, 3, 4, 5]], [[8, 6, 4, 1], [4, 2, 8, 5], [4, 6, 8, 3]])
    allocs = I.all_efx0()
    Xs = [I.bundles(o) for o in allocs]
    picks = I.sd((0, 2, 1))
    F, D, U, J = frozen_sets(I, picks)
    report('§11.9 (R2-M test): picks (0, 5, 4); D = {2}; receivers {0, 1}; |J| = 3; hard; one move repairs',
           picks == (0, 5, 4) and D == {2} and U == {0, 1} and len(J) == 3
           and not any(I.fits(picks, X, ('pick',), True) for X in Xs) and I.verdict(picks, allocs, True) == 'move')

    # §11.8: Lemma R2-0 on random perfect starts (junk to distinct receivers)
    rnd = random.Random(7)
    tested = bad = 0
    for _ in range(3000):
        n = rnd.randint(2, 4); m = rnd.randint(n, n + 4)
        vals = []
        for i in range(n):
            R = rnd.sample(range(m), rnd.randint(1, min(4, m)))
            vals.append({g: rnd.randint(1, 50) for g in R})
        I = Inst(vals, m)
        picks = I.sd(list(rnd.sample(range(n), n)))
        if None in picks:
            continue
        F, D, U, J = frozen_sets(I, picks)
        if not J or len(J) > len(U):
            continue
        tested += 1
        X = [{q} for q in picks]
        for g, u in zip(sorted(J), sorted(U)):
            X[u].add(g)
        bad += not I.efx0(X)
    report('Lemma R2-0 (§11.8): junk to distinct receivers is EFX0 on %d random perfect starts' % tested,
           tested > 100 and bad == 0, '(%d failures)' % bad)

    # Remark §7.5: the corrected two-round repair of RD5+
    I = Inst([dict(enumerate(r)) for r in [[2600, 5700, 1, 4400, 2300, 3300, 1], [1, 1200, 1100, 600, 1, 1, 1],
                                           [1, 900, 800, 600, 100, 1, 1], [3600, 1, 5300, 1, 1, 4700, 400]]], 7)
    picks = I.sd([0, 3, 1, 2])
    B0 = tuple(frozenset({q}) for q in picks)
    B1 = apply_chain(I, B0, (3, 1), [{0, 5}, set()])
    B2 = apply_chain(I, B1, (0, 2), [{3, 4}, set()]) if B1 else None
    X = [{3, 4, 6}, {2}, {1}, {0, 5}]
    ok = (picks == (1, 3, 4, 2) and B2 == (frozenset({3, 4}), frozenset({2}), frozenset({1}), frozenset({0, 5}))
          and I.efx0(X) and all(B2[a] <= X[a] for a in range(4)))
    # the printed version (with agent 0 adding good 6 in round 1): agent 2 must then take {1, 6}
    Bp = list(B1); Bp[0] = frozenset({1, 6}); Bp = tuple(Bp)
    Bq = apply_chain(I, Bp, (0, 2), [{3, 4}, set()])
    ok = ok and Bq is not None and Bq[2] == frozenset({1, 6}) and not (Bq[2] <= X[2])
    report('Remark §7.5 (RD5+): the corrected two-round repair is legal and EFX0; the printed one misses agent 2\'s base', ok)


def check_monotone_s3():
    """Lemma 9.6 on every nondegenerate monotone order of a 3-set (the 48 linear extensions of the Boolean lattice)."""
    subsets = [frozenset(c) for r in range(4) for c in itertools.combinations(range(3), r)]
    exts = []

    def rec(order, left):
        if not left:
            exts.append(order)
            return
        for S in left:
            if all(T in order for T in subsets if T < S):
                rec(order + [S], [T for T in left if T != S])
    rec([frozenset()], [S for S in subsets if S])
    bad = 0
    for order in exts:
        v = {S: r for r, S in enumerate(order)}
        s = sorted(range(3), key=lambda g: -v[frozenset({g})])
        wts = (4, 3, 2) if v[frozenset({s[0]})] < v[frozenset({s[1], s[2]})] else (6, 3, 2)
        w = {s[i]: wts[i] for i in range(3)}
        for A in subsets:
            for B in subsets:
                if A & B:
                    continue
                if (v[A] < v[B]) != (sum(w[g] for g in A) < sum(w[g] for g in B)):
                    bad += 1
    report('Lemma 9.6 (S3): the surrogate matches every disjoint comparison on all %d orders of a 3-set' % len(exts),
           len(exts) == 48 and bad == 0, '(%d mismatches)' % bad)


# ---------------- revision 5: REC-S, R2 forms, ROUND-P, W^sub/L^sub, T'_k, N3K5 ----------------

def completions_shape(I, B):
    """Every complete allocation containing the bases B (junk assigned arbitrarily): yields (X, extra-count list)."""
    J = sorted(set(range(I.m)) - set().union(*B))
    for asg in itertools.product(range(I.n), repeat=len(J)):
        X = [set(b) for b in B]
        for g, a in zip(J, asg):
            X[a].add(g)
        yield X, [len(X[a]) - len(B[a]) for a in range(I.n)]


def canonical_r2_states(I, picks):
    """The certifier's canonical chains (k4/oc1cert/verify_r2.py): x0 in D, x1 prefers y_x0 to y_x1, x_t a receiver,
    official rules (§2.4). Yields (path, state)."""
    F, D, U, J = frozen_sets(I, picks)
    start = tuple(frozenset({q}) for q in picks)
    for path, B in chain_states(I, start):
        x0, x1, xt = path[0], path[1], path[-1]
        if x0 in D and xt in U and I.v[x1].get(picks[x0], 0) > I.v[x1][picks[x1]]:
            yield path, B


def set_move_step(I, s, measure, maxd=2):
    """W^sub / L^sub (k4/haxell.md §6): is there a composite of at most maxd moves (set transfer, swap, rotation) from
    the partial allocation s (owner per good, I.n = pool) to a partial EFX0 allocation with a smaller pool, or the same
    pool and a better measure ('welfare' or 'leximin')?"""
    n, m, POOL = I.n, I.m, I.n
    bund = lambda t: [{g for g in range(m) if t[g] == a} for a in range(n)]
    vals = lambda t: [I.val(i, B) for i, B in enumerate(bund(t))]
    meas = (lambda t: sum(vals(t))) if measure == 'welfare' else (lambda t: sorted(vals(t)))
    pool = lambda t: sum(1 for x in t if x == POOL)
    p0, m0 = pool(s), meas(s)
    cycles = []
    for L in range(2, n + 1):
        for c in itertools.permutations(range(n), L):
            if c[0] == min(c):
                cycles.append(c)

    def moves(t):
        out = set()
        for h in list(range(n)) + [POOL]:
            held = [g for g in range(m) if t[g] == h]
            for r in range(1, len(held) + 1):
                for S in itertools.combinations(held, r):
                    for b in range(n):
                        if b != h:
                            u = list(t)
                            for g in S:
                                u[g] = b
                            out.add(tuple(u))
        for g, h in itertools.combinations(range(m), 2):
            if t[g] != t[h]:
                u = list(t); u[g], u[h] = t[h], t[g]; out.add(tuple(u))
        for c in cycles:
            nxt = {c[j]: c[(j + 1) % len(c)] for j in range(len(c))}
            out.add(tuple(nxt.get(x, x) for x in t))
        return out

    def good(t):
        pt = pool(t)
        if pt > p0 or (pt == p0 and not meas(t) > m0):
            return False
        return I.efx0(bund(t))
    seen, lvl = {s}, {s}
    for d in range(maxd):
        nxt = set()
        for t in lvl:
            nxt |= moves(t)
        nxt -= seen
        if any(good(t) for t in nxt):
            return True
        seen |= nxt; lvl = nxt
    return False


def check_revision5():
    # Theorem REC-S's repair of Prop 7.4 instance 1 (k4/oc1max_multi.md §12): E(2) = (2, 1) with T = {3, 4}, then the
    # Theorem S chain (0, 1) in I^- with h = 0 kept out for agent 1
    I = from_sets([[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]],
                  [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]])
    picks = I.sd((0, 3, 2, 1))
    B0 = tuple(frozenset({q}) for q in picks)
    wanters5 = sorted(i for i in range(4) if i != 2 and 5 in I.R[i] and I.v[i][5] > I.v[i][picks[i]])
    B1 = apply_chain(I, B0, (2, 1), [{3, 4}, set()])
    # Lemma SD-E: B1 without agent 2 and T is the SD outcome of (0, 3, 1) in I^-
    Im = Inst([{g: x for g, x in I.v[i].items() if g not in (3, 4)} for i in (0, 1, 3)], I.m)
    sde = Im.sd((0, 2, 1)) == (1, 5, 6)          # agents 0, 1, 3 renumbered 0, 1, 2
    B2 = apply_chain(I, B1, (0, 1), [{2, 5}, set()]) if B1 else None
    X = [{2, 5}, {1, 0}, {3, 4}, {6}]
    ok = (wanters5 == [1] and B1 is not None and sde and B2 is not None and I.efx0(X)
          and all(B2[a] <= X[a] for a in range(4)) and set().union(*X) == set(range(7)))
    report('Thm REC-S on Prop 7.4 instance 1: E(2) = (2, 1) takes {3, 4}; SD-E; chain (0, 1); final allocation EFX0',
           ok)

    # R2-M and R2* fail at n = 4, R2-C holds (certifier, results/k4_oc1max/r2m_fails_n4.jsonl, first entry)
    I = from_sets([[0, 5, 6], [1, 5, 6], [2, 3, 4, 5], [2, 3, 4, 6]], [[2, 3, 4], [2, 3, 4], [6, 4, 5, 8], [6, 5, 4, 8]])
    allocs = I.all_efx0()
    picks = (0, 1, 5, 6)
    F, D, U, J = frozen_sets(I, picks)
    sd_ok = any(I.sd(o) == picks for o in itertools.permutations(range(4)))
    Xs = [I.bundles(o) for o in allocs]
    hard = not any(I.fits(picks, X, ('pick',), True) for X in Xs)
    r2m = r2s = r2c = False
    for path, B in canonical_r2_states(I, picks):
        for X in Xs:
            if not all(B[a] <= X[a] for a in range(4)):
                continue
            ex = [len(X[a]) - len(B[a]) for a in range(4)]
            if sum(1 for e in ex if e >= 2) <= 1:
                r2c = True
            if all(e <= 1 for e in ex):
                r2s = True
                if all(ex[a] == 0 for a in range(4) if a != path[0] and len(B[a]) >= 2):
                    r2m = True
    report('§11.7 (R2 forms, n = 4): perfect hard start, receivers {0, 1}; R2-M and R2* fail; R2-C and OC1 hold',
           sd_ok and hard and U == {0, 1} and not r2m and not r2s and r2c and I.verdict(picks, allocs, True) == 'move',
           str((sorted(U), sorted(D))))

    # ROUND-P on the n = 5 start of §11.9: one round of two disjoint rings, (0 1) with junk 0, 1 and (3 4) with junk 6
    I = from_sets([[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]],
                  [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]])
    picks = I.sd((1, 4, 2, 0, 3))
    p = [I.v[i][picks[i]] for i in range(5)]
    X = [{2, 0}, {7, 1}, {3}, {4}, {5, 6}]
    gains = (I.val(0, {2, 0}) > p[0] and I.val(1, {7, 1}) > p[1] and I.val(3, {4}) > p[3] and I.val(4, {5, 6}) > p[4])
    report('§11.8 leaf 5d (ROUND-P): two disjoint rings repair the n = 5 start in one round (EFX0, every good placed)',
           picks == (7, 2, 3, 5, 4) and gains and I.efx0(X) and set().union(*X) == set(range(8)))

    # W^sub (welfare) and L^sub (leximin) fail at n = 4, k = 4 (k4/haxell.md §6)
    I = Inst([{4: 9, 5: 47, 6: 39}, {1: 8, 2: 3, 4: 2, 5: 4}, {0: 7, 1: 4, 3: 1, 5: 9}, {0: 38, 4: 7, 6: 32}], 7)
    s = (3, 2, 1, 1, 1, 0, 4)            # ({5}, {2, 3, 4}, {1}, {0}), good 6 pooled
    w3 = [{3, 6}, {1, 2, 4}, {5}, {0}]
    report('§12.5 (WS4): partial EFX0; no two-move welfare step; a leximin step exists; '
           '({3,6},{1,2,4},{5},{0}) is EFX0',
           I.efx0([{5}, {2, 3, 4}, {1}, {0}]) and not set_move_step(I, s, 'welfare') and set_move_step(I, s, 'leximin')
           and I.efx0(w3))
    I = Inst([{3: 30, 4: 20, 5: 55, 6: 57}, {1: 31, 3: 12, 4: 5, 5: 39}, {0: 44, 1: 32, 3: 29},
              {0: 60, 1: 31, 2: 7, 6: 43}], 7)
    s = (2, 4, 0, 0, 0, 1, 3)            # ({2, 3, 4}, {5}, {0}, {6}), good 1 pooled
    report('§12.5 (LS4): partial EFX0; no two-move leximin step; a welfare step exists',
           I.efx0([{2, 3, 4}, {5}, {0}, {6}]) and not set_move_step(I, s, 'leximin')
           and set_move_step(I, s, 'welfare'))

    # T'_k fails at n = 7, k = 3 (attempts/k4-k3oc1-tprime-k.md): values 10 > 8 > 7
    prefs = [(7, 0, 8), (5, 7, 9), (5, 10, 7), (0, 3, 2), (1, 2, 6), (1, 6, 4), (3, 4, 6)]
    I = Inst([{a: 10, b: 8, c: 7} for a, b, c in prefs], 11)
    picks = I.sd((2, 1, 0, 5, 6, 3, 4))
    base = [{q} for q in picks]
    draft_hard = not any(sum(1 for e in ex if e >= 2) <= 1 and I.efx0(X)
                         for X, ex in completions_shape(I, [frozenset(b) for b in base]))
    absorbers = []
    for rot, k in [({5: {6, 4}, 4: {1}}, 5), ({6: {4, 6}, 3: {3}, 4: {2}}, 6)]:
        B = [frozenset(base[a]) for a in range(7)]
        for a, S in rot.items():
            B[a] = frozenset(S)
        abs_ = set(); none_ok = False
        for X, ex in completions_shape(I, B):
            big = [a for a in range(7) if ex[a] >= 2]
            if len(big) <= 1 and I.efx0(X):
                if big:
                    abs_.add(big[0])
                else:
                    none_ok = True
        absorbers.append((k, abs_, none_ok))
    ok = (picks == (0, 7, 5, 2, 6, 1, 3) and draft_hard
          and all(abs_ and abs_ <= {3, 4} and not none_ok and k not in abs_ for k, abs_, none_ok in absorbers)
          and I.efx0([{0}, {7}, {5}, {2, 8, 9, 10}, {1}, {6, 4}, {3}]))
    report("§9 (T'_k, n = 7): picks; draft hard; after either rotation every one-absorber completion's absorber is 3 or 4",
           ok, str([(k, sorted(a)) for k, a, _ in absorbers]))

    # N3K5: one move fails at k = 5 already for n = 3 (k4/ksens.md)
    I = Inst([{0: 3, 2: 22, 3: 23, 4: 38, 5: 43}, {1: 15, 2: 17, 3: 27, 4: 40, 5: 43}, {1: 1, 4: 2, 5: 4}], 6)
    allocs = I.all_efx0()
    picks = I.sd((1, 0, 2))
    report('§8 (N3K5, k = 5, n = 3): picks (4, 5, 1); no free completion after one move; one round fails; '
           'two chains repair',
           picks == (4, 5, 1) and I.verdict(picks, allocs, one_absorber=False) == 'fails'
           and not round_fits(I, picks, allocs, False) and not forward_round(I, picks, allocs, False)
           and two_chains_fit(I, picks, allocs))


# ---------------- revision 6: RSD-IND's n = 5 counterexamples, VM1 on a core ----------------

def one_move_states(I, picks):
    """The picks and every state one move (§2.4) away: additions, and chains (which include rings: the start may take
    the end's base)."""
    start = tuple(frozenset({q}) for q in picks)
    J = set(range(I.m)) - set(picks)
    out = {start}
    for a in range(I.n):
        cand = sorted(J & I.R[a])
        for r in range(1, len(cand) + 1):
            for H in itertools.combinations(cand, r):
                B = list(start); B[a] = start[a] | frozenset(H); out.add(tuple(B))
    for _, B in chain_states(I, start):
        out.add(B)
    return out


def has_one_absorber_completion(I, B):
    return any(sum(1 for e in ex if e >= 2) <= 1 and I.efx0(X) for X, ex in completions_shape(I, B))


def threatens(I, i, S, value):
    """Does the bundle S threaten agent i at the value `value` (EFX0: some g with v_i(S - g) > value)?"""
    return any(I.val(i, set(S) - {g}) > value for g in S)


def check_revision6():
    # RSD-IND is refuted at n = 5 (k4/matching.md §6; k4/oc1_hall.md §24.4): 5_pure m = 10 idx 419
    I = from_sets([[0, 2, 6, 7], [1, 4, 8, 9], [3, 5, 8, 9], [4, 5, 7, 9], [6, 7, 8, 9]],
                  [[6, 3, 10, 8], [4, 8, 2, 3], [2, 8, 4, 3], [6, 7, 5, 3], [10, 7, 2, 6]])
    picks = (6, 4, 5, 9, 7)
    sd_ok = any(I.sd(o) == picks for o in itertools.permutations(range(5)))
    states = one_move_states(I, picks)
    no_one = not any(has_one_absorber_completion(I, B) for B in states)
    B0 = tuple(frozenset({q}) for q in picks)
    Ba = apply_chain(I, B0, (0, 4), [{0, 7}, set()])
    Bb = apply_chain(I, B0, (1, 3), [{1, 8, 9}, set()])
    both = None
    if Ba and Bb:
        both = tuple(Ba[a] if a in (0, 4) else Bb[a] if a in (1, 3) else B0[a] for a in range(5))
    p = [I.v[i][picks[i]] for i in range(5)]
    block = (threatens(I, 3, {0, 7}, p[3]) and threatens(I, 4, {1, 8, 9}, p[4])
             and not threatens(I, 3, {0, 7}, I.val(3, {4})) and not threatens(I, 4, {1, 8, 9}, I.val(4, {6})))
    report('§11.9 (RSD-IND, 5_pure #419): core; picks (6,4,5,9,7); no one-move repair; chains (0,4) and (1,3) '
           'together repair; each set threatens the agent only the other chain lifts',
           I.core_failures() == [] and sd_ok and no_one and both is not None
           and has_one_absorber_completion(I, both) and block, '(%d one-move states)' % len(states))

    # 5_pure m = 11 idx 447: no one-move repair; some round of two vertex-disjoint chains repairs
    I = from_sets([[0, 2, 5, 8], [1, 6, 7, 8], [3, 6, 9, 10], [4, 7, 9, 10], [5, 8, 9, 10]],
                  [[3, 4, 8, 6], [1, 6, 8, 4], [2, 10, 6, 3], [2, 8, 3, 4], [10, 8, 3, 6]])
    picks = (5, 1, 6, 7, 8)
    sd_ok = any(I.sd(o) == picks for o in itertools.permutations(range(5)))
    states = one_move_states(I, picks)
    no_one = not any(has_one_absorber_completion(I, B) for B in states)
    B0 = tuple(frozenset({q}) for q in picks)
    chains = list(chain_states(I, B0))
    pair = False
    for (P1, S1), (P2, S2) in itertools.combinations(chains, 2):
        if set(P1) & set(P2):
            continue
        new1 = {a: S1[a] for a in P1}; new2 = {a: S2[a] for a in P2}
        g1 = set().union(*new1.values()); g2 = set().union(*new2.values())
        if g1 & g2:
            continue
        B = tuple(new1.get(a, new2.get(a, B0[a])) for a in range(5))
        if has_one_absorber_completion(I, B):
            pair = True
            break
    report('§11.9 (RSD-IND, 5_pure #447): core; picks (5,1,6,7,8); no one-move repair; two vertex-disjoint chains '
           'repair', I.core_failures() == [] and sd_ok and no_one and pair, '(%d one-move states)' % len(states))

    # VM1 fails on a connected k = 4 core (P34; attempts/k4-vm-vm1-core.md): the printed facts this checker can test
    I = from_sets([[0, 2, 4, 5], [0, 2, 4, 6], [1, 3, 5, 6], [1, 3, 5, 6]],
                  [[4, 3, 2, 8], [4, 3, 2, 8], [4, 2, 8, 5], [4, 2, 8, 5]])
    X = [{0, 2, 4}, {6}, {5}, {3, 1}]
    report('§12.3 (VM1, P34): strict connected core; the two-move completion ({0,2,4},{6},{5},{1,3}) is EFX0',
           I.core_failures() == [] and I.efx0(X) and set().union(*X) == set(range(7)))

if __name__ == '__main__':
    sys.exit(1 if main(quick=len(sys.argv) > 1 and sys.argv[1] == 'quick') else 0)
