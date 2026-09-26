#!/usr/bin/env python3
"""A SAT encoding of conjecture C4min (k4/c4x.md §5) on one strict profile, for k4/c4min_hunt.md §4: a third
implementation, written from the definitions of k4/c4x.md §1 and sharing no code with k4/c4min_hunt.c, k4/c4x.c or
k4/c4min_brute.py, and usable on large instances (no bound on m).

Variables: x[i,k] (agent i takes base option k: a subset of R_i of at most two goods), exactly one per agent, at most
one chosen option containing each good. need[g] <-> some chosen option has g among its needs (exact); valid: need[g]
-> sing[g] (g is a one-good base). f* = the least K with |{g : need[g]}| <= K satisfiable (a totalizer, raised K by
K). Then C4min at the profile is: satisfiable with |NA| <= f* and
  - no owner: |J| <= S (S = slots with the original needs), or
  - an owner o (free), C ⊆ J, X = B_o ∪ (J \\ C) (inX exact), no agent j != o threatened by X holding B_j: for every
    option k of j and every q ⊆ R_j \\ B_jk with v_j(q) > v_j(B_jk) (X ⊄ R_j; 'out_j' <-> some good outside R_j in X),
    resp. v_j(q) - min v_j(q) > v_j(B_jk) (X ⊆ R_j), a clause forbids "x[j,k], q ⊆ X, out_j (resp. not out_j)"; and
    |C| <= S_o(C), where the slots count the owner's needs from X (need2 is forced true by every agent's needs but
    the owner's, and by the owner's pattern X ∩ R_o = p: every h in R_o \\ p with v_o(h) > v_o(p)); frozen2 and the
    slot literals are only bounded from the side the solver cannot exploit.
A model is a certificate (bases, owner, C); c4min_sat.run re-checks it with k4/c4min_brute.verify_certificate.

usage (library): fstar_and_holds(sets, m, vals) -> (f*, holds, certificate or None)
command line: c4min_sat.py --family=NAME:ARGS [--family=...] [--profiles=N] [--mode=uniform|paper|perturb:K] [--seed=S]
              [--jobs=J]   (families of k4/c4min_families.py; paper / perturb: §7's values for ht, ht2, htx, htc)
              --climb=ITERS [--restarts=R] [--stale=T]: hill-climbing with objective() instead (CEX lines if d* > 0)"""
import itertools, random, sys, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.solvers import Solver


DPOS = 6          # deficits up to +DPOS are measured exactly (larger ones are reported as DPOS + 1)


def val(v, S):
    return sum(v[g] for g in S)


class Enc:
    def __init__(self, sets, m, vals):
        self.sets, self.m, self.vals, self.n = sets, m, vals, len(sets)
        self.pool = IDPool()
        self.cl = []
        self.opts = [[frozenset(c) for r in range(3) for c in itertools.combinations(S, r)] for S in sets]
        self.needs = [[frozenset(g for g in S if g not in B and vals[i][g] > val(vals[i], B)) for B in self.opts[i]]
                      for i, S in enumerate(sets)]
        V = self.pool.id
        self.x = {(i, k): V(('x', i, k)) for i in range(self.n) for k in range(len(self.opts[i]))}
        for i in range(self.n):
            self.cl += CardEnc.equals([self.x[i, k] for k in range(len(self.opts[i]))], 1, vpool=self.pool, encoding=EncType.pairwise).clauses
        self.base = {}
        for g in range(m):
            L = [self.x[i, k] for i in range(self.n) for k, B in enumerate(self.opts[i]) if g in B]
            if len(L) > 1: self.cl += CardEnc.atmost(L, 1, vpool=self.pool, encoding=EncType.pairwise).clauses
            self.base[g] = self.equiv_or(('base', g), L)
        self.sing = {g: self.equiv_or(('sing', g), [self.x[i, k] for i in range(self.n) for k, B in enumerate(self.opts[i]) if B == {g}])
                     for g in range(m)}
        self.need = {g: self.equiv_or(('need', g), [self.x[i, k] for i in range(self.n) for k in range(len(self.opts[i])) if g in self.needs[i][k]])
                     for g in range(m)}
        for g in range(m): self.cl.append([-self.need[g], self.sing[g]])
        # frozen[i] <-> some one-good base of i is needed
        self.frozen = {}
        for i in range(self.n):
            fz = []
            for k, B in enumerate(self.opts[i]):
                if len(B) == 1:
                    (g,) = B
                    fz.append(self.equiv_and(('fz', i, k), [self.x[i, k], self.need[g]]))
            self.frozen[i] = self.equiv_or(('frozen', i), fz)

    def equiv_or(self, name, L):
        v = self.pool.id(name)
        self.cl.append([-v] + L)
        for l in L: self.cl.append([v, -l])
        return v

    def equiv_and(self, name, L):
        v = self.pool.id(name)
        for l in L: self.cl.append([-v, l])
        self.cl.append([v] + [-l for l in L])
        return v

    def owner_part(self):
        n, m, V = self.n, self.m, self.pool.id
        noown = V('noown')
        own = {o: V(('own', o)) for o in range(n)}
        self.cl += CardEnc.equals([noown] + list(own.values()), 1, vpool=self.pool, encoding=EncType.pairwise).clauses
        for o in range(n): self.cl.append([-own[o], -self.frozen[o]])
        # slots with the original needs (no owner)
        sl1, sl2 = {}, {}
        for i in range(n):
            small = [self.x[i, k] for k, B in enumerate(self.opts[i]) if len(B) <= 1]
            a = self.equiv_or(('small', i), small)
            sl1[i] = self.equiv_and(('sl1', i), [a, -self.frozen[i]])
            e = [self.x[i, k] for k, B in enumerate(self.opts[i]) if len(B) == 0][0]
            sl2[i] = e
        lits = [-self.base[g] for g in range(m)] + [-sl1[i] for i in range(n)] + [-sl2[i] for i in range(n)]
        t1 = ITotalizer(lits, ubound=2 * n + DPOS + 1, top_id=self.pool.top)
        self.pool.top = t1.top_id
        self.cl += t1.cnf.clauses
        # owner: C, X
        c = {g: V(('c', g)) for g in range(m)}
        for g in range(m): self.cl.append([-c[g], -self.base[g]])
        z = {}
        for o in range(n):
            for k, B in enumerate(self.opts[o]):
                if B: z[o, k] = self.equiv_and(('z', o, k), [own[o], self.x[o, k]])
        inX = {}
        for g in range(m):
            ob = self.equiv_or(('ob', g), [z[o, k] for o in range(n) for k, B in enumerate(self.opts[o]) if g in B])
            y = self.equiv_and(('y', g), [-self.base[g], -c[g]])
            inX[g] = self.equiv_or(('inX', g), [ob, y])
        out = {j: self.equiv_or(('out', j), [inX[g] for g in range(m) if g not in self.sets[j]]) for j in range(n)}
        # threats
        for j in range(n):
            vj = self.vals[j]
            for k, B in enumerate(self.opts[j]):
                vb = val(vj, B)
                rest = [g for g in self.sets[j] if g not in B]
                for r in range(1, len(rest) + 1):
                    for q in itertools.combinations(rest, r):
                        vq = val(vj, q)
                        if vq > vb:
                            self.cl.append([noown, own[j], -self.x[j, k], -out[j]] + [-inX[g] for g in q])
                        if vq - min(vj[g] for g in q) > vb:
                            self.cl.append([noown, own[j], -self.x[j, k], out[j]] + [-inX[g] for g in q])
        # the owner's needs from its bundle
        need2 = {g: V(('need2', g)) for g in range(m)}
        for i in range(n):
            for k in range(len(self.opts[i])):
                for g in self.needs[i][k]: self.cl.append([-self.x[i, k], own[i], need2[g]])
        for o in range(n):
            R, vo = self.sets[o], self.vals[o]
            for r in range(len(R) + 1):
                for p in itertools.combinations(R, r):
                    vp = val(vo, p)
                    hs = [h for h in R if h not in p and vo[h] > vp]
                    if not hs: continue
                    pre = [-own[o]] + [-inX[g] for g in p] + [inX[g] for g in R if g not in p]
                    for h in hs: self.cl.append(pre + [need2[h]])
        t1b, t2b = {}, {}
        for i in range(n):
            fz2 = V(('frozen2', i))
            for k, B in enumerate(self.opts[i]):
                if len(B) == 1:
                    (g,) = B
                    self.cl.append([-self.x[i, k], -need2[g], fz2])
            t1b[i], t2b[i] = V(('t1', i)), V(('t2', i))
            self.cl.append([-t1b[i], -fz2]); self.cl.append([-t1b[i], -own[i]]); self.cl.append([-t2b[i], -own[i]])
            self.cl.append([-t1b[i]] + [self.x[i, k] for k, B in enumerate(self.opts[i]) if len(B) <= 1])
            self.cl.append([-t2b[i]] + [self.x[i, k] for k, B in enumerate(self.opts[i]) if len(B) == 0])
        lits = [c[g] for g in range(m)] + [-t1b[i] for i in range(n)] + [-t2b[i] for i in range(n)]
        t2 = ITotalizer(lits, ubound=2 * n + DPOS + 1, top_id=self.pool.top)
        self.pool.top = t2.top_id
        self.cl += t2.cnf.clauses
        # selector sel[d] (-2n <= d <= DPOS): the deficit of the chosen (P, owner, C) is <= d
        # (no owner: |J| - S <= d; owner: |C| - S_o(C) <= d), i.e. the totalled sum is <= 2n + d
        self.sel = {}
        for d in range(-2 * n, DPOS + 1):
            v = V(('sel', d))
            self.sel[d] = v
            if 2 * n + d < 0:                   # a sum <= negative: impossible
                self.cl.append([-v])
                continue
            # a bound at or above the number of summed literals holds trivially (rhs is shorter then)
            if 2 * n + d < len(t1.rhs): self.cl.append([-v, -noown, -t1.rhs[2 * n + d]])
            if 2 * n + d < len(t2.rhs): self.cl.append([-v, noown, -t2.rhs[2 * n + d]])
        self.own, self.noown, self.c = own, noown, c


def fstar_and_holds(sets, m, vals, solver='cadical153', per_owner=False):
    """(f*, holds, certificate); with per_owner, also the list of owners o (None: no owner) for which some min-frozen
    P has deficit <= 0 with that owner (for the comparison with k4/c4min_hunt.c -1o)."""
    E = Enc(sets, m, vals)
    tot = ITotalizer([E.need[g] for g in range(m)], ubound=len(sets) + 1, top_id=E.pool.top)
    E.pool.top = tot.top_id
    base_cl = E.cl + tot.cnf.clauses
    with Solver(name=solver, bootstrap_with=base_cl) as s:
        f = 0
        while not s.solve(assumptions=[-tot.rhs[f]]): f += 1
    E.owner_part()
    with Solver(name=solver, bootstrap_with=E.cl + tot.cnf.clauses) as s:
        A = [-tot.rhs[f], E.sel[0]]
        ok = s.solve(assumptions=A)
        owners = None
        if per_owner:
            owners = [o for o in [None] + list(range(E.n))
                      if s.solve(assumptions=A + [E.noown if o is None else E.own[o]])]
        if not ok: return (f, False, None, owners) if per_owner else (f, False, None)
        s.solve(assumptions=A)
        mod = set(l for l in s.get_model() if l > 0)
    bases = [next(E.opts[i][k] for k in range(len(E.opts[i])) if E.x[i, k] in mod) for i in range(E.n)]
    owner = None if E.noown in mod else next(o for o in range(E.n) if E.own[o] in mod)
    C = [g for g in range(m) if E.c[g] in mod] if owner is not None else []
    return (f, True, (bases, owner, C), owners) if per_owner else (f, True, (bases, owner, C))


def objective(sets, m, vals, solver='cadical153'):
    """(owner needed, d*, number of owners o with a min-frozen P of deficit <= 0 when o owns; f*): the score of the
    SAT climber. d* as in k4/c4x.md §1: f* - sigma if f* <= sigma, else the least |C| - S_o(C) over owners, by the
    selectors (deficits above DPOS reported as DPOS + 1)."""
    E = Enc(sets, m, vals)
    tot = ITotalizer([E.need[g] for g in range(m)], ubound=len(sets) + 1, top_id=E.pool.top)
    E.pool.top = tot.top_id
    E.owner_part()
    n = len(sets)
    with Solver(name=solver, bootstrap_with=E.cl + tot.cnf.clauses) as s:
        f = 0
        while not s.solve(assumptions=[-tot.rhs[f]]): f += 1
        sigma = 2 * n - m
        if f <= sigma: dstar = f - sigma      # k4/c4x.md §1: def = |J| - S = f - sigma for every min-frozen P
        else:                                 # owners only: the least d with a SAT answer (monotone in d)
            lo = [d for d in range(-2 * n, DPOS + 1)]
            a, b = 0, len(lo)
            while a < b:
                mid = (a + b) // 2
                if s.solve(assumptions=[-tot.rhs[f], -E.noown, E.sel[lo[mid]]]): b = mid
                else: a = mid + 1
            dstar = lo[a] if a < len(lo) else DPOS + 1
        nown = sum(s.solve(assumptions=[-tot.rhs[f], E.sel[0], E.own[o]]) for o in range(n)) if f > 2 * n - m else n
    return (int(f > 2 * n - m), dstar, nown, f)


def climb(args):
    """hill-climbing of one family member with the SAT objective: maximize (owner needed, d*, -feasible owners)"""
    import c4min_common as cc, c4min_families as F
    fam, iters, restarts, seed, stale_lim = args
    name, *fargs = fam.split(':')
    sets, m = F.normalize(F.family(name, fargs))
    doms = cc.domains(sets, m)
    rng = random.Random(seed)
    out, best = [], None
    for r in range(restarts):
        cur = [rng.choice(D) for D in doms]
        sc = objective(sets, m, cur)
        key = lambda t: (t[0], t[1], -t[2])
        stale = 0
        for it in range(iters):
            cand = list(cur)
            for _ in range(1 if rng.random() < 0.75 else 2):
                i = rng.randrange(len(sets)); cand[i] = rng.choice(doms[i])
            sn = objective(sets, m, cand)
            if key(sn) >= key(sc):
                stale = 0 if key(sn) > key(sc) else stale + 1
                cur, sc = cand, sn
                if sc[1] > 0:
                    f, holds = run(sets, m, cur)
                    out.append(f'CEX {fam} d* {sc[1]} holds(re-check) {holds} sets {sets} values {[[v[g] for g in S] for S, v in zip(sets, cur)]}')
            else: stale += 1
            if stale > stale_lim: break
        out.append(f'RESTART {fam} #{r}: owner needed {sc[0]} d* {sc[1]} feasible owners {sc[2]} f* {sc[3]}')
        if best is None or key(sc) > key(best[0]): best = (sc, cur)
    sc, cur = best
    out.append(f'BEST {fam} (n {len(sets)}, m {m}): owner needed {sc[0]} d* {sc[1]} feasible owners {sc[2]} f* {sc[3]} '
               f'values {[[v[g] for g in S] for S, v in zip(sets, cur)]}')
    return out


def run(sets, m, vals):
    """f*, holds; the certificate re-checked literally (k4/c4min_brute.verify_certificate)"""
    import c4min_brute
    f, holds, cert = fstar_and_holds(sets, m, vals)
    if holds:
        fc = c4min_brute.verify_certificate(sets, vals, m, [sorted(b) for b in cert[0]], cert[1], cert[2])
        assert fc == f, (fc, f)
    return f, holds


def sample(args):
    """one family: N profiles (uniform, §7's values, or §7's values with K agents re-typed); returns the summary"""
    import c4min_common as cc, c4min_families as F
    fam, N, mode, seed = args
    name, *fargs = fam.split(':')
    sets, m = F.normalize(F.family(name, fargs))
    assert F.check_core(sets, m), fam
    doms = cc.domains(sets, m)
    rng = random.Random(seed)
    base = None
    if name in ('lt', 'ltp'):
        base = [dict(zip(S, w)) for S, w in zip(sets, F.lt_values(int(fargs[0]), int(fargs[1])))]
    elif name in ('ht', 'htc', 'ht2', 'htx'):
        want = [(8, 6, 5, 4) if (name != 'htc' and i == 0) else (8, 6, 4, 3) for i in range(len(sets))]
        base = [dict(zip(S, w)) for S, w in zip(sets, want)]
        if any(tuple(b[g] for g in S) not in {tuple(v[g] for g in S) for v in D} for S, b, D in zip(sets, base, doms)): base = None
    hist, fails, lines, t0 = {}, 0, [], time.time()
    for r in range(N):
        if mode == 'paper' and base: vals = base
        elif mode.startswith('perturb') and base:
            vals = list(base)
            for _ in range(int(mode.split(':')[1])):
                i = rng.randrange(len(sets)); vals[i] = rng.choice(doms[i])
        else: vals = [rng.choice(D) for D in doms]
        f, holds = run(sets, m, vals)
        hist[f] = hist.get(f, 0) + 1
        if not holds:
            fails += 1
            lines.append(f'FAIL {fam} sets {sets} values {[[v[g] for g in S] for S, v in zip(sets, vals)]}')
        if mode == 'paper': break
    lines.append(f'SAT {fam} (n {len(sets)}, m {m}, sigma {2 * len(sets) - m}, {mode}) profiles {sum(hist.values())} fails {fails} '
                 f'fstar {dict(sorted(hist.items()))} ({time.time() - t0:.1f} s; every certificate re-checked by c4min_brute)')
    return lines


def main():
    fams, N, seed, mode, jobs, climb_it, restarts, stale = [], 10, 1, 'uniform', 1, 0, 2, 60
    for a in sys.argv[1:]:
        k, _, v = a.partition('=')
        if k == '--family': fams.append(v)
        elif k == '--profiles': N = int(v)
        elif k == '--seed': seed = int(v)
        elif k == '--mode': mode = v
        elif k == '--jobs': jobs = int(v)
        elif k == '--climb': climb_it = int(v)
        elif k == '--restarts': restarts = int(v)
        elif k == '--stale': stale = int(v)
        else: raise SystemExit(f'unknown option {a}')
    from concurrent.futures import ProcessPoolExecutor
    if climb_it:
        with ProcessPoolExecutor(jobs) as ex:
            for lines in ex.map(climb, [(fam, climb_it, restarts, seed * 7919 + i, stale) for i, fam in enumerate(fams)]):
                for l in lines: print(l, flush=True)
        return
    tot = fails = 0
    with ProcessPoolExecutor(jobs) as ex:
        for lines in ex.map(sample, [(fam, N, mode, seed * 7919 + i) for i, fam in enumerate(fams)]):
            for l in lines:
                print(l, flush=True)
                if l.startswith('SAT'): tot += int(l.split(' profiles ')[1].split()[0]); fails += int(l.split(' fails ')[1].split()[0])
    print(f'TOTAL profiles {tot} fails {fails}')


if __name__ == '__main__':
    main()
