"""Second, independent covering for the exhaustive certification of DYN-exists (k4/girth.md section 6).

dyncert.py runs its own implementation of the pipeline (dyncert.Run / FastRun).  This file runs lss.py's pipeline
itself, unchanged (lss.Run.alg2_safe, lss.is_efx0, lss.park_dynamic_ec), on an instance whose values are symbolic:
every value is a linear form over one agent's goods, and every comparison of two forms is answered from a
representative profile and recorded.  The forms that lss.py compares have coefficients in {-1, 0, 1} after
cancelling (a sum of goods minus a sum of goods; the threat v_i(B) - min_h v_i(h) is the sum of B minus one good), so
each recorded comparison is "v_i(A) vs v_i(B)" for disjoint A, B; anything else raises.  The class of the run (the
profiles that answer every recorded comparison the same way) is computed directly from the type values, not with
dyncert's tables, and the covering bookkeeping is written separately.  Equality tests between two different goods are
answered "different" without recording (true for every strict type).

    python3 k4/girth/dyncert_sym.py N [FILE_GLOB_PART] [--limit=K] [--jobs=J] [--every=E] [--family=all|default]
    python3 k4/girth/dyncert_sym.py --selftest      class soundness: sampled profiles of a class, numeric lss.py
"""
import itertools
import multiprocessing as mp
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lss  # noqa: E402


class Lin:
    """sum of coef[g] * v_i(g) over goods g of agent i; compared through the recorder `rec`"""
    __slots__ = ('i', 'c', 'rec')

    def __init__(self, i, c, rec):
        self.i, self.c, self.rec = i, c, rec

    def _co(self, o):
        if isinstance(o, Lin):
            assert o.i == self.i, 'values of two agents compared'
            return o.c
        assert o == 0, ('arithmetic with a number', o)
        return {}

    def __add__(self, o):
        c = dict(self.c)
        for g, x in self._co(o).items():
            c[g] = c.get(g, 0) + x
        return Lin(self.i, {g: x for g, x in c.items() if x}, self.rec)

    __radd__ = __add__

    def __sub__(self, o):
        c = dict(self.c)
        for g, x in self._co(o).items():
            c[g] = c.get(g, 0) - x
        return Lin(self.i, {g: x for g, x in c.items() if x}, self.rec)

    def __rsub__(self, o):
        return Lin(self.i, {g: -x for g, x in self.c.items()}, self.rec).__add__(o)

    def sign(self, o):
        d = self - o
        return self.rec.sign(self.i, d.c)

    def __lt__(self, o):
        return self.sign(o) < 0

    def __le__(self, o):
        return self.sign(o) <= 0

    def __gt__(self, o):
        return self.sign(o) > 0

    def __ge__(self, o):
        return self.sign(o) >= 0

    def __eq__(self, o):
        d = (self - o).c
        if not d:
            return True
        A = [g for g, x in d.items() if x > 0]
        B = [g for g, x in d.items() if x < 0]
        assert all(abs(x) == 1 for x in d.values()), d
        if A and B and len(A) == 1 and len(B) == 1:
            return False                                   # two different goods: different in every strict type
        return self.sign(o) == 0

    def __ne__(self, o):
        return not self.__eq__(o)

    __hash__ = None


class Recorder:
    def __init__(self, vals):
        self.vals = vals                                   # vals[i]: dict good -> number (the representative)
        self.rec = [dict() for _ in vals]                  # i -> {(A, B) frozensets, A < B canonical: sign}

    def sign(self, i, c):
        assert all(x in (-1, 1) for x in c.values()), ('coefficient outside {-1, 0, 1}', c)
        A = frozenset(g for g, x in c.items() if x > 0)
        B = frozenset(g for g, x in c.items() if x < 0)
        if not A and not B:
            return 0
        if not B:
            return 1
        if not A:
            return -1
        a = sum(self.vals[i][g] for g in A)
        b = sum(self.vals[i][g] for g in B)
        assert a != b
        s = 1 if a > b else -1
        key = (A, B) if sorted(A) < sorted(B) else (B, A)
        sk = s if key[0] == A else -s
        old = self.rec[i].setdefault(key, sk)
        assert old == sk
        return s


def sym_inst(sets, m, vals):
    """an lss.Inst whose values are Lin forms (numbers only inside the recorder)"""
    I = lss.Inst([sorted(d) for d in vals], [[1] * len(d) for d in vals], m)
    rec = Recorder(vals)
    for i in range(I.n):
        I.v[i] = {g: Lin(i, {g: 1}, rec) for g in sorted(vals[i])}
    return I, rec


def all_labels(I, family):
    out = []
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        if family == 'default':
            out.append(lss.labels(I, z))
            continue
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                out.append(lss.labels(I, z, p, q))
    if family == 'default':
        return out
    # the same order as dyncert.labelings: the default one of each vertex 0 first
    firsts = [lss.labels(I, z) for z in range(I.n)]
    return firsts + [L for L in out if L not in firsts]


def run_lss(sets, m, vals, lab):
    I, rec = sym_inst(sets, m, vals)
    r = lss.Run(I, lab, check=False)
    r.alg2_safe()
    ok = lss.is_efx0(I, r.X) and lss.park_dynamic_ec(I, r.X, r.U) is not None
    return ok, rec.rec


def cover(task):
    name, sets, m, family = task
    from sources import domains
    t0 = time.time()
    doms = domains(sets, m)
    n = len(sets)
    I0 = lss.Inst([sorted(S) for S in sets], [[1] * len(S) for S in sets], m)
    labs = all_labels(I0, family)
    total = 1
    for D in doms:
        total *= len(D)
    covered = runs = 0
    cex = []
    stack = [(tuple(frozenset(range(len(D))) for D in doms), 0)]
    while stack:
        box, li = stack.pop()
        if any(not b for b in box):
            continue
        rep = [min(b) for b in box]
        if li == len(labs):
            cex.append(rep)
            continue
        vals = [doms[i][rep[i]] for i in range(n)]
        ok, rec = run_lss(sets, m, vals, labs[li])
        runs += 1
        cls = []
        for i in range(n):
            keep = set()
            for t in box[i]:
                v = doms[i][t]
                if all((sum(v[g] for g in A) > sum(v[g] for g in B)) == (s > 0) for (A, B), s in rec[i].items()):
                    keep.add(t)
            assert rep[i] in keep
            cls.append(frozenset(keep))
        if ok:
            size = 1
            for c in cls:
                size *= len(c)
            covered += size
        else:
            stack.append((tuple(cls), li + 1))
        for a in range(n):
            rest = box[a] - cls[a]
            if rest:
                stack.append((tuple(cls[:a]) + (rest,) + tuple(box[a + 1:]), li))
    return dict(name=name, profiles=total, covered=covered, runs=runs, cex=cex, time=time.time() - t0)


def selftest(k=200, seed=5):
    """the class recorded by a symbolic run is sound: profiles sampled in it give the same outcome with numbers"""
    import random
    from sources import cores, domains
    rng = random.Random(seed)
    allc = cores(3) + cores(4)
    runs = samples = 0
    for t in range(k):
        f, idx, sets, m = rng.choice(allc)
        doms = domains(sets, m)
        n = len(sets)
        rep = [rng.randrange(len(d)) for d in doms]
        I0 = lss.Inst([sorted(S) for S in sets], [[1] * len(S) for S in sets], m)
        for lab in rng.sample(all_labels(I0, 'all'), 3):
            ok, rec = run_lss(sets, m, [doms[i][rep[i]] for i in range(n)], lab)
            runs += 1
            cls = [[t2 for t2, v in enumerate(doms[i])
                    if all((sum(v[g] for g in A) > sum(v[g] for g in B)) == (s_ > 0) for (A, B), s_ in rec[i].items())]
                   for i in range(n)]
            for _ in range(4):
                vals = [doms[i][rng.choice(cls[i])] for i in range(n)]
                I = lss.Inst([sorted(d) for d in vals], [[d[g] for g in sorted(d)] for d in vals], m)
                r = lss.Run(I, lab, check=False)
                r.alg2_safe()
                ok2 = lss.is_efx0(I, r.X) and lss.park_dynamic_ec(I, r.X, r.U) is not None
                assert ok2 == ok, ('CLASS NOT SOUND', sets, vals, lab)
                samples += 1
    print('selftest: %d symbolic runs; %d profiles sampled in their classes, same outcome with numbers' % (runs, samples))


def main():
    if '--selftest' in sys.argv:
        selftest()
        return
    n = int(sys.argv[1])
    part = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else ''
    limit, jobs, every, family = None, mp.cpu_count(), 1, 'all'
    for a in sys.argv[2:]:
        if a.startswith('--limit='):
            limit = int(a[8:])
        if a.startswith('--jobs='):
            jobs = int(a[7:])
        if a.startswith('--every='):
            every = int(a[8:])
        if a.startswith('--family='):
            family = a[9:]
    from sources import cores
    tasks = [('%s#m%d#%d' % (f, m, idx), sets, m, family) for f, idx, sets, m in cores(n) if part in f][::every]
    if limit:
        tasks = tasks[:limit]
    print('$ python3 k4/girth/dyncert_sym.py', *sys.argv[1:], '(%d cores, %d jobs)' % (len(tasks), jobs), flush=True)
    t0 = time.time()
    tot = dict(profiles=0, covered=0, runs=0, cex=0, cores=0)
    with mp.Pool(jobs) as pool:
        for res in pool.imap_unordered(cover, tasks):
            tot['cores'] += 1
            for k in ('profiles', 'covered', 'runs'):
                tot[k] += res[k]
            tot['cex'] += len(res['cex'])
            st = 'CERTIFIED' if not res['cex'] and res['covered'] == res['profiles'] else 'NOT CERTIFIED'
            print('%-28s profiles %12d covered %12d runs %8d boxes-without-labeling %d %.1fs %s'
                  % (res['name'], res['profiles'], res['covered'], res['runs'], len(res['cex']), res['time'], st),
                  flush=True)
            for rep in res['cex'][:3]:
                print('   counterexample candidate: type indices', rep, flush=True)
    print('TOTAL', tot, '%.0fs' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
