"""Stress test of K4.D (the D2 shape: an EFX0 allocation with at most one bundle of more than two goods) on large
structured k = 4 cores made of 4-good agents (k4/d_stress.md). EVIDENCE only; every decision is exact (SAT).

Instances: a hypergraph (agents' good lists) that must be a k = 4 core (check4.is_core) and a strict core profile (each
agent's type from search4.domain: strictly balanced, strict, p + q < s + t for two private goods).
Decisions: search4.Core's SAT model, built fresh for each profile with every agent's domain fixed to its one type
(`fixed`); every allocation it returns is re-checked by the raw EFX0 definition and the shape (d_stress_check.raw):
  shape(prof, s, c)   an EFX0 allocation with at most c bundles of more than s goods, or None (default s = 2, c = 1:
                      the D2 shape; s = c = None: any shape);
  count(prof, cap)    the number of D2 EFX0 allocations, up to cap (blocking clauses; counts are not re-checked).
Families:
  chain t [heads h]    H_t of k4/c4.md section 7 (on PR #33's branch proof/k4-c4, not on main); with h > 1, several
                       heads, each starting a chain of t gadgets, all ends linked to the shared good z
  cycle t              gadgets only, in a cycle: e_j = g_{(j+1) mod t}, no head (a pure core, n = 4t, m = 10t)
  tree t               gadgets in a binary tree (heap order): gadget j's y links to its first child's g (a leaf's y to
                       the root good z); a second child is joined to g_j by a head-like agent {g_j, g_child, p, q}
  pure n m             one random connected pure core (every agent 4 goods) with n agents and m goods (high beta),
                       fixed by --seed and printed in the log
Margin: owners(prof) (d_stress_check.py, the independent encoding) = the agents o for which a D2 EFX0 allocation exists
with no bundle other than o's above 2 goods; --owners=STEPS hill-climbs profiles toward fewer owners (0 = no D2).
Usage: d_stress.py FAMILY ARGS [--profiles=N] [--owners=STEPS] [--restarts=R] [--climb=STEPS] [--cap=C] [--seed=S]
       [--values=paper] [--witnesses=OUT.json.gz]
  --witnesses writes {args, sets, witnesses: [[values, allocation], ...]} for the random profiles (gzip JSON), which
  d_stress_check.py FILE re-checks independently."""
import sys, os, time, random, json, itertools
import numpy as np
import subprocess, gzip
import search4 as S4
import check4
import d_stress_check as DC

# ----- families -----
def gadget(goods, g, e):
    """Three x's {a_i, b_i, c_i, g} and a y {a_1, a_2, a_3, e}; returns the four good lists (new goods from `goods`)."""
    a = [goods() for _ in range(3)]
    xs = [[a[i], goods(), goods(), g] for i in range(3)]
    return xs + [[a[0], a[1], a[2], e]]


def counter():
    c = itertools.count()
    return lambda: next(c)


def chain(t, heads=1):
    """H_t (heads = 1): head l = {g_1, z, u, u'}; gadget j's y links to g_{j+1}, the last to z. With several heads,
    head h starts its own chain of t gadgets, and the chains share the head goods z of the first head (gadget ends
    link to z)."""
    goods = counter()
    sets = []
    z = goods()
    for h in range(heads):
        gs = [goods() for _ in range(t)]
        sets.append([gs[0], z, goods(), goods()])
        for j in range(t):
            sets += gadget(goods, gs[j], gs[j + 1] if j + 1 < t else z)
    return sets


def cycle(t):
    """Gadgets only, in a cycle: gadget j's y links to g_{(j+1) mod t}; no head."""
    goods = counter()
    gs = [goods() for _ in range(t)]
    sets = []
    for j in range(t):
        sets += gadget(goods, gs[j], gs[(j + 1) % t])
    return sets


def tree(t):
    """Gadgets in a binary tree (heap order): gadget j's y has e_j = g of child 2j+1 if it exists, else the root good
    z; a gadget with two children links the second child through its head-like agent."""
    goods = counter()
    gs = [goods() for _ in range(t)]
    z = goods()
    sets = [[gs[0], z, goods(), goods()]]
    for j in range(t):
        c1, c2 = 2 * j + 1, 2 * j + 2
        sets += gadget(goods, gs[j], gs[c1] if c1 < t else z)
        if c2 < t: sets.append([gs[j], gs[c2], goods(), goods()])   # a head-like agent joining the second child
    return sets


def pure(n, m, rng, tries=100000):
    for _ in range(tries):
        sets = [sorted(rng.sample(range(m), 4)) for _ in range(n)]
        if check4.is_core(n, m, sets, True)[0]: return sets
    return None


def good_count(sets):
    return max(g for S in sets for g in S) + 1


# ----- decisions -----
class Inst:
    def __init__(self, sets):
        self.sets, self.m = sets, good_count(sets)
        self.n = len(self.sets)
        ok, _ = check4.is_core(self.n, self.m, self.sets, False)
        assert ok, 'not a k = 4 core'
        self.C = S4.Core(self.n, self.m, self.sets)
        self.dom = self.C.dom
        self.rechecked = 0

    def fixed(self, prof, s, c):
        """A fresh SAT model for this profile only (every agent's domain = its one type)."""
        self.C.dom = [[self.dom[i][t]] for i, t in enumerate(prof)]
        self.C.cache = {}
        sol, x, z = self.C.inner(s, c)
        self.C.dom = self.dom
        return sol, x, [zi[0] for zi in z]

    def shape(self, prof, s=2, c=1):
        sol, x, z = self.fixed(prof, s, c)
        if not sol.solve(assumptions=z): return None
        mod = sol.get_model()
        A = [next(j for j in range(self.n) if mod[x[g][j] - 1] > 0) for g in range(self.m)]
        # every witness re-checked by the raw definition (PROMPT.md section 5 rule 4) and the shape
        assert DC.raw(self.sets, self.values(prof), A), 'SAT allocation fails the raw EFX0 check'
        if s is not None: assert sum(1 for j in range(self.n) if A.count(j) > s) <= c, 'shape violated'
        self.rechecked += 1
        return A

    def count(self, prof, cap):
        sol, x, z = self.fixed(prof, 2, 1)
        k = 0
        while k < cap and sol.solve(assumptions=z):
            mod = sol.get_model()
            A = [next(j for j in range(self.n) if mod[x[g][j] - 1] > 0) for g in range(self.m)]
            sol.add_clause([-x[g][A[g]] for g in range(self.m)])
            k += 1
        return k

    def random_profile(self, rng):
        return [rng.randrange(len(D)) for D in self.dom]

    def values(self, prof):
        return [list(self.dom[i][t]) for i, t in enumerate(prof)]


def paper_profile(I):
    """The values of k4/c4.md section 7: (8, 6, 5, 4) for heads, (8, 6, 4, 3) for x's and y's, in good-list order."""
    prof = []
    for i, S in enumerate(I.sets):
        want = (8, 6, 5, 4) if i == 0 else (8, 6, 4, 3)
        ts = [t for t, v in enumerate(I.dom[i]) if tuple(v) == want]
        prof.append(ts[0] if ts else None)
    return prof if None not in prof else None


def climb(I, rng, steps, cap, start=None):
    """Hill-climb a profile toward fewer D2 allocations (count up to cap); returns (best count, best profile, trace)."""
    cur = start or I.random_profile(rng)
    cc = I.count(cur, cap)
    best, bestp, trace = cc, list(cur), [cc]
    for _ in range(steps):
        if cc == 0: break
        cand = list(cur)
        for i in rng.sample(range(I.n), rng.choice((1, 1, 2))):
            cand[i] = rng.randrange(len(I.dom[i]))
        k = I.count(cand, cap)
        if k <= cc:
            cur, cc = cand, k
            if k < best: best, bestp = k, list(cand)
        trace.append(cc)
    return best, bestp, trace


def climb_owners(I, rng, steps, start=None):
    """Hill-climb a profile toward fewer feasible large-bundle owners (d_stress_check.owners, the independent
    encoding); returns (min number of owners, profile, trace)."""
    import d_stress_check as DC
    cur = start or I.random_profile(rng)
    cc = len(DC.owners(I.sets, I.values(cur)))
    best, bestp, trace = cc, list(cur), [cc]
    for _ in range(steps):
        if cc == 0: break
        cand = list(cur)
        for i in rng.sample(range(I.n), rng.choice((1, 1, 2))):
            cand[i] = rng.randrange(len(I.dom[i]))
        k = len(DC.owners(I.sets, I.values(cand)))
        if k <= cc:
            cur, cc = cand, k
            if k < best: best, bestp = k, list(cand)
        trace.append(cc)
    return best, bestp, trace


def build(args, rng):
    fam = args[0]
    if fam == 'chain': return chain(int(args[1]), int(args[2]) if len(args) > 2 else 1)
    if fam == 'cycle': return cycle(int(args[1]))
    if fam == 'tree': return tree(int(args[1]))
    if fam == 'pure': return pure(int(args[1]), int(args[2]), rng)
    raise SystemExit('unknown family')


def git_head():
    """The current commit, flagged when a .py file in k4/ has uncommitted changes."""
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        run = lambda *a: subprocess.run(['git'] + list(a), capture_output=True, text=True, cwd=here).stdout.strip()
        return run('rev-parse', '--short', 'HEAD') + (' plus uncommitted changes to k4/*.py' if run('status', '--porcelain', '--', '*.py') else '')
    except Exception: return '?'


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    rng = random.Random(int(opts.get('seed', 1)))
    sets = build(args, rng)
    I = Inst(sets)
    print('commit %s' % git_head(), flush=True)
    if args[0] == 'pure': print('  hypergraph (seed %s): %s' % (opts.get('seed', 1), json.dumps(I.sets)), flush=True)
    n4 = sum(len(S) == 4 for S in I.sets)
    beta = sum(len(S) for S in I.sets) - I.n - I.m + 1
    print('%s: n = %d (%d with 4 goods), m = %d, beta = %d; domains %s' % (
        ' '.join(args), I.n, n4, I.m, beta, sorted(set(len(D) for D in I.dom))), flush=True)
    cap = int(opts.get('cap', 32))
    if opts.get('values') == 'paper':
        p = paper_profile(I)
        if not p: print('  paper values: not in the type domains (skipped)', flush=True)
        if p: print('  paper values: D2 %s, count %d' % ('yes' if I.shape(p) else 'NO', I.count(p, cap)), flush=True)
    npro = int(opts.get('profiles', 0))
    t0, worst, fails = time.time(), None, 0
    wit = []
    for k in range(npro):
        p = I.random_profile(rng)
        A = I.shape(p)
        if A is not None: wit.append([I.values(p), A])
        if A is None:
            fails += 1
            print('  NO D2 allocation: %s' % json.dumps(I.values(p)), flush=True)
            anyA = I.shape(p, None, None)
            print('    any shape: %s; two big bundles: %s' % (anyA is not None, I.shape(p, 2, 2) is not None), flush=True)
    if npro:
        print('  %d random profiles: %d without a D2 allocation (%.1f s); %d witnesses re-checked by the raw definition '
              'and the D2 shape' % (npro, fails, time.time() - t0, I.rechecked), flush=True)
        if 'witnesses' in opts:
            with gzip.open(opts['witnesses'], 'wt') as f: json.dump({'args': args, 'sets': I.sets, 'witnesses': wit}, f)
            print('  witnesses written to %s' % opts['witnesses'], flush=True)
    osteps = int(opts.get('owners', 0))
    if osteps:
        if opts.get('values') == 'paper' and paper_profile(I):
            print('  paper values: feasible large-bundle owners %d of %d' % (len(DC.owners(I.sets, I.values(paper_profile(I)))), I.n), flush=True)
        res = []
        for r in range(int(opts.get('restarts', 3))):
            t1 = time.time()
            b, bp, tr = climb_owners(I, rng, osteps)
            res.append(b)
            print('  owner climb %d: min feasible owners %d of %d after %d steps (%.0f s); trace %s' % (
                r, b, I.n, len(tr) - 1, time.time() - t1, tr[::max(1, len(tr) // 12)]), flush=True)
            if b == 0:
                print('  NO D2 allocation (owner climb): %s' % json.dumps(I.values(bp)), flush=True)
                print('    d_stress.py model: %s; any shape: %s' % ('D2' if I.shape(bp) else 'no D2',
                                                                     I.shape(bp, None, None) is not None), flush=True)
            else:
                print('  owners at the minimum: %s; profile %s' % (DC.owners(I.sets, I.values(bp)), json.dumps(I.values(bp))), flush=True)
        print('  min feasible owners over climbs: %d of %d' % (min(res), I.n), flush=True)
    steps = int(opts.get('climb', 0))
    if steps:
        restarts = int(opts.get('restarts', 3))
        res = []
        for r in range(restarts):
            b, bp, tr = climb(I, rng, steps, cap)
            res.append(b)
            print('  climb %d: min D2 count %d (cap %d) after %d steps; trace %s' % (r, b, cap, len(tr) - 1,
                                                                                     tr[::max(1, len(tr) // 10)]), flush=True)
            if b == 0:
                print('  NO D2 allocation (climb): %s' % json.dumps(I.values(bp)), flush=True)
                print('    any shape: %s' % (I.shape(bp, None, None) is not None), flush=True)
        print('  min over climbs: %d' % min(res), flush=True)


if __name__ == '__main__':
    main()
