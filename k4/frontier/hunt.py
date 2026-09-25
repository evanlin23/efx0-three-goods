"""Counterexample hunt beyond the certified range (EVIDENCE only, PROMPT.md §5 rule 3): random and structured k = 4
cores with n = 6..8, random and adversarial strict profiles.

Cores: agents of degree 3 or 4 (--p4: probability of 4; --pure: all 4). Each agent gets p_i <= d_i - 2 private goods;
the remaining slots go to m_s shared goods, each of degree >= 2, drawn with weights w_g ~ g^(-skew) (skew > 0 makes
hub goods relevant to many agents, the setting of k = 3's top-collision failures). Rejected unless every agent's goods
are distinct and the incidence graph is connected, so every output is a k = 4 core (checked by check4.is_core).
Profiles: types from search4's strict balanced representatives (with p + q < s + t for two private goods); "hard"
types are each agent's quarter of types unsafe in the most local configurations (hardness()).
Per core: --rand random profiles (half uniform, half from the hard types), each solved in the D2 model (search4.Core.inner: at most one bundle of more than 2
goods; incremental SAT with activation literals); then --climb steps of hill-climbing on the profile that minimizes the
score: for each choice of the large bundle's owner (or no large bundle), the number of D2 EFX₀ allocations with that
owner, capped at --cap, summed (score 0 = no D2 allocation), starting from a "collision" profile (every agent ranks
its highest-degree goods first). A profile with no D2 allocation is solved again without
the shape limit and written to --out; it counts only after the independent check verify_fail.c (brute force,
raw definition) confirms it.

Usage: hunt.py --n=6 [--m=LO:HI] [--p4=0.5|--pure] [--skew=0] [--cores=100] [--rand=200] [--climb=150] [--cap=2]
               [--seed=1] [--jobs=J] [--out=results/k4_hunt_fail.jsonl]"""
import json, os, sys, time
import numpy as np
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import search4 as S4
import check4 as CK

def random_core(rng, n, m_lo, m_hi, p4, skew, tries=10000):
    for _ in range(tries):
        m = int(rng.integers(m_lo, m_hi + 1))
        d = [4 if rng.random() < p4 else 3 for _ in range(n)]
        if 4 not in d: d[int(rng.integers(n))] = 4
        p = [int(rng.integers(0, di - 1)) for di in d]          # 0..d-2 private goods
        ms = m - sum(p)
        slots = sum(di - pi for di, pi in zip(d, p))
        if ms < 1 or slots < 2 * ms: continue
        w = np.arange(1, ms + 1, dtype=float) ** (-skew); w /= w.sum()
        # each shared good needs degree >= 2: two guaranteed slots each, the rest by weight
        extra = rng.multinomial(slots - 2 * ms, w) if slots > 2 * ms else np.zeros(ms, int)
        pool = [g for g in range(ms) for _ in range(2 + extra[g])]
        rng.shuffle(pool)
        sets, k, nxt = [], 0, ms
        ok = True
        for i in range(n):
            S = pool[k:k + d[i] - p[i]]; k += d[i] - p[i]
            if len(set(S)) != len(S): ok = False; break
            S = list(S) + list(range(nxt, nxt + p[i])); nxt += p[i]
            sets.append(sorted(S))
        if not ok: continue
        good, _ = CK.is_core(n, m, sets, all(x == 4 for x in d))
        if good: return m, sets
    return None

def partitions(xs):
    if not xs: yield []; return
    first, rest = xs[0], xs[1:]
    for P in partitions(rest):
        yield [[first]] + P
        for i in range(len(P)): yield P[:i] + [[first] + P[i]] + P[i + 1:]

def hardness(v):
    """Number of local configurations (own part O of R_i; the rest of R_i split into other bundles, each with or
    without a good outside R_i) in which type v is not safe (raw definition). Hard types have few safe spots."""
    k, bad = len(v), 0
    for O in range(1 << k):
        vO = sum(v[p] for p in range(k) if O >> p & 1)
        for P in partitions([p for p in range(k) if not O >> p & 1]):
            for ext in range(1 << len(P)):
                bad += any(vO < sum(v[p] for p in B) - (0 if ext >> b & 1 else min(v[p] for p in B)) for b, B in enumerate(P))
    return bad

class Hunter:
    def __init__(self, n, m, sets, rng):
        self.C = S4.Core(n, m, sets)
        self.sol, self.x, self.z = self.C.inner(2, 1)
        self.rng, self.n, self.m, self.sets = rng, n, m, sets
        self.sel = self.C.vp.top + 1000000                    # fresh selector literals for blocking clauses
        self.big = [self.C.vp.obj2id[('big', j)] for j in range(n)] if ('big', 0) in self.C.vp.obj2id else None
        self.hard = []                                          # per agent: its hardest quarter of types
        for D in self.C.dom:
            h = [hardness(v) for v in D]
            cut = sorted(h, reverse=True)[max(0, len(h) // 4 - 1)]
            self.hard.append([t for t in range(len(D)) if h[t] >= cut])

    def count(self, prof, cap, extra=()):
        """Number of D2 EFX₀ allocations for prof (under the extra assumptions), up to cap (blocking clauses guarded
        by a fresh selector, retired afterwards)."""
        self.sel += 1; s = self.sel
        assum = [self.z[i][t] for i, t in enumerate(prof)] + list(extra) + [s]
        c = 0
        while c < cap and self.sol.solve(assumptions=assum):
            mod = self.sol.get_model()
            own = [next(j for j in range(self.n) if mod[self.x[g][j] - 1] > 0) for g in range(self.m)]
            self.sol.add_clause([-s] + [-self.x[g][own[g]] for g in range(self.m)])
            c += 1
        self.sol.add_clause([-s])
        return c

    def score(self, prof, cap):
        """Sum over the large bundle's owner (none, or agent j) of the capped count; 0 iff no D2 allocation."""
        if self.big is None: return self.count(prof, cap)
        opts = [[-b for b in self.big]] + [[-b for k, b in enumerate(self.big) if k != j] for j in range(self.n)]
        return sum(self.count(prof, cap, o) for o in opts)

    def collision_profile(self):
        """Every agent's type: the one whose ranking puts its highest-degree goods first (ties at random)."""
        deg = [sum(g in S for S in self.sets) for g in range(self.m)]
        prof = []
        for i, S in enumerate(self.sets):
            key = [deg[g] + self.rng.random() for g in S]
            cands = [t for t, v in enumerate(self.C.dom[i])
                     if sorted(range(len(S)), key=lambda p: -v[p]) == sorted(range(len(S)), key=lambda p: -key[p])]
            prof.append(int(self.rng.choice(cands)) if cands else int(self.rng.integers(len(self.C.dom[i]))))
        return prof

def fail_record(h, prof, how):
    C = h.C
    sol, x, z = C.inner(None, None)
    A = C.allocation(sol, x, z, prof)
    return {'n': h.n, 'm': h.m, 'sets': h.sets, 'profile': [list(C.dom[i][t]) for i, t in enumerate(prof)],
            'found_by': how, 'efx0_any_shape': A is not None, 'alloc_any_shape': A}

def hunt_core(task):
    n, m_lo, m_hi, p4, skew, seed, R, climb, cap = task
    rng = np.random.default_rng(seed)
    rc = random_core(rng, n, m_lo, m_hi, p4, skew)
    if rc is None: return {'seed': seed, 'core': None}
    m, sets = rc
    t0 = time.time()
    h = Hunter(n, m, sets, rng)
    sizes = [len(D) for D in h.C.dom]
    fails, mins = [], []
    for r_ in range(R):                                          # half uniform, half from the hardest quarter
        prof = [int(rng.integers(s)) for s in sizes] if r_ % 2 == 0 else [int(rng.choice(H)) for H in h.hard]
        if not h.sol.solve(assumptions=[h.z[i][t] for i, t in enumerate(prof)]): fails.append(fail_record(h, prof, 'random'))
    prof = h.collision_profile()
    cur = h.score(prof, cap); best = cur; evals = 1
    T = 2.0
    for step in range(climb):
        if cur == 0: fails.append(fail_record(h, prof, 'climb')); break
        new = list(prof)
        i = int(rng.integers(n)); new[i] = int(rng.choice(h.hard[i])) if rng.random() < 0.7 else int(rng.integers(sizes[i]))
        c = h.score(new, cap); evals += 1
        if c <= cur or rng.random() < np.exp((cur - c) / T):
            prof, cur = new, c
            best = min(best, cur)
        T = max(0.1, T * 0.98)
    return {'seed': seed, 'n': n, 'm': m, 'sets': sets, 'n4': sum(len(S) == 4 for S in sets), 'min_count': best,
            'final_count': cur, 'evals': evals, 'fails': fails, 'time': round(time.time() - t0, 1)}

def main():
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    n = int(opt.get('n', 6))
    m_lo, m_hi = map(int, opt.get('m', f'{n}:{2 * n + 2}').split(':'))
    p4 = 1.0 if 'pure' in opt else float(opt.get('p4', 0.5))
    skew, ncores, seed = float(opt.get('skew', 0)), int(opt.get('cores', 100)), int(opt.get('seed', 1))
    R, climb, cap = int(opt.get('rand', 200)), int(opt.get('climb', 150)), int(opt.get('cap', 2))
    out = opt.get('out')
    print(f"command: python3 k4/frontier/hunt.py {' '.join(sys.argv[1:])}", flush=True)
    tasks = [(n, m_lo, m_hi, p4, skew, seed * 100003 + k, R, climb, cap) for k in range(ncores)]
    t0, done, nf, hist = time.time(), 0, 0, {}
    with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
        for r in pool.imap_unordered(hunt_core, tasks):
            if r.get('core', 1) is None: continue
            done += 1
            hist[r['min_count']] = hist.get(r['min_count'], 0) + 1
            for f in r['fails']:
                nf += 1
                print(f"  CANDIDATE (no D2 allocation; EFX0 in any shape: {f['efx0_any_shape']}): {json.dumps(f)}", flush=True)
                if out:
                    with open(out, 'a') as fo: fo.write(json.dumps(f) + '\n')
            if r['min_count'] <= 2:
                print(f"  seed {r['seed']} m={r['m']} n4={r['n4']}: min score {r['min_count']} ({r['evals']} evals, {r['time']}s) sets={r['sets']}", flush=True)
    print(f"n={n} m={m_lo}..{m_hi} p4={p4} skew={skew}: {done} cores, {done * R} random profiles + hill-climbing "
          f"({climb} steps, cap {cap}); candidates: {nf}; min scores (score: count): {dict(sorted(hist.items()))} [{time.time() - t0:.0f}s]", flush=True)

if __name__ == '__main__':
    main()
