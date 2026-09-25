"""k = 4 small-case search: every k = 4 core hypergraph, every profile of strict balanced order types (k4/order_types.py).

k = 4 core (k4/SCOUT.md §2): connected; every agent has 3 or 4 relevant goods; every good is relevant to some agent;
an agent with 4 goods has at most 2 private goods (valued by no other agent), one with 3 goods at most 1. Types: an
agent with 4 goods takes any of the 288 labeled strict balanced types (a < b + c + d), restricted to p + q < s + t when
it has 2 private goods p, q (else rule R2 peels it); one with 3 goods takes any of the 6 strict balanced types.
By the closure lemma of SCOUT.md §2, tied profiles need no separate search.

Per hypergraph, CEGAR as in src/frontier.py: an outer SAT over profiles (one type per agent) proposes a profile not yet
covered; an inner SAT finds an allocation for it in the model "at most c bundles with more than s goods" (s = None:
no shape limit); the profiles the allocation covers (for each agent the set of types under which it is safe, from the
raw EFX₀ definition with the types' integer representatives) are blocked. A profile with no allocation is recorded
and blocked alone; after `cap` of them the model is abandoned.
Pipeline per hypergraph (models D2 = (2, 1), D3 = (3, 1), ANY): run D2; the profiles it fails are solved in D3 or ANY
(and their minimum numbers of bundles with > 2 and > 3 goods are recorded); if D2 fails more than `cap` profiles,
run D3, then ANY, the same way. The certificate is the allocations used (they cover every profile).

Usage: search4.py n [n ...] [--pure] [--cap=N] [--jobs=J] [--out=results/k4_certs_n.json.gz]
  --pure: only cores whose agents all have 4 goods (default: cores with agent degrees 3 and 4, at least one 4)."""
import ctypes, gzip, json, itertools, os, shutil, subprocess, sys, time
import numpy as np
from multiprocessing import Pool
import networkx as nx
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

HERE = os.path.dirname(os.path.abspath(__file__))
GENBG = shutil.which('genbg') or shutil.which('nauty-genbg')
OT = json.load(open(os.path.join(HERE, 'order_types.json')))
_so = os.path.join(HERE, 'scan.so')
if not os.path.exists(_so) or os.path.getmtime(_so) < os.path.getmtime(os.path.join(HERE, 'scan.c')):
    subprocess.run(['gcc', '-O2', '-shared', '-fPIC', '-o', _so, os.path.join(HERE, 'scan.c')], check=True)
SCAN = ctypes.CDLL(_so)
STRICT_BAL = {k: [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict'] and t['balanced']] for k in (3, 4)}

def cores(n, m, pure):
    """k = 4 cores (connected) with n agents and m goods, one per isomorphism class: list of agent good-lists."""
    lo = 4 * n if pure else 3 * n + 1
    args = [GENBG, '-cq', f'-d{4 if pure else 3}:1', f'-D4:{n}', str(n), str(m), f'{lo}:{4 * n}']
    out = []
    for line in subprocess.run(args, capture_output=True, text=True, check=True).stdout.split():
        G = nx.from_graph6_bytes(line.encode())
        sets = [sorted(g - n for g in G[i]) for i in range(n)]
        deg = [G.degree(n + g) for g in range(m)]
        if all(sum(deg[g] == 1 for g in S) <= len(S) - 2 for S in sets):   # <= 2 private (4 goods), <= 1 (3 goods)
            out.append(sets)
    return out

def domain(S, deg):
    """Types (integer values on S, in S's order) an agent with good list S may take in a core."""
    priv = [p for p, g in enumerate(S) if deg[g] == 1]
    dom = STRICT_BAL[len(S)]
    if len(priv) == 2:
        dom = [v for v in dom if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
    return dom

class Core:
    def __init__(self, n, m, sets):
        self.n, self.m, self.sets = n, m, sets
        deg = [sum(g in S for S in sets) for g in range(m)]
        self.dom = [domain(S, deg) for S in sets]
        self.cache = {}

    def safe_mask(self, i, owner):
        """Bitmask over self.dom[i]: types under which agent i is safe (raw EFX₀ with the integer representative)."""
        S = self.sets[i]
        pos = {g: p for p, g in enumerate(S)}
        O = sum(1 << pos[g] for g in S if owner[g] == i)
        groups = {}
        for g in range(self.m):
            j = owner[g]
            if j == i: continue
            G, extra = groups.get(j, (0, False))
            groups[j] = (G | 1 << pos[g], extra) if g in pos else (G, True)
        key = (i, O, tuple(sorted(x for x in groups.values() if x[0])))
        if key in self.cache: return self.cache[key]
        mask = 0
        for t, v in enumerate(self.dom[i]):
            vO = sum(v[p] for p in range(len(S)) if O >> p & 1)
            ok = True
            for G, extra in key[2]:
                vals = [v[p] for p in range(len(S)) if G >> p & 1]
                if vO < sum(vals) - (0 if extra else min(vals)): ok = False; break
            if ok: mask |= 1 << t
        self.cache[key] = mask
        return mask

    def inner(self, s, c):
        """Allocation solver with activation literals z[i][t]; shape: at most c bundles with more than s goods."""
        n, m, vp = self.n, self.m, IDPool()
        x = [[vp.id(('x', g, j)) for j in range(n)] for g in range(m)]
        cl = []
        for g in range(m):
            cl += CardEnc.equals([x[g][j] for j in range(n)], 1, vpool=vp, encoding=EncType.pairwise).clauses
        if s is not None and s < m:
            big = [vp.id(('big', j)) for j in range(n)]
            for j in range(n):
                cl += [c_ + [big[j]] for c_ in CardEnc.atmost([x[g][j] for g in range(m)], s, vpool=vp,
                                                              encoding=EncType.seqcounter).clauses]
            if c < n: cl += CardEnc.atmost(big, c, vpool=vp, encoding=EncType.seqcounter).clauses
        z = []
        for i, S in enumerate(self.sets):
            k = len(S)
            ext = {j: vp.id(('e', i, j)) for j in range(n) if j != i}
            for j in ext:
                cl += [[-x[h][j], ext[j]] for h in range(m) if h not in S]
            guards = {}
            zi = []
            for t, v in enumerate(self.dom[i]):
                zt = vp.id(('z', i, t)); zi.append(zt)
                for O in range(1 << k):
                    vO = sum(v[p] for p in range(k) if O >> p & 1)
                    for G in range(1, 1 << k):
                        if G & O: continue
                        vals = [v[p] for p in range(k) if G >> p & 1]
                        for kind, bad in (('E', vO < sum(vals) - min(vals)), ('F', vO < sum(vals))):
                            if not bad: continue
                            if (O, G, kind) not in guards:
                                u = guards[(O, G, kind)] = vp.id(('u', i, O, G, kind))
                                for j in ext:
                                    base = [-u] + [x[S[p]][i] for p in range(k) if not O >> p & 1] \
                                           + [-x[S[p]][j] for p in range(k) if G >> p & 1]
                                    cl.append(base if kind == 'E' else base + [-ext[j]])
                            cl.append([-zt, guards[(O, G, kind)]])
            z.append(zi)
        self.vp = vp
        sol = Solver(name='cd15', bootstrap_with=cl)
        return sol, x, z

    def allocation(self, sol, x, z, prof):
        if not sol.solve(assumptions=[z[i][t] for i, t in enumerate(prof)]): return None
        mod = set(l for l in sol.get_model() if l > 0)
        return [next(j for j in range(self.n) if x[g][j] in mod) for g in range(self.m)]

    def best_allocation(self, sol, x, z, prof, tries):
        """Among up to `tries` allocations for prof, the one whose covered box is largest (log volume)."""
        sel = self.vp.id(('sel', len(self.vp.obj2id)))
        best, bestv = None, None
        for _ in range(tries):
            if not sol.solve(assumptions=[z[i][t] for i, t in enumerate(prof)] + [sel]): break
            mod = set(l for l in sol.get_model() if l > 0)
            A = [next(j for j in range(self.n) if x[g][j] in mod) for g in range(self.m)]
            masks = [self.safe_mask(i, A) for i in range(self.n)]
            vol = sum(np.log(bin(mk).count('1')) for mk in masks)
            if bestv is None or vol > bestv: best, bestv = (A, masks), vol
            sol.add_clause([-sel] + [-x[g][A[g]] for g in range(self.m)])
        sol.add_clause([-sel])
        return best

    def cegar(self, s, c, cap, extra_allocs=(), tries=8):
        """Returns (allocations, failing profiles, complete?). The C scanner (scan.c) proposes the first profile no
        allocation so far covers; a failing profile is blocked alone by a column covering just that profile."""
        n = self.n
        dom = (ctypes.c_int * n)(*[len(D) for D in self.dom])
        base = np.cumsum([0] + [len(D) for D in self.dom])
        cbase = (ctypes.c_long * n)(*base[:n].tolist())
        M = np.zeros((base[-1], 16), dtype=np.uint64)
        ncol = 0
        def add(masks):
            nonlocal M, ncol
            if ncol == 64 * M.shape[1]: M = np.concatenate([M, np.zeros_like(M)], axis=1)
            for i in range(n):
                ts = [t for t in range(len(self.dom[i])) if masks[i] >> t & 1]
                M[base[i] + np.array(ts, dtype=np.int64), ncol // 64] |= np.uint64(1 << (ncol % 64))
            ncol += 1
        sol, x, z = self.inner(s, c)
        allocs, fails = [], []
        start = (ctypes.c_int * n)(*([0] * n)); out = (ctypes.c_int * n)()
        for A in extra_allocs: add([self.safe_mask(i, A) for i in range(n)])
        while True:
            W = max(1, (ncol + 63) // 64)
            Mc = np.ascontiguousarray(M[:, :W])
            if not SCAN.scan(n, dom, W, Mc.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64)), cbase, start, out):
                return allocs, fails, True
            prof = list(out)
            for i in range(n): start[i] = prof[i]
            best = self.best_allocation(sol, x, z, prof, tries)
            if best is None:
                fails.append(prof)
                if len(fails) > cap: return allocs, fails, False
                add([1 << t for t in prof])
                continue
            allocs.append(best[0])
            add(best[1])

    def min_big(self, prof, s):
        """Fewest bundles with more than s goods over EFX₀ allocations for this profile."""
        for c in range(self.n + 1):
            sol, x, z = self.inner(s, c)
            if self.allocation(sol, x, z, prof) is not None: return c
        return None

def sizes(A, n):
    return sorted((A.count(j) for j in range(n)), reverse=True)

def solve(task):
    n, m, idx, sets, cap = task
    C, t0 = Core(n, m, sets), time.time()
    rec = {'n': n, 'm': m, 'idx': idx, 'sets': sets, 'domains': [len(D) for D in C.dom]}
    allocs, fails, complete = C.cegar(2, 1, cap)
    rec['D2_fails'] = len(fails) if complete else f'>{cap}'
    model_used = 'D2'
    if not complete:
        allocs, fails, complete = C.cegar(3, 1, cap)
        rec['D3_fails'] = len(fails) if complete else f'>{cap}'
        model_used = 'D3'
        if not complete:
            allocs, fails, complete = C.cegar(None, None, cap)
            model_used = 'ANY'
    rec['model'], rec['fail_profiles'] = model_used, []
    for prof in fails:
        sol, x, z = C.inner(None, None)
        A = C.allocation(sol, x, z, prof)
        info = {'profile': [list(C.dom[i][t]) for i, t in enumerate(prof)], 'efx0': A is not None}
        if A is not None:
            info['min_big2'], info['min_big3'] = C.min_big(prof, 2), C.min_big(prof, 3)
            sol, x, z = C.inner(3, info['min_big3'])
            A = C.allocation(sol, x, z, prof)
            info['alloc'] = A
            allocs.append(A)
        rec['fail_profiles'].append(info)
    rec['counterexample'] = any(not f['efx0'] for f in rec['fail_profiles']) or not complete
    rec['allocs'] = allocs
    rec['time'] = round(time.time() - t0, 2)
    return rec

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    pure, cap, jobs = 'pure' in opt, int(opt.get('cap', 20)), int(opt.get('jobs', os.cpu_count()))
    for n in map(int, args):
        t0, tasks = time.time(), []
        for m in range(4, 3 * n + 1):
            for idx, sets in enumerate(cores(n, m, pure)): tasks.append((n, m, idx, sets, cap))
        print(f"n={n} ({'pure' if pure else 'degrees 3-4'}): {len(tasks)} cores", flush=True)
        out, stats = [], {}
        with Pool(jobs) as pool:
            for rec in pool.imap_unordered(solve, tasks, chunksize=1):
                out.append(rec)
                st = stats.setdefault(rec['m'], {'cores': 0, 'D2 fails': 0, 'D3 fails': 0, 'cex': 0, 'allocs': 0})
                st['cores'] += 1; st['allocs'] += len(rec['allocs'])
                st['D2 fails'] += rec['D2_fails'] != 0
                st['D3 fails'] += rec.get('D3_fails', 0) != 0 or any(f.get('min_big3', 0) > 1 for f in rec['fail_profiles'])
                st['cex'] += rec['counterexample']
                if rec['counterexample']: print("  COUNTEREXAMPLE CANDIDATE", rec['sets'], rec['fail_profiles'][:1], flush=True)
        out.sort(key=lambda r: (r['m'], r['idx']))
        for m, st in sorted(stats.items()): print(f"  m={m}: {st}", flush=True)
        print(f"  [{time.time() - t0:.0f}s]", flush=True)
        path = opt.get('out', os.path.join(HERE, f"k4_certs_{n}{'_pure' if pure else ''}.json.gz"))
        with gzip.open(path, 'wt') as f: json.dump({'n': n, 'pure': pure, 'cores': out}, f, separators=(',', ':'))
        print(f"  wrote {path}", flush=True)

if __name__ == '__main__':
    main()
