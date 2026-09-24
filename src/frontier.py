"""Exhaustive, certified check of all CONNECTED cores with n agents and n+4 <= m <= 2n-1 goods (incl. multigraph cores).
Core: every agent has exactly 3 relevant goods (balanced, so EFX0 is ordinal), at most one private good, every good
relevant to someone. Agents with a private good have 2 shared goods, others 3; shared goods have degree >= 2.
Per hypergraph H (up to isomorphism), CEGAR over the 6^n ranking profiles:
  outer SAT picks a profile not covered by the allocations found so far; inner SAT finds a safe allocation in the model;
  the clause "some agent is unsafe under X" is computed with the RAW EFX0 definition (two balanced realizations).
Outer UNSAT => every profile covered. Certificate check: enumerate all 6^n profiles, verify coverage from raw masks.
Models: C2 = all bundles <= 2; C3s3 = one bundle may have 3 goods; C3 = one bundle of any size; G = unrestricted.
Cores come from nauty's genbg (cores_nauty.py; --enum python uses gen_cores below, which is much slower). Hypergraphs are
solved in parallel (--jobs, default: all CPUs). The v1 version of this file is in archive/v1-python-enumeration/.
Usage: frontier.py [n ...] [--jobs=N] [--enum=nauty|python]"""
import itertools, time, json, sys, collections, gzip, os, multiprocessing
import numpy as np, networkx as nx
from pysat.solvers import Glucose4
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

PERMS = list(itertools.permutations(range(3)))
VALS = [(2.0, 1.5, 1.0), (10.0, 9.0, 2.0)]

def gen_cores(n, m):
    out = []
    for pi in range(0, n + 1):
        ms = m - pi; excess = 3 * n - 2 * m + pi
        if excess < 0 or ms < 2: continue
        cap = 2 + excess
        pairs = list(itertools.combinations(range(ms), 2)); trips = list(itertools.combinations(range(ms), 3))
        deg = [0] * ms; chosen = []; buckets = {}
        def leaf():
            if min(deg) < 2 or any(deg[g] < deg[g + 1] for g in range(ms - 1)): return
            sets = [tuple(chosen[i]) + (ms + i,) for i in range(pi)] + [tuple(chosen[i]) for i in range(pi, n)]
            G = nx.Graph()
            for i, S in enumerate(sets):
                G.add_node(('a', i), kind='agent')
                for g in S: G.add_node(('g', g), kind='good'); G.add_edge(('a', i), ('g', g))
            if not nx.is_connected(G): return
            h = nx.weisfeiler_lehman_graph_hash(G, node_attr='kind', iterations=5)
            B = buckets.setdefault(h, [])
            if any(nx.is_isomorphic(G, G2, node_match=lambda x, y: x['kind'] == y['kind']) for G2 in B): return
            B.append(G); out.append((pi, sets))
        def rec(k, start):
            if sum(d - 2 for d in deg if d > 2) > excess: return
            rem = 2 * max(0, pi - k) + 3 * (n - max(k, pi))
            if sum(2 - d for d in deg if d < 2) > rem: return
            if k == n: leaf(); return
            cand = pairs if k < pi else trips
            for idx in range(0 if k == pi else start, len(cand)):
                S = cand[idx]
                if any(deg[g] >= cap for g in S): continue
                for g in S: deg[g] += 1
                chosen.append(S); rec(k + 1, idx); chosen.pop()
                for g in S: deg[g] -= 1
        rec(0, 0)
    return out

def build(n, m, sets, mode):
    pool = IDPool(); x = lambda g, j: pool.id(('x', g, j)); s = lambda g: pool.id(('s', g))
    cls = []
    for g in range(m):
        cls += CardEnc.equals(lits=[x(g, j) for j in range(n)], bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    for g in range(m):
        for j in range(n):
            for h in range(m):
                if h != g: cls.append([-s(g), -x(g, j), -x(h, j)])
    if mode == 'C2':
        for j in range(n):
            cls += CardEnc.atmost(lits=[x(g, j) for g in range(m)], bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    if mode in ('C3', 'C3s3'):
        big = [pool.id(('big', j)) for j in range(n)]
        for j in range(n):
            for g, h, k in itertools.combinations(range(m), 3): cls.append([big[j], -x(g, j), -x(h, j), -x(k, j)])
        cls += CardEnc.atmost(lits=big, bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    if mode == 'C3s3':
        for j in range(n):
            cls += CardEnc.atmost(lits=[x(g, j) for g in range(m)], bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
    sel = {}
    for i, S in enumerate(sets):
        for a in S:
            b, c = [g for g in S if g != a]
            yT = pool.id(('Ta2', i, a)); cls += [[-yT, x(a, i)], [-yT, x(b, i), x(c, i)]]
            y3 = pool.id(('T3', i, a)); cls.append([-y3, x(a, i)])
            if mode != 'C2':
                for j in range(n):
                    for h in range(m):
                        if h not in (b, c): cls.append([-y3, -x(b, j), -x(c, j), -x(h, j)])
            yP = pool.id(('P', i, a)); cls += [[-yP, x(b, i)], [-yP, x(c, i)]]
        for (a, b) in itertools.permutations(S, 2):
            yB = pool.id(('B', i, b, a)); cls += [[-yB, x(b, i)], [-yB, s(a)]]
        for c in S:
            a, b = [g for g in S if g != c]
            yC = pool.id(('C', i, c)); cls += [[-yC, x(c, i)], [-yC, s(a)], [-yC, s(b)]]
        yE = pool.id(('E', i)); cls += [[-yE, s(g)] for g in S]
        for k, p in enumerate(PERMS):
            a, b, c = S[p[0]], S[p[1]], S[p[2]]
            z = pool.id(('z', i, k)); sel[(i, k)] = z
            cls.append([-z, pool.id(('Ta2', i, a)), pool.id(('T3', i, a)), pool.id(('P', i, a)),
                        pool.id(('B', i, b, a)), pool.id(('C', i, c)), pool.id(('E', i))])
    return Glucose4(bootstrap_with=cls), sel, x

def raw_masks(n, m, sets, X):
    bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
    M = np.zeros((n, 6), dtype=bool)
    for i, S in enumerate(sets):
        for k, p in enumerate(PERMS):
            t = (S[p[0]], S[p[1]], S[p[2]]); ok = True
            for va, vb, vc in VALS:
                v = {t[0]: va, t[1]: vb, t[2]: vc}; own = sum(v.get(g, 0.0) for g in bundles[i])
                for j in range(n):
                    if j == i or len(bundles[j]) <= 1: continue
                    vs = [v.get(g, 0.0) for g in bundles[j]]
                    if sum(vs) - min(vs) > own + 1e-9: ok = False; break
                if not ok: break
            M[i, k] = ok
    return M

def cegar(n, m, sets, mode, limit=20000):
    inner, sel, x = build(n, m, sets, mode)
    pool = IDPool(); r = [[pool.id(('r', i, k)) for k in range(6)] for i in range(n)]
    outer = Glucose4()
    for i in range(n):
        for cl in CardEnc.equals(lits=r[i], bound=1, vpool=pool, encoding=EncType.pairwise).clauses: outer.add_clause(cl)
    masks, allocs, status, bad = [], [], 'OK', None
    while outer.solve():
        mdl = set(l for l in outer.get_model() if l > 0)
        prof = [next(k for k in range(6) if r[i][k] in mdl) for i in range(n)]
        if not inner.solve(assumptions=[sel[(i, prof[i])] for i in range(n)]): status, bad = 'FAIL', prof; break
        imdl = set(l for l in inner.get_model() if l > 0)
        X = [next(j for j in range(n) if x(g, j) in imdl) for g in range(m)]
        M = raw_masks(n, m, sets, X)
        if not all(M[i, prof[i]] for i in range(n)): status, bad = 'MODEL-MISMATCH', (prof, X); break
        masks.append(M); allocs.append(X)
        cl = [r[i][k] for i in range(n) for k in range(6) if not M[i, k]]
        if not cl: break
        outer.add_clause(cl)
        if len(masks) > limit: status = 'LIMIT'; break
    inner.delete(); outer.delete()
    return status, bad, masks, allocs

def certify(n, masks):
    """Number of the 6^n ranking profiles covered by no allocation. Axis i of cov is agent i's ranking; an allocation
    covers the box of profiles in which every agent i is safe, i.e. the product of the sets {k : M[i, k]}."""
    cov = np.zeros((6,) * n, dtype=bool)
    for M in masks: cov[np.ix_(*(np.flatnonzero(M[i]) for i in range(n)))] = True
    return int((~cov).sum())

def solve_core(task):
    """Try the models in order on one hypergraph; return its result record and, if a model succeeds, its certificate."""
    n, m, pi, sets, modes = task
    rec, cert = {'n': n, 'm': m, 'pi': pi, 'sets': sets, 'modes': {}}, None
    for md in modes:
        st, bad, masks, allocs = cegar(n, m, sets, md)
        rec['modes'][md] = {'status': st, 'bad': bad, 'ncert': len(masks)}
        if st == 'OK':
            unc = certify(n, masks); rec['modes'][md]['uncovered'] = unc
            rec['final'] = md if unc == 0 else md + '-CERTFAIL'
            cert = {'n': n, 'm': m, 'pi': pi, 'sets': sets, 'mode': md, 'allocations': allocs}; break
        if st != 'FAIL': rec['final'] = md + '-' + st; break
    else: rec['final'] = 'NO-EFX0'
    return rec, cert

def options(argv):
    """Positional integers, plus --key=value flags (a bare --key means --key=1)."""
    return [int(a) for a in argv if not a.startswith('--')], dict((a[2:].split('=', 1) + ['1'])[:2] for a in argv if a.startswith('--'))

if __name__ == '__main__':
    from cores_nauty import gen_cores_nauty
    levels, opts = options(sys.argv[1:]); levels = levels or [5, 6]
    enum = gen_cores if opts.get('enum') == 'python' else gen_cores_nauty
    jobs = int(opts.get('jobs', os.cpu_count()))
    tag = "_".join(map(str, levels)); t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True)
    results, certs, problems = [], [], 0
    with multiprocessing.Pool(jobs) as pool:
        for n in levels:
            for m in range(n + 4, 2 * n):
                t1 = time.time(); cores = enum(n, m)
                log(f"n={n} m={m} beta={2*n-m+1}: {len(cores)} connected cores (generated in {time.time()-t1:.0f}s, {jobs} jobs)")
                modes = ['C2', 'C3', 'G'] if m <= 2 * n - 2 else ['C2', 'C3s3', 'C3', 'G']
                tally = collections.Counter()
                for rec, cert in pool.imap(solve_core, [(n, m, pi, sets, modes) for pi, sets in cores]):
                    if cert: certs.append(cert)
                    if rec['final'] not in ('C2', 'C3s3', 'C3', 'G'): problems += 1
                    tally['final=' + rec['final']] += 1
                    if rec['modes']['C2']['status'] == 'FAIL': tally['C2 fails'] += 1
                    results.append(rec)
                log(f"n={n} m={m} DONE: {dict(tally)}")
                json.dump(results, open(f'frontier_results_{tag}.json', 'w'))
                with gzip.open(f'certs_{tag}.json.gz', 'wt') as f: json.dump(certs, f)
    log(f"ALL DONE; problems: {problems}"); sys.exit(1 if problems else 0)
