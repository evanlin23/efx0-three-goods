"""Independent checker for the certificates of k4/hunt/run.py (shares no code with cegar.py or search4.py).

For each certificate file (results/k4_hunt/*.json.gz; parts of one class may be given together):
  1. every listed hypergraph is a connected k = 4 core (agent degrees 3, 4; every good valued; an agent of degree d has
     at most d - 2 private goods) with exactly n4 agents of degree 4; no two are isomorphic; and the orbit sum
     sum n! m! / |Aut(H)| equals the number of labeled such cores (check4.labeled_count, the DP of k4/check4.py,
     self-tested there), so the list is the whole class (only when every part of the class is given and 'all' cores);
  2. every allocation is a complete assignment of the m goods to the n agents;
  3. coverage: under every profile of strict balanced types (types enumerated here from [1,16]^d, keyed by the signs of
     v(A) - v(B) over disjoint nonempty A, B; an agent of degree 4 with two private goods p, q also has
     p + q < s + t) some listed allocation is EFX₀ by the raw definition v_i(X_i) >= v_i(X_j) - v_i(h) for every
     j != i and h in X_j. Checked as UNSAT of: one type per agent (totalizer encoding) and, per allocation, "some agent
     has a type under which it is unsafe" (one-hot literals), with Glucose 4 (cegar.py uses CaDiCaL and comparison
     bits). Default engine: k4/check4_fast.py's C coverage loop fed with this file's types and safety rows
     (--engine=dfs); --engine=sat2 groups the one-hot literals by distinct unsafe set per (agent, other bundle),
     which scales to all-4-good n = 6 cores; --sat-sample=K also runs the plain one-hot SAT engine on K random cores.
Usage: check.py FILE [FILE ...] [--jobs=J] [--expect=N] [--engine=dfs|sat|sat2] [--sat-sample=K]   (exit status nonzero on any failure)"""
import sys, os, gzip, json, itertools, math
from functools import lru_cache
from multiprocessing import Pool
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
from pysat.solvers import Glucose4
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import check4     # only for labeled_count (the orbit-counting DP, written independently of search4.py)


@lru_cache(maxsize=None)
def types(d):
    subs = [S for S in range(1, 1 << d)]
    pairs = [(A, B) for A in subs for B in subs if A < B and not A & B]
    reps = {}
    for v in itertools.product(range(1, 17), repeat=d):
        s = {S: sum(v[p] for p in range(d) if S >> p & 1) for S in subs}
        if len(set(s.values())) < len(s): continue                 # not strict
        if 2 * max(v) >= sum(v): continue                         # not balanced
        key = tuple(s[A] > s[B] for A, B in pairs)
        reps.setdefault(key, v)
    return list(reps.values())


def domains(sets, m):
    deg = [sum(g in S for S in sets) for g in range(m)]
    out = []
    for S in sets:
        priv = [p for p, g in enumerate(S) if deg[g] == 1]
        D = types(len(S))
        if len(priv) == 2:
            D = [v for v in D if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
        out.append(D)
    return out


def unsafe(i, S, v, bundles):
    val = dict(zip(S, v))
    own = sum(val.get(g, 0) for g in bundles[i])
    for j, B in enumerate(bundles):
        if j == i: continue
        tot = sum(val.get(g, 0) for g in B)
        for h in B:
            if own < tot - val.get(h, 0): return True
    return False


def covered_sat(task):
    n, m, sets, allocs = task[:4]
    D = domains(sets, m)
    V = []                                    # V[i][t, g] = value of good g to agent i under its t-th type (0 if irrelevant)
    for i, S in enumerate(sets):
        Vi = np.zeros((len(D[i]), m), dtype=np.int64)
        for p, g in enumerate(S): Vi[:, g] = [v[p] for v in D[i]]
        V.append(Vi)
    vp = IDPool()
    z = [[vp.id((i, t)) for t in range(len(D[i]))] for i in range(n)]
    s = Glucose4()
    for zi in z:
        for c in CardEnc.equals(zi, 1, vpool=vp, encoding=EncType.totalizer).clauses: s.add_clause(c)
    for A in allocs:
        if len(A) != m or any(not (0 <= j < n) for j in A): return False, 'malformed allocation'
        cl = []
        for i in range(n):
            own = V[i][:, [g for g in range(m) if A[g] == i]].sum(axis=1)
            bad = np.zeros(len(D[i]), dtype=bool)
            for j in range(n):
                if j == i: continue
                Bj = [g for g in range(m) if A[g] == j]
                if not Bj: continue
                tot = V[i][:, Bj].sum(axis=1)
                for h in Bj: bad |= own < tot - V[i][:, h]          # raw: v_i(X_i) >= v_i(X_j) - v_i(h)
            cl += [z[i][t] for t in np.flatnonzero(bad)]
        s.add_clause(cl)
    ok = not s.solve()
    msg = ''
    if ok is False:
        mod = set(l for l in s.get_model() if l > 0)
        msg = f'uncovered profile {[D[i][t] for i in range(n) for t in range(len(D[i])) if z[i][t] in mod]}'
    s.delete()
    return ok, msg

def unsafe_table(n, m, sets, allocs):
    """bad[i][a] = boolean array over agent i's types: unsafe in allocation a (raw definition)."""
    D = domains(sets, m)
    V = []
    for i, S in enumerate(sets):
        Vi = np.zeros((len(D[i]), m), dtype=np.int64)
        for p, g in enumerate(S): Vi[:, g] = [v[p] for v in D[i]]
        V.append(Vi)
    bad = [[None] * len(allocs) for _ in range(n)]
    for a, A in enumerate(allocs):
        if len(A) != m or any(not (0 <= j < n) for j in A): return D, None
        for i in range(n):
            own = V[i][:, [g for g in range(m) if A[g] == i]].sum(axis=1)
            b = np.zeros(len(D[i]), dtype=bool)
            for j in range(n):
                if j == i: continue
                Bj = [g for g in range(m) if A[g] == j]
                if not Bj: continue
                tot = V[i][:, Bj].sum(axis=1)
                for h in Bj: b |= own < tot - V[i][:, h]          # raw: v_i(X_i) >= v_i(X_j) - v_i(h)
            bad[i][a] = b
    return D, bad


def covered_dfs(task):
    """Coverage by k4/check4_fast.py's C loop (minimal types, full-safety skip, memo), fed with this file's own types
    and raw-definition safety rows."""
    import ctypes
    import check4_fast
    n, m, sets, allocs = task[:4]
    D, bad = unsafe_table(n, m, sets, allocs)
    if bad is None: return False, 'malformed allocation'
    K = len(allocs); W = max(1, (K + 63) // 64)
    off = [0]
    for Di in D: off.append(off[-1] + len(Di) * W)
    M = (ctypes.c_uint64 * off[-1])()
    Mn = np.ctypeslib.as_array(M)
    for a in range(K):
        for i in range(n):
            Mn[off[i] + np.flatnonzero(~bad[i][a]) * W + a // 64] |= np.uint64(1 << (a % 64))
    F = (ctypes.c_uint64 * ((n + 1) * W))()
    Fn = np.ctypeslib.as_array(F).reshape(n + 1, W)
    Fn[n] = ~np.uint64(0)
    for l in range(n - 1, -1, -1):
        Fn[l] = Fn[l + 1] & np.bitwise_and.reduce(Mn[off[l]:off[l + 1]].reshape(len(D[l]), W), axis=0)
    ok = check4_fast.coverage(n, W, [len(Di) for Di in D], off, M, F)
    return ok, '' if ok else 'not covered (dfs)'


def covered_sat2(task):
    """SAT coverage with one variable per distinct unsafe set: for agent i and another bundle B of allocation X, the
    types t with v_t(X_i) < v_t(B) - v_t(h) for some h in B (raw definition) form a set W; u_W <-> OR_{t in W} z_t; the
    allocation adds the clause OR over (i, B) of u_W. Equivalent to the one-hot clause, grouped (Glucose 4)."""
    n, m, sets, allocs = task[:4]
    D = domains(sets, m)
    V = []
    for i, S in enumerate(sets):
        Vi = np.zeros((len(D[i]), m), dtype=np.int64)
        for p, g in enumerate(S): Vi[:, g] = [v[p] for v in D[i]]
        V.append(Vi)
    vp = IDPool()
    z = [[vp.id((i, t)) for t in range(len(D[i]))] for i in range(n)]
    s = Glucose4()
    for zi in z:
        for c in CardEnc.equals(zi, 1, vpool=vp, encoding=EncType.totalizer).clauses: s.add_clause(c)
    group = {}
    for A in allocs:
        if len(A) != m or any(not (0 <= j < n) for j in A): return False, 'malformed allocation'
        cl = []
        for i in range(n):
            own = V[i][:, [g for g in range(m) if A[g] == i]].sum(axis=1)
            for j in range(n):
                Bj = [g for g in range(m) if A[g] == j]
                if j == i or not Bj: continue
                tot = V[i][:, Bj].sum(axis=1)
                w = np.zeros(len(D[i]), dtype=bool)
                for h in Bj: w |= own < tot - V[i][:, h]
                if not w.any(): continue
                key = (i, np.packbits(w).tobytes())
                if key not in group:
                    u = group[key] = vp.id(('u',) + key)
                    ts = np.flatnonzero(w)
                    s.add_clause([-u] + [z[i][t] for t in ts])
                    for t in ts: s.add_clause([-z[i][t], u])
                cl.append(group[key])
        s.add_clause(cl)
    ok = not s.solve()
    msg = ''
    if ok is False:
        mod = set(l for l in s.get_model() if l > 0)
        msg = f'uncovered profile {[D[i][t] for i in range(n) for t in range(len(D[i])) if z[i][t] in mod]}'
    s.delete()
    return ok, msg


def covered(task):
    return {'sat': covered_sat, 'sat2': covered_sat2, 'dfs': covered_dfs}[task[4]](task)


def graph(n, m, sets):
    G = nx.Graph()
    G.add_nodes_from((('a', i) for i in range(n)), side='a')
    G.add_nodes_from((('g', g) for g in range(m)), side='g')
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    return G


def aut(task):
    n, m, sets = task
    G = graph(n, m, sets)
    return sum(1 for _ in GraphMatcher(G, G, node_match=lambda a, b: a['side'] == b['side']).isomorphisms_iter())


def expand(sets, m, allocs):
    """Every image of the allocations under the automorphisms of the incidence graph (computed here)."""
    n = len(sets)
    G = graph(n, m, sets)
    auts = [({a: iso[('a', a)][1] for a in range(n)}, {g: iso[('g', g)][1] for g in range(m)})
            for iso in GraphMatcher(G, G, node_match=lambda a, b: a['side'] == b['side']).isomorphisms_iter()]
    out, seen = [], set()
    for A in allocs:
        for ma, mg in auts:
            img = [0] * m
            for g in range(m): img[mg[g]] = ma[A[g]]
            if tuple(img) not in seen: seen.add(tuple(img)); out.append(img)
    return out


def is_core(n, m, sets, n4):
    deg = [sum(g in S for S in sets) for g in range(m)]
    return (all(len(set(S)) == len(S) and len(S) in (3, 4) and all(0 <= g < m for g in S) for S in sets)
            and sum(len(S) == 4 for S in sets) == n4 and all(d >= 1 for d in deg)
            and all(sum(deg[g] == 1 for g in S) <= len(S) - 2 for S in sets) and nx.is_connected(graph(n, m, sets)))


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    jobs = int(opt.get('jobs', os.cpu_count()))
    print('command: python3 k4/hunt/check.py ' + ' '.join(sys.argv[1:]), flush=True)
    print(f'types: d=3: {len(types(3))}, d=4: {len(types(4))}', flush=True)
    bad = 0
    if len(types(3)) != 6 or len(types(4)) != 288: print('TYPE COUNT MISMATCH'); bad += 1
    datas = [json.load(gzip.open(f, 'rt')) for f in files]
    for d in datas:                               # compact allocations: base36 strings, one character per good
        for c in d['cores']:
            c['allocs'] = [[int(ch, 36) for ch in A] if isinstance(A, str) else A for A in c['allocs']]
            if c.get('orbits'): c['allocs'] = expand(c['sets'], c.get('m') or d['m'], c['allocs'])
    named = all('set' in d for d in datas)
    if named:                                     # named cores: per-core n, m; no class, no completeness
        cores = [c for d in datas for c in d['cores']]
        n = m = n4 = None
        for c in cores:
            if not is_core(c['n'], c['m'], c['sets'], sum(len(S) == 4 for S in c['sets'])) or len(c['sets']) != c['n']:
                print('NOT A CORE', c['name'], c['sets']); bad += 1
        whole = False
        print(f"named cores: {len(cores)} in {len(files)} file(s); status "
              f"{dict((k, sum(c['status'] == k for c in cores)) for k in set(c['status'] for c in cores))}", flush=True)
    else:
        n, m, n4 = datas[0]['n'], datas[0]['m'], datas[0]['n4']
        cores = [c for d in datas for c in d['cores']]
        if any((d['n'], d['m'], d['n4']) != (n, m, n4) for d in datas): print('MIXED CLASSES'); sys.exit(1)
        for c in cores: c['n'], c['m'] = n, m
        st = {}
        for c in cores: st[c['status']] = st.get(c['status'], 0) + 1
        print(f'n={n} m={m} n4={n4}: {len(cores)} cores in {len(files)} file(s); status {st}', flush=True)
        for c in cores:
            if not is_core(n, m, c['sets'], n4): print('NOT A CORE OF THE CLASS', c['sets']); bad += 1
        whole = all(d['selection'] == 'all' for d in datas) and sorted(tuple(d['part']) for d in datas) == \
            [(i, datas[0]['part'][1]) for i in range(datas[0]['part'][1])]
    with Pool(jobs) as pool:
        if whole:
            auts = pool.map(aut, [(n, m, c['sets']) for c in cores], chunksize=16)
            orbit = sum(math.factorial(n) * math.factorial(m) // a for a in auts)
            lab = check4.labeled_count(n, m, False, n4)
            print(f'orbit sum {orbit}, labeled count {lab}: {"OK" if orbit == lab else "MISMATCH"}', flush=True)
            if orbit != lab: bad += 1
            # pairwise non-isomorphic: WL hash buckets, then exact isomorphism inside a bucket
            buckets = {}
            for k, c in enumerate(cores):
                G = graph(n, m, c['sets'])
                h = nx.weisfeiler_lehman_graph_hash(G, node_attr='side', iterations=4)
                buckets.setdefault(h, []).append(k)
            dup = 0
            for ks in buckets.values():
                Gs = [graph(n, m, cores[k]['sets']) for k in ks]
                for a in range(len(Gs)):
                    for b in range(a):
                        if GraphMatcher(Gs[a], Gs[b], node_match=lambda x, y: x['side'] == y['side']).is_isomorphic(): dup += 1
            print(f'isomorphic pairs: {dup}', flush=True)
            bad += dup > 0
        else:
            print('named cores, a sample, or not every part: completeness not checked', flush=True)
        eng = opt.get('engine', 'dfs')
        todo = [(c['n'], c['m'], c['sets'], c['allocs'], eng) for c in cores if c['status'] == 'certified']
        res = pool.map(covered, todo, chunksize=8)
    nc = 0
    for (t, (ok, msg)) in zip(todo, res):
        if ok: nc += 1
        else: print('NOT COVERED', t[2], msg, flush=True); bad += 1
    print(f'coverage ({eng}): {nc}/{len(todo)} certified cores covered (raw EFX₀, every strict profile)', flush=True)
    if 'sat-sample' in opt:                       # cross-check the two coverage engines on a random sample
        import random
        smp = random.Random(0).sample(todo, min(int(opt['sat-sample']), len(todo)))
        with Pool(jobs) as pool:
            r2 = pool.map(covered_sat, smp, chunksize=1)
        agree = sum(1 for t, (ok, _) in zip(smp, r2) if ok)
        print(f'coverage (sat, one-hot, Glucose 4) on a sample of {len(smp)}: {agree} covered', flush=True)
        if agree != len(smp): bad += 1
    if 'expect' in opt and int(opt['expect']) != nc: print('EXPECT MISMATCH'); bad += 1
    print('RESULT:', 'OK' if bad == 0 else f'{bad} PROBLEMS', flush=True)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
