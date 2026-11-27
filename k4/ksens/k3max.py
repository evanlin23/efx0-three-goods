"""OC1^max at k = 3, exhaustively over every strict profile (k4/ksens.md §8): for every connected agent / good
hypergraph with n agents, each valuing at most three goods (every good valued by someone; nauty-genbg), every strict
additive profile, and every serial-dictatorship start whose picks form a maximum matching: do the picks have a
one-absorber EFX0 completion, or does one improving chain (k4/sdc.md §29, rings and t = 0 included) give bases that
have one?

Why finitely many profiles suffice.  Every comparison the question makes is between two disjoint sets of goods valued
by one agent: SD compares single goods; a chain agent's new base is disjoint from its old base (or, for t = 0, a
superset of it); EFX0 compares X_i with X_j minus a good.  For an agent with three goods a > b > c the only
comparisons between disjoint subsets not fixed by the ranking are a against b + c.  So a strict profile (no ties
between disjoint subset sums) is determined, for this question, by its order type: per agent, a ranking and (three
goods) the side of a vs b + c.  Representatives: (4, 2, 1) for a > b + c and (4, 3, 2) for a < b + c, permuted over
the goods; (2, 1) permuted for two goods; (1) for one.  12, 2 or 1 types per agent.

Method (no SAT): for each profile and each maximum-matching start, the cached witnesses of the same picks are tried
first (a witness = the chain's gains and a complete allocation; it is re-checked under the profile from the raw
definitions: every chain agent strictly gains, EFX0, at most one agent with two or more goods outside its base).  On a
miss: an exact backtracking search for a completion of the picks, then every state one chain reaches (brute.Inst.chains,
official move rule: no agent hands on an empty base), each with the same completion search.  Every (profile, start)
is classified as completing at the picks, needing exactly one chain, or FAIL; a FAIL is re-checked with ocsat (SAT)
and with the free completion.

    python3 k4/ksens/k3max.py n [m ...] [--jobs=4] [--all] [--empty-pass]
--all: every start, not only the maximum-matching ones; --empty-pass: an agent with an empty base may pass it on
(ocsat's default rule) instead of the official rule."""
import sys, itertools, json, time, subprocess, collections, multiprocessing as mp
import networkx as nx
import _paths
import brute

TYPES = {1: [(1,)], 2: [(2, 1), (1, 2)],
         3: sorted(set(itertools.permutations((4, 2, 1))) | set(itertools.permutations((4, 3, 2))))}


def hypergraphs(n, m):
    out = subprocess.run(['nauty-genbg', '-c', '-q', '-d1:1', '-D3:%d' % n, str(n), str(m)], capture_output=True).stdout.split()   # exits 1 when there is none
    for line in out:
        G = nx.from_graph6_bytes(line)
        yield [sorted(g - n for g in G[i]) for i in range(n)]


def efx0(V, X):
    n = len(X)
    for i in range(n):
        own = sum(V[i][g] for g in X[i])
        for j in range(n):
            if j == i or not X[j]: continue
            vs = [V[i][g] for g in X[j]]
            if sum(vs) - min(vs) > own: return False
    return True


def find_completion(V, bases, m, A=1):
    """a complete EFX0 allocation containing every base with at most A agents holding two or more goods outside their
    base (A = None: no bound), by backtracking from the raw definition; None if there is none"""
    n = len(bases); X = [set(b) for b in bases]; inb = set(g for b in bases for g in b)
    J = [g for g in range(m) if g not in inb]; extra = [0] * n
    def worst(i, j):
        if not X[j]: return 0
        vs = [V[i][g] for g in X[j]]
        return sum(vs) - min(vs)
    def rec(k, rest):
        for i in range(n):
            cap = sum(V[i][g] for g in X[i]) + rest[i]
            for j in range(n):
                if j != i and worst(i, j) > cap: return None
        if k == len(J):
            return [frozenset(x) for x in X] if efx0(V, X) else None
        g = J[k]; nrest = [rest[i] - V[i][g] for i in range(n)]
        for a in range(n):
            if A is not None and extra[a] == 1 and sum(1 for b in range(n) if extra[b] >= 2) >= A: continue
            X[a].add(g); extra[a] += 1
            r = rec(k + 1, nrest)
            X[a].discard(g); extra[a] -= 1
            if r is not None: return r
        return None
    return rec(0, [sum(V[i][g] for g in J) for i in range(n)])


def nu(sets):
    G = nx.Graph(); G.add_nodes_from(('a', i) for i in range(len(sets)))
    for i, s in enumerate(sets):
        for g in s: G.add_edge(('a', i), ('g', g))
    return len(nx.max_weight_matching(G, maxcardinality=True))


def sd(prefs, order):
    left = set(); Y = [None] * len(prefs)
    for i in order:
        for g in prefs[i]:
            if g not in left: Y[i] = g; left.add(g); break
    return tuple(Y)


def sd_all(prefs):
    """every serial-dictatorship outcome over all orders (memoized on the agents left and the goods taken); equal to
    {sd(prefs, o) for every order o} (checked in k3max_xcheck.py)"""
    n = len(prefs); memo = {}
    def rec(rem, taken):
        key = (rem, taken)
        if key in memo: return memo[key]
        if not rem: out = {(-1,) * n}
        else:
            out = set()
            for a in rem:
                g = next((h for h in prefs[a] if h not in taken), None)
                for t in rec(rem - {a}, taken | {g} if g is not None else taken):
                    t = list(t); t[a] = g; out.add(tuple(t))
        memo[key] = out; return out
    return rec(frozenset(range(n)), frozenset())


def valid(V, w):
    gains, X = w
    for i, old, new in gains:
        if sum(V[i][g] for g in new) <= sum(V[i][g] for g in old): return False
    return efx0(V, X)


def hit(V, ws):
    """some cached witness is valid under V (moved to the front when found)"""
    for k, w in enumerate(ws):
        if valid(V, w):
            if k: ws[0], ws[k] = ws[k], ws[0]
            return True
    return False


ALL = '--all' in sys.argv; EMPTY = '--empty-pass' in sys.argv


def run(task):
    n, m, idx, sets = task; t0 = time.time(); v_ = nu(sets); orders = list(itertools.permutations(range(n)))
    C = collections.Counter(); fails = []; cache = collections.defaultdict(lambda: ([], []))   # picks -> (pick wits, chain wits)
    groups = []          # per agent: its types grouped by ranking (SD depends on the rankings only)
    for s in sets:
        d = collections.defaultdict(list)
        for t in TYPES[len(s)]: d[tuple(sorted(range(len(s)), key=lambda k: -t[k]))].append(t)
        groups.append(list(d.items()))
    for rk in itertools.product(*groups):
        prefs = [[s[k] for k in r] for s, (r, _) in zip(sets, rk)]
        starts = [Y for Y in set(sd(prefs, o) for o in orders) if ALL or sum(1 for g in Y if g is not None) == v_]
        for prof in itertools.product(*[ts for _, ts in rk]):
          V = [[0] * m for _ in range(n)]
          for i, (s, t) in enumerate(zip(sets, prof)):
              for g, x in zip(s, t): V[i][g] = x
          C['profiles'] += 1
          for Y in starts:
            C['starts' if ALL else 'max starts'] += 1; pw, cw = cache[Y]
            if hit(V, pw): C['complete at the picks'] += 1; C['hit'] += 1; continue
            base = [frozenset([g]) if g is not None else frozenset() for g in Y]
            X = find_completion(V, base, m, 1)
            if X is not None: pw.append(((), X)); C['complete at the picks'] += 1; continue
            if hit(V, cw): C['one chain'] += 1; C['hit'] += 1; continue
            I = brute.Inst(sets, [[V[i][g] for g in s] for i, s in enumerate(sets)], m); found = None
            for st in sorted(I.chains(base, empty_pass=EMPTY), key=lambda s: sorted(map(sorted, s))):
                X = find_completion(V, st, m, 1)
                if X is not None:
                    found = (tuple((i, base[i], st[i]) for i in range(n) if st[i] != base[i]), X); break
            if found: cw.append(found); C['one chain'] += 1; continue
            C['FAIL'] += 1
            free = find_completion(V, base, m, None) is not None or any(
                find_completion(V, st, m, None) is not None for st in I.chains(base, empty_pass=EMPTY))
            fails.append({'sets': sets, 'vals': [[V[i][g] for g in s] for i, s in enumerate(sets)], 'picks': Y,
                          'maximum': sum(1 for g in Y if g is not None) == v_,
                          'free completion after at most one chain': free})
    C['witnesses'] = sum(len(a) + len(b) for a, b in cache.values())
    return n, m, idx, sets, dict(C), fails, time.time() - t0


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    jobs = int(next((a.split('=')[1] for a in sys.argv[1:] if a.startswith('--jobs=')), 4))
    n = int(args[0]); ms = [int(a) for a in args[1:]] or list(range(n, 3 * n + 1))
    print('$ python3 k4/ksens/k3max.py', *sys.argv[1:], flush=True); t0 = time.time()
    print('starts:', 'every start' if ALL else 'maximum-matching starts', '; move rule:',
          'empty passes allowed' if EMPTY else 'official (no empty pass)', flush=True)
    tasks = [(n, m, idx, s) for m in ms for idx, s in enumerate(hypergraphs(n, m))]
    print('hypergraphs', len(tasks), 'for m in', ms, flush=True)
    tot = collections.Counter(); per_m = collections.defaultdict(collections.Counter); allf = []
    with mp.Pool(jobs) as P:
        for k, (n_, m, idx, sets, C, fails, dt) in enumerate(P.imap_unordered(run, tasks, chunksize=1)):
            tot.update(C); per_m[m].update(C); per_m[m]['hypergraphs'] += 1; tot['hypergraphs'] += 1
            for f in fails:
                allf.append(f); print('FAIL', json.dumps(f), flush=True)
            if (k + 1) % 50 == 0: print('...', k + 1, 'hypergraphs, %.0f s' % (time.time() - t0), flush=True)
    keys = ['hypergraphs', 'profiles', 'starts' if ALL else 'max starts', 'complete at the picks', 'one chain', 'FAIL']
    for m in sorted(per_m): print('n %d m %d:' % (n, m), ', '.join('%s %d' % (k, per_m[m][k]) for k in keys))
    print('total:', ', '.join('%s %d' % (k, tot[k]) for k in keys + ['witnesses', 'hit']))
    if allf:
        import ocsat
        for f in allf:
            S, Vv, Y = f['sets'], f['vals'], f['picks']; mm = 1 + max(max(s) for s in S)
            O = ocsat.OC(S, Vv, mm); b = ocsat.bases_of(Y, n)
            print('FAIL recheck (ocsat, SAT): one chain + one absorber holds =', O.holds(b, chain='any', A=1),
                  '; free =', O.holds(b, chain='any'), json.dumps(f)); O.close()
    print('time %.0f s' % (time.time() - t0))
