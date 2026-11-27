"""Second, independent implementation of the exhaustive check of Conjecture VM1-chain-plain (k4/vm.md section 7.9).
It shares NO code with k4/vm/vmlib.py, k4/vm/vm1chain_cert.py or any other module of the repository: only the data
files k4/order_types.json and results/k4_certs_*.json.gz are read.

Statement (for one strict profile of a k = 4 core): for some V-M matching Y (Viswanathan-Mehta Phases I-II, main
reading: Phase I gives the agents with v(top) > v(2nd) + v(3rd) their tops by a matching, Phase II steps k = 1..4 give
each remaining agent its k-th ranked good if still free, every conflict resolved every possible way), one of
  - nothing,
  - a pool upgrade (an agent holding one good y takes a pool set S with v(S) > v(y); y returns to the pool),
  - a two-agent exchange (i holding y takes j's good z, worthless to i or not, plus a pool set S; j takes y; both
    strictly gain),
  - a DE chain (an upgrade that keeps EFX0, then agents holding one good each take the good just released, which
    they value above their own),
applied to Y with an EFX0 result, followed by single-good placements, each keeping the allocation EFX0, and envy-cycle
rotations, ends with a complete EFX0 allocation (VM1-chain).  Runs without rotation are tried first; a rotation step
contributes the strict envy comparisons of its cycle (rotations keep EFX0 under every profile satisfying them).

Method (as in the first implementation, coded afresh):
  - every comparison is between disjoint sets of goods of ONE agent, so the statement depends only on the agents'
    strict balanced order types;
  - a successful run is turned into per-agent conditions:
      * V-M: agent a, run alone against the fixed environment "good g is taken at step s(g)" (s = 0 for Phase I),
        must reproduce its own pick at its own step (a direct simulation, not Lemma S);
      * linear conditions v_a(P) > v_a(Q) or v_a(P) <= v_a(Q) for the trade, the EFX0 check after it, and every
        placement's safety check;
    the box is the product over agents of the types meeting their conditions (evaluated with numpy);
  - boxes are closed under the hypergraph's automorphisms, found here as graph automorphisms of the agent-good
    incidence graph (networkx GraphMatcher), with types mapped through their disjoint-pair comparison vectors;
  - coverage by a numpy bitmap, or slices of agent 0's type (one per orbit) when the space exceeds 1.5e8.
A profile with no run is re-checked for VM1-chain WITH rotation (place_rot: placements and envy-cycle rotations,
exhaustively), and reported if that fails too.
    python3 k4/vm/vm1chain_cert2.py N [FILE_KEY] [--idx=I,J] [--procs=P]"""
import sys, os, json, gzip, time, itertools, collections, math
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
TYPES = json.load(open(os.path.join(ROOT, 'k4', 'order_types.json')))
SB = {k: [tuple(t['rep']) for t in TYPES[str(k)]['types'] if t['strict'] and t['balanced']] for k in (3, 4)}
FILES = {2: ['k4_certs_2.json.gz'], 3: ['k4_certs_3.json.gz'],
         4: ['k4_certs_4_n4_1.json.gz', 'k4_certs_4_n4_2.json.gz', 'k4_certs_4_n4_3.json.gz', 'k4_certs_4_pure.json.gz']}


def type_domain(goods, owners):
    priv = [p for p, g in enumerate(goods) if owners[g] == 1]
    out = list(SB[len(goods)])
    if len(priv) == 2:
        out = [w for w in out if w[priv[0]] + w[priv[1]] < sum(w) - w[priv[0]] - w[priv[1]]]
    return out


# ------------------------------------------------------------------ one profile
class P:
    def __init__(self, sets, vals):
        self.n = len(sets); self.m = 1 + max(max(S) for S in sets); self.sets = sets
        self.w = [dict(zip(S, W)) for S, W in zip(sets, vals)]
        self.order = [sorted(S, key=lambda g, a=a: -self.w[a][g]) for a, S in enumerate(sets)]

    def v(self, a, B):
        return sum(self.w[a].get(g, 0) for g in B)

    def threat_ok(self, a, B, own):
        """agent a, holding own, does not EFX0-envy the bundle B"""
        if len(B) < 2: return True
        base = self.v(a, own); tot = self.v(a, B)
        return all(tot - self.w[a].get(h, 0) <= base for h in B)

    def efx0(self, X):
        return all(self.threat_ok(a, X[b], X[a]) for a in range(self.n) for b in range(self.n) if a != b)


def strong(order, w):
    x = [w[g] for g in order[:3]] + [0, 0, 0]
    return x[0] > x[1] + x[2]


def vm_runs(p):
    """every (Y, step) of Phases I-II over all tie resolutions; Y[a] = pick or None, step[a] = 0 (Phase I), k, or None"""
    n = p.n; A = [a for a in range(n) if strong(p.order[a], p.w[a])]
    res = {}
    claims1 = collections.defaultdict(list)
    for a in A: claims1[p.order[a][0]].append(a)
    goods1 = sorted(claims1)
    for win in itertools.product(*[claims1[g] for g in goods1]):
        Y = [None] * n; step = [None] * n; taken = set()
        for g, a in zip(goods1, win): Y[a] = g; step[a] = 0; taken.add(g)
        def phase2(Y, step, taken, k):
            if k > 4:
                key = tuple(Y)
                if key not in res: res[key] = list(step)
                return
            claims = collections.defaultdict(list)
            for a in range(n):
                if Y[a] is None and len(p.order[a]) >= k and p.order[a][k - 1] not in taken:
                    claims[p.order[a][k - 1]].append(a)
            gs = sorted(claims)
            for win2 in itertools.product(*[claims[g] for g in gs]):
                Y2 = list(Y); s2 = list(step); t2 = set(taken)
                for g, a in zip(gs, win2): Y2[a] = g; s2[a] = k; t2.add(g)
                phase2(Y2, s2, t2, k + 1)
        phase2(Y, step, taken, 1)
    return [(list(Y), s) for Y, s in res.items()]


def env_ok(order, w, a, Y, step):
    """agent a with ranking `order` (and values w) alone against the environment fixed by Y and step: does it end with
    Y[a] taken at step[a]?"""
    holder = {Y[b]: b for b in range(len(Y)) if Y[b] is not None}
    st = lambda g: step[holder[g]]
    if strong(order, w):
        top = order[0]
        if step[a] == 0: return top == Y[a]
        if top not in holder or holder[top] == a or st(top) != 0: return False
    elif step[a] == 0:
        return False
    for k in range(1, 5):
        if k > len(order): break
        g = order[k - 1]
        if g not in holder: return False                    # a free good: a would take it
        h = holder[g]
        if h == a: return k == step[a]
        if st(g) < k: continue                              # already taken
        if st(g) == k: continue                             # taken at this step by h (a lost the tie)
        return False                                        # free at step k, claimed only by a
    return Y[a] is None


def place(p, X0, dead):
    """single-good placements without rotation from X0: the list of (g, s), or None; dead = states known to fail"""
    stack = [(tuple(tuple(b) for b in X0), ())]; seen = set()
    while stack:
        X, path = stack.pop()
        key = tuple(tuple(sorted(b)) for b in X)
        if key in seen or key in dead: continue
        seen.add(key)
        held = set(g for b in X for g in b); free = [g for g in range(p.m) if g not in held]
        if not free: return list(path)
        for g in free:
            for s in range(p.n):
                B = X[s] + (g,)
                if all(p.threat_ok(a, B, X[a]) for a in range(p.n) if a != s):
                    stack.append((X[:s] + (B,) + X[s + 1:], path + ((g, s),)))
    dead.update(seen)
    return None


def trades(p, Y):
    """(kind, data, state after, extra linear conditions, states whose EFX0 must be recorded)"""
    n = p.n; pool = [g for g in range(p.m) if g not in Y]
    out = []
    for i in range(n):
        if Y[i] is None: continue
        y = Y[i]; mine = [g for g in pool if g in p.w[i]]
        for r in range(1, len(mine) + 1):                   # upgrades
            for S in itertools.combinations(mine, r):
                if p.v(i, S) > p.w[i][y]:
                    X = [[g] if g is not None else [] for g in Y]; X[i] = list(S)
                    if p.efx0(X): out.append(('upgrade', (i, S), X, [(i, S, (y,), '>')], [X]))
        for j in range(n):                                  # exchanges
            if j == i or Y[j] is None: continue
            z = Y[j]
            if not p.w[j].get(y, 0) > p.w[j].get(z, 0): continue
            for r in range(0, len(mine) + 1):
                for S in itertools.combinations(mine, r):
                    if p.v(i, (z,) + S) > p.w[i][y]:
                        X = [[g] if g is not None else [] for g in Y]; X[i] = [z] + list(S); X[j] = [y]
                        if p.efx0(X):
                            out.append(('exchange', (i, j, z, S), X, [(i, (z,) + S, (y,), '>'), (j, (y,), (z,), '>')], [X]))
    for i in range(n):                                      # chains
        if Y[i] is None: continue
        y = Y[i]; mine = [g for g in pool if g in p.w[i]]
        for r in range(1, len(mine) + 1):
            for S in itertools.combinations(mine, r):
                if not p.v(i, S) > p.w[i][y]: continue
                X1 = [[g] if g is not None else [] for g in Y]; X1[i] = list(S)
                if not p.efx0(X1): continue
                stack = [(X1, y, {i}, [])]
                while stack:
                    X, g, used, steps = stack.pop()
                    if steps:
                        out.append(('chain', (i, S, tuple(steps)), X,
                                    [(i, S, (y,), '>')] + [(j, (gg,), (yj,), '>') for j, gg, yj in steps], [X1, X]))
                    for j in range(n):
                        if j in used or len(X[j]) != 1: continue
                        yj = X[j][0]
                        if p.w[j].get(g, 0) > p.w[j].get(yj, 0):
                            Z = [list(b) for b in X]; Z[j] = [g]
                            stack.append((Z, yj, used | {j}, steps + [(j, g, yj)]))
    return out


def efx0_lin(X, n):
    c = []
    for b in range(n):
        if len(X[b]) < 2: continue
        for a in range(n):
            if a == b: continue
            for h in X[b]:
                c.append((a, tuple(g for g in X[b] if g != h), tuple(X[a]), '<='))
    return c


def find_run(p):
    """(Y, step, linear conditions) of a successful run, or None"""
    runs = vm_runs(p); dead = set()
    def with_path(X0, path, lin):
        X = [list(b) for b in X0]
        for st_ in path:
            if st_[0] not in ('rot', 'place'): st_ = ('place',) + tuple(st_)     # (g, s) from place()
            if st_[0] == 'rot':
                cyc = st_[1]; L = len(cyc)
                for t in range(L): lin.append((cyc[t], tuple(X[cyc[(t + 1) % L]]), tuple(X[cyc[t]]), '>'))
                old = [list(b) for b in X]
                for t in range(L): X[cyc[t]] = old[cyc[(t + 1) % L]]
                continue
            _, g, s = st_
            B = X[s] + [g]
            if len(B) >= 2:
                for a in range(p.n):
                    if a == s: continue
                    for h in B: lin.append((a, tuple(u for u in B if u != h), tuple(X[a]), '<='))
            X[s] = B
        assert p.efx0(X) and sorted(g for b in X for g in b) == list(range(p.m))
        return lin
    for Y, step in runs:
        X0 = [[g] if g is not None else [] for g in Y]
        path = place(p, X0, dead)
        if path is not None: return Y, step, with_path(X0, path, []), 'none'
    for kind_wanted in ('upgrade', 'exchange', 'chain'):
        for Y, step in runs:
            for kind, data, X, lin, checks in trades(p, Y):
                if kind != kind_wanted: continue
                path = place(p, X, dead)
                if path is not None:
                    lin = list(lin)
                    for Z in checks: lin += efx0_lin(Z, p.n)
                    return Y, step, with_path(X, path, lin), kind
    for Y, step in runs:                                    # with rotation (VM1-chain proper)
        X0 = [[g] if g is not None else [] for g in Y]
        path = place_rot(p, X0, True)
        if path is not None: return Y, step, with_path(X0, path, []), 'none+rot'
    for kind_wanted in ('upgrade', 'exchange', 'chain'):
        for Y, step in runs:
            for kind, data, X, lin, checks in trades(p, Y):
                if kind != kind_wanted: continue
                path = place_rot(p, X, True)
                if path is not None:
                    lin = list(lin)
                    for Z in checks: lin += efx0_lin(Z, p.n)
                    return Y, step, with_path(X, path, lin), kind + '+rot'
    return None


def place_rot(p, X0, want_path=False):
    """single-good placements AND envy-cycle rotations (any simple cycle, any time), exhaustively: True (or the list
    of steps ('place', g, s) / ('rot', cycle)) if some sequence reaches a complete allocation, else None/False"""
    n = p.n; stack = [(tuple(tuple(b) for b in X0), ())]; seen = set()
    while stack:
        X, path = stack.pop(); key = tuple(tuple(sorted(b)) for b in X)
        if key in seen: continue
        seen.add(key)
        held = set(g for b in X for g in b); free = [g for g in range(p.m) if g not in held]
        if not free:
            assert p.efx0([list(b) for b in X]); return list(path) if want_path else True
        env = [[b for b in range(n) if b != a and p.v(a, X[b]) > p.v(a, X[a])] for a in range(n)]
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] != min(cyc): continue
                if all(cyc[(t + 1) % L] in env[cyc[t]] for t in range(L)):
                    Z = list(X)
                    for t in range(L): Z[cyc[t]] = X[cyc[(t + 1) % L]]
                    stack.append((tuple(Z), path + (('rot', cyc),)))
        for g in free:
            for s_ in range(n):
                B = X[s_] + (g,)
                if all(p.threat_ok(a, B, X[a]) for a in range(n) if a != s_):
                    stack.append((X[:s_] + (B,) + X[s_ + 1:], path + (('place', g, s_),)))
    return None if want_path else False


def recheck_rot(p):
    """VM1-chain with rotation on one profile: the first kind of trade (none, upgrade, exchange, chain) after which
    placements with rotation complete, or None"""
    runs = vm_runs(p)
    for Y, step in runs:
        if place_rot(p, [[g] if g is not None else [] for g in Y]): return 'none'
    for kind_wanted in ('upgrade', 'exchange', 'chain'):
        for Y, step in runs:
            for kind, data, X, lin, checks in trades(p, Y):
                if kind == kind_wanted and place_rot(p, X): return kind
    return None


# ------------------------------------------------------------------ boxes, symmetry, coverage
class HG:
    def __init__(self, sets):
        self.sets = sets; self.n = len(sets); self.m = 1 + max(max(S) for S in sets)
        owners = collections.Counter(g for S in sets for g in S)
        self.D = [type_domain(S, owners) for S in sets]
        self.M = [np.array(Da, dtype=np.int64) for Da in self.D]            # types x goods (in S order)
        self.orders = [[[S[k] for k in sorted(range(len(S)), key=lambda k: -rep[k])] for rep in Da]
                       for S, Da in zip(sets, self.D)]

    def box(self, Y, step, lin):
        T = []
        for a in range(self.n):
            S = self.sets[a]; pos = {g: k for k, g in enumerate(S)}
            ok = np.ones(len(self.D[a]), dtype=bool)
            for b, Pset, Qset, sense in lin:
                if b != a: continue
                coef = np.zeros(len(S), dtype=np.int64)
                for g in Pset:
                    if g in pos: coef[pos[g]] += 1
                for g in Qset:
                    if g in pos: coef[pos[g]] -= 1
                d = self.M[a] @ coef
                ok &= (d > 0) if sense == '>' else (d <= 0)
            for t in np.flatnonzero(ok):
                w = dict(zip(S, self.D[a][t]))
                if not env_ok(self.orders[a][t], w, a, Y, step): ok[t] = False
            T.append(np.flatnonzero(ok))
        return T


def comparison_vector(w):
    """the strict order type of w through the signs of v(A) - v(B) over all ordered pairs of disjoint nonempty sets"""
    k = len(w); subs = [s for s in range(1, 1 << k)]
    tot = [sum(w[t] for t in range(k) if s >> t & 1) for s in subs]
    return tuple(tot[x] > tot[y] for x in range(len(subs)) for y in range(len(subs)) if not (subs[x] & subs[y]))


def symmetries(hg, cap=2000):
    G = nx.Graph()
    for a in range(hg.n): G.add_node(('a', a), kind='a')
    for g in range(hg.m): G.add_node(('g', g), kind='g')
    for a, S in enumerate(hg.sets):
        for g in S: G.add_edge(('a', a), ('g', g))
    GM = GraphMatcher(G, G, node_match=lambda x, y: x['kind'] == y['kind'])
    lookup = [{comparison_vector(rep): t for t, rep in enumerate(Da)} for Da in hg.D]
    out = []
    for iso in GM.isomorphisms_iter():
        sigma = [iso[('a', a)][1] for a in range(hg.n)]; pi = {g: iso[('g', g)][1] for g in range(hg.m)}
        maps = []
        for a in range(hg.n):
            b = sigma[a]; Sa = hg.sets[a]; Sb = hg.sets[b]; inv = {pi[g]: g for g in Sa}
            maps.append(np.array([lookup[b][comparison_vector([dict(zip(Sa, rep))[inv[h]] for h in Sb])]
                                  for rep in hg.D[a]]))
        out.append((sigma, maps))
        if len(out) >= cap: break
    return out


def images(T, auts, n):
    for sigma, maps in auts:
        T2 = [None] * n
        for a in range(n): T2[sigma[a]] = np.unique(maps[a][T[a]])
        yield T2


def run_hg(sets):
    hg = HG(sets); n = hg.n; shape = tuple(len(Da) for Da in hg.D); size = math.prod(shape)
    auts = symmetries(hg); boxes = 0; fails = []; kinds = collections.Counter(); t0 = time.time()

    def solve(prof):
        nonlocal boxes
        vals = [list(hg.D[a][prof[a]]) for a in range(n)]
        r = find_run(P(sets, vals))
        if r is None:
            fails.append(vals); return None
        Y, step, lin, kind = r; kinds[kind] += 1; boxes += 1
        T = hg.box(Y, step, lin)
        for a in range(n): assert prof[a] in set(T[a].tolist()), (sets, vals, a)
        return T

    def sweep(cov, fixed, stored):
        flat = cov.reshape(-1); N = flat.size; pos = 0; CH = 1 << 20; sub = cov.shape
        while True:
            while pos < N:
                ch = flat[pos:pos + CH]; k = int(np.argmin(ch))
                if not ch[k]: pos += k; break
                pos += len(ch)
            if pos >= N: return
            prof = fixed + tuple(int(u) for u in np.unravel_index(pos, sub))
            T = solve(prof)
            if T is None:
                flat[pos] = True; continue
            for T2 in images(T, auts, n):
                if fixed:
                    if fixed[0] in set(T2[0].tolist()): cov[np.ix_(*T2[1:])] = True
                    stored.append((set(T2[0].tolist()), T2[1:]))
                else:
                    cov[np.ix_(*T2)] = True

    if size <= 1.5e8:
        sweep(np.zeros(shape, dtype=bool), (), None); mode = 'bitmap'
    else:
        stab = [maps[0] for sigma, maps in auts if sigma[0] == 0]; done0 = set(); stored = []; mode = 'slices'
        for t0 in range(shape[0]):
            if t0 in done0: continue
            done0.update(int(mp_[t0]) for mp_ in stab); done0.add(t0)
            cov = np.zeros(shape[1:], dtype=bool)
            for T0, Ts in stored:
                if t0 in T0: cov[np.ix_(*Ts)] = True
            sweep(cov, (t0,), stored)
    return boxes, fails, dict(kinds), len(auts), mode, time.time() - t0


def job(args):
    fn, c = args
    boxes, fails, kinds, na, mode, dt = run_hg(c['sets'])
    rk = collections.Counter(); bad = []
    for vals in fails:
        r = recheck_rot(P(c['sets'], vals)); rk[str(r)] += 1
        if r is None: bad.append(vals)
    return fn, c['idx'], len(c['sets']), 1 + max(max(S) for S in c['sets']), boxes, kinds, fails, na, mode, dt, dict(rk), bad


if __name__ == '__main__':
    import multiprocessing as mp
    N = int(sys.argv[1]); key = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else None
    opt = dict((a[2:].split('=') + ['1'])[:2] for a in sys.argv[2:] if a.startswith('--'))
    only = [int(s) for s in opt['idx'].split(',')] if 'idx' in opt else None
    procs = int(opt.get('procs', os.cpu_count()))
    print('$ python3 k4/vm/vm1chain_cert2.py', ' '.join(sys.argv[1:]), flush=True)
    jobs = [(fn, c) for fn in FILES[N] if not key or key in fn
            for c in json.load(gzip.open(os.path.join(ROOT, 'results', fn)))['cores'] if only is None or c['idx'] in only]
    tot = collections.Counter(); T0 = time.time()
    with mp.Pool(procs) as pool:
        for fn, idx, n, m, boxes, kinds, fails, na, mode, dt, rk, bad in pool.imap_unordered(job, jobs):
            tot['hypergraphs'] += 1; tot['boxes'] += boxes; tot['plain failing profiles'] += len(fails)
            for k, v in kinds.items(): tot['runs ' + k] += v
            for k, v in rk.items(): tot['with rotation: ' + k] += v
            print('  %s idx %d n=%d m=%d: %d boxes %s, %d automorphisms, %s, %d plain failing profiles %s, %.1f s' % (
                fn, idx, n, m, boxes, kinds, na, mode, len(fails), rk, dt), flush=True)
            for vals in bad[:3]:
                print('    VM1-CHAIN FAILS (with rotation too): %s' % json.dumps({'vals': vals}), flush=True)
    print('total', dict(tot), '; time %.0f s' % (time.time() - T0))
