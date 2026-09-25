"""Candidate shapes of a minimal counterexample to TARGET4 with cyclomatic number beta (k4/MINCEX.md, section 5).

A minimal counterexample (within the class C_beta) is a connected k = 4 core (K4.MC0) with strict types. By the
reductions of k4/MINCEX.md it has no agent with two private goods (K4.MC-PP), so its agents are P3 (3 goods, one
private), Q3 (3 goods, none), P4 (4 goods, one private) and Q4 (4 goods, none); deleting the private goods leaves a
bipartite graph G' (agents of degree 2, 3, 3, 4; shared goods of degree >= 2) with the same cyclomatic number. No good
of degree 2 is shared by two P3 agents (K4.MC3). G' is listed with nauty's genbg (one per isomorphism class); each agent
of degree 3 is then Q3 or P4. Kept: n >= 5 (K4.R3, K4.R4 cover n <= 4), at least one 4-good agent (TARGET covers
the rest), and at least three when n = 5 (K4.R5).

Profile restrictions (K4.MC-PX): for a P3 agent f sharing a good g of degree 2 with a Q3, P4 or Q4 agent e, the
profile restricted to (e, f) must lie in the set of profiles of configuration px (k4/mincex4.py) that no certified
reduction covers; each agent's type domain is cut to the projection of that set. An empty domain removes the shape.
Usage: mincex_shapes.py BETA [--write=out.json.gz]
"""
import itertools, json, gzip, subprocess, shutil, sys, collections
import numpy as np
import networkx as nx
import reduce4 as R4

GENBG = shutil.which('genbg') or shutil.which('nauty-genbg')


def gammas(beta, nmin=5, nmax=None):
    """G' graphs: (n, list of agent neighbourhoods as lists of shared-good indices, number of shared goods)."""
    for n in range(nmin, (nmax or 5 * (beta - 1)) + 1):
        for mp in range(1, n + beta):
            E = n + mp + beta - 1
            if not (max(2 * n, 2 * mp) <= E <= min(4 * n, n * mp)): continue     # degree bounds (genbg rejects these)
            out = subprocess.run([GENBG, '-cq', '-d2:2', '-D4:%d' % n, str(n), str(mp), '%d:%d' % (E, E)],
                                 capture_output=True, text=True, check=True).stdout.split()
            for g6 in out:
                G = nx.from_graph6_bytes(g6.encode())
                yield n, [sorted(x - n for x in G[a]) for a in range(n)], mp


def hypergraphs(beta, nmax=None):
    """Candidate cores: list of agent good-lists (private goods appended after the shared ones)."""
    for n, nb, mp in gammas(beta, nmax=nmax):
        if structural_prune(nb): continue
        deg = collections.Counter(g for N in nb for g in N)
        if any(deg[g] == 2 and all(len(nb[a]) == 2 for a in range(n) if g in nb[a]) for g in range(mp)): continue
        t = sum(d - 2 for d in deg.values())
        n2 = sum(len(N) == 4 for N in nb)
        assert n <= 5 * (beta - 1) - t - 2 * n2, 'bound K4.MC4 violated'
        three = [a for a in range(n) if len(nb[a]) == 3]
        for k in range(len(three) + 1):
            for P4 in itertools.combinations(three, k):
                n4 = n2 + k
                if n4 == 0 or (n == 5 and n4 < 3): continue
                sets, m = [], mp
                for a in range(n):
                    S = list(nb[a])
                    if len(S) == 2 or a in P4: S.append(m); m += 1
                    sets.append(S)
                yield n, m, sets


def canon_key(sets, m):
    G = nx.Graph()
    G.add_nodes_from((('a', i) for i in range(len(sets))), c=0)
    G.add_nodes_from((('g', g) for g in range(m)), c=1)
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    return G


def unique(hs):
    buckets = collections.defaultdict(list)
    for n, m, sets in hs:
        G = canon_key(sets, m)
        h = (n, m, nx.weisfeiler_lehman_graph_hash(G, node_attr='c'))
        if any(nx.is_isomorphic(G, G2, node_match=lambda x, y: x['c'] == y['c']) for _, _, _, G2 in buckets[h]): continue
        buckets[h].append((n, m, sets, G))
    return [(n, m, sets) for b in buckets.values() for n, m, sets, _ in b]


def kind(S, deg):
    priv = sum(deg[g] == 1 for g in S)
    return {(3, 1): 'P3', (3, 0): 'Q3', (4, 1): 'P4', (4, 0): 'Q4'}[(len(S), priv)]


_SYM = {}


def sym_allowed(fail, ke, closed):
    """Allowed (not reduced) e- and f-vectors of configuration px, in px label order with e's symmetric goods (those
    other than g, y and its private good) in a fixed order: a profile is reduced if some labeling of the symmetric
    goods reduces it, so the allowed set is the intersection over the permutations of their projections."""
    key = (ke, closed)
    if key in _SYM: return _SYM[key]
    fs = fail[key]
    lead = 2 if closed else 1
    nsym = {'Q3': 2, 'P4': 2, 'Q4': 3}[ke] - (1 if closed else 0)
    AE, AF = None, set(fv for _, fv in fs)
    for perm in itertools.permutations(range(nsym)):
        ae = set()
        for ev, fv in fs:
            ev = list(ev)
            ae.add(tuple(ev[:lead] + [ev[lead + perm[i]] for i in range(nsym)] + ev[lead + nsym:]))
        AE = ae if AE is None else AE & ae
    _SYM[key] = (AE, AF)
    return _SYM[key]


def restricted_domains(sets, m, fail):
    """fail[(kind of e, closed)] = set of (e-vector on the px labels, f-vector on (g, y, pf)) not reduced. Returns the
    per-agent lists of allowed value vectors (aligned with sets[i]) and the rules applied."""
    deg = collections.Counter(g for S in sets for g in S)
    kinds = [kind(S, deg) for S in sets]
    dom = [list(R4.TYPES[len(S)]) for S in sets]
    rules = []
    for f, Sf in enumerate(sets):
        if kinds[f] != 'P3': continue
        pf = next(g for g in Sf if deg[g] == 1)
        for g in Sf:
            if g == pf or deg[g] != 2: continue
            e = next(a for a in range(len(sets)) if a != f and g in sets[a])
            ke = kinds[e]
            y = next(x for x in Sf if x not in (g, pf))
            closed = y in sets[e]
            rest = sorted(x for x in sets[e] if x not in (g, y) and deg[x] > 1)
            pe = [x for x in sets[e] if deg[x] == 1]
            labels = [g] + ([y] if closed else []) + rest + pe          # e's goods in px order
            AE, AF = sym_allowed(fail, ke, closed)
            pos_e = [sets[e].index(x) for x in labels]
            pos_f = [Sf.index(x) for x in (g, y, pf)]
            dom[e] = [v for v in dom[e] if tuple(v[i] for i in pos_e) in AE]
            dom[f] = [v for v in dom[f] if tuple(v[i] for i in pos_f) in AF]
            rules.append((ke, closed, e, f, g))
    return dom, kinds, rules


def structural_prune(nb):
    """True if G' (agent neighbourhoods) is excluded whatever the Q3/P4 choice (K4.MC-PX with Q3 and P4, whose closed
    configurations are always reduced and whose open ones force the P3 agent to rank g last and e to rank g first)."""
    n = len(nb)
    deg = collections.Counter(g for N in nb for g in N)
    def partner(a, g): return next(b for b in range(n) if b != a and g in nb[b])
    tops = collections.Counter()
    for f in range(n):
        if len(nb[f]) != 2: continue
        e3 = []
        for g in nb[f]:
            if deg[g] != 2: continue
            e = partner(f, g)
            if len(nb[e]) == 3:
                y = next(x for x in nb[f] if x != g)
                if y in nb[e]: return True                        # closed: reduced
                e3.append(e); tops[e] += 1
        if len(e3) == 2: return True                              # f would rank each of its goods last
    return any(c >= 2 for c in tops.values())                     # e would rank two goods first


def px_fail():
    """Profiles of configuration px (kinds Q3, P4, Q4; open and closed) that DEL and the one-agent gadgets miss."""
    import mincex4 as M
    out = {}
    for ke in ('Q3', 'P4', 'Q4'):
        for closed in (False, True):
            cfg = M.px_config(ke, closed)
            u, _ = M.gadget_cover(cfg, jobs=4)
            ok, _ = R4.run(R4.Reduction(cfg, 'DEL', {}, set(), source=True), jobs=4)
            u = u | ok
            out[(ke, closed)] = {(tuple(cfg.dom['e'][i]), tuple(cfg.dom['f'][j])) for i, j in zip(*np.nonzero(~u))}
    return out


def main():
    beta = int(sys.argv[1])
    opts = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--') and '=' in a)
    fail = px_fail()
    for key, fs in sorted(fail.items()): print('px %s %s: %d profiles not reduced' % (key[0], 'closed' if key[1] else 'open', len(fs)))
    nmax = int(opts['nmax']) if 'nmax' in opts else None
    out, stat = [], collections.Counter()
    for n, m, sets in hypergraphs(beta, nmax):
        stat[(n, m)] += 1
        dom, kinds, rules = restricted_domains(sets, m, fail)
        size = int(np.prod([len(d) for d in dom], dtype=object))
        if size == 0: continue
        out.append({'n': n, 'm': m, 'sets': sets, 'kinds': kinds, 'domains': [[list(v) for v in d] for d in dom],
                    'profiles': size})
    uniq = unique([(r['n'], r['m'], r['sets']) for r in out])
    out = [r for r in out if any(r['sets'] == s2 for _, _, s2 in uniq)]
    print('beta = %d: candidate cores, listed per graph G\' and choice of P4 agents (isomorphic ones not merged)' % beta)
    for n, m in sorted(stat):
        left = [r['profiles'] for r in out if (r['n'], r['m']) == (n, m)]
        print('  n = %d, m = %d: %d listed, %d left after K4.MC-PX (up to isomorphism; profiles: max %s, total %s)' % (
            n, m, stat[(n, m)], len(left), max(left) if left else 0, sum(left)))
    if 'write' in opts:
        with gzip.open(opts['write'], 'wt') as f: json.dump(out, f)


if __name__ == '__main__':
    main()
