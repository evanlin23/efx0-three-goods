"""Independent check of the candidate cores of a minimal counterexample with cyclomatic number beta (k4/MINCEX.md,
section 6), and of their certificate (written by k4/mincex_shapes.py and k4/mincex_cert.py).

Written separately from mincex_shapes.py / mincex_cert.py:
  1. every connected k = 4 core with n agents (5 <= n <= 3(beta - 1), the bound K4.MC4) and cyclomatic number beta
     is listed with nauty's genbg at the level of the full incidence graph (agents of degree 3 or 4, goods of degree
     >= 1; mincex_shapes.py lists the graphs G' without private goods instead);
  2. filters, re-implemented: at most one private good per agent (K4.MC-PP), at least one agent with 4 goods, at
     least three when n = 5 (K4.R5), no good of degree 2 valued by two P3 agents (K4.MC3);
  3. type domains from this directory's check_reductions4.py enumeration (not the generator's), cut by the profiles
     of configuration px that the reduction certificate does NOT cover, as re-derived by check_reductions4.py
     (--fail-out file); a shape with an empty domain is excluded;
  4. every remaining core must be isomorphic to a certified core, and every profile in the product of its domains must
     have an EFX0 allocation among the certified ones (raw definition, v(own) >= v(B) - v(g)).
Usage: check_mincex_cores.py BETA certificate.json.gz px_fail.json"""
import sys, json, gzip, itertools, collections, shutil, subprocess
import numpy as np
import networkx as nx
from check_reductions4 import TY, safe

GENBG = shutil.which('genbg') or shutil.which('nauty-genbg')


def signature(R, v):
    """Type of valuation v (dict) on the ordered goods R: signs of v(S) - v(T) over disjoint nonempty S, T."""
    d = len(R)
    out = []
    for S in range(1, 1 << d):
        for T in range(S + 1, 1 << d):
            if S & T: continue
            a = sum(v[R[i]] for i in range(d) if S >> i & 1) - sum(v[R[i]] for i in range(d) if T >> i & 1)
            out.append((a > 0) - (a < 0))
    return tuple(out)


def cores(beta):
    for n in range(5, 3 * (beta - 1) + 1):
        for m in range(n, 3 * n + 1):
            E = n + m + beta - 1
            if not (max(3 * n, m) <= E <= min(4 * n, n * m)): continue
            res = subprocess.run([GENBG, '-cq', '-d3:1', '-D4:%d' % n, str(n), str(m), '%d:%d' % (E, E)],
                                 capture_output=True, text=True)
            for g6 in res.stdout.split():
                G = nx.from_graph6_bytes(g6.encode())
                yield n, m, [sorted(x - n for x in G[a]) for a in range(n)]


def kinds_of(sets):
    deg = collections.Counter(g for S in sets for g in S)
    out = []
    for S in sets:
        p = sum(deg[g] == 1 for g in S)
        if p > 1: return None, deg
        out.append(('P' if p else 'Q') + str(len(S)))
    return out, deg


def main():
    beta = int(sys.argv[1])
    cert = json.load(gzip.open(sys.argv[2], 'rt'))
    fails = json.load(open(sys.argv[3]))
    # allowed (e, f) signatures of configuration px, with e's goods in px order
    PX = {}
    for name, profs in fails.items():
        if not name.startswith('px-'): continue
        PX[name] = profs
    stat = collections.Counter()
    left = []
    for n, m, sets in cores(beta):
        stat['listed'] += 1
        kinds, deg = kinds_of(sets)
        if kinds is None: continue                              # K4.MC-PP
        n4 = sum(len(S) == 4 for S in sets)
        if n4 == 0 or (n == 5 and n4 < 3): continue
        if any(deg[g] == 2 and all(kinds[a] == 'P3' for a in range(n) if g in sets[a]) for g in range(m)): continue
        stat['after filters'] += 1
        dom = [[dict(zip(S, t)) for t in TY[len(S)]] for S in sets]
        for f in range(n):
            if kinds[f] != 'P3': continue
            pf = next(g for g in sets[f] if deg[g] == 1)
            for g in sets[f]:
                if g == pf or deg[g] != 2: continue
                e = next(a for a in range(n) if a != f and g in sets[a])
                y = next(x for x in sets[f] if x not in (g, pf))
                closed = y in sets[e]
                name = 'px-' + kinds[e] + ('-closed' if closed else '')
                sym = [x for x in sets[e] if x not in (g, y) and deg[x] > 1]
                pe = [x for x in sets[e] if deg[x] == 1]
                okE, okF = None, None
                for perm in itertools.permutations(sym):
                    labels = [g] + ([y] if closed else []) + list(perm) + pe
                    se, sf = set(), set()
                    for pr in PX[name]:
                        ve = {labels[i]: pr['e'][x] for i, x in enumerate(px_order(name))}
                        vf = {g: pr['f']['g'], y: pr['f']['y'], pf: pr['f']['pf']}
                        se.add(signature(sets[e], ve)); sf.add(signature(sets[f], vf))
                    okE = se if okE is None else okE & se
                    okF = sf if okF is None else okF & sf
                dom[e] = [v for v in dom[e] if signature(sets[e], v) in okE]
                dom[f] = [v for v in dom[f] if signature(sets[f], v) in okF]
        if any(not d for d in dom): continue
        stat['left'] += 1
        left.append((n, m, sets, dom))
    print('beta = %d: %d connected cores with 5 <= n <= %d listed; %d pass the filters; %d left after K4.MC-PX' % (
        beta, stat['listed'], 3 * (beta - 1), stat['after filters'], stat['left']))
    # match with the certificate and check coverage
    def graph(sets, m):
        G = nx.Graph()
        G.add_nodes_from((('a', i) for i in range(len(sets))), c='a')
        G.add_nodes_from((('g', g) for g in range(m)), c='g')
        G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
        return G
    certG = [(r, graph(r['sets'], r['m'])) for r in cert if 'allocs' in r]
    ok, d2 = True, True
    for n, m, sets, dom in left:
        G = graph(sets, m)
        match = None
        for r, G2 in certG:
            if r['n'] != n or r['m'] != m: continue
            gm = nx.algorithms.isomorphism.GraphMatcher(G, G2, node_match=lambda a, b: a['c'] == b['c'])
            if gm.is_isomorphic(): match = (r, gm.mapping); break
        if match is None:
            print('  NOT CERTIFIED: core %s' % sets); ok = False; continue
        r, mp = match
        gmap = {g: mp[('g', g)][1] for g in range(m)}
        amap = {a: mp[('a', a)][1] for a in range(n)}
        inv = {v: k for k, v in amap.items()}
        allocs = []                                            # owner lists in this core's labels
        for A in r['allocs']:
            allocs.append([inv[A[gmap[g]]] for g in range(m)])
        masks = []
        for a in range(n):
            M = np.zeros((len(dom[a]), len(allocs)), dtype=bool)
            for k, A in enumerate(allocs):
                bundles = collections.defaultdict(list)
                for g, o in enumerate(A): bundles[o].append(g)
                own = bundles[a]
                others = [B for o, B in bundles.items() if o != a]
                for t, v in enumerate(dom[a]): M[t, k] = safe(v, own, others)
            masks.append(M)
        order = sorted(range(n), key=lambda a: len(dom[a]))
        *head, x, y = order
        unc = 0
        for prof in itertools.product(*[range(len(dom[a])) for a in head]):
            acc = np.ones(len(allocs), dtype=bool)
            for a, t in zip(head, prof): acc &= masks[a][t]
            cov = (masks[x][:, acc].astype(np.float32) @ masks[y][:, acc].astype(np.float32).T) > 0.5
            unc += int((~cov).sum())
        big = max(sum(1 for c in collections.Counter(A).values() if c > 2) for A in allocs)
        d2 &= big <= 1
        prof_n = int(np.prod([len(d) for d in dom], dtype=object))
        print('  n = %d, m = %d, kinds %s: %d profiles, %d allocations, %d uncovered%s' % (
            n, m, ''.join(kinds_of(sets)[0]), prof_n, len(allocs), unc, '' if big <= 1 else ' (not D2)'))
        ok &= unc == 0
    print('every allocation has at most one bundle of more than 2 goods (D2): %s' % d2)
    print('RESULT: %s' % ('OK' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


def px_order(name):
    """Goods of agent e in configuration px (k4/MINCEX.md): g, then y if closed, then the symmetric goods, then pe."""
    kind = name.split('-')[1]
    closed = name.endswith('closed')
    sym = {'Q3': ['a', 'b'], 'P4': ['a', 'b'], 'Q4': ['a', 'b', 'c']}[kind]
    if closed: return ['g', 'y'] + sym[1:] + (['pe'] if kind == 'P4' else [])
    return ['g'] + sym + (['pe'] if kind == 'P4' else [])


if __name__ == '__main__':
    main()
