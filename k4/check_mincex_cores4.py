"""Independent check of the candidate cores of a minimal counterexample with cyclomatic number beta >= 4, and of their
certificate (k4/MINCEX.md, section 8). For beta = 3, see check_mincex_cores.py (which lists the full incidence graphs;
at beta = 4 that list is too long, so this checker starts from G').

Written separately from mincex_shapes.py / mincex_cert.py:
  1. G' (the incidence graph without private goods: n agents of degree 2-4, shared goods of degree >= 2, cyclomatic
     number beta) is listed with nauty's genbg for 5 <= n <= 3(beta - 1) (K4.MC4), and the list is complete by orbit
     counting (gamma_orbits.py: sum n! m'! / |Aut| = the labeled count, from check4.py's column-filling DP);
  2. every G' is expanded: an agent of degree 2 gets one private good (P3), one of degree 4 none (Q4), and one of
     degree 3 none (Q3) or one (P4), every combination (K4.MC2: no agent has two private goods);
  3. filters: at least one 4-good agent, at least three when n = 5 (K4.MC0(d)), no good of degree 2 valued by two P3
     agents (K4.MC3);
  4. type domains from check_reductions4.py's enumeration, cut by the profiles of configuration px that no certified
     reduction covers (K4.MC5; the file's SHA-256 must match the value check_reductions4.py recorded); cores with an
     empty domain are excluded; the rest are merged up to isomorphism;
  5. every remaining core must be isomorphic to a certified core; coverage of the full product of its domains is
     checked with check4.py's C routine (pruned depth-first search), from safety masks computed here with the raw
     definition (vectorized: v(own) >= v(B ∩ R) - [B ⊆ R] min_B v); every certified allocation must be D2.
Any failure makes the exit status nonzero.
Usage: check_mincex_cores4.py BETA certificate.json.gz px_uncovered.json [--reductions-log=PATH] [--jobs=J]"""
import sys, os, re, json, gzip, hashlib, itertools, collections, ctypes
import numpy as np
import networkx as nx
from multiprocessing import Pool
from check_reductions4 import TY
from check_mincex_cores import signature, px_order
import gamma_orbits as GO
import check4

HERE = os.path.dirname(os.path.abspath(__file__))


def expand(beta):
    """(n, m, sets) for every G' and every choice of Q3/P4 at its degree-3 agents (private goods appended)."""
    orbit_ok = True
    for n in range(5, 3 * (beta - 1) + 1):
        for mp in range(1, n + beta):
            E = n + mp + beta - 1
            gs = GO.genbg_list(n, mp, E)
            lab = GO.labeled_conn(n, mp, E)
            s = GO.orbit_sum(n, mp, gs) if gs else 0
            if lab or gs:
                print("  orbit count n = %d, m' = %d: %d graphs G', sum n! m'! / |Aut| = %d, labeled %d %s" % (
                    n, mp, len(gs), s, lab, 'ok' if s == lab else 'MISMATCH'), flush=True)
            orbit_ok &= s == lab
            for g6 in gs:
                G = nx.from_graph6_bytes(g6.encode())
                nb = [sorted(x - n for x in G[a]) for a in range(n)]
                three = [a for a in range(n) if len(nb[a]) == 3]
                for bits in itertools.product((0, 1), repeat=len(three)):
                    p4 = {a for a, b in zip(three, bits) if b}
                    sets, m = [], mp
                    for a in range(n):
                        S = list(nb[a])
                        if len(S) == 2 or a in p4: S.append(m); m += 1
                        sets.append(S)
                    yield n, m, sets
    yield None, orbit_ok, None


_CUT = {}


def allowed(PX, name, pos_e, pos_f, Se_len, Sf_len):
    """Signatures (on e's and f's goods in their own order) allowed by the uncovered px profiles; pos_e[i] = index in
    e's good list of the i-th px label (one tuple per labeling of e's symmetric goods)."""
    key = (name, pos_e, pos_f, Se_len, Sf_len)
    if key in _CUT: return _CUT[key]
    okE = okF = None
    Re, Rf = list(range(Se_len)), list(range(Sf_len))
    for pe in pos_e:
        se, sf = set(), set()
        for pr in PX[name]:
            ve = {pe[i]: pr['e'][x] for i, x in enumerate(px_order(name))}
            vf = {pos_f[0]: pr['f']['g'], pos_f[1]: pr['f']['y'], pos_f[2]: pr['f']['pf']}
            se.add(signature(Re, ve)); sf.add(signature(Rf, vf))
        okE = se if okE is None else okE & se
        okF = sf if okF is None else okF & sf
    _CUT[key] = (okE, okF)
    return okE, okF


def domains(sets, PX):
    n = len(sets)
    deg = collections.Counter(g for S in sets for g in S)
    kinds = [('P' if sum(deg[g] == 1 for g in S) else 'Q') + str(len(S)) for S in sets]
    dom = [[tuple(t) for t in TY[len(S)]] for S in sets]
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
            pos_e = tuple(tuple(sets[e].index(x) for x in [g] + ([y] if closed else []) + list(perm) + pe)
                          for perm in itertools.permutations(sym))
            pos_f = tuple(sets[f].index(x) for x in (g, y, pf))
            okE, okF = allowed(PX, name, pos_e, pos_f, len(sets[e]), len(sets[f]))
            dom[e] = [v for v in dom[e] if signature(list(range(len(v))), dict(enumerate(v))) in okE]
            dom[f] = [v for v in dom[f] if signature(list(range(len(v))), dict(enumerate(v))) in okF]
    return kinds, deg, dom


def graph(sets, m):
    G = nx.Graph()
    G.add_nodes_from((('a', i) for i in range(len(sets))), c='a')
    G.add_nodes_from((('g', g) for g in range(m)), c='g')
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    return G


def safe_masks(sets, m, dom, allocs):
    """masks[i][t, k]: agent i with type dom[i][t] is safe in allocation k (raw EFX0, vectorized over types)."""
    n = len(sets)
    out = []
    for i, S in enumerate(sets):
        V = np.array(dom[i], dtype=np.int64)                      # types x |S|
        pos = {g: p for p, g in enumerate(S)}
        M = np.zeros((len(dom[i]), len(allocs)), dtype=bool)
        for k, A in enumerate(allocs):
            own = [pos[g] for g in S if A[g] == i]
            mine = V[:, own].sum(1)
            ok = np.ones(len(V), dtype=bool)
            for j in range(n):
                if j == i: continue
                B = [g for g in range(m) if A[g] == j]
                if len(B) <= 1: continue
                inR = [pos[g] for g in B if g in pos]
                if not inR: continue
                vals = V[:, inR]
                thr = vals.sum(1) - (vals.min(1) if len(inR) == len(B) else 0)
                ok &= mine >= thr
            M[:, k] = ok
        out.append(M)
    return out


LIB = None


def covered(masks):
    """check4.py's C routine: every profile of the product of domains has a common allocation."""
    global LIB
    if LIB is None: LIB = check4.load_c()
    n = len(masks)
    K = masks[0].shape[1]
    W = max(1, (K + 63) // 64)
    off = [0]
    for Mi in masks: off.append(off[-1] + Mi.shape[0] * W)
    buf = np.zeros(off[-1], dtype=np.uint64)
    for i, Mi in enumerate(masks):
        pad = np.zeros((Mi.shape[0], W * 64), dtype=bool); pad[:, :K] = Mi
        words = np.packbits(pad.reshape(Mi.shape[0], W, 64)[:, :, ::-1], axis=2).view('>u8').reshape(Mi.shape[0], W)
        buf[off[i]:off[i + 1]] = words.astype(np.uint64).ravel()
    F = np.zeros((n + 1) * W, dtype=np.uint64)
    for l in range(n + 1):
        full = np.ones(K, dtype=bool)
        for j in range(l, n): full &= masks[j].all(0)
        pad = np.zeros(W * 64, dtype=bool); pad[:K] = full
        F[l * W:(l + 1) * W] = np.packbits(pad.reshape(W, 64)[:, ::-1], axis=1).view('>u8').ravel().astype(np.uint64)
    P = ctypes.POINTER(ctypes.c_uint64)
    return bool(LIB.covered(n, W, (ctypes.c_int * n)(*[Mi.shape[0] for Mi in masks]), (ctypes.c_long * n)(*off[:n]),
                            buf.ctypes.data_as(P), F.ctypes.data_as(P)))


CERT = None


def check_one(item):
    n, m, sets, dom, kinds = item
    G = graph(sets, m)
    h = nx.weisfeiler_lehman_graph_hash(G, node_attr='c')
    for r in CERT.get((n, m, h), []):
        gm = nx.algorithms.isomorphism.GraphMatcher(G, graph(r['sets'], r['m']), node_match=lambda a, b: a['c'] == b['c'])
        if not gm.is_isomorphic(): continue
        mp = gm.mapping
        if 'allocs' not in r: return sets, kinds, None, 'not certified (%s)' % ('timeout' if 'timeout' in r else 'no allocations')
        gmap = {g: mp[('g', g)][1] for g in range(m)}
        inv = {mp[('a', a)][1]: a for a in range(n)}
        allocs = [[inv[A[gmap[g]]] for g in range(m)] for A in r['allocs']]
        masks = safe_masks(sets, m, dom, allocs)
        ok = covered(masks)
        d2 = all(sum(1 for c in collections.Counter(A).values() if c > 2) <= 1 for A in allocs)
        prof = int(np.prod([len(d) for d in dom], dtype=object))
        return sets, kinds, (ok, d2, prof, len(allocs)), None
    return sets, kinds, None, 'no isomorphic core in the certificate'


def _init(c):
    global CERT
    CERT = c


def main():
    beta = int(sys.argv[1])
    cert = json.load(gzip.open(sys.argv[2], 'rt'))
    raw = open(sys.argv[3], 'rb').read()
    opts = dict(a[2:].split('=', 1) for a in sys.argv[4:] if a.startswith('--') and '=' in a)
    log = opts.get('reductions-log', os.path.join(HERE, '..', 'results', 'k4_check_min_cex_reductions.log'))
    rec = re.findall(r'written to (\S+) \(sha256 ([0-9a-f]{64})\)', open(log).read())
    want = [h for f, h in rec if os.path.basename(f) == os.path.basename(sys.argv[3])]
    got = hashlib.sha256(raw).hexdigest()
    sha_ok = bool(want) and all(h == got for h in want)
    print('uncovered-profile file %s: sha256 %s, %s' % (sys.argv[3], got, 'matches %s' % log if sha_ok else
                                                         'DOES NOT MATCH the value recorded in %s' % log), flush=True)
    PX = {k: v for k, v in json.loads(raw).items() if k.startswith('px-')}
    stat = collections.Counter()
    left, buckets = [], collections.defaultdict(list)
    orbit_ok = False
    for n, m, sets in expand(beta):
        if n is None: orbit_ok = m; continue
        stat['expanded'] += 1
        n4 = sum(len(S) == 4 for S in sets)
        if n4 == 0 or (n == 5 and n4 < 3): continue
        deg = collections.Counter(g for S in sets for g in S)
        p3 = [len(S) == 3 and any(deg[g] == 1 for g in S) for S in sets]
        if any(deg[g] == 2 and all(p3[a] for a in range(n) if g in sets[a]) for g in deg): continue
        stat['after filters'] += 1
        kinds, deg, dom = domains(sets, PX)
        if any(not d for d in dom): continue
        G = graph(sets, m)
        h = (n, m, nx.weisfeiler_lehman_graph_hash(G, node_attr='c'))
        if any(nx.is_isomorphic(G, G2, node_match=lambda a, b: a['c'] == b['c']) for G2 in buckets[h]): continue
        buckets[h].append(G)
        left.append((n, m, sets, dom, kinds))
    print('beta = %d: %d cores expanded from G\' (5 <= n <= %d), %d pass the filters, %d left after K4.MC5 up to '
          'isomorphism; orbit counting %s' % (beta, stat['expanded'], 3 * (beta - 1), stat['after filters'], len(left),
                                              'OK' if orbit_ok else 'FAILED'), flush=True)
    cb = collections.defaultdict(list)
    for r in cert:
        cb[(r['n'], r['m'], nx.weisfeiler_lehman_graph_hash(graph(r['sets'], r['m']), node_attr='c'))].append(r)
    ok, d2all, nprof, bad = True, True, 0, collections.Counter()
    with Pool(int(opts.get('jobs', 4)), initializer=_init, initargs=(cb,)) as pool:
        for sets, kinds, res, err in pool.imap_unordered(check_one, left, chunksize=4):
            if err:
                ok = False; bad[err.split(' (')[0]] += 1
                if bad[err.split(' (')[0]] <= 20: print('  %s: %s %s' % (err, ''.join(kinds), sets))
                continue
            cov, d2, prof, na = res
            nprof += prof
            if not cov:
                ok = False; print('  UNCOVERED profiles: %s %s' % (''.join(kinds), sets))
            d2all &= d2
    print('checked %d cores (%d profiles in all): %s; problems: %s' % (len(left), nprof, 'all covered' if ok else
                                                                       'NOT all covered', dict(bad)))
    print('every allocation has at most one bundle of more than 2 goods (D2): %s' % d2all)
    ok = ok and d2all and sha_ok and orbit_ok
    print('RESULT: %s' % ('OK' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
