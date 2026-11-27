"""Independent check of a certificate of run_mc.py for the minimal-counterexample candidates with exactly N agents and
cyclomatic number BMIN..BMAX.

The candidate list and the cut type domains are regenerated with k4/check_mincex_cores4.py's own code (written
separately from mincex_shapes.py, which produced the list that was searched): G' from genbg, complete by orbit
counting (gamma_orbits.py), the K4.MC2/MC3 expansion and filters, domains from check_reductions4.py's type enumeration
cut by the uncovered px profiles of results/k4_min_cex_px_uncovered.json (SHA-256 checked against the reductions log),
merged up to isomorphism. Every regenerated candidate must be isomorphic to a certified record; the record's
allocations are mapped through the isomorphism, safety masks are computed with check_mincex_cores4.safe_masks (raw
definition, vectorized), and coverage of the full product of the domains is decided by SAT (Glucose 4): one type per
agent, and per allocation "some agent has a type unsafe in it", with one variable per distinct unsafe set of an agent.
Shape (D2) is not required: TARGET₄ needs EFX₀ only.
Usage: check_mc_n.py N CERT.json.gz [CERT2.json.gz ...] [--bmin=5] [--bmax=B] [--jobs=J] [--expect=K]"""
import sys, os, re, json, gzip, hashlib, collections
import numpy as np
import networkx as nx
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); K4 = os.path.dirname(HERE); ROOT = os.path.dirname(K4)
sys.path.insert(0, K4)
sys.argv = [a if a.startswith('--') or not os.path.exists(a) else os.path.abspath(a) for a in sys.argv]
os.chdir(K4)
import check_mincex_cores4 as CM
import gamma_orbits as GO
from pysat.solvers import Glucose4
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def sat_covered(masks):
    vp = IDPool()
    z = [[vp.id((i, t)) for t in range(M.shape[0])] for i, M in enumerate(masks)]
    s = Glucose4()
    for zi in z:
        for c in CardEnc.equals(zi, 1, vpool=vp, encoding=EncType.totalizer).clauses: s.add_clause(c)
    K = masks[0].shape[1]
    group = {}
    for k in range(K):
        cl = []
        for i, M in enumerate(masks):
            bad = ~M[:, k]
            if not bad.any(): continue
            key = (i, np.packbits(bad).tobytes())
            if key not in group:
                u = group[key] = vp.id(('u',) + key)
                ts = np.flatnonzero(bad)
                s.add_clause([-u] + [z[i][t] for t in ts])
                for t in ts: s.add_clause([-z[i][t], u])
            cl.append(group[key])
        s.add_clause(cl)
    ok = not s.solve()
    s.delete()
    return ok


CERT = None
def _init(c):
    global CERT
    CERT = c

def check_one(item):
    n, m, sets, dom, kinds = item
    G = CM.graph(sets, m)
    h = nx.weisfeiler_lehman_graph_hash(G, node_attr='c')
    for r in CERT.get((n, m, h), []):
        gm = nx.algorithms.isomorphism.GraphMatcher(G, CM.graph(r['sets'], r['m']), node_match=lambda a, b: a['c'] == b['c'])
        if not gm.is_isomorphic(): continue
        if r.get('status', 'certified' if 'allocs' in r else None) != 'certified': return sets, kinds, None, 'record not certified (%s)' % r.get('status')
        mp = gm.mapping
        gmap = {g: mp[('g', g)][1] for g in range(m)}
        inv = {mp[('a', a)][1]: a for a in range(n)}
        allocs = [[inv[A[gmap[g]]] for g in range(m)] for A in r['allocs']]
        if any(len(A) != m for A in r['allocs']): return sets, kinds, None, 'malformed allocation'
        masks = CM.safe_masks(sets, m, dom, allocs)
        prof = int(np.prod([len(d) for d in dom], dtype=object))
        return sets, kinds, (sat_covered(masks), prof, len(allocs)), None
    return sets, kinds, None, 'no isomorphic core in the certificate'


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    N = int(args[0]); bmin = int(opt.get('bmin', 5)); bmax = int(opt.get('bmax', 3 * N - 2))
    jobs = int(opt.get('jobs', 4))
    print('command: python3 k4/hunt/check_mc_n.py ' + ' '.join(sys.argv[1:]), flush=True)
    pxf = os.path.join(ROOT, 'results', 'k4_min_cex_px_uncovered.json')
    raw = open(pxf, 'rb').read()
    log = open(os.path.join(ROOT, 'results', 'k4_check_min_cex_reductions.log')).read()
    want = [h for f, h in re.findall(r'written to (\S+) \(sha256 ([0-9a-f]{64})\)', log) if os.path.basename(f) == os.path.basename(pxf)]
    got = hashlib.sha256(raw).hexdigest()
    sha_ok = bool(want) and all(h == got for h in want)
    print(f'uncovered-profile file: sha256 {got}, {"matches the reductions log" if sha_ok else "DOES NOT MATCH"}', flush=True)
    PX = {k: v for k, v in json.loads(raw).items() if k.startswith('px-')}
    cert = [r for f in args[1:] for r in json.load(gzip.open(f, 'rt'))]
    for r in cert:                                # compact allocations: base36 strings, one character per good
        r['allocs'] = [[int(ch, 36) for ch in A] if isinstance(A, str) else A for A in r.get('allocs', [])]
    cb = collections.defaultdict(list)
    for r in cert:
        cb[(r['n'], r['m'], nx.weisfeiler_lehman_graph_hash(CM.graph(r['sets'], r['m']), node_attr='c'))].append(r)
    ok, total_left, orbit_ok = sha_ok, 0, True
    stats = collections.Counter()
    with Pool(jobs, initializer=CM._init_px, initargs=(PX,)) as pool:
        left, buckets = [], collections.defaultdict(list)
        for beta in range(bmin, bmax + 1):
            nb = 0
            for mp in range(1, N + beta):
                E = N + mp + beta - 1
                gs = GO.genbg_list(N, mp, E)
                lab = GO.labeled_conn(N, mp, E)
                sm = GO.orbit_sum(N, mp, gs) if gs else 0
                if lab or gs:
                    print(f"  beta={beta} orbit count n={N}, m'={mp}: {len(gs)} graphs G', orbit sum {sm}, labeled {lab} "
                          f"{'ok' if sm == lab else 'MISMATCH'}", flush=True)
                orbit_ok &= sm == lab
                chunks = [(N, mp, gs[i:i + 200]) for i in range(0, len(gs), 200)]
                for surv, cnt in pool.imap_unordered(CM.expand_chunk, chunks):
                    for n_, m, sets, dom, kinds in surv:
                        G = CM.graph(sets, m)
                        h = (n_, m, nx.weisfeiler_lehman_graph_hash(G, node_attr='c'))
                        if any(nx.is_isomorphic(G, G2, node_match=lambda a, b: a['c'] == b['c']) for G2 in buckets[h]): continue
                        buckets[h].append(G)
                        left.append((n_, m, sets, dom, kinds)); nb += 1
            print(f'  beta={beta}: {nb} candidates left after the filters and K4.MC5, up to isomorphism', flush=True)
    print(f'regenerated candidates: {len(left)} (n = {N}, beta {bmin}..{bmax}); orbit counting {"OK" if orbit_ok else "FAILED"}', flush=True)
    with Pool(jobs, initializer=_init, initargs=(cb,)) as pool:
        for sets, kinds, res, err in pool.imap_unordered(check_one, left, chunksize=4):
            if err:
                stats[err] += 1; ok = False
                if stats[err] <= 10: print(f'  {err}: {"".join(kinds)} {sets}', flush=True)
                continue
            cov, prof, na = res
            stats['covered' if cov else 'NOT COVERED'] += 1
            stats['profiles'] += prof
            if not cov: ok = False; print(f'  NOT COVERED: {"".join(kinds)} {sets}', flush=True)
    print(f'checked {len(left)} candidates: {dict(stats)}', flush=True)
    if 'expect' in opt and int(opt['expect']) != stats['covered']: print('EXPECT FAILED'); ok = False
    ok = ok and orbit_ok
    print('RESULT:', 'OK' if ok else 'FAILED', flush=True)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
