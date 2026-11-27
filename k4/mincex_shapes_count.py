"""Streaming size count of the minimal-counterexample candidate list for cyclomatic number BETA (k4/MINCEX.md §5;
companion of mincex_shapes.py, which keeps every listed candidate's type domains in memory before removing isomorphic
copies and runs out of memory at beta = 5).  Same generator (mincex_shapes.hypergraphs), same isomorphism test
(Weisfeiler-Lehman buckets + networkx isomorphism, as mincex_shapes.unique) and same K4.MC5 domain restriction
(mincex_shapes.restricted_domains), but isomorphic copies are dropped as they are generated and only the profile count of
each surviving candidate is kept.  Prints, per (n, m): candidates listed, left after isomorphism, left after K4.MC5,
max and total profiles.  Measures the size of a beta = 5 certification; certifies nothing.
    python3 k4/mincex_shapes_count.py BETA [--nmin=N] [--nmax=N]"""
import sys, collections, time
import numpy as np
import networkx as nx
import mincex_shapes as MS


def main():
    beta = int(sys.argv[1])
    opts = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--') and '=' in a)
    nmin, nmax = int(opts.get('nmin', 5)), int(opts['nmax']) if 'nmax' in opts else None
    print('$ python3 k4/mincex_shapes_count.py', *sys.argv[1:], flush=True)
    t0 = time.time(); fail = MS.px_uncovered()
    print('px tables built [%.0f s]' % (time.time() - t0), flush=True)
    buckets = collections.defaultdict(list); listed = collections.Counter(); iso = collections.Counter()
    left = collections.defaultdict(list); last = None
    for n, m, sets in MS.hypergraphs(beta, nmax):
        if n < nmin: continue
        if last != n:
            if last is not None: report(last, listed, iso, left, t0)
            last = n
        listed[(n, m)] += 1
        G = MS.canon_key(sets, m); h = (n, m, nx.weisfeiler_lehman_graph_hash(G, node_attr='c'))
        if any(nx.is_isomorphic(G, G2, node_match=lambda x, y: x['c'] == y['c']) for G2 in buckets[h]): continue
        buckets[h].append(G); iso[(n, m)] += 1
        dom, kinds, rules = MS.restricted_domains(sets, m, fail)
        size = int(np.prod([len(d) for d in dom], dtype=object))
        if size: left[(n, m)].append(size)
    if last is not None: report(last, listed, iso, left, t0)


def report(n, listed, iso, left, t0):
    for (nn, m) in sorted(k for k in listed if k[0] == n):
        L = left[(nn, m)]
        print('  n = %d, m = %d: %d listed, %d up to isomorphism, %d left after K4.MC5 (profiles: max %s, total %s)'
              % (nn, m, listed[(nn, m)], iso[(nn, m)], len(L), max(L) if L else 0, sum(L)), flush=True)
    print('  [n = %d done, %.0f s]' % (n, time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
