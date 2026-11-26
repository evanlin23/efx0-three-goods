"""Hypergraph generators for k4/girth (degree <= 4 unless said otherwise).  A hypergraph is a list of edges (lists of
agents); edge index = good.  `with_values` attaches random additive values (1..vmax) to every incidence.

    random_linear(n, rng, maxdeg=4, sizes=(2,3,4), tries=200, private=0.3)   linear (girth >= 3), triangles allowed
    random_triangle_free(n, rng, ...)                                        no 3-cycle, 2-cycles allowed
    random_deg4(n, rng, ...)                                                 anything with degree <= 4
    fano(), ag23(), pg23(), complete_graph(k)                                structured linear examples
"""
import itertools
import random

from lss import Inst


def with_values(n, edges, rng, vmax=30, mode='uniform'):
    sets = [[] for _ in range(n)]
    vals = [[] for _ in range(n)]
    for g, e in enumerate(edges):
        for x in e:
            sets[x].append(g)
    for x in range(n):
        k = len(sets[x])
        if mode == 'uniform':
            vs = [rng.randint(1, vmax) for _ in range(k)]
        elif mode == 'flat':                       # nearly equal values: balanced agents
            base = rng.randint(vmax // 2, vmax)
            vs = [base + rng.randint(0, 3) for _ in range(k)]
        elif mode == 'geom':                       # top-heavy / spread
            vs = [rng.randint(1, 4) * 2 ** rng.randint(0, 4) for _ in range(k)]
        else:
            raise ValueError(mode)
        vals[x] = vs
    return Inst(sets, vals, len(edges))


def _deg(edges, n):
    d = [0] * n
    for e in edges:
        for x in e:
            d[x] += 1
    return d


def random_linear(n, rng, maxdeg=4, sizes=(2, 3, 4), tries=200, private=0.3):
    edges, pairs = [], set()
    d = [0] * n
    for _ in range(tries):
        s = rng.choice(sizes)
        free = [x for x in range(n) if d[x] < maxdeg]
        if len(free) < s:
            continue
        e = sorted(rng.sample(free, s))
        if any((x, y) in pairs for x, y in itertools.combinations(e, 2)):
            continue
        edges.append(e)
        for x, y in itertools.combinations(e, 2):
            pairs.add((x, y))
        for x in e:
            d[x] += 1
    for x in range(n):
        while d[x] < maxdeg and rng.random() < private:
            edges.append([x])
            d[x] += 1
    return edges


def has_triangle_edges(edges, n):
    I = Inst([[g for g, e in enumerate(edges) if x in e] for x in range(n)],
             [[1] * sum(x in e for e in edges) for x in range(n)], len(edges))
    from lss import triangles
    return bool(triangles(I))


def random_triangle_free(n, rng, maxdeg=4, sizes=(2, 3), tries=200, private=0.3, allow2=True):
    """no 3-cycle (three agents pairwise sharing distinct goods); 2-cycles allowed if allow2"""
    edges = []
    d = [0] * n
    for _ in range(tries):
        s = rng.choice(sizes)
        free = [x for x in range(n) if d[x] < maxdeg]
        if len(free) < s:
            continue
        e = sorted(rng.sample(free, s))
        cand = edges + [e]
        if not allow2:
            pairs = set()
            bad = False
            for f in cand:
                for x, y in itertools.combinations(f, 2):
                    if (x, y) in pairs:
                        bad = True
                    pairs.add((x, y))
            if bad:
                continue
        if has_triangle_edges(cand, n):
            continue
        edges.append(e)
        for x in e:
            d[x] += 1
    for x in range(n):
        while d[x] < maxdeg and rng.random() < private:
            edges.append([x])
            d[x] += 1
    return edges


def random_deg4(n, rng, maxdeg=4, sizes=(2, 3, 4), tries=200, private=0.3):
    edges = []
    d = [0] * n
    for _ in range(tries):
        s = rng.choice(sizes)
        free = [x for x in range(n) if d[x] < maxdeg]
        if len(free) < s:
            continue
        e = sorted(rng.sample(free, s))
        edges.append(e)
        for x in e:
            d[x] += 1
    for x in range(n):
        while d[x] < maxdeg and rng.random() < private:
            edges.append([x])
            d[x] += 1
    return edges


def fano():
    return 7, [[0, 1, 3], [1, 2, 4], [2, 3, 5], [3, 4, 6], [4, 5, 0], [5, 6, 1], [6, 0, 2]]


def ag23():
    pts = [(x, y) for x in range(3) for y in range(3)]
    idx = {p: k for k, p in enumerate(pts)}
    lines = set()
    for p, q in itertools.combinations(pts, 2):
        dx, dy = (q[0] - p[0]) % 3, (q[1] - p[1]) % 3
        line = frozenset(idx[((p[0] + t * dx) % 3, (p[1] + t * dy) % 3)] for t in range(3))
        lines.add(line)
    return 9, [sorted(l) for l in sorted(lines, key=sorted)]


def pg23():
    """projective plane of order 3: 13 points, 13 lines of size 4, every point on 4 lines"""
    F = range(3)
    pts = []
    for v in itertools.product(F, repeat=3):
        if any(v):
            first = next(c for c in v if c)
            if first == 1:
                pts.append(v)
    idx = {p: k for k, p in enumerate(pts)}
    lines = []
    for l in pts:
        lines.append(sorted(idx[p] for p in pts if sum(a * b for a, b in zip(l, p)) % 3 == 0))
    return 13, lines


def complete_graph(k):
    return k, [list(e) for e in itertools.combinations(range(k), 2)]
