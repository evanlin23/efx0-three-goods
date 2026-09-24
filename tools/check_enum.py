"""Completeness of the hypergraph list in a certificate file, by orbit counting; independent of nauty and gen_cores.
A connected core with n agents and m goods is a connected bipartite graph (agents | goods) in which every agent has
degree 3, every good degree >= 1, and no agent has two goods of degree 1. For each (n, m) in the file, checks that
  1. every hypergraph is such a core,
  2. no two hypergraphs are isomorphic (isomorphisms map agents to agents and goods to goods; networkx VF2),
  3. the orbits add up: sum over hypergraphs H of n! m! / |Aut(H)| equals the number of labeled connected cores.
Then every labeled core lies in the orbit of exactly one listed H, i.e. the list is complete up to isomorphism.
Labeled count: T(a, g) counts a x g 0/1 matrices with row sums 3, no zero column, at most one column of sum 1 in each
row (choose the p private columns and their distinct owner rows, then fill the rest with every column sum >= 2, a DP
over columns on how many rows still need 1, 2 or 3 goods); connected counts come from the component of agent 1.
Usage: check_enum.py certs.json.gz [certs.json.gz ...]
       check_enum.py --selftest     compares the labeled counts with brute force over all small matrices (about 1 min)"""
import sys, json, gzip, collections, itertools
from functools import lru_cache
from math import comb, factorial
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

@lru_cache(maxsize=None)
def fill(c1, c2, c3, q):
    """Ways to fill q labeled columns, each with >= 2 ones, so that c1, c2, c3 labeled rows get 1, 2, 3 ones."""
    if c1 + 2 * c2 + 3 * c3 < 2 * q: return 0
    if q == 0: return int(c1 == c2 == c3 == 0)
    return sum(comb(c1, k1) * comb(c2, k2) * comb(c3, k3) * fill(c1 - k1 + k2, c2 - k2 + k3, c3 - k3, q - 1)
               for k1 in range(c1 + 1) for k2 in range(c2 + 1) for k3 in range(c3 + 1) if k1 + k2 + k3 >= 2)

@lru_cache(maxsize=None)
def labeled(a, g):
    """Labeled cores with a agents and g goods, connected or not."""
    return sum(comb(g, p) * factorial(a) // factorial(a - p) * fill(0, p, a - p, g - p) for p in range(min(a, g) + 1))

@lru_cache(maxsize=None)
def connected(a, g):
    """Labeled connected cores: subtract the ways in which agent 1's component is smaller than everything."""
    if a == 0: return 0
    return labeled(a, g) - sum(comb(a - 1, a1 - 1) * comb(g, g1) * connected(a1, g1) * labeled(a - a1, g - g1)
                               for a1 in range(1, a + 1) for g1 in range(g + 1) if (a1, g1) != (a, g))

def incidence(sets):
    G = nx.Graph()
    for i, S in enumerate(sets):
        G.add_node(('a', i), kind='a')
        for x in S: G.add_node(('g', x), kind='g'); G.add_edge(('a', i), ('g', x))
    return G

def is_core(n, m, sets):
    deg = collections.Counter(x for S in sets for x in S)
    return (len(sets) == n and all(len(set(S)) == 3 for S in sets) and set(deg) == set(range(m))
            and all(sum(deg[x] == 1 for x in S) <= 1 for S in sets) and nx.is_connected(incidence(sets)))

same = lambda u, v: u['kind'] == v['kind']

def check(n, m, hypergraphs):
    """Returns (problems, orbit sum, labeled connected count)."""
    problems, orbits, buckets = 0, 0, collections.defaultdict(list)
    for sets in hypergraphs:
        if not is_core(n, m, sets): print("not a connected core:", sets); problems += 1; continue
        G = incidence(sets)
        B = buckets[nx.weisfeiler_lehman_graph_hash(G, node_attr='kind', iterations=4)]
        if any(nx.is_isomorphic(G, H, node_match=same) for H in B): print("isomorphic duplicate:", sets); problems += 1
        B.append(G)
        aut = sum(1 for _ in GraphMatcher(G, G, node_match=same).isomorphisms_iter())
        orbits += factorial(n) * factorial(m) // aut
    total = connected(n, m)
    if orbits != total: print(f"(n,m)=({n},{m}): orbit sum {orbits} != labeled connected cores {total}"); problems += 1
    return problems, orbits, total

def selftest(limit=4e6):
    """Brute force: every a x g choice of 3 goods per agent, for all sizes with at most `limit` choices."""
    bad = 0
    for a in range(1, 6):
        for g in range(3, 3 * a + 1):
            if comb(g, 3) ** a > limit: continue
            tot = con = 0
            for rows in itertools.product(list(itertools.combinations(range(g), 3)), repeat=a):
                deg = collections.Counter(x for S in rows for x in S)
                if len(deg) == g and all(sum(deg[x] == 1 for x in S) <= 1 for S in rows):
                    tot += 1; con += nx.is_connected(incidence(rows))
            ok = (tot, con) == (labeled(a, g), connected(a, g)); bad += not ok
            print(f"a={a} g={g}: brute force {tot} labeled, {con} connected; DP {labeled(a, g)}, {connected(a, g)}"
                  f" {'OK' if ok else 'MISMATCH'}", flush=True)
    return bad

if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        bad = selftest(); print(f"problems: {bad}"); sys.exit(1 if bad else 0)
    problems = 0
    for path in sys.argv[1:]:
        by = collections.defaultdict(list)
        for r in json.load(gzip.open(path, 'rt')): by[(r['n'], r['m'])].append(r['sets'])
        for (n, m), hs in sorted(by.items()):
            p, orbits, total = check(n, m, hs); problems += p
            print(f"{path}: (n,m)=({n},{m}): {len(hs)} hypergraphs, orbit sum {orbits}, labeled connected cores {total}"
                  f" -> {'complete' if not p else 'PROBLEMS'}", flush=True)
    print(f"problems: {problems}"); sys.exit(1 if problems else 0)
