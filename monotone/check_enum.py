"""Independent re-enumeration of the hypergraph families of monotone/hypergraphs.py (no shared code).

Method: every multiset of m good-types (nonempty agent sets) via itertools.combinations_with_replacement,
the pruning conditions re-implemented from their definitions (degree 3..k, at least 2 shared goods per
agent, connected via networkx), and isomorphism classes taken as orbits of agent permutations acting on
the count vector. Compares the set of classes with hypergraphs.enumerate_hypergraphs.

Usage: python3 monotone/check_enum.py n m k [n m k ...]
"""
import sys
import os
from itertools import combinations_with_replacement, permutations
import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def classes(n, m, k):
    types = [frozenset(a for a in range(n) if (t >> a) & 1) for t in range(1, 1 << n)]
    perms = list(permutations(range(n)))
    seen = set()
    for combo in combinations_with_replacement(range(len(types)), m):
        goods = [types[c] for c in combo]
        deg = [sum(1 for G in goods if a in G) for a in range(n)]
        if min(deg) < 3 or max(deg) > k:
            continue
        shared = [sum(1 for G in goods if a in G and len(G) >= 2) for a in range(n)]
        if min(shared) < 2:
            continue
        g = nx.Graph()
        g.add_nodes_from(("a", a) for a in range(n))
        for idx, G in enumerate(goods):
            for a in G:
                g.add_edge(("a", a), ("g", idx))
        if not nx.is_connected(g):
            continue
        orbit = []
        for p in perms:
            orbit.append(tuple(sorted(tuple(sorted(p[a] for a in G)) for G in goods)))
        seen.add(min(orbit))
    return seen


def main():
    from hypergraphs import enumerate_hypergraphs
    args = list(map(int, sys.argv[1:]))
    allok = True
    for t in range(0, len(args), 3):
        n, m, k = args[t:t + 3]
        mine = classes(n, m, k)
        theirs = enumerate_hypergraphs(n, m, k)
        conv = set()
        for h in theirs:
            # convert bitmask types to the same canonical form as above
            goods = [frozenset(a for a in range(n) if (x >> a) & 1) for x in h]
            orbit = [tuple(sorted(tuple(sorted(p[a] for a in G)) for G in goods)) for p in permutations(range(n))]
            conv.add(min(orbit))
        ok = conv == mine and len(conv) == len(theirs)
        allok &= ok
        print(f"n={n} m={m} k<={k}: independent {len(mine)}, hypergraphs.py {len(theirs)}  {'OK' if ok else 'MISMATCH'}")
    sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
