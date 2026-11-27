"""Second independent re-enumeration of the hypergraph families (fast enough for n = 5; no shared code with
monotone/hypergraphs.py or monotone/check_enum.py).

Method: a hypergraph up to permuting goods is a count vector c over the 2^n - 1 nonempty agent sets.
1. Generate every LABELED count vector with sum m and the degree caps, by recursion over the agent sets in
   decreasing size order (hypergraphs.py recurses over sets in increasing bitmask order and canonicalises
   each leaf).
2. Filter with the conditions re-implemented here: every degree in [3, k], at least 2 shared goods per agent,
   connected (networkx).
3. Isomorphism classes are orbits under agent permutations, which act on the coordinates of c. The canonical
   form is the lexicographic minimum over all n! permuted vectors, computed with numpy.
Compares the classes with the lists produced by hypergraphs.enumerate_hypergraphs (from a cached JSON file or
recomputed).

Usage: python3 monotone/check_enum5.py n m k [cached.json]
"""
import sys
import json
from itertools import permutations
import numpy as np
import networkx as nx


def labeled_vectors(n, m, k):
    sets = [s for s in range(1, 1 << n)]
    sets.sort(key=lambda s: (-bin(s).count("1"), s))
    members = [[a for a in range(n) if (s >> a) & 1] for s in sets]
    out = []
    c = [0] * len(sets)
    deg = [0] * n

    def rec(t, left):
        if left == 0:
            out.append(list(c))
            return
        if t == len(sets):
            return
        # every remaining set is at least as small as sets[t]; cap by degree room
        room = min(k - deg[a] for a in members[t])
        for x in range(min(room, left), -1, -1):
            c[t] = x
            for a in members[t]:
                deg[a] += x
            rec(t + 1, left - x)
            for a in members[t]:
                deg[a] -= x
            c[t] = 0

    rec(0, m)
    return sets, out


def ok(n, sets, vec, k):
    deg = [0] * n
    shared = [0] * n
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for s, x in zip(sets, vec):
        if not x:
            continue
        mem = [a for a in range(n) if (s >> a) & 1]
        for a in mem:
            deg[a] += x
            if len(mem) >= 2:
                shared[a] += x
        for a in mem[1:]:
            G.add_edge(mem[0], a)
    return min(deg) >= 3 and max(deg) <= k and min(shared) >= 2 and nx.is_connected(G)


def main():
    n, m, k = map(int, sys.argv[1:4])
    sets, vecs = labeled_vectors(n, m, k)
    vecs = [v for v in vecs if ok(n, sets, v, k)]
    idx = {s: i for i, s in enumerate(sets)}
    perms = list(permutations(range(n)))
    A = np.array(vecs, dtype=np.int16) if vecs else np.zeros((0, len(sets)), dtype=np.int16)
    best = None
    for p in perms:
        # coordinate of set s moves to the coordinate of p(s)
        tgt = []
        for s in sets:
            u = 0
            for a in range(n):
                if (s >> a) & 1:
                    u |= 1 << p[a]
            tgt.append(idx[u])
        P = np.empty_like(A)
        P[:, tgt] = A
        if best is None:
            best = P
        else:
            # rowwise lexicographic minimum of best and P
            diff = P != best
            first = np.where(diff.any(axis=1), diff.argmax(axis=1), 0)
            rows = np.arange(len(A))
            smaller = diff.any(axis=1) & (P[rows, first] < best[rows, first])
            best[smaller] = P[smaller]
    mine = set(map(tuple, best.tolist())) if len(A) else set()
    # the other enumeration, converted to the same canonical form
    if len(sys.argv) > 4:
        theirs = [tuple(h) for h in json.load(open(sys.argv[4]))]
    else:
        sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
        from hypergraphs import enumerate_hypergraphs
        theirs = enumerate_hypergraphs(n, m, k)
    conv = set()
    for h in theirs:
        vec = [0] * len(sets)
        for t in h:
            vec[idx[t]] += 1
        cands = []
        for p in perms:
            w = [0] * len(sets)
            for s, x in zip(sets, vec):
                u = 0
                for a in range(n):
                    if (s >> a) & 1:
                        u |= 1 << p[a]
                w[idx[u]] = x
            cands.append(tuple(w))
        conv.add(min(cands))
    same = (mine == conv) and len(conv) == len(theirs)
    print(f"n={n} m={m} k<={k}: labeled vectors {len(vecs)}, classes {len(mine)}; hypergraphs.py {len(theirs)}  "
          f"{'OK' if same else 'MISMATCH'}")
    sys.exit(0 if same else 1)


if __name__ == "__main__":
    main()
