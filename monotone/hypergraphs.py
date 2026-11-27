"""Enumerate relevance hypergraphs up to isomorphism for the monotone threshold search.

A hypergraph on n agents and m goods is a multiset of m good-types, a good-type being the nonempty set of
agents that may value the good (bitmask over agents). Canonical form: the lexicographically least sorted
tuple of types over all agent permutations. Goods are interchangeable within a type in the hypergraph,
not in a valuation, which the SAT search chooses freely.

Pruning (each rule is valid for a counterexample with the fewest agents, then the fewest goods, among
monotone instances with |R_i| <= k; see monotone/threshold.md §2):
  * no junk: every type is nonempty (L3 is valid for monotone valuations);
  * connected incidence graph (L6);
  * every agent has >= 3 relevant goods (|R_i| <= 2 => R1 peels it whatever its valuation);
  * every agent shares >= 2 of its goods with other agents. If at most one relevant good Q of i is shared,
    the private part P satisfies v(P) >= v(Q), so R2 peels P (or R1 when |R_i| <= 2), or v(Q) > v(P),
    so Q is a single good worth more than everything else of i and R1 peels it;
  * m >= n + 4 (Mahara: m <= n + 3 always has an EFX0 allocation for monotone valuations), and m >= 8
    when n = 3 (Akrami et al. v4, Theorem 1.2).
"""
from itertools import permutations


def canonical(types, n):
    best = None
    for perm in permutations(range(n)):
        mapped = []
        for t in types:
            u = 0
            for a in range(n):
                if (t >> a) & 1:
                    u |= 1 << perm[a]
            mapped.append(u)
        mapped.sort()
        tm = tuple(mapped)
        if best is None or tm < best:
            best = tm
    return best


def connected(types, n):
    # union-find over agents through goods
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for t in types:
        ags = [a for a in range(n) if (t >> a) & 1]
        for a in ags[1:]:
            ra, rb = find(ags[0]), find(a)
            if ra != rb:
                parent[ra] = rb
    return len(set(find(a) for a in range(n))) == 1


def enumerate_hypergraphs(n, m, kmax, kmin=3, min_shared=2):
    alltypes = list(range(1, 1 << n))
    out = set()

    def rec(start, chosen, deg):
        if len(chosen) == m:
            if min(deg) < kmin:
                return
            shared = [0] * n
            for t in chosen:
                if bin(t).count("1") >= 2:
                    for a in range(n):
                        if (t >> a) & 1:
                            shared[a] += 1
            if min(shared) < min_shared:
                return
            if not connected(chosen, n):
                return
            out.add(canonical(chosen, n))
            return
        # remaining goods must still be able to lift every degree to kmin
        rem = m - len(chosen)
        if sum(max(0, kmin - d) for d in deg) > rem * n:
            return
        for idx in range(start, len(alltypes)):
            t = alltypes[idx]
            nd = list(deg)
            okk = True
            for a in range(n):
                if (t >> a) & 1:
                    nd[a] += 1
                    if nd[a] > kmax:
                        okk = False
            if not okk:
                continue
            chosen.append(t)
            rec(idx, chosen, nd)
            chosen.pop()

    rec(0, [], [0] * n)
    return sorted(out)


def to_R(types, n):
    """Relevant sets R_i (lists of goods) from a type tuple."""
    return [[g for g, t in enumerate(types) if (t >> a) & 1] for a in range(n)]


if __name__ == "__main__":
    import sys
    n, m, k = map(int, sys.argv[1:4])
    hs = enumerate_hypergraphs(n, m, k)
    print(f"n={n} m={m} k<={k}: {len(hs)} hypergraphs")
    for h in hs[:10]:
        print("  ", h, [len(r) for r in to_R(h, n)])
