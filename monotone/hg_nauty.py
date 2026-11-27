"""Hypergraph families of monotone/threshold.md §2 via nauty's genbg (third enumeration, fast for n = 6).

genbg -c -d3:1 -D{k}:{n} n m lists the connected bicoloured graphs (agents first, goods second; isomorphisms keep
the colour classes) with agent degrees 3..k and good degrees >= 1, one per isomorphism class. We keep those in
which every agent shares at least 2 of its goods. Output: type tuples (sorted agent-set bitmasks of the goods),
the same objects as monotone/hypergraphs.py, but not canonicalised in the same way, so comparisons go through
canonical forms.

Usage: python3 monotone/hg_nauty.py n m k [--count] [--out file.json] [--compare]
"""
import sys
import json
import shutil
import subprocess
from itertools import permutations

GENBG = shutil.which("genbg") or shutil.which("nauty-genbg")


def decode_graph6(line, n, m):
    """Neighbourhoods of the first n vertices (agents) among the last m (goods) from a graph6 line."""
    s = line.strip()
    N = ord(s[0]) - 63
    assert N == n + m
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for b in range(5, -1, -1):
            bits.append((v >> b) & 1)
    adj = [set() for _ in range(N)]
    k = 0
    for j in range(1, N):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return [sorted(g - n for g in adj[a]) for a in range(n)]


def families(n, m, k):
    args = [GENBG, "-cq", f"-d3:1", f"-D{k}:{n}", str(n), str(m)]
    proc = subprocess.Popen(args, stdout=subprocess.PIPE, text=True)
    for line in proc.stdout:
        nb = decode_graph6(line, n, m)
        deg = [0] * m
        for a in range(n):
            for g in nb[a]:
                deg[g] += 1
        if any(sum(1 for g in nb[a] if deg[g] >= 2) < 2 for a in range(n)):
            continue
        types = [0] * m
        for a in range(n):
            for g in nb[a]:
                types[g] |= 1 << a
        yield tuple(sorted(types))
    proc.wait()


def canon(types, n):
    best = None
    for p in permutations(range(n)):
        t = tuple(sorted(sum(1 << p[a] for a in range(n) if (x >> a) & 1) for x in types))
        if best is None or t < best:
            best = t
    return best


def main():
    n, m, k = map(int, sys.argv[1:4])
    hs = list(families(n, m, k))
    print(f"n={n} m={m} k<={k}: {len(hs)} hypergraphs (genbg)", flush=True)
    if "--out" in sys.argv:
        json.dump([list(h) for h in hs], open(sys.argv[sys.argv.index("--out") + 1], "w"))
    if "--compare" in sys.argv:
        import os
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        if "--cached" in sys.argv:
            theirs = [tuple(h) for h in json.load(open(sys.argv[sys.argv.index("--cached") + 1]))]
        else:
            from hypergraphs import enumerate_hypergraphs
            theirs = enumerate_hypergraphs(n, m, k)
        a = set(canon(h, n) for h in hs)
        b = set(canon(h, n) for h in theirs)
        print(f"   genbg classes {len(a)} (listed {len(hs)}), hypergraphs.py {len(b)}: "
              f"{'OK' if a == b and len(a) == len(hs) else 'MISMATCH'}")


if __name__ == "__main__":
    main()
