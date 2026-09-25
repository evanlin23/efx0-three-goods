"""Completeness of the G' lists (k4/MINCEX.md, section 8) by orbit counting.

G' = incidence graph of a k = 4 core without its private goods: bipartite, connected, n agents of degree 2, 3 or 4,
m' shared goods of degree >= 2, cyclomatic number beta (E = n + m' + beta - 1 edges). For every (n, m'), the graphs
nauty's genbg lists (one per isomorphism class) must satisfy sum n! m'! / |Aut| = the number of labeled such graphs.
|Aut| counts automorphisms that keep the two sides: countg's group size of the graph with a marker path X - Y added,
X adjacent to every agent (X is the only vertex of degree n + 1, so it is fixed, and so is the agent side).
Labeled counts: check4.fill (labeled columns with >= 2 ones for given row sums; self-tested in check4.py) summed over
the agents' degree vectors, then the connected ones by removing the component of agent 1.
Usage: gamma_orbits.py BETA NMIN NMAX"""
import sys, math, shutil, subprocess, itertools, re, collections
from functools import lru_cache
import networkx as nx
import check4

check4.fill = lru_cache(maxsize=None)(check4.fill)          # memoized; its recursion uses the module attribute
GENBG = shutil.which('genbg') or shutil.which('nauty-genbg')
COUNTG = shutil.which('countg') or shutil.which('nauty-countg')


@lru_cache(maxsize=None)
def labeled_all(n, m, E):
    if n == 0: return int(m == 0 and E == 0)
    tot = 0
    for c in itertools.combinations_with_replacement((2, 3, 4), n):
        if sum(c) != E: continue
        mult = math.factorial(n) // math.prod(math.factorial(c.count(d)) for d in (2, 3, 4))
        tot += mult * check4.fill(tuple(sorted(c)), m)
    return tot


@lru_cache(maxsize=None)
def labeled_conn(n, m, E):
    tot = labeled_all(n, m, E)
    for n1 in range(1, n + 1):
        for m1 in range(0, m + 1):
            for E1 in range(0, E + 1):
                if (n1, m1, E1) == (n, m, E): continue
                c = labeled_conn(n1, m1, E1)
                if c: tot -= math.comb(n - 1, n1 - 1) * math.comb(m, m1) * c * labeled_all(n - n1, m - m1, E - E1)
    return tot


def genbg_list(n, mp, E):
    if not (max(2 * n, 2 * mp) <= E <= min(4 * n, n * mp)): return []
    out = subprocess.run([GENBG, '-cq', '-d2:2', '-D4:%d' % n, str(n), str(mp), '%d:%d' % (E, E)],
                         capture_output=True, text=True, check=True).stdout.split()
    return out


def orbit_sum(n, mp, g6s):
    marked = []
    for g6 in g6s:
        G = nx.from_graph6_bytes(g6.encode())
        X, Y = n + mp, n + mp + 1
        G.add_edges_from([(X, a) for a in range(n)] + [(X, Y)])
        marked.append(nx.to_graph6_bytes(G, header=False).decode().strip())
    out = subprocess.run([COUNTG, '--a'], input='\n'.join(marked) + '\n', capture_output=True, text=True).stdout
    rows = re.findall(r'(\d+) graphs? : groupsize=(\S+)', out)
    assert sum(int(c) for c, _ in rows) == len(g6s), out
    f = math.factorial(n) * math.factorial(mp)
    tot = 0
    for c, a in rows:
        a = int(float(a)); assert f % a == 0
        tot += int(c) * (f // a)
    return tot


def main():
    beta, nmin, nmax = map(int, sys.argv[1:4])
    ok = True
    total = 0
    for n in range(nmin, nmax + 1):
        for mp in range(1, n + beta):
            E = n + mp + beta - 1
            lab = labeled_conn(n, mp, E)
            gs = genbg_list(n, mp, E)
            s = orbit_sum(n, mp, gs) if gs else 0
            total += len(gs)
            if lab or gs:
                print("n = %d, m' = %d: %d graphs listed, sum n! m'! / |Aut| = %d, labeled %d %s" % (
                    n, mp, len(gs), s, lab, 'ok' if s == lab else 'MISMATCH'), flush=True)
            ok &= s == lab
    print('beta = %d, %d <= n <= %d: %d graphs G\'; RESULT: %s' % (beta, nmin, nmax, total, 'OK' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
