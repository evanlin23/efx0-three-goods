"""SAT-free checker for k = 4 certificates (written independently of search4.py and order_types.py).

For each certificate file (results/k4_certs_*.json.gz), checks:
  1. every listed hypergraph is a k = 4 core: connected, agent degrees in {3, 4} (all 4 if the file says pure), every
     good relevant to someone, at most d - 2 private goods for an agent of degree d;
  2. no two are isomorphic, and the orbits add up: sum of n! m! / |Aut(H)| equals the number of labeled such cores
     (computed below by a DP, self-tested against brute force with --selftest); so the list is complete;
  3. coverage: for every profile of strict balanced types (an agent of degree 4 with private goods p, q also has
     p + q < s + t), one of the listed allocations is EFX₀. Types are enumerated here from scratch: integer vectors in
     [1, 16]^d, grouped by the dense ranking of all their nonempty subset sums (k4/SCOUT.md §2 shows [1, 16]^4 meets
     every type); strict = all nonempty subset sums distinct; balanced = max < sum of the others. Safety is the raw
     definition: v_i(X_i) >= v_i(X_j) - v_i(h) for all j != i and h in X_j, all goods counted.
  4. reports how many cores are covered using only allocations with at most one bundle of more than 2 goods (D2) or
     of more than 3 goods (D3).
Coverage loop in C (compiled at run time from the string below), everything else plain Python.
Usage: check4.py FILE [FILE ...]      check4.py --selftest"""
import ctypes, gzip, itertools, json, math, os, subprocess, sys, tempfile
from functools import lru_cache
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

C_SRC = r"""
#include <stdint.h>
/* all profiles covered? masks[off[i] + t*W + w]; returns 1 if every profile has a common allocation */
static int n_, W_; static const int *D_; static const long *off_; static const uint64_t *M_, *F_;
static int go(int l, const uint64_t *pre) {
    uint64_t cur[W_];
    for (int t = 0; t < D_[l]; t++) {
        const uint64_t *m = M_ + off_[l] + (long)t * W_;
        int any = 0;
        if (l + 1 == n_) {                      /* last agent: some common allocation? (stop at the first) */
            for (int w = 0; w < W_ && !any; w++) any = (pre[w] & m[w]) != 0;
            if (!any) return 0;
            continue;
        }
        for (int w = 0; w < W_; w++) { cur[w] = pre[w] & m[w]; if (cur[w]) any = 1; }
        if (!any) return 0;
        int full = 0;                           /* an allocation safe for all later agents with every type */
        for (int w = 0; w < W_ && !full; w++) full = (cur[w] & F_[(l + 1) * W_ + w]) != 0;
        if (!full && !go(l + 1, cur)) return 0;
    }
    return 1;
}
int covered(int n, int W, const int *D, const long *off, const uint64_t *M, const uint64_t *F) {
    n_ = n; W_ = W; D_ = D; off_ = off; M_ = M; F_ = F;
    uint64_t all[W]; for (int w = 0; w < W; w++) all[w] = ~(uint64_t)0;
    return go(0, all);
}
"""

def load_c():
    d = tempfile.mkdtemp()
    with open(os.path.join(d, 'c.c'), 'w') as f: f.write(C_SRC)
    subprocess.run(['gcc', '-O2', '-shared', '-fPIC', '-o', os.path.join(d, 'c.so'), os.path.join(d, 'c.c')], check=True)
    return ctypes.CDLL(os.path.join(d, 'c.so'))

@lru_cache(maxsize=None)
def strict_balanced_types(d, ties=False):
    """One integer representative per strict balanced order type of d goods (ties=True: every balanced type)."""
    reps = {}
    for v in itertools.product(range(1, 17), repeat=d):
        sums = [sum(v[g] for g in range(d) if S >> g & 1) for S in range(1, 1 << d)]
        if (not ties and len(set(sums)) < len(sums)) or max(v) >= sum(v) - max(v): continue
        order = sorted(set(sums))
        key = tuple(order.index(s) for s in sums)
        reps.setdefault(key, v)
    return list(reps.values())

def is_core(n, m, sets, pure):
    deg = [sum(g in S for S in sets) for g in range(m)]
    G = nx.Graph()
    G.add_nodes_from([('a', i) for i in range(n)] + [('g', g) for g in range(m)])
    G.add_edges_from((('a', i), ('g', g)) for i, S in enumerate(sets) for g in S)
    return (all(len(set(S)) == len(S) and len(S) in ((4,) if pure else (3, 4)) for S in sets)
            and all(d >= 1 for d in deg) and nx.is_connected(G)
            and all(sum(deg[g] == 1 for g in S) <= len(S) - 2 for S in sets)), G

@lru_cache(maxsize=None)
def fill(need, q):
    """Ways to fill q labeled columns, each with >= 2 ones, giving labeled rows the remaining needs `need` (a sorted
    tuple of positive ints; rows are labeled, the state is the multiset)."""
    if sum(need) < 2 * q: return 0
    if q == 0: return int(not need)
    cnt = [need.count(r) for r in range(5)]
    total = 0
    for ks in itertools.product(*(range(cnt[r] + 1) for r in range(5))):
        if ks[0] or sum(ks) < 2: continue
        ways = math.prod(math.comb(cnt[r], ks[r]) for r in range(5))
        new = [r for r in range(1, 5) for _ in range(cnt[r] - ks[r])] + [r - 1 for r in range(1, 5) for _ in range(ks[r]) if r > 1]
        total += ways * fill(tuple(sorted(new)), q - 1)
    return total

def labeled_all(n, m, degs):
    """Labeled n x m matrices, row sums in degs, no zero column, row of sum d has <= d - 2 columns of sum 1."""
    if n == 0: return int(m == 0)
    total = 0
    choices = [(d, p) for d in degs for p in range(d - 1)]
    for rows in itertools.product(choices, repeat=n):
        P = sum(p for _, p in rows)
        if P > m: continue
        ways = math.factorial(m) // (math.factorial(m - P) * math.prod(math.factorial(p) for _, p in rows))
        need = tuple(sorted(d - p for d, p in rows if d - p > 0))
        total += ways * fill(need, m - P)
    return total

@lru_cache(maxsize=None)
def labeled_conn(n, m, degs):
    tot = labeled_all(n, m, degs)
    for n1 in range(1, n + 1):
        for m1 in range(0, m + 1):
            if (n1, m1) == (n, m): continue
            c = labeled_conn(n1, m1, degs)
            if c: tot -= math.comb(n - 1, n1 - 1) * math.comb(m, m1) * c * labeled_all(n - n1, m - m1, degs)
    return tot

def labeled_count(n, m, pure):
    return labeled_conn(n, m, (4,)) if pure else labeled_conn(n, m, (3, 4)) - labeled_conn(n, m, (3,))

def brute(n, m, pure):
    degs = (4,) if pure else (3, 4)
    rows = [S for d in degs for S in itertools.combinations(range(m), d)]
    return sum(1 for sets in itertools.product(rows, repeat=n)
               if (pure or any(len(S) == 4 for S in sets)) and is_core(n, m, [list(S) for S in sets], pure)[0])

def aut_size(G):
    same = lambda a, b: a['side'] == b['side']
    for v in G: G.nodes[v]['side'] = v[0]
    return sum(1 for _ in GraphMatcher(G, G, node_match=same).isomorphisms_iter())

def efx0_safe(i, vals, bundles):
    own = sum(vals.get(g, 0) for g in bundles[i])
    return all(own >= sum(vals.get(g, 0) for g in B) - vals.get(h, 0)
               for j, B in enumerate(bundles) if j != i for h in B)

def check_file(path, lib):
    data = json.load(gzip.open(path, 'rt'))
    n, pure, cores, ties = data['n'], data['pure'], data['cores'], data.get('ties', False)
    ok, byM = True, {}
    for rec in cores: byM.setdefault(rec['m'], []).append(rec)
    d2 = d3 = 0
    for m, recs in sorted(byM.items()):
        graphs, orbit = [], 0
        for rec in recs:
            good, G = is_core(n, m, rec['sets'], pure)
            if not good: print(f"  NOT A CORE: {rec['sets']}"); ok = False
            for v in G: G.nodes[v]['side'] = v[0]
            h = nx.weisfeiler_lehman_graph_hash(G, node_attr='side')
            for h2, G2 in graphs:
                if h == h2 and nx.is_isomorphic(G, G2, node_match=lambda a, b: a['side'] == b['side']):
                    print(f"  DUPLICATE: {rec['sets']}"); ok = False
            graphs.append((h, G))
            orbit += math.factorial(n) * math.factorial(m) // aut_size(G)
        lab = labeled_count(n, m, pure)
        if orbit != lab: print(f"  m={m}: orbit sum {orbit} != labeled count {lab}"); ok = False
        # coverage
        bad = 0
        for rec in recs:
            sets, A_list = rec['sets'], rec['allocs']
            deg = [sum(g in S for S in sets) for g in range(m)]
            doms = []
            for S in sets:
                priv = [g for g in S if deg[g] == 1]
                dom = []
                for v in strict_balanced_types(len(S), ties):
                    vals = dict(zip(S, v))
                    if len(priv) == 2 and vals[priv[0]] + vals[priv[1]] >= sum(v) - vals[priv[0]] - vals[priv[1]]: continue
                    dom.append(vals)
                doms.append(dom)
            K = len(A_list); W = max(1, (K + 63) // 64)
            off = [0]
            for D in doms: off.append(off[-1] + len(D) * W)
            M = (ctypes.c_uint64 * off[-1])()
            for a, A in enumerate(A_list):
                bundles = [[g for g in range(m) if A[g] == j] for j in range(n)]
                for i, D in enumerate(doms):
                    for t, vals in enumerate(D):
                        if efx0_safe(i, vals, bundles): M[off[i] + t * W + a // 64] |= 1 << (a % 64)
            F = (ctypes.c_uint64 * ((n + 1) * W))()      # F[l]: allocations safe for agents l..n-1 with every type
            for a in range(K):
                for l in range(n + 1):
                    if all(M[off[j] + t * W + a // 64] >> (a % 64) & 1 for j in range(l, n) for t in range(len(doms[j]))):
                        F[l * W + a // 64] |= 1 << (a % 64)
            cov = lib.covered(n, W, (ctypes.c_int * n)(*[len(D) for D in doms]), (ctypes.c_long * n)(*off[:n]), M, F)
            if not cov: bad += 1; ok = False; print(f"  NOT COVERED: {sets}")
            big = lambda A, s: sum(A.count(j) > s for j in range(n))
            d2 += cov and all(big(A, 2) <= 1 for A in A_list)
            d3 += cov and all(big(A, 3) <= 1 for A in A_list)
        print(f"  n={n} m={m}{' pure' if pure else ''}{' ties' if ties else ''}: {len(recs)} cores, orbit sum {orbit} = labeled {lab}: "
              f"{'yes' if orbit == lab else 'NO'}; all profiles covered in {len(recs) - bad}/{len(recs)}", flush=True)
    print(f"  {path}: {'OK' if ok else 'FAILED'}; cores covered by allocations with <= 1 bundle of > 2 goods: "
          f"{d2}/{len(cores)}, of > 3 goods: {d3}/{len(cores)}", flush=True)
    return ok

if __name__ == '__main__':
    if '--selftest' in sys.argv:
        for n, m, pure in [(1, 4, True), (2, 4, True), (2, 5, True), (2, 6, True), (2, 4, False), (2, 5, False),
                           (2, 6, False), (3, 4, True), (3, 5, True), (3, 5, False), (3, 6, True)]:
            a, b = labeled_count(n, m, pure), brute(n, m, pure)
            print(f"n={n} m={m} {'pure' if pure else 'mixed'}: DP {a}, brute force {b}: {'ok' if a == b else 'MISMATCH'}", flush=True)
        print("types (strict balanced, balanced):", {d: (len(strict_balanced_types(d)), len(strict_balanced_types(d, True))) for d in (3, 4)})
        sys.exit(0)
    lib = load_c()
    sys.exit(0 if all([check_file(p, lib) for p in sys.argv[1:]]) else 1)
