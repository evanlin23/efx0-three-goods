"""Fast SAT-free checker for k = 4 certificates: k4/check4.py with a faster coverage step (compute/k4-frontier).

k4/check4.py (unchanged, the simple independent checker; its coverage step is a plain depth-first walk over every
type) is too slow for n = 5 cores with four or five 4-good agents. This file makes the same checks 1-5 below, with
the same type enumeration, core test, orbit counting, D2 test and format test (copied verbatim from check4.py), and
changes only how coverage (check 3) is computed. Written independently of search4.py and order_types.py; note that
its coverage loop uses the same ideas as k4/frontier/scan2.c (minimal rows, a store of covered prefix sets, the last
level by columns), written in the same session, so for an independent confirmation run k4/check4.py where affordable.

For each certificate file (results/k4_certs_*.json.gz), checks:
  1. every listed hypergraph is a k = 4 core: connected, agent degrees in {3, 4} (all 4 if the file says pure), every
     good relevant to someone, at most d - 2 private goods for an agent of degree d;
  2. no two are isomorphic, and the orbits add up: sum of n! m! / |Aut(H)| equals the number of labeled such cores
     (computed below by a DP, self-tested against brute force with --selftest); so the list is complete;
  3. coverage (safety tables vectorized with numpy, the plain loop efx0_safe re-run on every 16th allocation and
     required to agree): for every profile of strict balanced types (an agent of degree 4 with private goods p, q also has
     p + q < s + t), one of the listed allocations is EFX₀. Types are enumerated here from scratch: integer vectors in
     [1, 16]^d, grouped by the dense ranking of all their nonempty subset sums (k4/SCOUT.md §2 shows [1, 16]^4 meets
     every type); strict = all nonempty subset sums distinct; balanced = max < sum of the others. Safety is the raw
     definition: v_i(X_i) >= v_i(X_j) - v_i(h) for all j != i and h in X_j, all goods counted.
  4. D2: every listed allocation has at most one bundle of more than 2 goods;
  5. format: exactly n agents, goods in range(m), allocations of exactly m owners in range(n); every m in 1..3n is
     checked (a missing m group must have labeled count 0), and with --expect the number of cores per file.
Any failure makes the exit status nonzero. Coverage loop in C (compiled at run time from the string below), run in
parallel over cores; everything else plain Python. The loop walks the agents in order, keeping the set `pre` of
allocations safe for every agent so far; each step below is sound because coverage is monotone in `pre` (a larger
`pre` meets every row that a smaller one meets):
  - each agent's types are cut to those whose row (the allocations under which the type is safe) contains no other
    type's row (equal rows: the lowest index); if row_t contains row_u, a profile using t is covered whenever the
    same profile with u is;
  - a child subtree is skipped when the child's set pre & row_t meets F[l+1] (allocations safe for all later agents
    with every type; F is computed over the full domains); a node is skipped when `pre` contains a set already
    proved covered at the same level (memo, levels 1..n-3, reset per core, a set stored only after its subtree was
    fully checked); children are visited smallest set first (order only);
  - the last two agents are checked together: for each type t of agent n-2, every type of agent n-1 meets
    pre & row_t iff the union over the allocations in pre & row_t of their columns (types of agent n-1 safe under
    that allocation) is all of agent n-1's types (used when agent n-1 has at most 512 kept types, else the walk).
Tests: k4/frontier/test_check4_fast.py (this coverage vs check4.py's on thinned certificates of every class, and vs
brute force on random rows). Each run prints this file's SHA-256 after the command line.
Usage: check4_fast.py FILE [FILE ...] [--expect n:MODE:cores ...] [--jobs=J]     MODE = pure, an exact n4, or any
       check4_fast.py --selftest"""
import ctypes, gzip, itertools, json, math, os, subprocess, sys, tempfile
from functools import lru_cache
import networkx as nx
import numpy as np
from networkx.algorithms.isomorphism import GraphMatcher

C_SRC = r"""
#include <stdint.h>
#include <stdlib.h>
/* all profiles covered? masks[off[i] + t*W + w]; returns 1 if every profile has a common allocation, 0 if some
   profile has none, -1 if n > 16 or memory ran out (treated as a failure).
   Memo: DONE[l] lists prefix sets `pre` for which go(l, pre) returned 1 (at levels 1..n-3, at most CAP each). If a
   listed set is contained in `pre`, then go(l, pre) is 1 too: every completion meets the listed set, hence `pre`. */
#define CAP 50000
static int n_, W_; static const int *D_; static const long *off_; static const uint64_t *M_, *F_;
static uint64_t *DONE[16]; static int NDONE[16], *DPC[16];
static int popc(const uint64_t *x);
static int listed(int l, const uint64_t *pre) {
    int p = popc(pre);
    for (int k = 0; k < NDONE[l]; k++) {
        if (DPC[l][k] > p) continue;            /* a subset of pre has at most popc(pre) bits */
        const uint64_t *s = DONE[l] + (long)k * W_; int sub = 1;
        for (int w = 0; w < W_ && sub; w++) sub = (s[w] & ~pre[w]) == 0;
        if (sub) return 1;
    }
    return 0;
}
static uint64_t *CH[16]; static int *PC[16], *IX[16];
static uint64_t *COL, ALL[8]; static int WB;    /* COL[a*WB..]: the last agent's types whose row contains allocation a */
static int popc(const uint64_t *x) { int c = 0; for (int w = 0; w < W_; w++) c += __builtin_popcountll(x[w]); return c; }
static int go(int l, const uint64_t *pre) {
    if (l + 1 == n_) {                          /* last agent: some common allocation for every type? */
        for (int t = 0; t < D_[l]; t++) {
            const uint64_t *m = M_ + off_[l] + (long)t * W_;
            int any = 0;
            for (int w = 0; w < W_ && !any; w++) any = (pre[w] & m[w]) != 0;
            if (!any) return 0;
        }
        return 1;
    }
    if (l + 2 == n_ && COL) {                   /* last two agents: for each type t of agent l, every type of the last */
        uint64_t cur[W_], acc[8];               /* agent meets pre & row_t iff the union of COL over it is everything */
        for (int t = 0; t < D_[l]; t++) {
            const uint64_t *m = M_ + off_[l] + (long)t * W_;
            int any = 0, full = 0;
            for (int w = 0; w < W_; w++) { cur[w] = pre[w] & m[w]; if (cur[w]) any = 1; }
            if (!any) return 0;
            for (int w = 0; w < W_ && !full; w++) full = (cur[w] & F_[(l + 1) * W_ + w]) != 0;
            if (full) continue;
            for (int v = 0; v < WB; v++) acc[v] = 0;
            for (int w = 0; w < W_; w++)
                for (uint64_t b = cur[w]; b; b &= b - 1) {
                    const uint64_t *c = COL + (long)(64 * w + __builtin_ctzll(b)) * WB;
                    for (int v = 0; v < WB; v++) acc[v] |= c[v];
                }
            for (int v = 0; v < WB; v++) if (acc[v] != ALL[v]) return 0;
        }
        return 1;
    }
    int memo = l >= 1 && l <= n_ - 3;
    if (memo && listed(l, pre)) return 1;
    uint64_t *ch = CH[l]; int *pc = PC[l], *ix = IX[l], k = 0;
    for (int t = 0; t < D_[l]; t++) {           /* children: pre & row_t for every type t of agent l */
        const uint64_t *m = M_ + off_[l] + (long)t * W_;
        uint64_t *cur = ch + (long)t * W_;
        int any = 0;
        for (int w = 0; w < W_; w++) { cur[w] = pre[w] & m[w]; if (cur[w]) any = 1; }
        if (!any) return 0;
        int full = 0;                           /* an allocation safe for all later agents with every type */
        for (int w = 0; w < W_ && !full; w++) full = (cur[w] & F_[(l + 1) * W_ + w]) != 0;
        if (!full) { pc[t] = popc(cur); ix[k++] = t; }
    }
    for (int a = 1; a < k; a++) {               /* smallest sets first: they make the strongest memo entries */
        int v = ix[a], b = a - 1;
        while (b >= 0 && pc[ix[b]] > pc[v]) { ix[b + 1] = ix[b]; b--; }
        ix[b + 1] = v;
    }
    for (int a = 0; a < k; a++) if (!go(l + 1, ch + (long)ix[a] * W_)) return 0;
    if (memo && NDONE[l] < CAP) { for (int w = 0; w < W_; w++) DONE[l][(long)NDONE[l] * W_ + w] = pre[w]; DPC[l][NDONE[l]++] = popc(pre); }
    return 1;
}
int covered(int n, int W, const int *D, const long *off, const uint64_t *M, const uint64_t *F) {
    n_ = n; W_ = W; D_ = D; off_ = off; M_ = M; F_ = F;
    if (n > 16) return -1;
    int oom = 0;
    for (int l = 0; l < n; l++) {
        DONE[l] = malloc(sizeof(uint64_t) * CAP * W); NDONE[l] = 0; DPC[l] = malloc(sizeof(int) * CAP);
        CH[l] = malloc(sizeof(uint64_t) * (D[l] + 1) * W); PC[l] = malloc(sizeof(int) * (D[l] + 1)); IX[l] = malloc(sizeof(int) * (D[l] + 1));
        if (!DONE[l] || !DPC[l] || !CH[l] || !PC[l] || !IX[l]) oom = 1;
    }
    COL = 0;
    if (n >= 2 && D[n - 1] <= 512) {
        int L = n - 1; WB = (D[L] + 63) / 64;
        COL = calloc((size_t)64 * W * WB, sizeof(uint64_t));
        if (!COL) oom = 1;
        for (int v = 0; v < 8; v++) ALL[v] = 0;
        for (int t = 0; t < D[L] && COL; t++) {
            ALL[t / 64] |= (uint64_t)1 << (t % 64);
            for (int a = 0; a < 64 * W; a++)
                if (M[off[L] + (long)t * W + a / 64] >> (a % 64) & 1) COL[(long)a * WB + t / 64] |= (uint64_t)1 << (t % 64);
        }
    }
    uint64_t all[W]; for (int w = 0; w < W; w++) all[w] = ~(uint64_t)0;
    int r = oom ? -1 : go(0, all);
    free(COL); COL = 0;
    for (int l = 0; l < n; l++) { free(DONE[l]); free(DPC[l]); free(CH[l]); free(PC[l]); free(IX[l]); }
    return r;
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

def labeled_all(n, m):
    """Labeled n x m matrices, row sums in {3, 4}, no zero column, a row of sum d has <= d - 2 columns of sum 1;
    as a list P with P[k] = number of such matrices with exactly k rows of sum 4."""
    P = [0] * (n + 1)
    if n == 0: P[0] = int(m == 0); return P
    choices = [(d, p) for d in (3, 4) for p in range(d - 1)]
    for rows in itertools.product(choices, repeat=n):
        Ptot = sum(p for _, p in rows)
        if Ptot > m: continue
        ways = math.factorial(m) // (math.factorial(m - Ptot) * math.prod(math.factorial(p) for _, p in rows))
        need = tuple(sorted(d - p for d, p in rows if d - p > 0))
        P[sum(d == 4 for d, _ in rows)] += ways * fill(need, m - Ptot)
    return P

@lru_cache(maxsize=None)
def labeled_conn(n, m):
    """Connected ones (component of agent 1 peeled off), by number of rows of sum 4."""
    tot = labeled_all(n, m)
    for n1 in range(1, n + 1):
        for m1 in range(0, m + 1):
            if (n1, m1) == (n, m): continue
            c = labeled_conn(n1, m1)
            if not any(c): continue
            rest = labeled_all(n - n1, m - m1)
            f = math.comb(n - 1, n1 - 1) * math.comb(m, m1)
            for k1, a in enumerate(c):
                for k2, b in enumerate(rest):
                    if a and b: tot[k1 + k2] -= f * a * b
    return tot

def labeled_count(n, m, pure, n4=None):
    P = labeled_conn(n, m)
    if n4 is not None: return P[n4]
    return P[n] if pure else sum(P[1:])

def brute(n, m, pure, n4=None):
    degs = (4,) if pure else (3, 4)
    rows = [S for d in degs for S in itertools.combinations(range(m), d)]
    return sum(1 for sets in itertools.product(rows, repeat=n)
               if (pure or any(len(S) == 4 for S in sets)) and (n4 is None or sum(len(S) == 4 for S in sets) == n4)
               and is_core(n, m, [list(S) for S in sets], pure)[0])

def aut_size(G):
    same = lambda a, b: a['side'] == b['side']
    for v in G: G.nodes[v]['side'] = v[0]
    return sum(1 for _ in GraphMatcher(G, G, node_match=same).isomorphisms_iter())

def efx0_safe(i, vals, bundles):
    own = sum(vals.get(g, 0) for g in bundles[i])
    return all(own >= sum(vals.get(g, 0) for g in B) - vals.get(h, 0)
               for j, B in enumerate(bundles) if j != i for h in B)

def safe_all_types(Vi, An, i, n):
    """efx0_safe for every type at once: Vi[t, g] = agent i's value of good g under type t (0 off R_i), An[g] = owner.
    Row t is True iff v(X_i) >= v(X_j) - v(h) for every j != i and h in X_j, i.e. v(X_i) >= v(X_j) - min over h."""
    own = Vi[:, An == i].sum(axis=1)
    ok = np.ones(len(Vi), dtype=bool)
    for j in range(n):
        cols = An == j
        if j == i or not cols.any(): continue
        sub = Vi[:, cols]
        ok &= own >= sub.sum(axis=1) - sub.min(axis=1)
    return ok

def core_domains(sets, m, ties):
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
    return doms

def minimal_types(M, off, D, W):
    """One agent's types whose row (bits: allocations under which the type is safe; row t at M[off + t*W ...]) contains
    no other type's row; of equal rows only the lowest index. Every other type t has a kept u with row_u inside row_t,
    so a profile using t is covered whenever the same profile using u is: checking the kept types suffices."""
    rows = [sum(M[off + t * W + w] << (64 * w) for w in range(W)) for t in range(D)]
    return [t for t, r in enumerate(rows)
            if not any(u != t and q & ~r == 0 and (q != r or u < t) for u, q in enumerate(rows))]

LIB = None
def covered(task):
    """Is every profile of the core covered by one of its allocations (raw EFX₀)? Runs in a worker process."""
    global LIB
    if LIB is None: LIB = load_c()
    n, m, sets, A_list, ties = task
    doms = core_domains(sets, m, ties)
    K = len(A_list); W = max(1, (K + 63) // 64)
    off = [0]
    for D in doms: off.append(off[-1] + len(D) * W)
    M = (ctypes.c_uint64 * off[-1])()
    Mn = np.ctypeslib.as_array(M)                    # the same memory, as a numpy array
    V = [np.array([[vals.get(g, 0) for g in range(m)] for vals in D], dtype=np.int64) for D in doms]
    for a, A in enumerate(A_list):
        An = np.array(A)
        bundles = [[g for g in range(m) if A[g] == j] for j in range(n)] if a % 16 == 0 else None
        for i, D in enumerate(doms):
            ok = safe_all_types(V[i], An, i, n)
            if bundles is not None:                  # every 16th allocation: also the plain loop, must agree
                if any(bool(ok[t]) != efx0_safe(i, vals, bundles) for t, vals in enumerate(D)):
                    print(f"  MASK MISMATCH: sets={sets} allocation={A} agent={i}", flush=True); return False
            Mn[off[i] + np.flatnonzero(ok) * W + a // 64] |= np.uint64(1 << (a % 64))
    F = (ctypes.c_uint64 * ((n + 1) * W))()          # F[l]: allocations safe for agents l..n-1 with every type
    Fn = np.ctypeslib.as_array(F).reshape(n + 1, W)
    Fn[n] = ~np.uint64(0)
    for l in range(n - 1, -1, -1):
        Fn[l] = Fn[l + 1] & np.bitwise_and.reduce(Mn[off[l]:off[l + 1]].reshape(len(doms[l]), W), axis=0)
    return coverage(n, W, [len(D) for D in doms], off, M, F)

def coverage(n, W, sizes, off, M, F):
    """Given the rows (agent i's type t: words M[off[i] + t*W ...], a bit per allocation) and F (F[l*W ...]:
    allocations safe for agents l..n-1 with every type; F[n] all ones), is every profile covered? Cuts each agent to
    its minimal types, then runs the C loop. Also called directly by k4/frontier/test_check4_fast.py on random rows."""
    global LIB
    if LIB is None: LIB = load_c()
    keep = [minimal_types(M, off[i], sizes[i], W) for i in range(n)]
    off2 = [0]
    for kt in keep: off2.append(off2[-1] + len(kt) * W)
    M2 = (ctypes.c_uint64 * off2[-1])()
    for i, kt in enumerate(keep):
        for r, t in enumerate(kt):
            for w in range(W): M2[off2[i] + r * W + w] = M[off[i] + t * W + w]
    r = LIB.covered(n, W, (ctypes.c_int * n)(*[len(kt) for kt in keep]), (ctypes.c_long * n)(*off2[:n]), M2, F)
    if r < 0: print(f"  COVERAGE LOOP FAILED (n > 16 or out of memory): n={n}", flush=True)
    return r == 1

def well_formed(rec, n):
    """Format: m in 1..3n, exactly n agent lists of distinct goods in range(m), allocations of exactly m owners in
    range(n), nothing else of the wrong type."""
    m = rec.get('m')
    if not isinstance(m, int) or not 1 <= m <= 3 * n: return False
    if rec.get('n', n) != n: return False
    sets, allocs = rec.get('sets'), rec.get('allocs')
    if not isinstance(sets, list) or len(sets) != n: return False
    for S in sets:
        if not isinstance(S, list) or len(set(S)) != len(S): return False
        if not all(isinstance(g, int) and 0 <= g < m for g in S): return False
    if not isinstance(allocs, list): return False
    for A in allocs:
        if not isinstance(A, list) or len(A) != m: return False
        if not all(isinstance(j, int) and 0 <= j < n for j in A): return False
    return True

def big(A, n, s):
    return sum(A.count(j) > s for j in range(n))

def check_file(path, pool, expect=None):
    """Returns (ok, key, number of cores); key = (n, mode) with mode 'pure', the exact n4, or 'any'."""
    data = json.load(gzip.open(path, 'rt'))
    n, pure, cores, ties, n4 = data['n'], data['pure'], data['cores'], data.get('ties', False), data.get('n4')
    key = (n, 'pure' if pure else (str(n4) if n4 is not None else 'any'))
    ok, byM = True, {}
    for rec in cores:
        if not well_formed(rec, n):
            print(f"  MALFORMED record: m={rec.get('m')} sets={rec.get('sets')}"); ok = False; continue
        byM.setdefault(rec['m'], []).append(rec)
    nD2 = 0
    for m in range(1, 3 * n + 1):                      # every m, also those without listed cores
        recs = byM.get(m, [])
        graphs, orbit = [], 0
        for rec in recs:
            good, G = is_core(n, m, rec['sets'], pure)
            if n4 is not None and sum(len(S) == 4 for S in rec['sets']) != n4: good = False
            if not pure and n4 is None and not any(len(S) == 4 for S in rec['sets']): good = False
            if not good: print(f"  NOT A CORE: {rec['sets']}"); ok = False
            for v in G: G.nodes[v]['side'] = v[0]
            h = nx.weisfeiler_lehman_graph_hash(G, node_attr='side')
            for h2, G2 in graphs:
                if h == h2 and nx.is_isomorphic(G, G2, node_match=lambda a, b: a['side'] == b['side']):
                    print(f"  DUPLICATE: {rec['sets']}"); ok = False
            graphs.append((h, G))
            orbit += math.factorial(n) * math.factorial(m) // aut_size(G)
        lab = labeled_count(n, m, pure, n4)
        if orbit != lab: print(f"  n={n} m={m}: orbit sum {orbit} != labeled count {lab}"); ok = False
        if not recs: continue
        cov = pool.map(covered, [(n, m, r['sets'], r['allocs'], ties) for r in recs], chunksize=1)
        for r, cv in zip(recs, cov):
            if not cv: print(f"  NOT COVERED: {r['sets']}"); ok = False
            nonD2 = [A for A in r['allocs'] if big(A, n, 2) > 1]
            if nonD2: print(f"  NOT D2 (more than one bundle of > 2 goods): {r['sets']} {nonD2[0]}"); ok = False
            else: nD2 += 1
        print(f"  n={n} m={m}{' pure' if pure else ''}{'' if n4 is None else f' n4={n4}'}{' ties' if ties else ''}: "
              f"{len(recs)} cores, orbit sum {orbit} = labeled {lab}: {'yes' if orbit == lab else 'NO'}; "
              f"all profiles covered in {sum(cov)}/{len(recs)}", flush=True)
    if expect is not None and expect.get(key) != len(cores):
        print(f"  EXPECTED {expect.get(key)} cores for n={key[0]} {key[1]}, file has {len(cores)}"); ok = False
    print(f"  {path}: {'OK' if ok else 'FAILED'}; {len(cores)} cores; every allocation has at most one bundle of more "
          f"than 2 goods (D2) in {nD2}/{len(cores)}", flush=True)
    return ok, key, len(cores)

if __name__ == '__main__':
    if '--selftest' in sys.argv:
        for n, m, pure, n4 in [(1, 4, True, None), (2, 4, True, None), (2, 5, True, None), (2, 6, True, None),
                               (2, 4, False, None), (2, 5, False, None), (2, 6, False, None), (3, 4, True, None),
                               (3, 5, True, None), (3, 5, False, None), (3, 6, True, None), (3, 5, False, 1),
                               (3, 5, False, 2), (3, 6, False, 1), (3, 6, False, 2)]:
            a, b = labeled_count(n, m, pure, n4), brute(n, m, pure, n4)
            print(f"n={n} m={m} {'pure' if pure else 'mixed'}{'' if n4 is None else f' n4={n4}'}: DP {a}, brute force {b}:"
                  f" {'ok' if a == b else 'MISMATCH'}", flush=True)
        print("types (strict balanced, balanced):", {d: (len(strict_balanced_types(d)), len(strict_balanced_types(d, True))) for d in (3, 4)})
        sys.exit(0)
    from multiprocessing import Pool
    print("command: python3 k4/check4_fast.py " + ' '.join(sys.argv[1:]), flush=True)
    import hashlib
    print("checker sha256: " + hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest(), flush=True)
    files, expect, jobs, i = [], None, os.cpu_count(), 1
    while i < len(sys.argv):
        a = sys.argv[i]
        if a == '--expect':
            expect = {}
            while i + 1 < len(sys.argv) and not sys.argv[i + 1].startswith('--') and ':' in sys.argv[i + 1]:
                nn, mode, cnt = sys.argv[i + 1].split(':'); expect[(int(nn), mode)] = int(cnt); i += 1
        elif a.startswith('--jobs='): jobs = int(a.split('=')[1])
        else: files.append(a)
        i += 1
    with Pool(jobs) as pool:
        res = [check_file(p, pool, expect) for p in files]
    ok = all(r[0] for r in res)
    if expect is not None:
        seen = {r[1] for r in res}
        for k in expect:
            if k not in seen: print(f"  EXPECTED a file for n={k[0]} {k[1]}, none given"); ok = False
    print("ALL OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)
