/* Two-phase local search for EFX0 in cores (workstream proof/local-search; proofs/local_search.md).
   Phase 1 keeps a JUNK-FREE partial allocation Y (every allocated good is held by an agent that values it) and
   applies Pareto moves; Phase 2 places the unallocated goods U as junk. This program checks, for every core read
   on stdin, every ranking profile and every junk-free partial allocation Y that is "stable":
     (s1) Y is EFX0 (ordinal rule, Lemma 1);  (s2) no agent envies a good of U;  (s3) the envy graph is acyclic;
     (s4) no "valued add": for u in U and an agent j valuing u, Y with u added to Y_j is not EFX0;
   that U can be placed as junk (each u to a bundle whose holder does not value u) so that the complete
   allocation is EFX0. Only bundles of sources can receive junk (Lemma in the notes); we search all such placements.
   Input: lines "n m g00 g01 g02 g10 ..." as for ls_check. Output per core, and "FAIL" records.
   Stability also requires (s5) no valued single-agent rebundle, (s6) no champion path, and with -x (s7) no augmented
   envy cycle (proofs/local_search.md, Phase 1 moves M1, M2, M3).
   Usage: ls_twophase [-x] [-l LIMIT] [-a] [-w] [-1] [-g|-G] [-c]
     -x  also require (s7);  -w  weak stability: (s1)-(s4) only;  -a  allow junk into any bundle, not only sources;
     -1  test the rule "all of U into one source";  -g  test "every u has a clean source";  -G  as -g but tolerate
     |U| = 1;  -c  test "|U| <= number of one-good sources" (these rules are dead ends, see attempts/). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 9
#define MAXM 18
static int n, m;
static int G[MAXN][3];
static int bitv[MAXN][MAXM];
static int ra[MAXN], rb[MAXN], rc[MAXN];
static const int IDX[8] = {0, 1, 2, 4, 3, 5, 6, 7};
static const int PERM[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static int val_by[MAXM][MAXN], nval[MAXM];   /* agents valuing good g (independent of the profile) */
static long long print_limit = 10, n_stable, n_fail, n_trivial;
static int use_s7 = 0, weak = 0;
static int any_bundle = 0, single_mode = 0, perg_mode = 0, count_mode = 0;

static inline int popc(unsigned x) { return __builtin_popcount(x); }
static inline int levm(int i, unsigned mask) {
    int b = ((mask >> ra[i] & 1) << 2) | ((mask >> rb[i] & 1) << 1) | (mask >> rc[i] & 1);
    return IDX[b];
}
static inline int ownbits(int i, unsigned mask) {
    return ((mask >> ra[i] & 1) << 2) | ((mask >> rb[i] & 1) << 1) | (mask >> rc[i] & 1);
}
/* safety of agent i given owner array o (-1 = unallocated) and bundle masks */
static int safe_i(const int *o, const unsigned *bm, int i) {
    int b = ownbits(i, bm[i]);
    if (popc(b) >= 2) return 1;
#define FREE(g) (o[g] < 0 || popc(bm[o[g]]) == 1)
    if (b == 4) { int x = o[rb[i]], y = o[rc[i]]; return !(x >= 0 && x == y && popc(bm[x]) >= 3); }
    if (b == 2) return FREE(ra[i]);
    if (b == 1) return FREE(ra[i]) && FREE(rb[i]);
    return FREE(ra[i]) && FREE(rb[i]) && FREE(rc[i]);
#undef FREE
}
static int efx0(const int *o) {
    unsigned bm[MAXN] = {0};
    for (int g = 0; g < m; g++) if (o[g] >= 0) bm[o[g]] |= 1u << g;
    for (int i = 0; i < n; i++) if (!safe_i(o, bm, i)) return 0;
    return 1;
}
static void set_rank(int i, int p) {
    for (int g = 0; g < m; g++) bitv[i][g] = 0;
    ra[i] = G[i][PERM[p][0]]; rb[i] = G[i][PERM[p][1]]; rc[i] = G[i][PERM[p][2]];
    bitv[i][ra[i]] = 4; bitv[i][rb[i]] = 2; bitv[i][rc[i]] = 1;
}
static void print_state(const int *o) {
    unsigned bm[MAXN] = {0}, pool = 0;
    for (int g = 0; g < m; g++) { if (o[g] < 0) pool |= 1u << g; else bm[o[g]] |= 1u << g; }
    printf("   rankings(a,b,c):");
    for (int i = 0; i < n; i++) printf(" (%d,%d,%d)", ra[i], rb[i], rc[i]);
    printf("\n   bundles:");
    for (int j = 0; j < n; j++) { printf(" {"); int f = 1;
        for (int g = 0; g < m; g++) if (bm[j] >> g & 1) { printf(f ? "%d" : ",%d", g); f = 0; }
        printf("}"); }
    printf("  unallocated {"); int f = 1;
    for (int g = 0; g < m; g++) if (pool >> g & 1) { printf(f ? "%d" : ",%d", g); f = 0; }
    printf("}\n");
}

/* phase 2: place the goods of U (list) into allowed bundles, junk only; DFS with full check at the leaf */
static int ulist[MAXM], nu, allowed[MAXN], nallowed;
static int place(int *o, int k) {
    if (k == nu) return efx0(o);
    int u = ulist[k];
    for (int q = 0; q < nallowed; q++) { int j = allowed[q];
        if (bitv[j][u]) continue;              /* junk only */
        o[u] = j;
        if (place(o, k + 1)) { o[u] = -1; return 1; }
        o[u] = -1; }
    return 0;
}


static int path[MAXN], plen;
static int try_path(const int *o, const unsigned *bm, unsigned pool) {
    int s = path[0], k = path[plen - 1];
    unsigned Rk = (1u << ra[k]) | (1u << rb[k]) | (1u << rc[k]);
    unsigned avail = (bm[s] | pool) & Rk;
    int Lk = levm(k, bm[k]);
    for (unsigned Z = avail; Z; Z = (Z - 1) & avail) {
        if (levm(k, Z) <= Lk) continue;
        int t[MAXM]; memcpy(t, o, sizeof t);
        for (int g = 0; g < m; g++) if (bm[s] >> g & 1) t[g] = -1;
        for (int q = 0; q + 1 < plen; q++) { int a = path[q], nx = path[q + 1];
            for (int g = 0; g < m; g++) if (bm[nx] >> g & 1) t[g] = bitv[a][g] ? a : -1; }
        for (int g = 0; g < m; g++) if (Z >> g & 1) t[g] = k;
        if (efx0(t)) return 1;
    }
    return 0;
}
static int dfs_path(const int *o, const unsigned *bm, unsigned pool, int adj[MAXN][MAXN], int used) {
    if (plen >= 2 && try_path(o, bm, pool)) return 1;
    int v = path[plen - 1];
    for (int w = 0; w < n; w++) if (adj[v][w] && !(used >> w & 1)) {
        path[plen++] = w; int f = dfs_path(o, bm, pool, adj, used | 1 << w); plen--; if (f) return 1; }
    return 0;
}
static int champion_paths(const int *o, const unsigned *bm, unsigned pool, int adj[MAXN][MAXN]) {
    for (int v = 0; v < n; v++) { path[0] = v; plen = 1; if (dfs_path(o, bm, pool, adj, 1 << v)) return 1; }
    return 0;
}


/* s7: junk-free augmented envy cycle i_0 -> ... -> i_{k-1} -> i_0 (k >= 2): i_t's new bundle Z_t is a set of its own
   goods taken from Y_{i_{t+1}} (at least one) and U, with v(Z_t) > v(Y_{i_t}); the Z_t are disjoint; the other goods
   of the cycle's bundles go to U. (A champion path is the case where all but one Z_t are whole bundles.) */
static int xcyc[MAXN], xlen; static unsigned xZ[MAXN];
static int try_X(const int *o, const unsigned *bm, unsigned pool, int t, unsigned used) {
    if (t == xlen) {
        int u[MAXM]; memcpy(u, o, sizeof u);
        for (int q = 0; q < xlen; q++) for (int g = 0; g < m; g++) if (bm[xcyc[q]] >> g & 1) u[g] = -1;
        for (int q = 0; q < xlen; q++) for (int g = 0; g < m; g++) if (xZ[q] >> g & 1) u[g] = xcyc[q];
        return efx0(u);
    }
    int i = xcyc[t], nx = xcyc[(t + 1) % xlen];
    unsigned Ri = (1u << ra[i]) | (1u << rb[i]) | (1u << rc[i]);
    unsigned avail = (bm[nx] | pool) & Ri & ~used;
    if (!(avail & bm[nx])) return 0;
    int L = levm(i, bm[i]);
    for (unsigned Z = avail; Z; Z = (Z - 1) & avail) {
        if (!(Z & bm[nx]) || levm(i, Z) <= L) continue;
        xZ[t] = Z;
        if (try_X(o, bm, pool, t + 1, used | Z)) return 1;
    }
    return 0;
}
static int dfs_X(const int *o, const unsigned *bm, unsigned pool, int used) {
    int v = xcyc[xlen - 1];
    for (int w = 0; w < n; w++) if (w != v) {
        if (w == xcyc[0] && xlen >= 2) { if (try_X(o, bm, pool, 0, 0)) return 1; }
        else if (w > xcyc[0] && !(used >> w & 1)) {
            xcyc[xlen++] = w; int f = dfs_X(o, bm, pool, used | 1 << w); xlen--; if (f) return 1; }
    }
    return 0;
}
static int aug_cycles(const int *o, const unsigned *bm, unsigned pool) {
    for (int v = 0; v < n; v++) { xcyc[0] = v; xlen = 1; if (dfs_X(o, bm, pool, 1 << v)) return 1; }
    return 0;
}

static void check_profile_state(int *o) {
    unsigned bm[MAXN] = {0}, pool = 0;
    for (int g = 0; g < m; g++) { if (o[g] < 0) pool |= 1u << g; else bm[o[g]] |= 1u << g; }
    /* s2: no envy of an unallocated good */
    for (int i = 0; i < n; i++) { int L = levm(i, bm[i]);
        for (int g = 0; g < m; g++) if ((pool >> g & 1) && bitv[i][g] && levm(i, 1u << g) > L) return; }
    /* s3: acyclic envy graph */
    int adj[MAXN][MAXN], indeg[MAXN] = {0};
    for (int i = 0; i < n; i++) { int L = levm(i, bm[i]);
        for (int j = 0; j < n; j++) { adj[i][j] = (i != j) && levm(i, bm[j]) > L; indeg[j] += adj[i][j]; } }
    { int deg[MAXN], q[MAXN], h = 0, t = 0, seen = 0; memcpy(deg, indeg, sizeof deg);
      for (int i = 0; i < n; i++) if (!deg[i]) q[t++] = i;
      while (h < t) { int v = q[h++]; seen++; for (int w = 0; w < n; w++) if (adj[v][w] && !--deg[w]) q[t++] = w; }
      if (seen < n) return; }
    /* s4: no valued add */
    for (int u = 0; u < m; u++) if (pool >> u & 1)
        for (int k = 0; k < nval[u]; k++) { int j = val_by[u][k];
            o[u] = j; int ok = efx0(o); o[u] = -1; if (ok) return; }
    /* s5: no valued single-agent rebundle: i's new bundle Y' within R_i and Y_i + U, level up, still EFX0 */
    if (!weak) for (int i = 0; i < n; i++) {
        unsigned avail = (bm[i] | pool) & ((1u << ra[i]) | (1u << rb[i]) | (1u << rc[i]));
        int L = levm(i, bm[i]);
        for (unsigned Y = avail; Y; Y = (Y - 1) & avail) {
            if (levm(i, Y) <= L) continue;
            int t[MAXM]; memcpy(t, o, sizeof t);
            for (int g = 0; g < m; g++) { if (bm[i] >> g & 1) t[g] = -1; if (Y >> g & 1) t[g] = i; }
            if (efx0(t)) return;
        }
    }
    /* s6: no champion path: s=t0 -> t1 -> ... -> tr=k (r >= 1) in the envy graph; t_q takes Y_{t_{q+1}} (its own
       goods of it; the rest goes to U), k takes Z within R_k and Y_s + U with level up; Y_s minus Z goes to U */
    if (!weak && champion_paths(o, bm, pool, adj)) return;
    if (use_s7 && aug_cycles(o, bm, pool)) return;
    n_stable++;
    nu = 0; for (int u = 0; u < m; u++) if (pool >> u & 1) ulist[nu++] = u;
    nallowed = 0; for (int j = 0; j < n; j++) if (any_bundle || !indeg[j]) allowed[nallowed++] = j;
    if (count_mode) {   /* hypothesis: |U| <= number of singleton sources (all bundles nonempty) */
        int ss = 0, empty = 0;
        for (int j = 0; j < n; j++) { if (!bm[j]) empty = 1; if (!indeg[j] && popc(bm[j]) == 1) ss++; }
        if (!empty && nu > ss) { n_fail++;
            if (n_fail <= print_limit) { printf("  |U|=%d > singleton sources=%d\n", nu, ss); print_state(o); } }
        return;
    }
    if (perg_mode) {   /* per-good rule: every u has a source s such that Y with u added to Y_s is EFX0 */
        for (int k = 0; k < nu; k++) { int u = ulist[k], okk = 0;
            for (int q = 0; q < nallowed && !okk; q++) { int j = allowed[q];
                /* conflict-free: no a-holder i != j with {b_i,c_i} = {u, y}, y in Y_j, when |Y_j| >= 1 and the
                   bundle may grow to >= 3 goods; tested as: Y_j + u + (a dummy extra good) keeps i safe */
                int conflict = 0;
                for (int i = 0; i < n; i++) if (i != j && ownbits(i, bm[i]) == 4) {
                    int y = (rb[i] == u) ? rc[i] : (rc[i] == u) ? rb[i] : -1;
                    if (y >= 0 && o[y] == j) conflict = 1; }
                if (!conflict) okk = 1; }
            if (!okk && nu == 1 && perg_mode == 2) continue;   /* -G: tolerate a lone unallocated good (exception) */
            if (!okk) { n_fail++;
                if (n_fail <= print_limit) { printf("  NO CONFLICT-FREE SOURCE for good %d\n", u); print_state(o); }
                return; } }
        return;
    }
    if (single_mode) {   /* rule: all of U into one source bundle */
        for (int q = 0; q < nallowed; q++) { int j = allowed[q];
            for (int k = 0; k < nu; k++) o[ulist[k]] = j;
            int ok = efx0(o);
            for (int k = 0; k < nu; k++) o[ulist[k]] = -1;
            if (ok) return; }
        n_fail++;
        if (n_fail <= print_limit) { printf("  FAIL (single source)\n"); print_state(o); fflush(stdout); }
        return;
    }
    if (place(o, 0)) return;
    n_fail++;
    if (n_fail <= print_limit) { printf("  FAIL (no junk placement)\n"); print_state(o); fflush(stdout); }
}

/* enumerate junk-free partial allocations: good g -> -1 or one of its valuers; states outer, profiles inner */
static int o_cur[MAXM];
static void profiles(int i) {
    if (i == n) {
        unsigned bm[MAXN] = {0};
        for (int g = 0; g < m; g++) if (o_cur[g] >= 0) bm[o_cur[g]] |= 1u << g;
        for (int a = 0; a < n; a++) if (!safe_i(o_cur, bm, a)) return;
        check_profile_state(o_cur); return;
    }
    for (int p = 0; p < 6; p++) {
        set_rank(i, p);
        /* prune: agent i must be safe (its safety depends only on its own ranking) */
        unsigned bm[MAXN] = {0};
        for (int g = 0; g < m; g++) if (o_cur[g] >= 0) bm[o_cur[g]] |= 1u << g;
        if (!safe_i(o_cur, bm, i)) continue;
        int L = levm(i, bm[i]), envies_pool = 0;      /* (s2) for agent i: depends only on its own ranking */
        for (int g = 0; g < 3; g++) { int x = G[i][g]; if (o_cur[x] < 0 && levm(i, 1u << x) > L) envies_pool = 1; }
        if (envies_pool) continue;
        profiles(i + 1);
    }
}
static void states(int g) {
    if (g == m) {
        int haspool = 0; for (int h = 0; h < m; h++) if (o_cur[h] < 0) haspool = 1;
        if (!haspool) { n_trivial++; return; }
        profiles(0); return;
    }
    o_cur[g] = -1; states(g + 1);
    for (int k = 0; k < nval[g]; k++) { o_cur[g] = val_by[g][k]; states(g + 1); }
    o_cur[g] = -1;
}

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-l") && a + 1 < argc) print_limit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "-a")) any_bundle = 1;
        else if (!strcmp(argv[a], "-1")) single_mode = 1;
        else if (!strcmp(argv[a], "-g")) perg_mode = 1;
        else if (!strcmp(argv[a], "-G")) perg_mode = 2;
        else if (!strcmp(argv[a], "-c")) count_mode = 1;
        else if (!strcmp(argv[a], "-x")) use_s7 = 1;
        else if (!strcmp(argv[a], "-w")) weak = 1;
    }
    int core_id = 0; long long total_fail = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        for (int i = 0; i < n; i++) for (int k = 0; k < 3; k++) if (scanf("%d", &G[i][k]) != 1) return 2;
        for (int g = 0; g < m; g++) nval[g] = 0;
        for (int i = 0; i < n; i++) for (int k = 0; k < 3; k++) { int g = G[i][k]; val_by[g][nval[g]++] = i; }
        long long s0 = n_stable, f0 = n_fail;
        states(0);
        printf("core %d n=%d m=%d goods", core_id, n, m);
        for (int i = 0; i < n; i++) printf(" (%d,%d,%d)", G[i][0], G[i][1], G[i][2]);
        printf(": stable %lld, fail %lld\n", n_stable - s0, n_fail - f0); fflush(stdout);
        total_fail += n_fail - f0; core_id++;
    }
    printf("TOTAL cores %d, stable junk-free states %lld, junk placement fails %lld\n", core_id, n_stable, n_fail);
    return total_fail ? 1 : 0;
}
