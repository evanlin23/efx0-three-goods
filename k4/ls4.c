/* ls4.c: two-phase local search for k = 4 cores (workstream proof/k4-localsearch).
 *
 * Phase 1 keeps a junk-free partial EFX0 allocation Y (every allocated good valued by its holder) and applies
 * Pareto moves; Phase 2 places the unallocated goods U.  Values: the algorithm decides with V = 32 v + w, where v is
 * the (possibly tied) integer type and w_i(g) = 2^(index of g in R_i); V refines v, is strict, and EFX0 under V
 * implies EFX0 under v (integer argument, see local_search4.md).  Every output is checked against the RAW EFX0
 * definition with v.
 *
 * Input (stdin), one task per block:
 *   n m
 *   d_i g_1 .. g_d            (n lines, the core)
 *   T_i                       (n blocks: number of types, then T_i lines of d_i integers = v on g_1..g_d)
 *   ... types
 *   MODE K SEED               MODE 0: all profiles (product); 1: K random profiles
 * Options (argv): -p PHASE2 (see phase2()), -x (allow cyclic exchanges), -v (verbose failures), -r policy.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>

#define MAXN 8
#define MAXM 32
#define MAXT 1400
typedef uint32_t mask;

static int n, m, d[MAXN], rg[MAXN][4];
static mask R[MAXN];
static int T[MAXN];
static int types[MAXN][MAXT][4];
static long V[MAXN][MAXM];          /* algorithm values (strict) */
static long RV[MAXN][MAXM];         /* raw values */
static int useG = 0, useX = 0, verbose = 0, policy = 0, p2mode = 0;

static unsigned long long rng_s = 88172645463325252ULL;
static unsigned long long rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

static inline long vs(long (*W)[MAXM], int i, mask S) {
    long s = 0; S &= R[i];
    while (S) { int g = __builtin_ctz(S); s += W[i][g]; S &= S - 1; }
    return s;
}
/* threat of nonempty bundle B to agent i: v(B) if B has a good outside R_i (as v(B cap R)), else v(B) - min */
static inline long threat(long (*W)[MAXM], int i, mask B) {
    if (!B) return LONG_MIN;
    if (B & ~R[i]) return vs(W, i, B);
    long s = 0, mn = LONG_MAX;
    while (B) { int g = __builtin_ctz(B); s += W[i][g]; if (W[i][g] < mn) mn = W[i][g]; B &= B - 1; }
    return s - mn;
}
static int efx0(long (*W)[MAXM], const mask *X) {
    for (int i = 0; i < n; i++) {
        long own = vs(W, i, X[i]);
        for (int j = 0; j < n; j++) if (j != i && X[j] && threat(W, i, X[j]) > own) return 0;
    }
    return 1;
}
/* raw definition, literally: v_i(X_i) >= v_i(X_j) - v_i(h) for all j != i, h in X_j */
static int efx0_raw(const mask *X) {
    for (int i = 0; i < n; i++) {
        long own = 0; for (int g = 0; g < m; g++) if (X[i] >> g & 1) own += (R[i] >> g & 1) ? RV[i][g] : 0;
        for (int j = 0; j < n; j++) if (j != i) {
            long tot = 0; for (int g = 0; g < m; g++) if (X[j] >> g & 1) tot += (R[i] >> g & 1) ? RV[i][g] : 0;
            for (int h = 0; h < m; h++) if (X[j] >> h & 1) {
                long vh = (R[i] >> h & 1) ? RV[i][h] : 0;
                if (own < tot - vh) return 0;
            }
        }
    }
    return 1;
}
static int level(int i, mask S) {   /* rank of V_i(S cap R_i) among subset sums of R_i */
    long v = vs(V, i, S); int r = 0;
    for (int z = 0; z < (1 << d[i]); z++) { long s = 0; for (int t = 0; t < d[i]; t++) if (z >> t & 1) s += V[i][rg[i][t]]; if (s < v) r++; }
    return r;
}
static mask loc2glob(int i, int z) { mask S = 0; for (int t = 0; t < d[i]; t++) if (z >> t & 1) S |= 1u << rg[i][t]; return S; }

/* ---------------- state ---------------- */
static mask Y[MAXN], U, ALL;
static long stat_moves[8], stat_steps_max, stat_runs, stat_fail, stat_p2[8], stat_big[8];

static int envies(int i, int j) { return Y[j] && vs(V, i, Y[j]) > vs(V, i, Y[i]); }

/* apply exchange: movers ag[0..L-1] get Z[0..L-1] (drawn from movers' old bundles and U); check EFX0 under V */
static int try_exchange(int L, const int *ag, const mask *Z, int apply) {
    mask NY[MAXN]; memcpy(NY, Y, sizeof NY);
    for (int t = 0; t < L; t++) NY[ag[t]] = 0;
    for (int t = 0; t < L; t++) NY[ag[t]] = Z[t];
    /* only new bundles and movers' values changed: check threats of new bundles to everyone, and movers vs all */
    if (!efx0(V, NY)) return 0;
    if (apply) { mask alloc = 0; memcpy(Y, NY, sizeof NY); for (int i = 0; i < n; i++) alloc |= Y[i]; U = ALL & ~alloc; }
    return 1;
}

/* M1: single-agent rebundle Z subset R_h cap (Y_h cup U), V(Z) > V(Y_h). policy 0: first found (agent order, subset
 * order by decreasing value); returns 1 if applied */
static int move_M1(void) {
    for (int h = 0; h < n; h++) {
        long cur = vs(V, h, Y[h]);
        mask avail = (Y[h] | U) & R[h];
        int best = -1; long bv = LONG_MAX;
        for (int z = 1; z < (1 << d[h]); z++) {
            mask Z = loc2glob(h, z);
            if (Z & ~avail) continue;
            long v = vs(V, h, Z);
            if (v <= cur) continue;
            if (!try_exchange(1, &h, &Z, 0)) continue;
            /* policy 0: smallest improving value; policy 1: largest */
            if (policy == 0 ? v < bv : (best < 0 || v > bv)) { best = z; bv = v; }
        }
        if (best >= 0) { mask Z = loc2glob(h, best); try_exchange(1, &h, &Z, 1); stat_moves[0]++; return 1; }
    }
    return 0;
}
/* R: rotation along an envy cycle */
static int move_R(void) {
    int E[MAXN][MAXN];
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) E[i][j] = i != j && envies(i, j);
    for (int s = 0; s < n; s++) {       /* DFS for a cycle through s */
        int path[MAXN], on[MAXN] = {0}, it[MAXN], L = 1; path[0] = s; on[s] = 1; it[0] = 0;
        while (L > 0) {
            int u = path[L - 1];
            if (it[L - 1] >= n) { on[u] = 0; L--; continue; }
            int w = it[L - 1]++;
            if (!E[u][w]) continue;
            if (w == s) {
                int ag[MAXN]; mask Z[MAXN];
                for (int t = 0; t < L; t++) { ag[t] = path[t]; Z[t] = Y[path[(t + 1) % L]]; }
                if (!try_exchange(L, ag, Z, 1)) { fprintf(stderr, "rotation invalid?!\n"); exit(3); }
                stat_moves[1]++; return 1;
            }
            if (!on[w] && w > s) { path[L] = w; on[w] = 1; it[L] = 0; L++; }
        }
    }
    return 0;
}
/* X: general cyclic exchange with the pool: distinct agents i_0..i_{L-1}, L >= 2, Z_t subset R cap (Y_{i_{t+1}} cup U),
 * disjoint, V(Z_t) > V(Y_{i_t}); first valid found. */
static int cyc[MAXN], cycL; static mask cz[MAXN];
static int dfs_X(int t, mask usedU) {
    int h = cyc[t], nx = cyc[(t + 1) % cycL];
    long cur = vs(V, h, Y[h]);
    mask avail = (Y[nx] | (U & ~usedU)) & R[h];
    for (int z = 1; z < (1 << d[h]); z++) {
        mask Z = loc2glob(h, z);
        if ((Z & ~avail) || vs(V, h, Z) <= cur) continue;
        if (!(Z & Y[nx])) continue;            /* must take something from the successor */
        cz[t] = Z;
        if (t + 1 == cycL) { if (try_exchange(cycL, cyc, cz, 0)) return 1; }
        else if (dfs_X(t + 1, usedU | (Z & U))) return 1;
    }
    return 0;
}
static int perm_next(int *a, int k) { /* next permutation of a[1..k-1] */
    int i = k - 2; while (i >= 1 && a[i] >= a[i + 1]) i--; if (i < 1) return 0;
    int j = k - 1; while (a[j] <= a[i]) j--; int x = a[i]; a[i] = a[j]; a[j] = x;
    for (int l = i + 1, r = k - 1; l < r; l++, r--) { x = a[l]; a[l] = a[r]; a[r] = x; }
    return 1;
}
static int move_X(void) {
    for (cycL = 2; cycL <= n; cycL++) {
        for (unsigned S = 0; S < (1u << n); S++) {
            if (__builtin_popcount(S) != cycL) continue;
            int k = 0; for (int i = 0; i < n; i++) if (S >> i & 1) cyc[k++] = i;
            do { if (dfs_X(0, 0)) { try_exchange(cycL, cyc, cz, 1); stat_moves[2]++; return 1; } } while (perm_next(cyc, cycL));
        }
    }
    return 0;
}


/* G: general coalition move: agents of a set A (|A| >= 2) re-divide the goods of their bundles and U; each takes a set
 * of its own goods worth strictly more than before; first valid found (A in increasing order of size). */
static int coA[MAXN], coL; static mask coZ[MAXN];
static int dfs_G(int t, mask avail) {
    if (t == coL) return try_exchange(coL, coA, coZ, 0);
    int h = coA[t]; long cur = vs(V, h, Y[h]);
    for (int z = 1; z < (1 << d[h]); z++) {
        mask Z = loc2glob(h, z);
        if ((Z & ~avail) || vs(V, h, Z) <= cur) continue;
        coZ[t] = Z;
        if (dfs_G(t + 1, avail & ~Z)) return 1;
    }
    return 0;
}
static int move_G(void) {
    for (coL = 2; coL <= n; coL++)
        for (unsigned S = 0; S < (1u << n); S++) {
            if (__builtin_popcount(S) != coL) continue;
            int k = 0; mask pool = U; for (int i = 0; i < n; i++) if (S >> i & 1) { coA[k++] = i; pool |= Y[i]; }
            if (dfs_G(0, pool)) { try_exchange(coL, coA, coZ, 1); stat_moves[3]++; return 1; }
        }
    return 0;
}

/* Phase 2 exact search: place every good of U; mode 0: only at sources not valuing it (junk); 1: anywhere */
static int P2ok; static mask P2X[MAXN]; static int ug[MAXM], nu;
static int src[MAXN];
static int p2dfs(int k, mask *X, int anywhere) {
    if (k == nu) { if (efx0(V, X) && efx0_raw(X)) { memcpy(P2X, X, sizeof P2X); return 1; } return 0; }
    int g = ug[k];
    for (int r = 0; r < n; r++) {
        if (!anywhere && (!src[r] || (R[r] >> g & 1))) continue;
        X[r] |= 1u << g;
        if (p2dfs(k + 1, X, anywhere)) return 1;
        X[r] &= ~(1u << g);
    }
    return 0;
}
static int phase2_exact(int anywhere) {
    mask X[MAXN]; memcpy(X, Y, sizeof X);
    for (int j = 0; j < n; j++) { src[j] = 1; for (int i = 0; i < n; i++) if (i != j && envies(i, j)) src[j] = 0; }
    nu = 0; for (int g = 0; g < m; g++) if (U >> g & 1) ug[nu++] = g;
    return p2dfs(0, X, anywhere);
}

static void print_state(const char *tag) {
    printf("%s Y:", tag);
    for (int i = 0; i < n; i++) { printf(" {"); int f = 1; for (int g = 0; g < m; g++) if (Y[i] >> g & 1) { printf(f ? "%d" : ",%d", g); f = 0; } printf("}"); }
    printf(" U:{"); int f = 1; for (int g = 0; g < m; g++) if (U >> g & 1) { printf(f ? "%d" : ",%d", g); f = 0; } printf("}\n");
}
static void print_profile(void) {
    printf("  sets/values:");
    for (int i = 0; i < n; i++) { printf(" ["); for (int t = 0; t < d[i]; t++) printf(t ? " %d:%ld" : "%d:%ld", rg[i][t], RV[i][rg[i][t]]); printf("]"); }
    printf("\n");
}

static int run(void) {
    for (int i = 0; i < n; i++) Y[i] = 0;
    U = ALL;
    int steps = 0;
    for (;;) {
        if (move_M1() || move_R()) { steps++; continue; }
        if (!U) break;
        if (useX && move_X()) { steps++; continue; }
        if (useG && move_G()) { steps++; continue; }
        break;
    }
    if (steps > stat_steps_max) stat_steps_max = steps;
    if (!efx0(V, Y)) { printf("PHASE1 NOT EFX0\n"); exit(4); }
    if (!U) { stat_p2[0]++; if (!efx0_raw(Y)) { printf("RAW FAIL complete\n"); exit(4); } return 1; }
    if (phase2_exact(0)) { stat_p2[1]++;
        int big = 0; for (int i = 0; i < n; i++) if (__builtin_popcount(P2X[i]) > 2) big++;
        stat_big[big > 3 ? 3 : big]++;
        return 1; }
    if (phase2_exact(1)) { stat_p2[2]++; if (verbose) { print_profile(); print_state("  NEEDS-VALUED-PLACEMENT"); } return 1; }
    stat_fail++;
    if (verbose && stat_fail <= 20) { print_profile(); print_state("  FAIL"); }
    return 0;
}

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-x")) useX = 1;
        else if (!strcmp(argv[a], "-g")) useG = 1;
        else if (!strcmp(argv[a], "-v")) verbose = 1;
        else if (!strcmp(argv[a], "-r")) policy = atoi(argv[++a]);
        else if (!strcmp(argv[a], "-p")) p2mode = atoi(argv[++a]);
    }
    while (scanf("%d %d", &n, &m) == 2) {
        ALL = (m == 32) ? 0xffffffffu : ((1u << m) - 1);
        for (int i = 0; i < n; i++) { if (scanf("%d", &d[i]) != 1) return 1; R[i] = 0; for (int t = 0; t < d[i]; t++) { if (scanf("%d", &rg[i][t]) != 1) return 1; R[i] |= 1u << rg[i][t]; } }
        for (int i = 0; i < n; i++) { if (scanf("%d", &T[i]) != 1) return 1; for (int t = 0; t < T[i]; t++) for (int q = 0; q < d[i]; q++) if (scanf("%d", &types[i][t][q]) != 1) return 1; }
        int mode; long K; unsigned long long seed;
        if (scanf("%d %ld %llu", &mode, &K, &seed) != 3) return 1;
        rng_s = seed * 2654435761ULL + 12345;
        memset(stat_moves, 0, sizeof stat_moves); memset(stat_p2, 0, sizeof stat_p2); memset(stat_big, 0, sizeof stat_big);
        stat_steps_max = 0; stat_runs = 0; stat_fail = 0;
        int idx[MAXN] = {0};
        for (long r = 0;; r++) {
            if (mode == 1) { if (r >= K) break; for (int i = 0; i < n; i++) idx[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) for (int t = 0; t < d[i]; t++) { int g = rg[i][t]; RV[i][g] = types[i][idx[i]][t]; V[i][g] = 32L * RV[i][g] + (1L << t); }
            run(); stat_runs++;
            if (mode == 0) { int i = 0; while (i < n && ++idx[i] == T[i]) { idx[i] = 0; i++; } if (i == n) break; }
        }
        printf("RESULT runs=%ld fail=%ld complete=%ld p2src=%ld p2any=%ld big0=%ld big1=%ld big2=%ld big3+=%ld M1=%ld R=%ld X=%ld G=%ld maxsteps=%ld\n",
               stat_runs, stat_fail, stat_p2[0], stat_p2[1], stat_p2[2], stat_big[0], stat_big[1], stat_big[2], stat_big[3],
               stat_moves[0], stat_moves[1], stat_moves[2], stat_moves[3], stat_steps_max);
        fflush(stdout);
    }
    return 0;
}
