/* ls4alg.c: Algorithm LS4 (k4/local_search4.md) for k = 4 cores, run exhaustively or on samples.
 *
 * Phase 1 keeps a junk-free partial EFX0 allocation Y and applies, first applicable first:
 *   M1  one agent h replaces Y_h by Z subset R_h cap (Y_h cup U) with V_h(Z) > V_h(Y_h), result EFX0
 *       (among h's options: the least valuable improving Z; agents in index order);
 *   R   rotation of an envy cycle;
 *   then, if U is empty or Phase 2 can place U, Phase 1 stops; otherwise
 *   X   an exchange cycle: distinct agents i_0..i_{L-1} (L >= 2), each i_t takes Z_t subset R cap (Y_{i_t} cup
 *       Y_{i_{t+1}} cup U) meeting Y_{i_{t+1}}, pairwise disjoint, V(Z_t) > V(Y_{i_t}), and threat-free for every
 *       other agent w.r.t. the OLD values (theta_x(Z_t) <= V_x(Y_x)).
 * Phase 2 (U nonempty): (a) an empty bundle takes all of U; (b) a source whose bundle plus U is threat-free takes
 *   all of U; (c) DM: a source s* takes J subset U with Y_s* cup J threat-free and every other good of U goes alone
 *   to a distinct other source s with Y_s cup {u} threat-free; (d) otherwise: exact search (reported, never used).
 * The algorithm sees only V = 32 v + w (w_i(g) = 2^(position of g in R_i)), a strict type refining v; it only
 * compares subset sums, so its run depends only on the strict type of V.
 * Checks: after every step Y is junk-free and EFX0 and the level sum rose; the output is complete and EFX0 by the RAW
 * definition for the representative values AND for every tied type whose perturbation has the same strict type
 * (the preimage lists below), so one run covers all tied profiles mapping to that strict profile.
 *
 * Input (stdin), one task per block:
 *   n m
 *   d_i g_1 .. g_d                         (n lines)
 *   per agent: T_i, then T_i blocks: "P  v_1 .. v_d" (representative) followed by P preimage lines "v_1 .. v_d"
 *   MODE K SEED                            MODE 0: all profiles; 1: K random profiles
 * Compile with -DCMOVE=k to add, when stuck, the coalition re-divisions C_2..C_k of LS4+ (level sum must rise).
 * Compile with -DEARLY to stop as soon as Phase 2 (b) or (c) applies (before any further move).
 * Compile with -DALT for another choice rule (most valuable M1 set, rotating agent order, longest cycles first).
 * Output: one RESULT line per task; FAIL lines on any failure (and exit status 1 at the end).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>

#define MAXN 8
#define MAXM 32
#define MAXT 300
#define MAXP 64
typedef uint32_t mask;

static int n, m, d[MAXN], rg[MAXN][4], T[MAXN];
static mask R[MAXN], ALL;
static int rep[MAXN][MAXT][4], np_[MAXN][MAXT], pre[MAXN][MAXT][MAXP][4];
static long V[MAXN][MAXM];
static mask Y[MAXN], U;
static long cnt_run, cnt_fail, cnt_move[4], cnt_p2[5], cnt_steps_max, cnt_big[4], cnt_L[MAXN + 1], cnt_levels_max;
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static inline long vs(int i, mask S) { long s = 0; S &= R[i]; while (S) { s += V[i][__builtin_ctz(S)]; S &= S - 1; } return s; }
static inline long threat(int i, mask B) {             /* max over g in B of V_i(B \ g); B nonempty */
    if (B & ~R[i]) return vs(i, B);
    long s = 0, mn = LONG_MAX; while (B) { long x = V[i][__builtin_ctz(B)]; s += x; if (x < mn) mn = x; B &= B - 1; }
    return s - mn;
}
static int efx0(const mask *X) {
    for (int i = 0; i < n; i++) { long own = vs(i, X[i]);
        for (int j = 0; j < n; j++) if (j != i && X[j] && threat(i, X[j]) > own) return 0; }
    return 1;
}
static int envies(int i, int j) { return i != j && Y[j] && vs(i, Y[j]) > vs(i, Y[i]); }
static int is_src(int s) { for (int i = 0; i < n; i++) if (envies(i, s)) return 0; return 1; }
static int level_sum(void) {
    int L = 0;
    for (int i = 0; i < n; i++) { long v = vs(i, Y[i]);
        for (int z = 0; z < (1 << d[i]); z++) { long s = 0; for (int t = 0; t < d[i]; t++) if (z >> t & 1) s += V[i][rg[i][t]]; if (s < v) L++; } }
    return L;
}
static mask loc(int i, int z) { mask S = 0; for (int t = 0; t < d[i]; t++) if (z >> t & 1) S |= 1u << rg[i][t]; return S; }
static void apply(int L, const int *ag, const mask *Z) {
    for (int t = 0; t < L; t++) Y[ag[t]] = 0;
    for (int t = 0; t < L; t++) Y[ag[t]] = Z[t];
    mask a = 0; for (int i = 0; i < n; i++) a |= Y[i]; U = ALL & ~a;
}

/* M1 */
static int rot;                           /* ALT: agents scanned from a rotating start */
static int move_M1(void) {
    for (int hh = 0; hh < n; hh++) {
#ifdef ALT
        int h = (hh + rot) % n;
        long cur = vs(h, Y[h]), bv = LONG_MIN; mask best = 0, avail = (Y[h] | U) & R[h];
        for (int z = 1; z < (1 << d[h]); z++) {
            mask Z = loc(h, z); long v;
            if ((Z & ~avail) || (v = vs(h, Z)) <= cur || v <= bv) continue;   /* ALT: most valuable improving Z */
#else
        int h = hh;
        long cur = vs(h, Y[h]), bv = LONG_MAX; mask best = 0, avail = (Y[h] | U) & R[h];
        for (int z = 1; z < (1 << d[h]); z++) {
            mask Z = loc(h, z); long v;
            if ((Z & ~avail) || (v = vs(h, Z)) <= cur || v >= bv) continue;
#endif
            int ok = 1;
            for (int x = 0; x < n && ok; x++) if (x != h && threat(x, Z) > vs(x, Y[x])) ok = 0;
            if (ok) { bv = v; best = Z; }
        }
        if (best) { apply(1, &h, &best); cnt_move[0]++; return 1; }
    }
    return 0;
}
/* R */
static int move_R(void) {
    for (int s = 0; s < n; s++) {
        int path[MAXN], on[MAXN] = {0}, it[MAXN], L = 1; path[0] = s; on[s] = 1; it[0] = 0;
        while (L > 0) {
            int u = path[L - 1];
            if (it[L - 1] >= n) { on[u] = 0; L--; continue; }
            int w = it[L - 1]++;
            if (!envies(u, w)) continue;
            if (w == s) { mask Z[MAXN]; for (int t = 0; t < L; t++) Z[t] = Y[path[(t + 1) % L]]; apply(L, path, Z); cnt_move[1]++; return 1; }
            if (!on[w] && w > s) { path[L] = w; on[w] = 1; it[L] = 0; L++; }
        }
    }
    return 0;
}
/* X */
static int cyc[MAXN], cL; static mask cz[MAXN];
static int dfs_X(int t, mask used) {
    int h = cyc[t], nx = cyc[(t + 1) % cL];
    long cur = vs(h, Y[h]);
    mask avail = (Y[h] | Y[nx] | U) & ~used & R[h];
    for (int z = 1; z < (1 << d[h]); z++) {
        mask Z = loc(h, z);
        if ((Z & ~avail) || !(Z & Y[nx]) || vs(h, Z) <= cur) continue;
        int ok = 1;
        for (int x = 0; x < n && ok; x++) if (x != h && threat(x, Z) > vs(x, Y[x])) ok = 0;
        if (!ok) continue;
        cz[t] = Z;
        if (t + 1 == cL) return 1;                  /* used holds every earlier Z, so the Z_t are disjoint */
        else if (dfs_X(t + 1, used | Z)) return 1;
    }
    return 0;
}
static int perm_next(int *a, int k) {
    int i = k - 2; while (i >= 1 && a[i] >= a[i + 1]) i--; if (i < 1) return 0;
    int j = k - 1; while (a[j] <= a[i]) j--; int x = a[i]; a[i] = a[j]; a[j] = x;
    for (int l = i + 1, r = k - 1; l < r; l++, r--) { x = a[l]; a[l] = a[r]; a[r] = x; }
    return 1;
}
static int move_X(void) {
#ifdef ALT
    for (cL = n; cL >= 2; cL--)                 /* ALT: longest cycles first */
#else
    for (cL = 2; cL <= n; cL++)
#endif
        for (unsigned S = 0; S < (1u << n); S++) {
            if (__builtin_popcount(S) != cL) continue;
            int k = 0; for (int i = 0; i < n; i++) if (S >> i & 1) cyc[k++] = i;
            do {
                if (dfs_X(0, 0)) {
                    mask all = 0; for (int t = 0; t < cL; t++) { if (all & cz[t]) { puts("FAIL X overlap"); exit(2); } all |= cz[t]; }
                    apply(cL, cyc, cz); cnt_move[2]++; cnt_L[cL]++; return 1;
                }
            } while (perm_next(cyc, cL));
        }
    return 0;
}

/* C_k (LS4+, k4/ls4plus.md): a coalition of 2..CMOVE agents re-divides its bundles and the pool, each member taking
 * a set of its own goods; the result must be EFX0 (checked exactly) and raise the level sum (some members may lose). */
#ifdef CMOVE
static int lev_of(int i, mask S) { long v = vs(i, S); int r = 0;
    for (int z = 0; z < (1 << d[i]); z++) { long t = 0; for (int q = 0; q < d[i]; q++) if (z >> q & 1) t += V[i][rg[i][q]]; if (t < v) r++; } return r; }
static int coA[MAXN], coL, coOld; static mask coZ[MAXN];
static int dfs_C(int t, mask avail, int newsum) {
    if (t == coL) {
        if (newsum <= coOld) return 0;
        mask NY[MAXN]; memcpy(NY, Y, sizeof NY);
        for (int q = 0; q < coL; q++) NY[coA[q]] = coZ[q];
        return efx0(NY);
    }
    int h = coA[t];
    for (int z = 0; z < (1 << d[h]); z++) {             /* z = 0: the member ends with nothing */
        mask Z = loc(h, z); if (Z & ~avail) continue;
        coZ[t] = Z;
        if (dfs_C(t + 1, avail & ~Z, newsum + lev_of(h, Z))) return 1;
    }
    return 0;
}
static long cnt_C[MAXN + 1];
static int move_C(void) {
    for (coL = 2; coL <= CMOVE && coL <= n; coL++)
        for (unsigned S = 0; S < (1u << n); S++) {
            if (__builtin_popcount(S) != coL) continue;
            int k = 0; mask pool = U; coOld = 0;
            for (int i = 0; i < n; i++) if (S >> i & 1) { coA[k++] = i; pool |= Y[i]; coOld += lev_of(i, Y[i]); }
            if (dfs_C(0, pool, 0)) { apply(coL, coA, coZ); cnt_C[coL]++; return 1; }
        }
    return 0;
}
#endif

/* Phase 2 */
static mask P2[MAXN];
static int ok_at(int s, mask J) { mask B = Y[s] | J; for (int h = 0; h < n; h++) if (h != s && threat(h, B) > vs(h, Y[h])) return 0; return 1; }
static int solo_rec(int sstar, mask rest, int *used) {
    if (!rest) return 1;
    int u = __builtin_ctz(rest);
    for (int s = 0; s < n; s++) if (!used[s] && s != sstar && is_src(s) && !(R[s] >> u & 1) && ok_at(s, 1u << u)) {
        used[s] = 1; P2[s] = Y[s] | (1u << u);
        if (solo_rec(sstar, rest & (rest - 1), used)) return 1;
        used[s] = 0; P2[s] = Y[s];
    }
    return 0;
}
static int ex_rec(mask rest) {
    if (!rest) return efx0(P2);
    int u = __builtin_ctz(rest);
    for (int s = 0; s < n; s++) if (is_src(s) && !(R[s] >> u & 1)) {
        P2[s] |= 1u << u; if (ex_rec(rest & (rest - 1))) return 1; P2[s] &= ~(1u << u);
    }
    return 0;
}
static int restrict_bc;                   /* EARLY: only the directly checked cases (b), (c) */
static int phase2(void) {                 /* returns case index 1..4, 0 if no placement */
    memcpy(P2, Y, sizeof P2);
#ifdef BADDUMP                            /* sensitivity test: dump U at the first source without any check */
    for (int s = 0; s < n; s++) if (is_src(s) && Y[s]) { P2[s] |= U; return 2; }
#endif
    if (!restrict_bc) for (int e = 0; e < n; e++) if (!Y[e]) { P2[e] = U; return 1; }
    for (int s = 0; s < n; s++) if (is_src(s) && !(U & R[s]) && ok_at(s, U)) { P2[s] |= U; return 2; }
    for (int s = 0; s < n; s++) if (is_src(s)) {
        mask Uj = U & ~R[s];
        for (mask J = Uj;; J = (J - 1) & Uj) {
            if (ok_at(s, J)) { int used[MAXN] = {0}; memcpy(P2, Y, sizeof P2); P2[s] = Y[s] | J; if (solo_rec(s, U & ~J, used)) return 3; }
            if (!J) break;
        }
    }
    memcpy(P2, Y, sizeof P2);
    if (!restrict_bc && ex_rec(U)) return 4;
    return 0;
}

static int cur_idx[MAXN];
static void report(const char *what) {
    cnt_fail++;
    if (cnt_fail > 5) return;
    printf("FAIL %s: n=%d m=%d", what, n, m);
    for (int i = 0; i < n; i++) { printf(" ["); for (int t = 0; t < d[i]; t++) printf(t ? " %d:%d" : "%d:%d", rg[i][t], rep[i][cur_idx[i]][t]); printf("]"); }
    printf(" Y:"); for (int i = 0; i < n; i++) printf(" %x", Y[i]); printf(" U:%x\n", U);
}
/* raw EFX0 of X for agent i with integer values val (on rg[i]) */
static int raw_safe(int i, const int *val, const mask *X) {
    long w[MAXM] = {0}; for (int t = 0; t < d[i]; t++) w[rg[i][t]] = val[t];
    long own = 0; for (int g = 0; g < m; g++) if (X[i] >> g & 1) own += w[g];
    for (int j = 0; j < n; j++) if (j != i) {
        long tot = 0; for (int g = 0; g < m; g++) if (X[j] >> g & 1) tot += w[g];
        for (int h = 0; h < m; h++) if ((X[j] >> h & 1) && own < tot - w[h]) return 0;
    }
    return 1;
}

static void run(void) {
    for (int i = 0; i < n; i++) Y[i] = 0;
    U = ALL;
    int steps = 0, lev = level_sum(); rot = 0;
    restrict_bc = 0;
    for (;;) {
#ifdef EARLY                              /* stop as soon as (b) or (c) places the pool (both checked directly) */
        if (U) { restrict_bc = 1; if (phase2()) break; restrict_bc = 0; }
#endif
        int moved = move_M1() || move_R();
        if (!moved) {
            if (!U) break;
            if (phase2()) break;
#ifndef NOX
            moved = move_X();
#endif
#ifdef CMOVE
            if (!moved) moved = move_C();
#endif
            if (!moved) break;
        }
        steps++; rot++;
#ifdef TRACE
        printf("STEP"); for (int i = 0; i < n; i++) printf(" %x", Y[i]); printf("\n");
#endif
        mask a = 0; for (int i = 0; i < n; i++) { if (Y[i] & ~R[i]) report("junk"); a |= Y[i]; }
        if (!efx0(Y)) report("step not EFX0");
        int l2 = level_sum(); if (l2 <= lev) report("level sum did not rise"); lev = l2;
    }
    if (lev > cnt_levels_max) cnt_levels_max = lev;
    if (steps > cnt_steps_max) cnt_steps_max = steps;
    int c = 0;
    if (U) { c = phase2(); if (!c) { report("no placement"); return; } }
    else memcpy(P2, Y, sizeof P2);
    cnt_p2[c]++;
    mask a = 0; for (int i = 0; i < n; i++) { if (a & P2[i]) report("overlap"); a |= P2[i]; }
    if (a != ALL) report("incomplete");
    if (!efx0(P2)) report("output not EFX0 (V)");
    for (int i = 0; i < n; i++) {
        if (!raw_safe(i, rep[i][cur_idx[i]], P2)) report("output not EFX0 (raw, representative)");
        for (int p = 0; p < np_[i][cur_idx[i]]; p++) if (!raw_safe(i, pre[i][cur_idx[i]][p], P2)) report("output not EFX0 (raw, tied preimage)");
    }
    int big = 0; for (int i = 0; i < n; i++) if (__builtin_popcount(P2[i]) > 2) big++;
    cnt_big[big > 3 ? 3 : big]++;
}

#ifndef LS4_NO_MAIN
int main(void) {
    int anyfail = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        ALL = (1u << m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &d[i]) != 1) return 3; R[i] = 0;
            for (int t = 0; t < d[i]; t++) { if (scanf("%d", &rg[i][t]) != 1) return 3; R[i] |= 1u << rg[i][t]; } }
        for (int i = 0; i < n; i++) {
            if (scanf("%d", &T[i]) != 1 || T[i] > MAXT) return 3;
            for (int t = 0; t < T[i]; t++) {
                if (scanf("%d", &np_[i][t]) != 1 || np_[i][t] > MAXP) return 3;
                for (int q = 0; q < d[i]; q++) if (scanf("%d", &rep[i][t][q]) != 1) return 3;
                for (int p = 0; p < np_[i][t]; p++) for (int q = 0; q < d[i]; q++) if (scanf("%d", &pre[i][t][p][q]) != 1) return 3;
            }
        }
        int mode; long K; unsigned long long seed;
        if (scanf("%d %ld %llu", &mode, &K, &seed) != 3) return 3;
        rs = seed * 2654435761ULL + 12345;
        cnt_run = cnt_fail = cnt_steps_max = cnt_levels_max = 0;
        memset(cnt_move, 0, sizeof cnt_move); memset(cnt_p2, 0, sizeof cnt_p2); memset(cnt_big, 0, sizeof cnt_big); memset(cnt_L, 0, sizeof cnt_L);
        memset(cur_idx, 0, sizeof cur_idx);
        for (long r = 0;; r++) {
            if (mode == 1) { if (r >= K) break; for (int i = 0; i < n; i++) cur_idx[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) for (int t = 0; t < d[i]; t++) V[i][rg[i][t]] = 32L * rep[i][cur_idx[i]][t] + (1L << t);
            run(); cnt_run++;
            if (mode == 0) { int i = 0; while (i < n && ++cur_idx[i] == T[i]) { cur_idx[i] = 0; i++; } if (i == n) break; }
        }
        printf("RESULT runs=%ld fail=%ld complete=%ld empty=%ld dump=%ld dm=%ld exact=%ld M1=%ld R=%ld X=%ld "
               "L2=%ld L3=%ld L4=%ld L5=%ld maxsteps=%ld maxlevels=%ld big0=%ld big1=%ld big2=%ld big3+=%ld\n",
               cnt_run, cnt_fail, cnt_p2[0], cnt_p2[1], cnt_p2[2], cnt_p2[3], cnt_p2[4], cnt_move[0], cnt_move[1], cnt_move[2],
               cnt_L[2], cnt_L[3], cnt_L[4], cnt_L[5], cnt_steps_max, cnt_levels_max, cnt_big[0], cnt_big[1], cnt_big[2], cnt_big[3]);
        fflush(stdout);
        if (cnt_fail) anyfail = 1;
    }
    return anyfail;
}
#endif
