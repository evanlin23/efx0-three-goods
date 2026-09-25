/* gm4_explore.c: structure of the level-sum maxima of k = 4 cores (k4/gm4.md, conjecture GM4 of k4/ls4plus.md).
 *
 * For each strict profile (all, or K random ones), every junk-free partial allocation Y (each good in the pool or
 * with one of its valuers) is enumerated; the EFX0 ones (raw definition: v_i(Y_i) >= v_i(Y_j \ g) for all i != j,
 * g in Y_j) whose level sum  sum_i l_i(Y_i),  l_i(S) = #{T subset R_i : v_i(T) < v_i(S)},  is maximum are the
 * *maxima*.  For every maximum with a nonempty pool U it records:
 *   empty bundles; sources (agents nobody envies); at which sources the single dump works (s values no good of U and
 *   Y_s cup U is threat-free for s); whether some junk placement (every good of U to an agent not valuing it) gives
 *   an EFX0 allocation (exhaustive, raw definition).
 * The type representatives are strict: all nonempty subset sums of R_i are distinct (k4/check4.py strict domain).
 * Input (stdin), one task per block:
 *   n m
 *   d_i g_1 .. g_d            (n lines)
 *   per agent: T_i, then T_i lines "v_1 .. v_d" (values of g_1 .. g_d)
 *   MODE K SEED               MODE 0: all profiles; 1: K random profiles
 * Output: RESULT line per task; with -DOUT a line "M <values> | <Y masks> | U" per maximum with nonempty pool
 * (at most OUT per task), for k4/gm4_analyze.py.  Exit status 1 if a maximum without any placement is found. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#define MAXN 8
#define MAXM 20
#define MAXT 300
#define MAXS (1 << 21)
typedef uint32_t mask;
static int n, m, d[MAXN], rg[MAXN][4], T[MAXN], rep[MAXN][MAXT][4], cur[MAXN];
static mask R[MAXN], ALL;
static long v[MAXN][MAXM];
static unsigned long long rs;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static long val(int i, mask S) { long s = 0; S &= R[i]; while (S) { s += v[i][__builtin_ctz(S)]; S &= S - 1; } return s; }
static long thr(int i, mask B) {      /* max_{g in B} v_i(B \ g), B nonempty; min over ALL goods of B */
    long s = 0, mn = LONG_MAX;
    for (mask b = B; b; b &= b - 1) { int g = __builtin_ctz(b); long x = (R[i] >> g & 1) ? v[i][g] : 0; s += x; if (x < mn) mn = x; }
    return s - mn;
}
static int lev(int i, mask S) {       /* #{T subset R_i : v_i(T) < v_i(S)} */
    long x = val(i, S); int c = 0;
    for (int z = 0; z < (1 << d[i]); z++) { long s = 0; for (int t = 0; t < d[i]; t++) if (z >> t & 1) s += v[i][rg[i][t]]; if (s < x) c++; }
    return c;
}
static int efx0(const mask *X) {
    for (int i = 0; i < n; i++) { long o = val(i, X[i]);
        for (int j = 0; j < n; j++) if (j != i && X[j] && thr(i, X[j]) > o) return 0; }
    return 1;
}
static int gv[MAXM][MAXN + 1], ngv[MAXM];
static void decode(long c, mask *X) {
    for (int i = 0; i < n; i++) X[i] = 0;
    for (int g = 0; g < m; g++) { int k = c % ngv[g]; c /= ngv[g]; if (k) X[gv[g][k - 1]] |= 1u << g; }
}
/* some junk placement of U completes Y to an EFX0 allocation? */
static int place_rec(mask *X, mask U) {
    if (!U) return efx0(X);
    int g = __builtin_ctz(U);
    for (int j = 0; j < n; j++) if (!(R[j] >> g & 1)) { X[j] |= 1u << g; int ok = place_rec(X, U & (U - 1)); X[j] &= ~(1u << g); if (ok) return 1; }
    return 0;
}
static long cnt[32];
enum { C_MAX, C_POOL, C_EMPTY, C_DUMP_ANY, C_DUMP_ALL, C_PLACE, C_NOPLACE, C_SRC1, C_SRC2, C_SRC3, C_SRC4P, C_NODUMP_PLACE,
       C_ENVYFREE, C_ENVSRC, C_ENVSRC_FAIL, C_ISOSRC, C_ISOSRC_FAIL, C_NC };
int main(void) {
    static long list[MAXS]; int anyfail = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        ALL = (1u << m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &d[i]) != 1) return 3; R[i] = 0;
            for (int t = 0; t < d[i]; t++) { if (scanf("%d", &rg[i][t]) != 1) return 3; R[i] |= 1u << rg[i][t]; } }
        for (int i = 0; i < n; i++) { if (scanf("%d", &T[i]) != 1 || T[i] > MAXT) return 3;
            for (int t = 0; t < T[i]; t++) for (int q = 0; q < d[i]; q++) if (scanf("%d", &rep[i][t][q]) != 1) return 3; }
        int mode; long K; unsigned long long seed;
        if (scanf("%d %ld %llu", &mode, &K, &seed) != 3) return 3;
        rs = seed * 2654435761ULL + 88172645463325252ULL;
        long NS = 1;
        for (int g = 0; g < m; g++) { ngv[g] = 1; for (int i = 0; i < n; i++) if (R[i] >> g & 1) gv[g][ngv[g]++ - 1] = i; NS *= ngv[g]; }
        if (NS > MAXS) { printf("SKIP NS=%ld\n", NS); continue; }
        memset(cnt, 0, sizeof cnt); memset(cur, 0, sizeof cur); long runs = 0, out = 0;
        for (;;) {
            if (mode == 1) { if (runs >= K) break; for (int i = 0; i < n; i++) cur[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) { memset(v[i], 0, sizeof v[i]); for (int t = 0; t < d[i]; t++) v[i][rg[i][t]] = rep[i][cur[i]][t]; }
            int best = -1; long nl = 0;
            for (long c = 0; c < NS; c++) {
                mask X[MAXN]; decode(c, X); if (!efx0(X)) continue;
                int s = 0; for (int i = 0; i < n; i++) s += lev(i, X[i]);
                if (s > best) { best = s; nl = 0; }
                if (s == best) list[nl++] = c;
            }
            for (long q = 0; q < nl; q++) {
                mask Y[MAXN], a = 0; decode(list[q], Y); for (int i = 0; i < n; i++) a |= Y[i];
                mask U = ALL & ~a; cnt[C_MAX]++;
                if (!U) continue;
                cnt[C_POOL]++;
                int empty = 0; for (int i = 0; i < n; i++) if (!Y[i]) empty = 1;
                long sig[MAXN]; for (int i = 0; i < n; i++) sig[i] = val(i, Y[i]);
                int src[MAXN], ns = 0, nd = 0;
                int nedge = 0, envfail = 0;
                for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j && val(i, Y[j]) > sig[i]) nedge++;
                for (int s = 0; s < n; s++) { int ok = 1, outd = 0; for (int i = 0; i < n; i++) if (i != s && val(i, Y[s]) > sig[i]) ok = 0;
                    if (!ok) continue; src[ns++] = s;
                    for (int j = 0; j < n; j++) if (j != s && val(s, Y[j]) > sig[s]) outd++;
                    int dump = !(R[s] & U);
                    for (int x = 0; x < n && dump; x++) if (x != s && thr(x, Y[s] | U) > sig[x]) dump = 0;
                    nd += dump;
                    if (outd) { cnt[C_ENVSRC]++; if (!dump) { cnt[C_ENVSRC_FAIL]++; envfail = 1; } }
                    else { cnt[C_ISOSRC]++; if (!dump) cnt[C_ISOSRC_FAIL]++; } }
                if (!nedge) cnt[C_ENVYFREE]++;
                int pl = place_rec(Y, U);
                if (empty) cnt[C_EMPTY]++;
                cnt[ns == 1 ? C_SRC1 : ns == 2 ? C_SRC2 : ns == 3 ? C_SRC3 : C_SRC4P]++;
                if (nd) cnt[C_DUMP_ANY]++;
                if (nd == ns) cnt[C_DUMP_ALL]++;
                if (pl) cnt[C_PLACE]++; else { cnt[C_NOPLACE]++; anyfail = 1; }
                if (pl && !empty && !nd) cnt[C_NODUMP_PLACE]++;
#ifdef OUT
                if (out++ < OUT) { printf("M");
                    for (int i = 0; i < n; i++) { printf(" "); for (int t = 0; t < d[i]; t++) printf(t ? ",%d" : "%d", rep[i][cur[i]][t]); }
                    printf(" |"); for (int i = 0; i < n; i++) printf(" %u", Y[i]); printf(" | %u\n", U); }
#endif
                if (envfail || !nedge) { printf(envfail ? "H1FAIL" : "H0FAIL"); for (int i = 0; i < n; i++) { printf(" "); for (int t = 0; t < d[i]; t++) printf(t ? ",%d" : "%d", rep[i][cur[i]][t]); }
                    printf(" |"); for (int i = 0; i < n; i++) printf(" %u", Y[i]); printf(" | %u\n", U); }
                if (!pl) { printf("GMFAIL"); for (int i = 0; i < n; i++) { printf(" "); for (int t = 0; t < d[i]; t++) printf(t ? ",%d" : "%d", rep[i][cur[i]][t]); }
                    printf(" |"); for (int i = 0; i < n; i++) printf(" %u", Y[i]); printf(" | %u\n", U); }
            }
            runs++;
            if (mode == 0) { int i = 0; while (i < n && ++cur[i] == T[i]) { cur[i] = 0; i++; } if (i == n) break; }
        }
        (void)out;
        printf("RESULT runs=%ld maxima=%ld pool=%ld empty=%ld dump_any=%ld dump_all_src=%ld place=%ld noplace=%ld src1=%ld src2=%ld src3=%ld src4p=%ld nodump_place=%ld envyfree=%ld envsrc=%ld envsrc_fail=%ld isosrc=%ld isosrc_fail=%ld\n",
               runs, cnt[C_MAX], cnt[C_POOL], cnt[C_EMPTY], cnt[C_DUMP_ANY], cnt[C_DUMP_ALL], cnt[C_PLACE], cnt[C_NOPLACE],
               cnt[C_SRC1], cnt[C_SRC2], cnt[C_SRC3], cnt[C_SRC4P], cnt[C_NODUMP_PLACE],
               cnt[C_ENVYFREE], cnt[C_ENVSRC], cnt[C_ENVSRC_FAIL], cnt[C_ISOSRC], cnt[C_ISOSRC_FAIL]);
        fflush(stdout);
    }
    return anyfail;
}
