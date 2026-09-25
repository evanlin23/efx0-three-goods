/* gm4_escape.c: how do junk-free EFX0 partial allocations in which *no* single dump works escape by raising the level
 * sum?  (k4/gm4.md, exploration.)  Same input format as gm4_explore.c.
 * For each profile: all junk-free partial allocations are enumerated and the EFX0 ones kept (raw definition).  A state
 * Y is *bad* if U != {}, no bundle is empty, and no source admits the single dump.  With -DPSTABLE only bad states
 * that are Pareto-stable (no EFX0 junk-free Z with l_i(Z_i) >= l_i(Y_i) for all i and a larger level sum) are kept.
 * For each bad state, among the EFX0 states Z with a larger level sum, those changing the fewest bundles are the
 * *minimal escapes*; the program counts them by (number of changed agents, number of losers) and, for one minimal
 * escape per state, whether the losers are sources of Y, and prints examples (-DSHOW=k per task).
 * Output: RESULT runs=.. bad=.. hist... ; ESC lines (examples). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#define MAXN 8
#define MAXM 20
#define MAXT 300
#define MAXS (1 << 20)
#ifndef SHOW
#define SHOW 3
#endif
typedef uint32_t mask;
static int n, m, d[MAXN], rg[MAXN][4], T[MAXN], rep[MAXN][MAXT][4], cur[MAXN];
static mask R[MAXN], ALL;
static long v[MAXN][MAXM];
static unsigned long long rs;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static long val(int i, mask S) { long s = 0; S &= R[i]; while (S) { s += v[i][__builtin_ctz(S)]; S &= S - 1; } return s; }
static long thr(int i, mask B) {
    long s = 0, mn = LONG_MAX;
    for (mask b = B; b; b &= b - 1) { int g = __builtin_ctz(b); long x = (R[i] >> g & 1) ? v[i][g] : 0; s += x; if (x < mn) mn = x; }
    return s - mn;
}
static int lev(int i, mask S) {
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
static mask st[MAXS][MAXN]; static signed char lv[MAXS][MAXN]; static int ls[MAXS];
static void pr(const mask *X) { for (int i = 0; i < n; i++) printf(" %u", X[i]); }
int main(void) {
    long hist[MAXN + 1][MAXN + 1]; long tot_bad = 0, runs_all = 0, loser_src = 0, loser_nonsrc = 0, nolos = 0;
    memset(hist, 0, sizeof hist);
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
        memset(cur, 0, sizeof cur); long runs = 0; int shown = 0;
        for (;;) {
            if (mode == 1) { if (runs >= K) break; for (int i = 0; i < n; i++) cur[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) { memset(v[i], 0, sizeof v[i]); for (int t = 0; t < d[i]; t++) v[i][rg[i][t]] = rep[i][cur[i]][t]; }
            long ne = 0;
            for (long c = 0; c < NS; c++) { mask X[MAXN]; decode(c, X); if (!efx0(X)) continue;
                memcpy(st[ne], X, sizeof X); ls[ne] = 0; for (int i = 0; i < n; i++) { lv[ne][i] = lev(i, X[i]); ls[ne] += lv[ne][i]; } ne++; }
            for (long y = 0; y < ne; y++) {
                mask *Y = st[y], a = 0; int empty = 0; for (int i = 0; i < n; i++) { a |= Y[i]; if (!Y[i]) empty = 1; }
                mask U = ALL & ~a; if (!U || empty) continue;
                long sig[MAXN]; for (int i = 0; i < n; i++) sig[i] = val(i, Y[i]);
                int issrc[MAXN], anydump = 0;
                for (int s = 0; s < n; s++) { issrc[s] = 1; for (int i = 0; i < n; i++) if (i != s && val(i, Y[s]) > sig[i]) issrc[s] = 0;
                    if (!issrc[s] || (R[s] & U)) continue;
                    int ok = 1; for (int x = 0; x < n && ok; x++) if (x != s && thr(x, Y[s] | U) > sig[x]) ok = 0;
                    if (ok) anydump = 1; }
                if (anydump) continue;
#ifdef PSTABLE
                int pareto = 0;
                for (long z = 0; z < ne && !pareto; z++) { if (ls[z] <= ls[y]) continue; int ok = 1;
                    for (int i = 0; i < n; i++) if (lv[z][i] < lv[y][i]) { ok = 0; break; } pareto = ok; }
                if (pareto) continue;
#endif
                tot_bad++;
                int bestc = n + 1, bestl = n + 1; long bz = -1;
                for (long z = 0; z < ne; z++) { if (ls[z] <= ls[y]) continue;
                    int ch = 0, lo = 0; for (int i = 0; i < n; i++) { if (st[z][i] != Y[i]) ch++; if (lv[z][i] < lv[y][i]) lo++; }
                    if (ch < bestc || (ch == bestc && lo < bestl)) { bestc = ch; bestl = lo; bz = z; } }
                if (bz < 0) { printf("NOESC"); pr(Y); printf(" | %u\n", U); continue; }   /* a maximum without a dump */
                hist[bestc][bestl]++;
                for (int i = 0; i < n; i++) if (lv[bz][i] < lv[y][i]) { if (issrc[i]) loser_src++; else loser_nonsrc++; }
                if (!bestl) nolos++;
                if (shown++ < SHOW) { printf("ESC changed=%d losers=%d vals", bestc, bestl);
                    for (int i = 0; i < n; i++) { printf(" "); for (int t = 0; t < d[i]; t++) printf(t ? ",%d" : "%d", rep[i][cur[i]][t]); }
                    printf(" | Y"); pr(Y); printf(" | U %u | Z", U); pr(st[bz]); printf(" | lev"); for (int i = 0; i < n; i++) printf(" %d>%d", lv[y][i], lv[bz][i]); printf("\n"); }
            }
            runs++;
            if (mode == 0) { int i = 0; while (i < n && ++cur[i] == T[i]) { cur[i] = 0; i++; } if (i == n) break; }
        }
        runs_all += runs;
        fflush(stdout);
    }
    printf("RESULT runs=%ld bad=%ld loser_src=%ld loser_nonsrc=%ld nolosers=%ld", runs_all, tot_bad, loser_src, loser_nonsrc, nolos);
    for (int c = 0; c <= n; c++) for (int l = 0; l <= n; l++) if (hist[c][l]) printf(" c%dl%d=%ld", c, l, hist[c][l]);
    printf("\n");
    return 0;
}
