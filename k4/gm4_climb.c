/* gm4_climb.c: targeted counterexample search for GM4S / GM4 (k4/gm4.md).  For a profile, let
 *   M   = max level sum over all junk-free EFX0 partial allocations,
 *   P   = max level sum over the *bad* ones: nonempty pool, no empty bundle, and no source admitting the single dump.
 * A bad state with P = M is a maximum without a single dump (a GM4S counterexample; it is then checked for any junk
 * placement, i.e. GM4).  The search hill-climbs on gap = M - P over the profiles of one core: change one agent's
 * type at random, keep the change if the gap does not grow; restart after STEPS steps.
 * Input: as gm4_explore.c, with "MODE K SEED" read as "restarts STEPS SEED" (MODE ignored: always climbs).
 * Output: per task "RESULT restarts=.. evals=.. best_gap=.. hist_gapK=.."; lines GM4S / GMFAIL for hits. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#define MAXN 8
#define MAXM 20
#define MAXT 300
#define MAXS (1 << 20)
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
static int place_rec(mask *X, mask U) {
    if (!U) return efx0(X);
    int g = __builtin_ctz(U);
    for (int j = 0; j < n; j++) if (!(R[j] >> g & 1)) { X[j] |= 1u << g; int ok = place_rec(X, U & (U - 1)); X[j] &= ~(1u << g); if (ok) return 1; }
    return 0;
}
static int gv[MAXM][MAXN + 1], ngv[MAXM]; static long NS;
static void decode(long c, mask *X) {
    for (int i = 0; i < n; i++) X[i] = 0;
    for (int g = 0; g < m; g++) { int k = c % ngv[g]; c /= ngv[g]; if (k) X[gv[g][k - 1]] |= 1u << g; }
}
static int bad(const mask *Y) {
    mask a = 0; for (int i = 0; i < n; i++) { if (!Y[i]) return 0; a |= Y[i]; }
    mask U = ALL & ~a; if (!U) return 0;
    long sig[MAXN]; for (int i = 0; i < n; i++) sig[i] = val(i, Y[i]);
    for (int s = 0; s < n; s++) {
        int src = 1; for (int i = 0; i < n; i++) if (i != s && val(i, Y[s]) > sig[i]) src = 0;
        if (!src || (R[s] & U)) continue;
        int ok = 1; for (int x = 0; x < n && ok; x++) if (x != s && thr(x, Y[s] | U) > sig[x]) ok = 0;
        if (ok) return 0;
    }
    return 1;
}
static long evals;
static mask stS[MAXS][MAXN]; static signed char stL[MAXS][MAXN]; static int stSum[MAXS], ord_[MAXS];
static int cmpd(const void *a, const void *b) { return stSum[*(const int *)b] - stSum[*(const int *)a]; }
/* returns M - P (99 if none), P = max level sum of a bad state with no Pareto improvement (-DNOPSTABLE: any bad state) */
static int gap(mask *hit) {
    int M = -1; long ne = 0; evals++;
    for (int i = 0; i < n; i++) { memset(v[i], 0, sizeof v[i]); for (int t = 0; t < d[i]; t++) v[i][rg[i][t]] = rep[i][cur[i]][t]; }
    for (long c = 0; c < NS; c++) { mask X[MAXN]; decode(c, X); if (!efx0(X)) continue;
        memcpy(stS[ne], X, sizeof(mask) * n); stSum[ne] = 0;
        for (int i = 0; i < n; i++) { stL[ne][i] = lev(i, X[i]); stSum[ne] += stL[ne][i]; }
        if (stSum[ne] > M) M = stSum[ne]; ord_[ne] = ne; ne++; }
    qsort(ord_, ne, sizeof(int), cmpd);
    for (long a = 0; a < ne; a++) { int y = ord_[a];
        if (!bad(stS[y])) continue;
#ifndef NOPSTABLE
        int dom = 0;
        for (long b = 0; b < a && !dom; b++) { int z = ord_[b]; if (stSum[z] <= stSum[y]) break;
            int ok = 1; for (int i = 0; i < n; i++) if (stL[z][i] < stL[y][i]) { ok = 0; break; } dom = ok; }
        if (dom) continue;
#endif
        memcpy(hit, stS[y], sizeof(mask) * n); return M - stSum[y];
    }
    return 99;
}
static void prline(const char *tag, const mask *Y) {
    mask a = 0; for (int i = 0; i < n; i++) a |= Y[i];
    printf("%s", tag);
    for (int i = 0; i < n; i++) { printf(" "); for (int t = 0; t < d[i]; t++) printf(t ? ",%d" : "%d", rep[i][cur[i]][t]); }
    printf(" |"); for (int i = 0; i < n; i++) printf(" %u", Y[i]); printf(" | %u\n", ALL & ~a);
}
int main(void) {
    int anyfail = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        ALL = (1u << m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &d[i]) != 1) return 3; R[i] = 0;
            for (int t = 0; t < d[i]; t++) { if (scanf("%d", &rg[i][t]) != 1) return 3; R[i] |= 1u << rg[i][t]; } }
        for (int i = 0; i < n; i++) { if (scanf("%d", &T[i]) != 1 || T[i] > MAXT) return 3;
            for (int t = 0; t < T[i]; t++) for (int q = 0; q < d[i]; q++) if (scanf("%d", &rep[i][t][q]) != 1) return 3; }
        int restarts; long steps; unsigned long long seed;
        if (scanf("%d %ld %llu", &restarts, &steps, &seed) != 3) return 3;
        if (restarts == 0) restarts = 1;
        rs = seed * 2654435761ULL + 88172645463325252ULL;
        NS = 1;
        for (int g = 0; g < m; g++) { ngv[g] = 1; for (int i = 0; i < n; i++) if (R[i] >> g & 1) gv[g][ngv[g]++ - 1] = i; NS *= ngv[g]; }
        if (NS > MAXS) { printf("SKIP NS=%ld\n", NS); continue; }
        long hist[100] = {0}; int bestg = 99, hits = 0; evals = 0;
        for (int r = 0; r < restarts; r++) {
            for (int i = 0; i < n; i++) cur[i] = rnd() % T[i];
            mask hit[MAXN]; int g = gap(hit);
            for (long st = 0; st < steps && g > 0; st++) {
                int i = rnd() % n, old = cur[i]; cur[i] = rnd() % T[i];
                mask h2[MAXN]; int g2 = gap(h2);
                if (g2 <= g) { g = g2; memcpy(hit, h2, sizeof hit); } else cur[i] = old;
            }
            hist[g]++; if (g < bestg) bestg = g;
#ifdef SHOWGAP
            if (g == SHOWGAP) prline("GAP", hit);
#endif
            if (g == 0) { hits++; mask X[MAXN]; memcpy(X, hit, sizeof X); mask a = 0; for (int i = 0; i < n; i++) a |= hit[i];
                if (place_rec(X, ALL & ~a)) prline("GM4S", hit); else { anyfail = 1; prline("GMFAIL", hit); } }
        }
        printf("RESULT restarts=%d evals=%ld hits=%d", restarts, evals, hits);
        for (int g = 0; g < 100; g++) if (hist[g]) printf(" gap%d=%ld", g, hist[g]);
        printf("\n"); fflush(stdout);
    }
    return anyfail;
}
