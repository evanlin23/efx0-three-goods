/* gm4_fast.c: all level-sum maxima of a strict profile of a k = 4 core by branch and bound, and the GM4 check
 * (k4/gm4.md).  Same input format as gm4_explore.c (MODE 0: all profiles, 1: K random ones).
 * Search: agents in index order each choose a bundle Y_i subset R_i among the goods not yet taken (so every state is a
 * junk-free partial allocation); a branch is cut when two chosen bundles violate EFX0 (raw definition: v_i(Y_i) >=
 * v_i(Y_j \ g) for all g in Y_j), or when its level sum plus sum over later agents of l_i(R_i minus taken goods)
 * is below the best found.  All states reaching the maximum are kept (ties included).
 * For every maximum with a nonempty pool U: (a) an empty bundle, (b) a source s valuing no good of U with Y_s cup U
 * threat-free for s.  If neither applies, all junk placements are searched: GM4S lines (no single dump) and GMFAIL
 * lines (no placement at all: a counterexample to GM4).  Exit status 1 if a GMFAIL occurs.
 * Per profile: pfail = some maximum admits no placement (GM4 fails); pallfail = no maximum admits a placement (the
 * existence form GM4E fails: then every maximum has a nonempty pool); GMALL lines print such profiles.
 * -DOUT=k prints up to k maxima with a nonempty pool per task as M lines (gm4_analyze.py format). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#define MAXN 8
#define MAXM 32
#define MAXT 300
#define MAXL 4096
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
/* per-agent local subsets */
static mask lm[MAXN][16]; static long lval[MAXN][16]; static int llev[MAXN][16];
static long tP[MAXN][MAXN][16];   /* tP[i][j][k] = theta_i(lm[j][k]) */
static int ch[MAXN], best, nl; static mask lst[MAXL][MAXN]; static long overflow;
static int ubound(int k, mask used) { int b = 0; for (int i = k; i < n; i++) { mask a = R[i] & ~used; for (int c = 0; c < (1 << d[i]); c++) if (lm[i][c] == a) { b += llev[i][c]; break; } } return b; }
static void dfs(int k, mask used, int ps) {
    if (k == n) {
        if (ps > best) { best = ps; nl = 0; }
        if (ps == best) { if (nl < MAXL) { for (int i = 0; i < n; i++) lst[nl][i] = lm[i][ch[i]]; nl++; } else overflow++; }
        return;
    }
    if (ps + ubound(k, used) < best) return;
    for (int c = (1 << d[k]) - 1; c >= 0; c--) {
        if (lm[k][c] & used) continue;
        long sk = lval[k][c]; int ok = 1;
        for (int j = 0; j < k && ok; j++) {
            if (ch[j] && tP[k][j][ch[j]] > sk) ok = 0;
            if (c && tP[j][k][c] > lval[j][ch[j]]) ok = 0;
        }
        if (!ok) continue;
        ch[k] = c; dfs(k + 1, used | lm[k][c], ps + llev[k][c]);
    }
}
static int place_rec(mask *X, mask U) {
    if (!U) return efx0(X);
    int g = __builtin_ctz(U);
    for (int j = 0; j < n; j++) if (!(R[j] >> g & 1)) { X[j] |= 1u << g; int ok = place_rec(X, U & (U - 1)); X[j] &= ~(1u << g); if (ok) return 1; }
    return 0;
}
static void prline(const char *tag, const mask *Y, mask U) {
    printf("%s", tag);
    for (int i = 0; i < n; i++) { printf(" "); for (int t = 0; t < d[i]; t++) printf(t ? ",%d" : "%d", rep[i][cur[i]][t]); }
    printf(" |"); for (int i = 0; i < n; i++) printf(" %u", Y[i]); printf(" | %u\n", U);
}
int main(void) {
    int anyfail = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        ALL = (1u << m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &d[i]) != 1) return 3; R[i] = 0;
            for (int t = 0; t < d[i]; t++) { if (scanf("%d", &rg[i][t]) != 1) return 3; R[i] |= 1u << rg[i][t]; } }
        for (int i = 0; i < n; i++) { if (scanf("%d", &T[i]) != 1 || T[i] > MAXT) return 3;
            for (int t = 0; t < T[i]; t++) for (int q = 0; q < d[i]; q++) if (scanf("%d", &rep[i][t][q]) != 1) return 3; }
        int mode; long K; unsigned long long seed;
        if (scanf("%d %ld %llu", &mode, &K, &seed) != 3) return 3;
        rs = seed * 2654435761ULL + 88172645463325252ULL;
        for (int i = 0; i < n; i++) for (int c = 0; c < (1 << d[i]); c++) { lm[i][c] = 0; for (int t = 0; t < d[i]; t++) if (c >> t & 1) lm[i][c] |= 1u << rg[i][t]; }
        memset(cur, 0, sizeof cur);
        long runs = 0, maxima = 0, pool = 0, empty = 0, dump = 0, nodump = 0, fail = 0, out = 0, pfail = 0, pallfail = 0;
        for (;;) {
            if (mode == 1) { if (runs >= K) break; for (int i = 0; i < n; i++) cur[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) { memset(v[i], 0, sizeof v[i]); for (int t = 0; t < d[i]; t++) v[i][rg[i][t]] = rep[i][cur[i]][t]; }
            for (int i = 0; i < n; i++) for (int c = 0; c < (1 << d[i]); c++) { lval[i][c] = val(i, lm[i][c]); llev[i][c] = lev(i, lm[i][c]); }
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) for (int c = 0; c < (1 << d[j]); c++) tP[i][j][c] = c ? thr(i, lm[j][c]) : 0;
            best = -1; nl = 0; dfs(0, 0, 0);
            int nbadq = 0;
            for (int q = 0; q < nl; q++) {
                mask *Y = lst[q], a = 0; for (int i = 0; i < n; i++) a |= Y[i];
                mask U = ALL & ~a; maxima++;
                if (!U) continue;
                pool++;
                int e = 0; for (int i = 0; i < n; i++) if (!Y[i]) e = 1;
                if (e) { empty++; continue; }
                long sig[MAXN]; for (int i = 0; i < n; i++) sig[i] = val(i, Y[i]);
                int ok = 0;
                for (int s = 0; s < n && !ok; s++) {
                    int src = 1; for (int i = 0; i < n; i++) if (i != s && val(i, Y[s]) > sig[i]) src = 0;
                    if (!src || (R[s] & U)) continue;
                    ok = 1; for (int x = 0; x < n && ok; x++) if (x != s && thr(x, Y[s] | U) > sig[x]) ok = 0;
                }
#ifdef OUT
                if (out < OUT) { out++; prline("M", Y, U); }
#endif
                if (ok) { dump++; continue; }
                nodump++;
                mask X[MAXN]; memcpy(X, Y, sizeof X);
                if (place_rec(X, U)) prline("GM4S", Y, U);
                else { fail++; nbadq++; anyfail = 1; prline("GMFAIL", Y, U); }
            }
            if (nbadq) pfail++;
            if (nl && nbadq == nl) { pallfail++; prline("GMALL", lst[0], 0); }
            runs++;
            if (mode == 0) { int i = 0; while (i < n && ++cur[i] == T[i]) { cur[i] = 0; i++; } if (i == n) break; }
        }
        printf("RESULT runs=%ld maxima=%ld pool=%ld empty=%ld dump=%ld nodump=%ld fail=%ld pfail=%ld pallfail=%ld overflow=%ld\n", runs, maxima, pool, empty, dump, nodump, fail, pfail, pallfail, overflow);
        fflush(stdout);
    }
    return anyfail;
}
