/* ls4_gm.c: conjecture GM4 (k4/ls4plus.md): every junk-free EFX0 partial allocation maximizing a potential admits a
 * placement of the pool (LS4 Phase 2 (a)-(d); (a) is sound here because a maximum admits no M1 move).
 * Potentials: POT=0 sum of levels; POT=1 leximin of levels (sorted ascending, lexicographic); POT=2 levels in agent
 * order, lexicographic (fixed priority).  For each profile all junk-free partial allocations are enumerated.
 * Same input format as ls4alg.c.  Output: RESULT runs=profiles nmaximal=... fail=profiles with a maximal state
 * without placement, allfail=profiles all of whose maximal states lack one. */
#define LS4_NO_MAIN
#include "ls4alg.c"
#ifndef POT
#define POT 0
#endif
#define MAXS (1 << 22)
static int gvv[MAXM][MAXN + 1], ngvv[MAXM];
static void decode(long c, mask *X) {
    for (int i = 0; i < n; i++) X[i] = 0;
    for (int g = 0; g < m; g++) { int k = c % ngvv[g]; c /= ngvv[g]; if (k) X[gvv[g][k]] |= 1u << g; }
}
static int lev1(int i, mask S) { long v = vs(i, S); int r = 0;
    for (int z = 0; z < (1 << d[i]); z++) { long s = 0; for (int t = 0; t < d[i]; t++) if (z >> t & 1) s += V[i][rg[i][t]]; if (s < v) r++; } return r; }
static void key(const mask *X, int *k) {          /* potential as a vector compared lexicographically */
    int l[MAXN]; for (int i = 0; i < n; i++) l[i] = lev1(i, X[i]);
#if POT == 0
    int s = 0; for (int i = 0; i < n; i++) s += l[i]; k[0] = s; for (int i = 1; i < n; i++) k[i] = 0;
#elif POT == 1
    for (int i = 0; i < n; i++) k[i] = l[i];
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (k[b] < k[a]) { int t = k[a]; k[a] = k[b]; k[b] = t; }
#else
    for (int i = 0; i < n; i++) k[i] = l[i];
#endif
}
static int cmpk(const int *a, const int *b) { for (int i = 0; i < n; i++) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1; return 0; }
int main(void) {
    int anyfail = 0; static long list[MAXS];
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
        long NS = 1;
        for (int g = 0; g < m; g++) { ngvv[g] = 0; gvv[g][ngvv[g]++] = -1; for (int i = 0; i < n; i++) if (R[i] >> g & 1) gvv[g][ngvv[g]++] = i; NS *= ngvv[g]; }
        if (NS > MAXS) { printf("SKIP\n"); continue; }
        long runs = 0, maxstates = 0, fail = 0, allfail = 0; int printed = 0;
        memset(cur_idx, 0, sizeof cur_idx);
        for (long r = 0;; r++) {
            if (mode == 1) { if (r >= K) break; for (int i = 0; i < n; i++) cur_idx[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) for (int t = 0; t < d[i]; t++) V[i][rg[i][t]] = 32L * rep[i][cur_idx[i]][t] + (1L << t);
            int best[MAXN]; long nl = 0; best[0] = -1;
            for (long c = 0; c < NS; c++) {
                mask X[MAXN]; decode(c, X); if (!efx0(X)) continue;
                int k[MAXN]; key(X, k);
                int cm = best[0] < 0 ? 1 : cmpk(k, best);
                if (cm > 0) { memcpy(best, k, sizeof best); nl = 0; }
                if (cm >= 0) list[nl++] = c;
            }
            int nf = 0;
            for (long q = 0; q < nl; q++) {
                decode(list[q], Y); mask a = 0; for (int i = 0; i < n; i++) a |= Y[i]; U = ALL & ~a;
                restrict_bc = 0;
                if (U && !phase2()) { nf++;
                    if (printed++ < 3) { printf("GMFAIL n=%d m=%d", n, m);
                        for (int i = 0; i < n; i++) { printf(" ["); for (int t = 0; t < d[i]; t++) printf(t ? " %d:%d" : "%d:%d", rg[i][t], rep[i][cur_idx[i]][t]); printf("]"); }
                        printf(" Y:"); for (int i = 0; i < n; i++) printf(" %x", Y[i]); printf(" U:%x\n", U); } }
            }
            maxstates += nl; if (nf) fail++; if (nf == nl) allfail++;
            runs++;
            if (mode == 0) { int i = 0; while (i < n && ++cur_idx[i] == T[i]) { cur_idx[i] = 0; i++; } if (i == n) break; }
        }
        printf("RESULT runs=%ld nmaximal=%ld fail=%ld allfail=%ld\n", runs, maxstates, fail, allfail);
        fflush(stdout);
        if (fail) anyfail = 1;
    }
    return 0;
}
