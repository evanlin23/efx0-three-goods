/* pd3.c: is every partial EFX0 allocation value-dominated by a complete EFX0 allocation?  (P1 of k4/sdc.md §1, in
 * the equivalent "domination" form PD), three agents, any number of relevant goods, brute force.
 *
 * Complete allocations: all 3^m, raw EFX0 test, Pareto frontier of their value vectors.  Partial allocations: all
 * 4^m (a good may stay unallocated), raw EFX0 test among the allocated bundles; each value vector is checked against
 * the frontier.  A partial EFX0 allocation with no dominating complete one refutes PD (and P1) for that instance.
 *
 * ctypes: long long pd3(int m, const long long *v, int *bad)   returns the number of undominated partial EFX0
 * allocations (0: PD holds); bad gets one of them as 4 masks (bundles 0..2, unallocated), or -1.
 * Also: long long pd3_count[2] = {complete EFX0, partial EFX0}.
 */
#include <stdlib.h>
#include <string.h>

long long pd3_count[2];

static int efx(int S, const long long *sum, const long long *mn, const int *X)
{
    for (int i = 0; i < 3; i++) {
        long long own = sum[i * S + X[i]];
        for (int j = 0; j < 3; j++) {
            if (j == i || __builtin_popcount(X[j]) < 2) continue;
            if (sum[i * S + X[j]] - mn[i * S + X[j]] > own) return 0;
        }
    }
    return 1;
}

long long pd3(int m, const long long *v, int *bad)
{
    int S = 1 << m, full = S - 1;
    long long *sum = malloc(sizeof(long long) * 3 * S), *mn = malloc(sizeof(long long) * 3 * S);
    for (int i = 0; i < 3; i++) {
        sum[i * S] = 0; mn[i * S] = 0;
        for (int s = 1; s < S; s++) {
            int g = __builtin_ctz(s), r = s & (s - 1);
            sum[i * S + s] = sum[i * S + r] + v[i * m + g];
            mn[i * S + s] = (r == 0 || v[i * m + g] < mn[i * S + r]) ? v[i * m + g] : mn[i * S + r];
        }
    }
    int cap = 1 << 16, nf = 0;
    long long (*fr)[3] = malloc(sizeof(long long[3]) * cap);
    int X[3];
    pd3_count[0] = pd3_count[1] = 0;
    /* complete allocations: frontier */
    for (int a = 0; a < S; a++) {
        int ra = full & ~a;
        for (int b = ra;; b = (b - 1) & ra) {
            X[0] = a; X[1] = b; X[2] = ra & ~b;
            if (efx(S, sum, mn, X)) {
                pd3_count[0]++;
                long long u[3] = {sum[X[0]], sum[S + X[1]], sum[2 * S + X[2]]};
                int dom = 0;
                for (int k = 0; k < nf && !dom; k++)
                    if (fr[k][0] >= u[0] && fr[k][1] >= u[1] && fr[k][2] >= u[2]) dom = 1;
                if (!dom) {
                    int w = 0;
                    for (int k = 0; k < nf; k++)
                        if (!(u[0] >= fr[k][0] && u[1] >= fr[k][1] && u[2] >= fr[k][2])) {
                            fr[w][0] = fr[k][0]; fr[w][1] = fr[k][1]; fr[w][2] = fr[k][2]; w++;
                        }
                    nf = w;
                    if (nf == cap) { cap *= 2; fr = realloc(fr, sizeof(long long[3]) * cap); }
                    fr[nf][0] = u[0]; fr[nf][1] = u[1]; fr[nf][2] = u[2]; nf++;
                }
            }
            if (b == 0) break;
        }
    }
    long long nbad = 0;
    for (int k = 0; k < 4; k++) bad[k] = -1;
    /* partial allocations: c = allocated set, then 3-split of c */
    for (int c = 0; c < S; c++) {
        if (c == full) continue;
        for (int a = c;; a = (a - 1) & c) {
            int ra = c & ~a;
            for (int b = ra;; b = (b - 1) & ra) {
                X[0] = a; X[1] = b; X[2] = ra & ~b;
                if (efx(S, sum, mn, X)) {
                    pd3_count[1]++;
                    long long u[3] = {sum[X[0]], sum[S + X[1]], sum[2 * S + X[2]]};
                    int dom = 0;
                    for (int k = 0; k < nf && !dom; k++)
                        if (fr[k][0] >= u[0] && fr[k][1] >= u[1] && fr[k][2] >= u[2]) dom = 1;
                    if (!dom) {
                        if (nbad == 0) { bad[0] = X[0]; bad[1] = X[1]; bad[2] = X[2]; bad[3] = full & ~c; }
                        nbad++;
                    }
                }
                if (b == 0) break;
            }
            if (a == 0) break;
        }
    }
    free(sum); free(mn); free(fr);
    return nbad;
}

/* pd3_min: the least number of complete EFX0 allocations that value-dominate a partial EFX0 allocation (over all
 * partial EFX0 allocations whose value vector no complete EFX0 allocation attains exactly; 0 = PD fails; 10^9 if
 * there is none), for adversarial climbs.  The least is attained on the Pareto frontier of the partial vectors, so
 * only that frontier is scanned.  arg: one argmin partial allocation (4 masks). */
long long pd3_min(int m, const long long *v, int *arg)
{
    int S = 1 << m, full = S - 1;
    long long *sum = malloc(sizeof(long long) * 3 * S), *mn = malloc(sizeof(long long) * 3 * S);
    for (int i = 0; i < 3; i++) {
        sum[i * S] = 0; mn[i * S] = 0;
        for (int s = 1; s < S; s++) {
            int g = __builtin_ctz(s), r = s & (s - 1);
            sum[i * S + s] = sum[i * S + r] + v[i * m + g];
            mn[i * S + s] = (r == 0 || v[i * m + g] < mn[i * S + r]) ? v[i * m + g] : mn[i * S + r];
        }
    }
    int capc = 1 << 12, nc = 0, capp = 1 << 10, np = 0;
    long long (*cv)[3] = malloc(sizeof(long long[3]) * capc);
    long long (*pv)[3] = malloc(sizeof(long long[3]) * capp);
    int (*pa)[4] = malloc(sizeof(int[4]) * capp);
    int X[3];
    for (int c = 0; c < S; c++) {
        for (int a = c;; a = (a - 1) & c) {
            int ra = c & ~a;
            for (int b = ra;; b = (b - 1) & ra) {
                X[0] = a; X[1] = b; X[2] = ra & ~b;
                if (efx(S, sum, mn, X)) {
                    long long u[3] = {sum[X[0]], sum[S + X[1]], sum[2 * S + X[2]]};
                    if (c == full) {
                        if (nc == capc) { capc *= 2; cv = realloc(cv, sizeof(long long[3]) * capc); }
                        cv[nc][0] = u[0]; cv[nc][1] = u[1]; cv[nc][2] = u[2]; nc++;
                    }
                    /* frontier of the strictly partial allocations (some good unallocated) */
                    if (c == full) goto next;
                    int dom = 0;
                    for (int k = 0; k < np && !dom; k++)
                        if (pv[k][0] >= u[0] && pv[k][1] >= u[1] && pv[k][2] >= u[2]) dom = 1;
                    if (!dom) {
                        int w = 0;
                        for (int k = 0; k < np; k++)
                            if (!(u[0] >= pv[k][0] && u[1] >= pv[k][1] && u[2] >= pv[k][2])) {
                                pv[w][0] = pv[k][0]; pv[w][1] = pv[k][1]; pv[w][2] = pv[k][2];
                                for (int t = 0; t < 4; t++) pa[w][t] = pa[k][t];
                                w++;
                            }
                        np = w;
                        if (np == capp) { capp *= 2; pv = realloc(pv, sizeof(long long[3]) * capp); pa = realloc(pa, sizeof(int[4]) * capp); }
                        pv[np][0] = u[0]; pv[np][1] = u[1]; pv[np][2] = u[2];
                        pa[np][0] = X[0]; pa[np][1] = X[1]; pa[np][2] = X[2]; pa[np][3] = full & ~c; np++;
                    }
                }
            next:
                if (b == 0) break;
            }
            if (a == 0) break;
        }
    }
    /* the least count over the frontier of strictly partial allocations; vectors that a complete EFX0 allocation
     * attains exactly are skipped (trivially dominated) */
    long long best = 1000000000;
    for (int t = 0; t < 4; t++) arg[t] = -1;
    for (int k = 0; k < np; k++) {
        long long cnt = 0; int exact = 0;
        for (int t = 0; t < nc; t++)
            if (cv[t][0] >= pv[k][0] && cv[t][1] >= pv[k][1] && cv[t][2] >= pv[k][2]) {
                cnt++;
                if (cv[t][0] == pv[k][0] && cv[t][1] == pv[k][1] && cv[t][2] == pv[k][2]) exact = 1;
            }
        if (exact) continue;
        if (cnt < best) { best = cnt; for (int t = 0; t < 4; t++) arg[t] = pa[k][t]; }
    }
    free(sum); free(mn); free(cv); free(pv); free(pa);
    return best;
}
