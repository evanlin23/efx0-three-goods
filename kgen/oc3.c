/* oc3.c: brute force for Conjecture OC1 (k4/sdc.md §29) with n = 3 agents and any number of relevant goods.
 *
 * Independent of the SAT code in k4/sdc: it enumerates all 3^m complete allocations, tests EFX0 from the raw
 * definition (v_i(X_i) >= v_i(X_j \ g) for all i != j, g in X_j), and tests, for each of the 6 serial-dictatorship
 * orders, whether the allocation is reachable from the order's picks by
 *   - no move, then a one-absorber completion;                                    (class NONE)
 *   - one improving chain (k4/sdc/de_free.py's chain, any t >= 0), then a one-absorber completion (class CODE:
 *     the moves oc_absorb.py tests; t = 0 means x0 adds positive-valued junk to its own pick);
 *   - the same with t >= 1 only (class STRICT: the definition in k4/sdc.md §29, where a chain has t >= 1);
 *   - no move, free completion (SD-C for this order: class FREE0);
 *   - at most one chain (t >= 1), free completion (Conjecture OC: class FREEOC);
 *   - value domination of the picks (Conjecture MD for this order: class MD).
 * The chain's sets H are unbounded here (de_free.py caps them at DF_HMAX; at large k the cap is the instance's k).
 *
 * Reachability of a fixed allocation X from picks y (y_i = -1: no pick), J = goods that are no pick, R_i = goods
 * i values positively.  Taking every H as large as X allows is optimal (the improvement inequalities and the
 * absorber count are monotone in H), so:
 *   chain (x0) [t = 0]:       y_i in X_i for all i;  H0 = X_x0 & J & R_x0 nonempty; bases y_i, and y_x0 + H0.
 *   chain (x0,x1) [t = 1]:    y_x0 in X_x1, y_z in X_z (z the third agent); H1 = X_x1 & J & R_x1,
 *                             v_x1(y_x0 + H1) > v_x1(y_x1); H0 = X_x0 & (J + y_x1) & R_x0, v_x0(H0) > v_x0(y_x0).
 *   chain (x0,x1,x2) [t = 2]: y_x0 in X_x1, y_x1 in X_x2; H1 = X_x1 & J & R_x1, v_x1(y_x0 + H1) > v_x1(y_x1);
 *                             H2 = X_x2 & J & R_x2, v_x2(y_x1 + H2) > v_x2(y_x2); H0 = X_x0 & (J + y_x2) & R_x0,
 *                             v_x0(H0) > v_x0(y_x0).
 *   one-absorber completion: with bases B'_i, at most one i has |X_i \ B'_i| >= 2.
 * (de_free.py also requires y_{x_{i-1}} to exist to extend a chain past x_{i-1}; so do we.)
 *
 * Interface (ctypes): int oc3(int m, const long long *v, long long *out, int *wit)
 *   v: 3*m values (agent-major), m <= 20;  out: 6 orders x 8 counters
 *   [NONE, CODE, STRICT, FREE0, FREEOC, MD, EFX, unused];  wit: 6 orders x 3 masks, a CODE witness (or -1).
 * Picks: favourite remaining positively valued good, ties to the smaller index (as sdc_orders.sd).
 * Returns the number of EFX0 allocations.
 */
#include <stdlib.h>
#include <string.h>

static const int ORD[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};

static int popc(unsigned x) { return __builtin_popcount(x); }

int oc3(int m, const long long *v, long long *out, int *wit)
{
    int full = (1 << m) - 1, S = 1 << m;
    long long *sum = malloc(sizeof(long long) * 3 * S), *mn = malloc(sizeof(long long) * 3 * S);
    int R[3] = {0, 0, 0};
    for (int i = 0; i < 3; i++)
        for (int g = 0; g < m; g++) if (v[i * m + g] > 0) R[i] |= 1 << g;
    for (int i = 0; i < 3; i++) {
        sum[i * S] = 0; mn[i * S] = 0;
        for (int s = 1; s < S; s++) {
            int g = __builtin_ctz(s); int r = s & (s - 1);
            sum[i * S + s] = sum[i * S + r] + v[i * m + g];
            mn[i * S + s] = (r == 0 || v[i * m + g] < mn[i * S + r]) ? v[i * m + g] : mn[i * S + r];
        }
    }
    /* picks per order */
    int y[6][3];
    for (int o = 0; o < 6; o++) {
        int left = full;
        for (int k = 0; k < 3; k++) {
            int i = ORD[o][k], best = -1;
            for (int g = 0; g < m; g++)
                if ((left >> g & 1) && v[i * m + g] > 0 && (best < 0 || v[i * m + g] > v[i * m + best])) best = g;
            y[o][i] = best;
            if (best >= 0) left &= ~(1 << best);
        }
    }
    memset(out, 0, sizeof(long long) * 48);
    for (int k = 0; k < 18; k++) wit[k] = -1;
    long long nefx = 0;
    int X[3];
    for (int a = 0; a < S; a++) {
        int ra = full & ~a;
        /* enumerate b subset of ra */
        for (int b = ra;; b = (b - 1) & ra) {
            X[0] = a; X[1] = b; X[2] = ra & ~b;
            int ok = 1;
            for (int i = 0; i < 3 && ok; i++) {
                long long own = sum[i * S + X[i]];
                for (int j = 0; j < 3; j++) {
                    if (j == i || popc(X[j]) < 2) continue;
                    if (sum[i * S + X[j]] - mn[i * S + X[j]] > own) { ok = 0; break; }
                }
            }
            if (ok) {
                nefx++;
                for (int o = 0; o < 6; o++) {
                    long long *ou = out + o * 8;
                    const int *yy = y[o];
                    int pm = 0;   /* picks mask */
                    for (int i = 0; i < 3; i++) if (yy[i] >= 0) pm |= 1 << yy[i];
                    int J = full & ~pm;
                    int own[3];
                    for (int i = 0; i < 3; i++) own[i] = (yy[i] < 0) || (X[i] >> yy[i] & 1);
                    int allown = own[0] && own[1] && own[2];
                    /* MD */
                    int md = 1;
                    for (int i = 0; i < 3; i++)
                        if (yy[i] >= 0 && sum[i * S + X[i]] < v[i * m + yy[i]]) md = 0;
                    if (md) ou[5]++;
                    ou[6]++;
                    int rnone = 0, rt0 = 0, rt1 = 0, rt2 = 0, ft1 = 0, ft2 = 0;
                    if (allown) {
                        ou[3]++;
                        int big = 0;
                        for (int i = 0; i < 3; i++) {
                            int base = yy[i] >= 0 ? (1 << yy[i]) : 0;
                            if (popc(X[i] & ~base) >= 2) big++;
                        }
                        rnone = big <= 1;
                        for (int x = 0; x < 3 && !rt0; x++) {
                            if (yy[x] < 0) continue;
                            int H0 = X[x] & J & R[x];
                            if (!H0) continue;
                            int bg = 0;
                            for (int i = 0; i < 3; i++) {
                                int base = (1 << yy[i]) | (i == x ? H0 : 0);
                                if (yy[i] < 0) base = 0;
                                if (popc(X[i] & ~base) >= 2) bg++;
                            }
                            if (bg <= 1) rt0 = 1;
                        }
                    }
                    /* t = 1 */
                    for (int x0 = 0; x0 < 3; x0++) for (int x1 = 0; x1 < 3; x1++) {
                        if (x1 == x0) continue;
                        int z = 3 - x0 - x1;
                        if (yy[x0] < 0 || !(X[x1] >> yy[x0] & 1)) continue;
                        if (!own[z]) continue;
                        int H1 = X[x1] & J & R[x1];
                        long long old1 = yy[x1] >= 0 ? v[x1 * m + yy[x1]] : 0;
                        if (v[x1 * m + yy[x0]] + sum[x1 * S + H1] <= old1) continue;
                        int pool0 = J | (yy[x1] >= 0 ? 1 << yy[x1] : 0);
                        int H0 = X[x0] & pool0 & R[x0];
                        if (sum[x0 * S + H0] <= v[x0 * m + yy[x0]]) continue;
                        ft1 = 1;
                        int B[3]; B[x0] = H0; B[x1] = (1 << yy[x0]) | H1; B[z] = yy[z] >= 0 ? 1 << yy[z] : 0;
                        int bg = 0;
                        for (int i = 0; i < 3; i++) if (popc(X[i] & ~B[i]) >= 2) bg++;
                        if (bg <= 1) rt1 = 1;
                    }
                    /* t = 2 */
                    for (int p = 0; p < 6; p++) {
                        int x0 = ORD[p][0], x1 = ORD[p][1], x2 = ORD[p][2];
                        if (yy[x0] < 0 || yy[x1] < 0) continue;
                        if (!(X[x1] >> yy[x0] & 1) || !(X[x2] >> yy[x1] & 1)) continue;
                        int H1 = X[x1] & J & R[x1];
                        if (v[x1 * m + yy[x0]] + sum[x1 * S + H1] <= v[x1 * m + yy[x1]]) continue;
                        int H2 = X[x2] & J & R[x2];
                        long long old2 = yy[x2] >= 0 ? v[x2 * m + yy[x2]] : 0;
                        if (v[x2 * m + yy[x1]] + sum[x2 * S + H2] <= old2) continue;
                        int pool0 = J | (yy[x2] >= 0 ? 1 << yy[x2] : 0);
                        int H0 = X[x0] & pool0 & R[x0];
                        if (sum[x0 * S + H0] <= v[x0 * m + yy[x0]]) continue;
                        ft2 = 1;
                        int B[3]; B[x0] = H0; B[x1] = (1 << yy[x0]) | H1; B[x2] = (1 << yy[x1]) | H2;
                        int bg = 0;
                        for (int i = 0; i < 3; i++) if (popc(X[i] & ~B[i]) >= 2) bg++;
                        if (bg <= 1) rt2 = 1;
                    }
                    if (rnone) ou[0]++;
                    if (rnone || rt0 || rt1 || rt2) {
                        ou[1]++;
                        if (wit[o * 3] < 0) { wit[o * 3] = X[0]; wit[o * 3 + 1] = X[1]; wit[o * 3 + 2] = X[2]; }
                    }
                    if (rnone || rt1 || rt2) ou[2]++;
                    if (allown || ft1 || ft2) ou[4]++;
                }
            }
            if (b == 0) break;
        }
    }
    free(sum); free(mn);
    return (int)(nefx > 2000000000 ? 2000000000 : nefx);
}
