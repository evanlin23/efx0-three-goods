/* ocn.c: brute force for OC1 and its variants with n <= 5 agents and any number of relevant goods (generalizes
 * kgen/oc3.c; same classes, same reachability characterization of a fixed allocation, see kgen/n3.md §1).
 *
 * All n^m complete allocations are enumerated (raw EFX0 test).  For every EFX0 allocation and every distinct pick
 * vector (over all n! orders), reachability from the picks is tested for
 *   NONE   (picks kept, one-absorber completion),
 *   CODE   (no move, or one chain with t >= 0, then one absorber: the moves of k4/sdc/oc_absorb.py),
 *   STRICT (the same with t >= 1 only),
 *   FREE0  (picks kept, free completion: SD-C for the order),
 *   FREEOC (picks kept, or one chain with t >= 1, free completion: Conjecture OC),
 *   MD     (value domination of the picks).
 * A chain is a path x0, ..., xt of distinct agents; the agents before xt pass nonempty bases.  Fixed X, picks y,
 * J = non-picks, R_i = positively valued goods; with every H as large as X allows:
 *   t = 0: y_a in X_a for all a; H0 = X_x0 & J & R_x0 nonempty; base of x0 = y_x0 + H0.
 *   t >= 1: y_{x_{i-1}} in X_{x_i} (i >= 1), y_a in X_a off the path; H_i = X_{x_i} & J & R_{x_i},
 *           v(y_{x_{i-1}} + H_i) > v(y_{x_i}); H0 = X_x0 & (J + y_xt) & R_x0, v(H0) > v(y_x0).
 *
 * ctypes: int ocn(int n, int m, const long long *v, long long *out, int *picks)
 *   out[o*8 + k], o = order index (orders in lexicographic order of permutations), k = NONE, CODE, STRICT, FREE0,
 *   FREEOC, MD, EFX; picks[o*n + i] = pick of agent i under order o (-1: none).  n <= 5, m <= 16 (n^m <= ~2e8).
 */
#include <stdlib.h>
#include <string.h>

#define MAXN 5
static int popc(unsigned x) { return __builtin_popcount(x); }

static int nperm(int n) { int f = 1; for (int i = 2; i <= n; i++) f *= i; return f; }
static void perms(int n, int (*P)[MAXN])
{
    int a[MAXN], cnt = 0, N = nperm(n);
    for (int i = 0; i < n; i++) a[i] = i;
    /* lexicographic generation */
    for (;;) {
        for (int i = 0; i < n; i++) P[cnt][i] = a[i];
        cnt++;
        if (cnt == N) break;
        int i = n - 2; while (i >= 0 && a[i] > a[i + 1]) i--;
        int j = n - 1; while (a[j] < a[i]) j--;
        int t = a[i]; a[i] = a[j]; a[j] = t;
        for (int l = i + 1, r = n - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    }
}

typedef struct { int n, m, S; const long long *v; long long *sum, *mn; int R[MAXN]; } Inst;

static long long val1(const Inst *I, int i, int g) { return g < 0 ? 0 : I->v[i * I->m + g]; }

/* chain search state */
static int path[MAXN], onpath[MAXN];

static void test_paths(const Inst *I, const int *X, const int *y, int J, int len, int *rc0, int *rc1, int *f1)
{
    /* path[0..len-1] is fixed; test it as a chain, then extend */
    int n = I->n, S = I->S, t = len - 1;
    int ok = 1, B[MAXN];
    for (int a = 0; a < n && ok; a++) if (!onpath[a]) { if (y[a] >= 0 && !(X[a] >> y[a] & 1)) ok = 0; B[a] = y[a] >= 0 ? 1 << y[a] : 0; }
    if (ok) {
        if (t == 0) {
            int x = path[0];
            if (y[x] >= 0 && (X[x] >> y[x] & 1)) {
                int H0 = X[x] & J & I->R[x];
                if (H0) {
                    B[x] = (1 << y[x]) | H0;
                    int bg = 0; for (int a = 0; a < n; a++) if (popc(X[a] & ~B[a]) >= 2) bg++;
                    if (bg <= 1) *rc0 = 1;
                }
            }
        } else {
            int good = 1;
            for (int i = 1; i <= t && good; i++) {
                int xi = path[i], xp = path[i - 1];
                if (y[xp] < 0 || !(X[xi] >> y[xp] & 1)) { good = 0; break; }
                int Hi = X[xi] & J & I->R[xi];
                if (val1(I, xi, y[xp]) + I->sum[xi * S + Hi] <= val1(I, xi, y[xi])) { good = 0; break; }
                B[xi] = (1 << y[xp]) | Hi;
            }
            if (good) {
                int x0 = path[0], xt = path[t];
                int pool = J | (y[xt] >= 0 ? 1 << y[xt] : 0);
                int H0 = X[x0] & pool & I->R[x0];
                if (I->sum[x0 * S + H0] > val1(I, x0, y[x0])) {
                    B[x0] = H0; *f1 = 1;
                    int bg = 0; for (int a = 0; a < n; a++) if (popc(X[a] & ~B[a]) >= 2) bg++;
                    if (bg <= 1) *rc1 = 1;
                }
            }
        }
    }
    if (len == n) return;
    if (y[path[len - 1]] < 0) return;            /* cannot pass an empty base */
    for (int a = 0; a < n; a++) if (!onpath[a]) {
        onpath[a] = 1; path[len] = a;
        test_paths(I, X, y, J, len + 1, rc0, rc1, f1);
        onpath[a] = 0;
    }
}

int ocn(int n, int m, const long long *v, long long *out, int *picks)
{
    Inst I; I.n = n; I.m = m; I.S = 1 << m; I.v = v;
    int S = I.S, full = S - 1, NP = nperm(n);
    I.sum = malloc(sizeof(long long) * n * S); I.mn = malloc(sizeof(long long) * n * S);
    for (int i = 0; i < n; i++) {
        I.R[i] = 0;
        for (int g = 0; g < m; g++) if (v[i * m + g] > 0) I.R[i] |= 1 << g;
        I.sum[i * S] = 0; I.mn[i * S] = 0;
        for (int s = 1; s < S; s++) {
            int g = __builtin_ctz(s), r = s & (s - 1);
            I.sum[i * S + s] = I.sum[i * S + r] + v[i * m + g];
            I.mn[i * S + s] = (r == 0 || v[i * m + g] < I.mn[i * S + r]) ? v[i * m + g] : I.mn[i * S + r];
        }
    }
    int (*P)[MAXN] = malloc(sizeof(int[MAXN]) * NP);
    perms(n, P);
    /* picks per order; distinct pick vectors */
    int (*Y)[MAXN] = malloc(sizeof(int[MAXN]) * NP), *cls = malloc(sizeof(int) * NP), nd = 0;
    int (*D)[MAXN] = malloc(sizeof(int[MAXN]) * NP);
    for (int o = 0; o < NP; o++) {
        int left = full;
        for (int k = 0; k < n; k++) {
            int i = P[o][k], best = -1;
            for (int g = 0; g < m; g++)
                if ((left >> g & 1) && v[i * m + g] > 0 && (best < 0 || v[i * m + g] > v[i * m + best])) best = g;
            Y[o][i] = best; if (best >= 0) left &= ~(1 << best);
        }
        int c = -1;
        for (int d = 0; d < nd && c < 0; d++) { int same = 1; for (int i = 0; i < n; i++) if (D[d][i] != Y[o][i]) same = 0; if (same) c = d; }
        if (c < 0) { for (int i = 0; i < n; i++) D[nd][i] = Y[o][i]; c = nd++; }
        cls[o] = c;
        for (int i = 0; i < n; i++) picks[o * n + i] = Y[o][i];
    }
    long long (*cnt)[8] = calloc(nd, sizeof(long long[8]));
    /* odometer over assignments */
    int asg[32], X[MAXN];
    for (int g = 0; g < m; g++) asg[g] = 0;
    for (int i = 0; i < n; i++) X[i] = 0;
    X[0] = full;
    for (;;) {
        int ok = 1;
        for (int i = 0; i < n && ok; i++) {
            long long own = I.sum[i * S + X[i]];
            for (int j = 0; j < n; j++) {
                if (j == i || popc(X[j]) < 2) continue;
                if (I.sum[i * S + X[j]] - I.mn[i * S + X[j]] > own) { ok = 0; break; }
            }
        }
        if (ok) {
            for (int d = 0; d < nd; d++) {
                const int *y = D[d];
                long long *c = cnt[d];
                int pm = 0; for (int i = 0; i < n; i++) if (y[i] >= 0) pm |= 1 << y[i];
                int J = full & ~pm;
                int allown = 1, md = 1;
                for (int i = 0; i < n; i++) {
                    if (y[i] >= 0 && !(X[i] >> y[i] & 1)) allown = 0;
                    if (y[i] >= 0 && I.sum[i * S + X[i]] < v[i * m + y[i]]) md = 0;
                }
                c[6]++; if (md) c[5]++;
                int rnone = 0;
                if (allown) {
                    c[3]++;
                    int bg = 0;
                    for (int i = 0; i < n; i++) { int b = y[i] >= 0 ? 1 << y[i] : 0; if (popc(X[i] & ~b) >= 2) bg++; }
                    rnone = bg <= 1;
                }
                int rc0 = 0, rc1 = 0, f1 = 0;
                for (int a = 0; a < n; a++) { memset(onpath, 0, sizeof onpath); onpath[a] = 1; path[0] = a; test_paths(&I, X, y, J, 1, &rc0, &rc1, &f1); }
                if (rnone) c[0]++;
                if (rnone || rc0 || rc1) c[1]++;
                if (rnone || rc1) c[2]++;
                if (allown || f1) c[4]++;
            }
        }
        /* next assignment */
        int g = 0;
        while (g < m) {
            X[asg[g]] &= ~(1 << g);
            asg[g]++;
            if (asg[g] < n) { X[asg[g]] |= 1 << g; break; }
            asg[g] = 0; X[0] |= 1 << g; g++;
        }
        if (g == m) break;
    }
    memset(out, 0, sizeof(long long) * 8 * NP);
    for (int o = 0; o < NP; o++) for (int k = 0; k < 8; k++) out[o * 8 + k] = cnt[cls[o]][k];
    free(I.sum); free(I.mn); free(P); free(Y); free(cls); free(D); free(cnt);
    return nd;
}
