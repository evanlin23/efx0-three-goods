/* DE4 conjecture checker (k = 4), second implementation (C), written from the definitions:
 * holdings: empty, single goods, minimal sets worth more than the top (MB), lower pair {c,d} with b < c+d < a;
 * valid: V1 every wanted good (worth more than the holder's holding) is a singleton holding; V2 no holding
 *        threatens another agent (exact EFX0 threat, holdings only);
 * level: empty 0, single a/b/c/d = 4/3/2/1, lower pair 3, MB 5;
 * maxima: maximum level sum, then value-Pareto-maximal among those;
 * completable: some assignment of the leftover goods to agents makes the allocation EFX0.
 * Input (stdin): lines "n m", then n lines "k g1..gk", then n lines "cnt" followed by cnt*k values (options).
 * Args: chunk nchunks. Enumerates profiles with index % nchunks == chunk.
 * Output: counts, and the first failing profiles. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 6
#define MAXM 16
#define MAXH 24
#define MAXOPT 300

static int n, m, k[MAXN], gs[MAXN][4], nopt[MAXN];
static int opt[MAXN][MAXOPT][4];
static int v[MAXN][MAXM];       /* current profile values */
static int R[MAXN];             /* relevant masks */

typedef struct { int mask, val, lev, want, sz; } Hold;
static Hold H[MAXN][MAXH]; static int nh[MAXN];

static int popc(int x) { return __builtin_popcount(x); }
static int val(int i, int S) { int s = 0; for (int g = 0; g < m; g++) if (S >> g & 1) s += v[i][g]; return s; }
static int theta(int i, int B) {
    if (popc(B) <= 1) return 0;
    int s = 0, mn = 1 << 30;
    for (int g = 0; g < m; g++) if (B >> g & 1) { s += v[i][g]; if (v[i][g] < mn) mn = v[i][g]; }
    return s - mn;   /* goods outside R_i have value 0, so mn = 0 then */
}

static void build_holdings(void) {
    for (int i = 0; i < n; i++) {
        int ord[4]; for (int t = 0; t < k[i]; t++) ord[t] = gs[i][t];
        /* rank by value desc, tie by good index */
        for (int a = 0; a < k[i]; a++) for (int b = a + 1; b < k[i]; b++) {
            int ga = ord[a], gb = ord[b];
            if (v[i][gb] > v[i][ga] || (v[i][gb] == v[i][ga] && gb < ga)) { ord[a] = gb; ord[b] = ga; }
        }
        int top = v[i][ord[0]];
        nh[i] = 0;
        for (int sub = 0; sub < (1 << k[i]); sub++) {
            int S = 0; for (int t = 0; t < k[i]; t++) if (sub >> t & 1) S |= 1 << gs[i][t];
            int sz = popc(S), vs = val(i, S), lev = -1;
            if (sz == 0) lev = 0;
            else if (sz == 1) { for (int t = 0; t < k[i]; t++) if (S == 1 << ord[t]) lev = 4 - t; }
            else {
                if (vs > top) {
                    int minimal = 1;
                    for (int T = (S - 1) & S; T; T = (T - 1) & S) if (val(i, T) > top) { minimal = 0; break; }
                    if (minimal) lev = 5;
                }
                if (lev < 0 && k[i] == 4 && S == ((1 << ord[2]) | (1 << ord[3])) && vs > v[i][ord[1]]) lev = 3;
            }
            if (lev < 0) continue;
            int want = 0;
            for (int t = 0; t < k[i]; t++) { int g = gs[i][t]; if (!(S >> g & 1) && v[i][g] > vs) want |= 1 << g; }
            H[i][nh[i]++] = (Hold){S, vs, lev, want, sz};
        }
    }
}

/* states */
#define MAXST 200000
static unsigned char st[MAXST][MAXN]; static int nst;
static int cur[MAXN];
static void rec(int i, int used) {
    if (i == n) {
        int W = 0, S1 = 0;
        for (int j = 0; j < n; j++) { W |= H[j][cur[j]].want; if (H[j][cur[j]].sz == 1) S1 |= H[j][cur[j]].mask; }
        if ((W & ~S1) != 0) return;
        for (int j = 0; j < n; j++) if (H[j][cur[j]].sz >= 2)
            for (int x = 0; x < n; x++) if (x != j && theta(x, H[j][cur[j]].mask) > H[x][cur[x]].val) return;
        if (nst < MAXST) { for (int j = 0; j < n; j++) st[nst][j] = cur[j]; nst++; }
        return;
    }
    for (int h = 0; h < nh[i]; h++) if (!(H[i][h].mask & used)) { cur[i] = h; rec(i + 1, used | H[i][h].mask); }
}

/* completion search */
static int X[MAXN], Jg[MAXM], nJ;
static int efx0(void) {
    for (int i = 0; i < n; i++) { int vi = val(i, X[i]);
        for (int j = 0; j < n; j++) if (i != j && theta(i, X[j]) > vi) return 0; }
    return 1;
}
static int comp_rec(int t) {
    if (t == nJ) return efx0();
    for (int i = 0; i < n; i++) { X[i] |= 1 << Jg[t]; if (comp_rec(t + 1)) return 1; X[i] &= ~(1 << Jg[t]); }
    return 0;
}
static int completable(int s) {
    int held = 0;
    for (int j = 0; j < n; j++) { X[j] = H[j][st[s][j]].mask; held |= X[j]; }
    nJ = 0; for (int g = 0; g < m; g++) if (!(held >> g & 1)) Jg[nJ++] = g;
    return comp_rec(0);
}

int main(int argc, char **argv) {
    int chunk = argc > 1 ? atoi(argv[1]) : 0, nch = argc > 2 ? atoi(argv[2]) : 1;
    long long prof = 0, every_fail = 0, some_fail = 0, nstates = 0, nmax = 0; int printed = 0;
    if (scanf("%d %d", &n, &m) != 2) return 1;
    for (int i = 0; i < n; i++) { scanf("%d", &k[i]); R[i] = 0; for (int t = 0; t < k[i]; t++) { scanf("%d", &gs[i][t]); R[i] |= 1 << gs[i][t]; } }
    for (int i = 0; i < n; i++) { scanf("%d", &nopt[i]); for (int o = 0; o < nopt[i]; o++) for (int t = 0; t < k[i]; t++) scanf("%d", &opt[i][o][t]); }
    long long total = 1; for (int i = 0; i < n; i++) total *= nopt[i];
    for (long long idx = chunk; idx < total; idx += nch) {
        long long r = idx;
        memset(v, 0, sizeof v);
        for (int i = n - 1; i >= 0; i--) { int o = r % nopt[i]; r /= nopt[i]; for (int t = 0; t < k[i]; t++) v[i][gs[i][t]] = opt[i][o][t]; }
        prof++;
        build_holdings();
        nst = 0; rec(0, 0); nstates += nst;
        int best = -1;
        for (int s = 0; s < nst; s++) { int L = 0; for (int j = 0; j < n; j++) L += H[j][st[s][j]].lev; if (L > best) best = L; }
        int any_ok = 0, any_bad = 0;
        for (int s = 0; s < nst; s++) {
            int L = 0; for (int j = 0; j < n; j++) L += H[j][st[s][j]].lev;
            if (L != best) continue;
            int dom = 0;
            for (int u = 0; u < nst && !dom; u++) {
                int L2 = 0; for (int j = 0; j < n; j++) L2 += H[j][st[u][j]].lev;
                if (L2 != best) continue;
                int ge = 1, gt = 0;
                for (int j = 0; j < n; j++) { int a = H[j][st[u][j]].val, b = H[j][st[s][j]].val; if (a < b) ge = 0; if (a > b) gt = 1; }
                if (ge && gt) dom = 1;
            }
            if (dom) continue;
            nmax++;
            if (completable(s)) any_ok = 1; else {
                any_bad = 1;
                if (printed < 3) { printed++;
                    printf("FAIL profile %lld:", idx);
                    for (int i = 0; i < n; i++) { printf(" ["); for (int t = 0; t < k[i]; t++) printf("%d%s", v[i][gs[i][t]], t + 1 < k[i] ? "," : ""); printf("]"); }
                    printf(" state:"); for (int j = 0; j < n; j++) printf(" %x", H[j][st[s][j]].mask); printf("\n"); }
            }
        }
        if (any_bad) every_fail++;
        if (!any_ok) some_fail++;
    }
    printf("profiles %lld states %lld maxima %lld every_fail %lld some_fail %lld\n", prof, nstates, nmax, every_fail, some_fail);
    return 0;
}
