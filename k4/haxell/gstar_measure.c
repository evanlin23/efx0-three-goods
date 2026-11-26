/* Candidate measures for a one-step lemma behind CONN_2 (k4/haxell.md §6).

   For a measure mu = (|pool|, phi), compared lexicographically, the one-step lemma reads: from every partial EFX0
   allocation s with a nonempty pool, some step of at most two generic local moves (move, swap, trade; intermediate
   state arbitrary) leads to a partial EFX0 allocation t with mu(t) < mu(s).  It implies CONN_2 by well-foundedness
   (mu takes finitely many values).  This program enumerates every partial EFX0 allocation of each instance (as
   gstar.c) and, for each candidate phi, counts the *stuck* states: nonempty pool and no such step.  phi = 0 is AUG_2
   itself (only the pool may fall).  A candidate with no stuck state on every instance survives.

   phi:  0  none (AUG_2)
         1  -sum_i v_i(X_i)                                 utilitarian welfare, maximized
         2  leximin: the ascending vector of v_i(X_i), maximized lexicographically
         3  sum_j |X_j|^2, minimized (spread the goods)
         4  -sum_j |X_j|^2 (concentrate the goods)
         5  number of envy pairs v_i(X_j) > v_i(X_i), minimized
         6  number of allocated goods held by an agent that values them 0, minimized
         7  minus the number of victim-free placements (g in pool, agent j: X_j + g keeps EFX0), maximized
         8  blockedness of placements: the sum over ordered pairs (i, j), i != j, of the least strong-envy excess
            max(0, v_i(X_j + g) - min_{X_j + g} v_i - v_i(X_i)) over pool goods g, minimized
         9  -sum_i |X_i cap R_i| (relevant goods held by a valuer), maximized
        10-18  welfare (phi 1) first, ties broken by phi 2, 4, 3, 8, 7, 5, 6, 9; and 18: leximin (phi 2), then welfare
   Input as gstar.c.  Output per instance: n m states, then "phiK stuck N" for each K, and one stuck state for the
   first phi with one.  With argument 3, a step may be a composite of three moves (the third pass runs only on states
   still stuck after two).  With ROT = 1 a rotation of the bundles along any cycle of agents also counts as one local
   move.  With SUB = 1, giving a set of goods of one holder (an agent or the pool) to one agent is also one move.
   cc -O2 -o gstar_measure gstar_measure.c;  ./gstar_measure [RADIUS=2] [ROT=0] [ONLY=-1] [SUB=0] < input */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 6
#define MAXM 11
#define NPHI 19
static int n, m;
static long val[MAXN][MAXM];
static long NS;
static unsigned char *ok;
static int RADIUS = 2, ROT = 0, ONLY = -1, SUB = 0;
static int ncyc, cyclen[512], cyc[512][MAXN];
static long stuck3fixed[NPHI];

static void decode(long s, int *own) { for (int g = 0; g < m; g++) { own[g] = s % (n + 1); s /= (n + 1); } }
static long encode(const int *own) { long s = 0; for (int g = m - 1; g >= 0; g--) s = s * (n + 1) + own[g]; return s; }
static int poolsz(const int *own) { int c = 0; for (int g = 0; g < m; g++) c += own[g] == n; return c; }
static int efx0(const int *own) {
    long tot[MAXN][MAXN], mn[MAXN][MAXN]; int cnt[MAXN];
    for (int j = 0; j < n; j++) { cnt[j] = 0; for (int i = 0; i < n; i++) { tot[i][j] = 0; mn[i][j] = -1; } }
    for (int g = 0; g < m; g++) { int j = own[g]; if (j == n) continue; cnt[j]++;
        for (int i = 0; i < n; i++) { long x = val[i][g]; tot[i][j] += x; if (mn[i][j] < 0 || x < mn[i][j]) mn[i][j] = x; } }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        if (j != i && cnt[j] >= 2 && tot[i][j] - mn[i][j] > tot[i][i]) return 0;
    return 1;
}
/* phi as a vector of up to MAXN+1 longs, compared lexicographically (smaller is better) */
typedef struct { long x[MAXN + 1]; } Phi;
static int cmpphi(const Phi *a, const Phi *b) { for (int t = 0; t <= MAXN; t++) { if (a->x[t] < b->x[t]) return -1; if (a->x[t] > b->x[t]) return 1; } return 0; }
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
static void phi1(int K, const int *own, Phi *out);
static void phi(int K, const int *own, Phi *out) {
    static const int tie[] = {2, 4, 3, 8, 7, 5, 6, 9};
    if (K >= 10 && K <= 17) {       /* welfare, then the tie-breaker, packed as (W, tie...) */
        Phi a, b; phi1(1, own, &a); phi1(tie[K - 10], own, &b);
        memset(out, 0, sizeof *out); out->x[0] = a.x[0];
        for (int t = 1; t <= MAXN; t++) out->x[t] = b.x[t - 1];
        return; }
    if (K == 18) {                  /* leximin, then welfare (leximin uses n slots) */
        Phi a, b; phi1(2, own, &a); phi1(1, own, &b); *out = a; out->x[n] = b.x[0]; return; }
    phi1(K, own, out);
}
static void phi1(int K, const int *own, Phi *out) {
    memset(out, 0, sizeof *out);
    long hold[MAXN]; int sz[MAXN];
    for (int i = 0; i < n; i++) { hold[i] = 0; sz[i] = 0; }
    for (int g = 0; g < m; g++) if (own[g] < n) { hold[own[g]] += val[own[g]][g]; sz[own[g]]++; }
    if (K == 0) return;
    if (K == 1) { long s = 0; for (int i = 0; i < n; i++) s += hold[i]; out->x[0] = -s; return; }
    if (K == 2) { long h[MAXN]; memcpy(h, hold, sizeof(long) * n); qsort(h, n, sizeof(long), cmpl);
        for (int i = 0; i < n; i++) out->x[i] = -h[i]; return; }
    if (K == 3 || K == 4) { long s = 0; for (int i = 0; i < n; i++) s += (long)sz[i] * sz[i]; out->x[0] = K == 3 ? s : -s; return; }
    if (K == 5) { long c = 0; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (j != i) {
            long v = 0; for (int g = 0; g < m; g++) if (own[g] == j) v += val[i][g]; if (v > hold[i]) c++; }
        out->x[0] = c; return; }
    if (K == 6) { long c = 0; for (int g = 0; g < m; g++) if (own[g] < n && val[own[g]][g] == 0) c++; out->x[0] = c; return; }
    if (K == 7) { long c = 0; int o[MAXM];
        for (int g = 0; g < m; g++) if (own[g] == n) for (int j = 0; j < n; j++) { memcpy(o, own, sizeof(int) * m); o[g] = j; if (efx0(o)) c++; }
        out->x[0] = -c; return; }
    if (K == 8) { long tot = 0;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (j != i) {
            long best = 0; int any = 0;
            for (int g = 0; g < m; g++) if (own[g] == n) {   /* X_j + g */
                long t = val[i][g], mn = val[i][g]; int c = 1;
                for (int h = 0; h < m; h++) if (own[h] == j) { t += val[i][h]; if (val[i][h] < mn) mn = val[i][h]; c++; }
                long ex = c >= 2 ? t - mn - hold[i] : 0; if (!any || ex < best) { best = ex; any = 1; } }
            if (any && best > 0) tot += best; }
        out->x[0] = tot; return; }
    if (K == 9) { long c = 0; for (int g = 0; g < m; g++) if (own[g] < n && val[own[g]][g] > 0) c++; out->x[0] = -c; return; }
}
static int nb_count; static long nb_buf[4096];
static void gen_cycles(void);
static void neighbours(const int *own) {
    int o[MAXM]; nb_count = 0;
    for (int g = 0; g < m; g++) for (int b = 0; b < n; b++) if (b != own[g]) { memcpy(o, own, sizeof(int) * m); o[g] = b; nb_buf[nb_count++] = encode(o); }
    for (int g = 0; g < m; g++) for (int h = g + 1; h < m; h++) if (own[g] != own[h]) {
        memcpy(o, own, sizeof(int) * m); o[g] = own[h]; o[h] = own[g]; nb_buf[nb_count++] = encode(o); }
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        for (int g = 0; g < m; g++) o[g] = own[g] == a ? b : own[g] == b ? a : own[g]; nb_buf[nb_count++] = encode(o); }
    if (SUB) {   /* subset transfers: a set of two or more goods of one holder (an agent or the pool) to another agent */
        for (int h = 0; h <= n; h++) {
            int gs[MAXM], c = 0; for (int g = 0; g < m; g++) if (own[g] == h) gs[c++] = g;
            if (c < 2) continue;
            for (int mask = 1; mask < (1 << c); mask++) { if (__builtin_popcount(mask) < 2) continue;
                for (int b = 0; b < n; b++) { if (b == h) continue;
                    memcpy(o, own, sizeof(int) * m); for (int t = 0; t < c; t++) if (mask >> t & 1) o[gs[t]] = b;
                    if (nb_count < 4000) nb_buf[nb_count++] = encode(o); } } } }
    if (ROT) {   /* rotations of bundles along every cycle of 3 or more agents (2-cycles are the trades above) */
        for (int c = 0; c < ncyc; c++) {
            int to[MAXN]; for (int a = 0; a < n; a++) to[a] = a;
            for (int t = 0; t < cyclen[c]; t++) to[cyc[c][t]] = cyc[c][(t + 1) % cyclen[c]];
            for (int g = 0; g < m; g++) o[g] = own[g] == n ? n : to[own[g]];
            nb_buf[nb_count++] = encode(o); } }
}
static void gen_cycles(void) {
    /* every cycle a_0 -> a_1 -> ... -> a_{L-1} -> a_0 with a_0 the smallest agent, L >= 3: bundle of a_t goes to a_{t+1} */
    ncyc = 0; int perm[MAXN];
    for (int mask = 0; mask < (1 << n); mask++) {
        int L = __builtin_popcount(mask); if (L < 3) continue;
        int el[MAXN], k = 0; for (int a = 0; a < n; a++) if (mask >> a & 1) el[k++] = a;
        /* permutations of el[1..L-1] */
        int idx[MAXN]; for (int t = 0; t < L - 1; t++) idx[t] = t + 1;
        while (1) {
            perm[0] = el[0]; for (int t = 0; t < L - 1; t++) perm[t + 1] = el[idx[t]];
            cyclen[ncyc] = L; memcpy(cyc[ncyc], perm, sizeof(int) * L); ncyc++;
            int i = L - 3; while (i >= 0 && idx[i] > idx[i + 1]) i--; if (i < 0) break;
            int j = L - 2; while (idx[j] < idx[i]) j--; int tmp = idx[i]; idx[i] = idx[j]; idx[j] = tmp;
            for (int a = i + 1, b = L - 2; a < b; a++, b--) { tmp = idx[a]; idx[a] = idx[b]; idx[b] = tmp; }
        }
    }
}
int main(int argc, char **argv) {
    if (argc > 1) RADIUS = atoi(argv[1]);
    if (argc > 2) ROT = atoi(argv[2]);
    if (argc > 3) ONLY = atoi(argv[3]);   /* evaluate only phi0 and phi ONLY (the others are reported as 0); -1: all */
    if (argc > 4) SUB = atoi(argv[4]);    /* 1: a set of goods given by one holder to one agent is one move */
    while (scanf("%d %d", &n, &m) == 2) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "instance too large: n %d m %d (MAXN %d MAXM %d)\n", n, m, MAXN, MAXM); return 2; }
        memset(val, 0, sizeof val);
        for (int i = 0; i < n; i++) { int d; if (scanf("%d", &d) != 1) return 1;
            for (int t = 0; t < d; t++) { int g; long v; if (scanf("%d %ld", &g, &v) != 2) return 1; val[i][g] = v; } }
        NS = 1; for (int g = 0; g < m; g++) NS *= (n + 1);
        if (ROT) gen_cycles();
        ok = calloc(NS, 1); int own[MAXM]; long states = 0;
        for (long s = 0; s < NS; s++) { decode(s, own); if (efx0(own)) { ok[s] = 1; states++; } }
        long stuck[NPHI]; memset(stuck, 0, sizeof stuck); memset(stuck3fixed, 0, sizeof stuck3fixed); long ex[NPHI]; for (int K = 0; K < NPHI; K++) ex[K] = -1;
        for (long s = 0; s < NS; s++) {
            if (!ok[s]) continue; decode(s, own); int p = poolsz(own); if (p == 0) continue;
            Phi ps[NPHI]; for (int K = 0; K < NPHI; K++) phi(K, own, &ps[K]);
            int done[NPHI]; memset(done, 0, sizeof done); int left = NPHI;
            if (ONLY >= 0) { for (int K = 0; K < NPHI; K++) if (K != ONLY && K != 0) { done[K] = 1; left--; } }
            neighbours(own); int c1 = nb_count; long first[4096]; memcpy(first, nb_buf, sizeof(long) * c1);
            for (int pass = 0; pass < (RADIUS < 2 ? RADIUS : 2) && left; pass++)
                for (int t = 0; t < c1 && left; t++) {
                    int c2 = 1; long cand[4096];
                    if (pass == 0) cand[0] = first[t];
                    else { int o1[MAXM]; decode(first[t], o1); neighbours(o1); c2 = nb_count; memcpy(cand, nb_buf, sizeof(long) * c2); }
                    for (int w = 0; w < c2 && left; w++) { long u = cand[w]; if (!ok[u]) continue;
                        int ou[MAXM]; decode(u, ou); int pu = poolsz(ou); if (pu > p) continue;
                        for (int K = 0; K < NPHI; K++) { if (done[K]) continue;
                            int better = pu < p;
                            if (!better && K > 0) { Phi q; phi(K, ou, &q); better = cmpphi(&q, &ps[K]) < 0; }
                            if (better) { done[K] = 1; left--; } } }
                }
            if (left && RADIUS >= 3) {      /* third pass: composites of three moves, only for the measures still stuck */
                for (int t = 0; t < c1 && left; t++) { int o1[MAXM]; decode(first[t], o1); neighbours(o1);
                    int c2 = nb_count; long sec[4096]; memcpy(sec, nb_buf, sizeof(long) * c2);
                    for (int w = 0; w < c2 && left; w++) { int o2[MAXM]; decode(sec[w], o2); neighbours(o2);
                        for (int z = 0; z < nb_count && left; z++) { long u = nb_buf[z]; if (!ok[u]) continue;
                            int ou[MAXM]; decode(u, ou); int pu = poolsz(ou); if (pu > p) continue;
                            for (int K = 0; K < NPHI; K++) { if (done[K]) continue; int better = pu < p;
                                if (!better && K > 0) { Phi q; phi(K, ou, &q); better = cmpphi(&q, &ps[K]) < 0; }
                                if (better) { done[K] = 1; left--; stuck3fixed[K]++; } } } } } }
            for (int K = 0; K < NPHI; K++) if (!done[K]) { stuck[K]++; if (ex[K] < 0) ex[K] = s; }
        }
        printf("%d %d states %ld", n, m, states);
        for (int K = 0; K < NPHI; K++) printf(" phi%d %ld", K, stuck[K]);
        int K0 = -1; for (int K = 1; K < NPHI; K++) if (ex[K] >= 0) { K0 = K; break; }
        if (K0 >= 0) { decode(ex[K0], own); printf(" example_phi%d", K0); for (int g = 0; g < m; g++) printf(" %d", own[g] == n ? -1 : own[g]); }
        printf("\n"); fflush(stdout); free(ok);
    }
    return 0;
}
