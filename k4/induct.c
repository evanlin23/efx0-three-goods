/* k4/induct.c: the insertion lemma of k4/induct.md, tested by brute force.

For an instance I (n agents, m goods, integer additive values) and a task, enumerate every EFX0 allocation X' of the
smaller instance and measure how far it is from an EFX0 allocation of I.

Tasks:
  G w d   remove good d (d relevant to agent w). I - d has the goods M - {d}; every agent's values are restricted.
          For X' EFX0 on I - d, r(X') = min over EFX0 allocations X of I of the number of goods g != d with
          X(g) != X'(g) (d itself is placed freely).
  A w     remove agent w (its goods stay; nobody else's values change). For X' EFX0 on I - w (agents other than w),
          r(X') = min over EFX0 X of I of the number of goods g with X(g) != X'(g) (goods given to w count).
  B w d   remove agent w and good d (d relevant to w). Distance as for A, over the goods other than d.

Input (stdin), repeated:  n m  /  n lines of m values  /  t  /  t task lines.   Output: one line per task:
  TASK kind w d | E' <#EFX0 X'> D2 <#D2 X'> | maxr <max r over X'> maxrD2 <max r over D2 X'> | hist r0 r1 r2 r3+
  | d_at_w <#X' with r = 0 where some zero-repair X gives d to w> | worst <owner vector of a worst X' (D2 first)>
r is computed exactly: direct neighbourhood search up to radius RMAX (default 3, option -r), then a scan of every
EFX0 allocation of I for the X' left; with -q the scan is skipped and those X' count as r = RMAX + 1 ("RMAX+").

Options: -r R (radius of the direct search), -q (no full scan), -D (only D2 X' are enumerated: at most one bundle of
more than 2 goods), -v (print every X' with r >= 1).

The EFX0 test is the raw definition: v_i(X_i) >= v_i(X_j) - min_{g in X_j} v_i(g) for all i != j with |X_j| >= 2. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 24
#define MAXM 64
typedef unsigned char u8;

static int n, m;
static long long v[MAXN][MAXM];
static int RMAX = 3, QUICK = 0, ONLYD2 = 0, VERBOSE = 0;

/* ---------- raw EFX0 test of a complete allocation (owner vector; absent agents/goods excluded) ---------- */
static int agent_on[MAXN], good_on[MAXM], small_on[MAXN];   /* small_on: the agents of the smaller instance */

static int efx0(const u8 *own) {
    static long long S[MAXN][MAXN], mn[MAXN][MAXN];
    static int cnt[MAXN];
    for (int j = 0; j < n; j++) { cnt[j] = 0; for (int i = 0; i < n; i++) { S[i][j] = 0; mn[i][j] = (long long)4e18; } }
    for (int g = 0; g < m; g++) {
        if (!good_on[g]) continue;
        int j = own[g]; cnt[j]++;
        for (int i = 0; i < n; i++) { S[i][j] += v[i][g]; if (v[i][g] < mn[i][j]) mn[i][j] = v[i][g]; }
    }
    for (int i = 0; i < n; i++) if (agent_on[i])
        for (int j = 0; j < n; j++) if (j != i && agent_on[j] && cnt[j] >= 2)
            if (S[i][i] < S[i][j] - mn[i][j]) return 0;
    return 1;
}

static int is_d2(const u8 *own) {
    int cnt[MAXN] = {0}, big = 0;
    for (int g = 0; g < m; g++) if (own[g] != 255) cnt[own[g]]++;
    for (int j = 0; j < n; j++) if (cnt[j] > 2) big++;
    return big <= 1;
}

/* ---------- enumeration of every EFX0 allocation by backtracking with a sound prune ---------- */
/* Goods are assigned in a fixed order. Once every good relevant to agent i is assigned, v_i(X_i) is final, and
   theta_i(X_j) = v_i(X_j) - min_{X_j} v_i can only grow when goods are added (monotone under inclusion), so a violation
   for i is final. */
static int order[MAXM], no;               /* goods in assignment order */
static int done_at[MAXN];                 /* agent i is complete after this many assigned goods */
static long long S[MAXN][MAXN], MN[MAXN][MAXN];
static int CNT[MAXN];
static u8 cur[MAXM];
static u8 *store; static long nstore, capstore;
static int d2only;

static void push(const u8 *own) {          /* capstore is the capacity in bytes (m changes between instances) */
    if ((nstore + 1) * (size_t)m > (size_t)capstore) {
        capstore = capstore ? 2 * capstore : 1 << 20;
        while ((nstore + 1) * (size_t)m > (size_t)capstore) capstore *= 2;
        store = realloc(store, (size_t)capstore);
        if (!store) { fprintf(stderr, "out of memory\n"); exit(2); }
    }
    memcpy(store + nstore * (size_t)m, own, m); nstore++;
}

static int check_agent(int i) {
    for (int j = 0; j < n; j++) if (j != i && agent_on[j] && CNT[j] >= 2)
        if (S[i][i] < S[i][j] - MN[i][j]) return 0;
    return 1;
}

static void rec(int k) {
    if (k == no) { push(cur); return; }
    int g = order[k];
    for (int j = 0; j < n; j++) {
        if (!agent_on[j]) continue;
        if (d2only && CNT[j] == 2) {         /* j would become a second big bundle? */
            int big = 0; for (int x = 0; x < n; x++) if (CNT[x] > 2) big++;
            if (big >= 1) continue;
        }
        long long saveS[MAXN], saveM[MAXN];
        for (int i = 0; i < n; i++) { saveS[i] = S[i][j]; saveM[i] = MN[i][j]; S[i][j] += v[i][g]; if (v[i][g] < MN[i][j]) MN[i][j] = v[i][g]; }
        CNT[j]++; cur[g] = (u8)j;
        int ok = 1;
        for (int i = 0; i < n && ok; i++) if (agent_on[i] && done_at[i] <= k + 1) ok = check_agent(i);
        if (ok) rec(k + 1);
        CNT[j]--;
        for (int i = 0; i < n; i++) { S[i][j] = saveS[i]; MN[i][j] = saveM[i]; }
    }
}

/* Early-exit search for an EFX0 allocation in which nobody envies agent ps_w (and, with d2only, D2). Same order and
   prune as rec(), plus: once agent j is complete, v_j(X_j) is final and v_j(X_w) can only grow, so v_j(X_w) > v_j(X_j)
   is final. Returns 1 as soon as one is found (left in cur[]). */
static int ps_w;
static int rec_ps(int k) {
    if (k == no) return 1;
    int g = order[k];
    for (int j = 0; j < n; j++) {
        if (!agent_on[j]) continue;
        if (d2only && CNT[j] == 2) {
            int big = 0; for (int x = 0; x < n; x++) if (CNT[x] > 2) big++;
            if (big >= 1) continue;
        }
        long long saveS[MAXN], saveM[MAXN];
        for (int i = 0; i < n; i++) { saveS[i] = S[i][j]; saveM[i] = MN[i][j]; S[i][j] += v[i][g]; if (v[i][g] < MN[i][j]) MN[i][j] = v[i][g]; }
        CNT[j]++; cur[g] = (u8)j;
        int ok = 1;
        for (int i = 0; i < n && ok; i++) if (agent_on[i] && done_at[i] <= k + 1) {
            ok = check_agent(i);
            if (ok && i != ps_w && S[i][ps_w] > S[i][i]) ok = 0;
        }
        if (ok && rec_ps(k + 1)) { CNT[j]--; for (int i = 0; i < n; i++) { S[i][j] = saveS[i]; MN[i][j] = saveM[i]; } return 1; }
        CNT[j]--;
        for (int i = 0; i < n; i++) { S[i][j] = saveS[i]; MN[i][j] = saveM[i]; }
    }
    return 0;
}

/* enumerate EFX0 allocations of the instance restricted to agent_on / good_on; result in store[0..nstore) */
static void setup_order(void) {
    int seen[MAXM] = {0}; no = 0;
    for (int i = 0; i < n; i++) if (agent_on[i])
        for (int g = 0; g < m; g++) if (good_on[g] && v[i][g] > 0 && !seen[g]) { seen[g] = 1; order[no++] = g; }
    for (int g = 0; g < m; g++) if (good_on[g] && !seen[g]) { seen[g] = 1; order[no++] = g; }
    for (int i = 0; i < n; i++) {
        done_at[i] = 0;
        for (int k = 0; k < no; k++) if (v[i][order[k]] > 0) done_at[i] = k + 1;
    }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { S[i][j] = 0; MN[i][j] = (long long)4e18; }
    for (int j = 0; j < n; j++) CNT[j] = 0;
    memset(cur, 255, sizeof cur);
}

static int ps_search(int w, int onlyd2) { d2only = onlyd2; ps_w = w; setup_order(); return rec_ps(0); }

static void enumerate(int onlyd2) {
    nstore = 0; d2only = onlyd2;
    /* order: agents by index, each contributes its relevant goods not yet listed; then the rest */
    int seen[MAXM] = {0}; no = 0;
    for (int i = 0; i < n; i++) if (agent_on[i])
        for (int g = 0; g < m; g++) if (good_on[g] && v[i][g] > 0 && !seen[g]) { seen[g] = 1; order[no++] = g; }
    for (int g = 0; g < m; g++) if (good_on[g] && !seen[g]) { seen[g] = 1; order[no++] = g; }
    for (int i = 0; i < n; i++) {
        done_at[i] = 0;
        for (int k = 0; k < no; k++) if (v[i][order[k]] > 0) done_at[i] = k + 1;
    }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { S[i][j] = 0; MN[i][j] = (long long)4e18; }
    for (int j = 0; j < n; j++) CNT[j] = 0;
    memset(cur, 255, sizeof cur);
    for (int g = 0; g < m; g++) if (!good_on[g]) cur[g] = 255;
    rec(0);
}

/* ---------- repair distance ---------- */
/* Direct search: does some EFX0 allocation of I lie within distance r of X' (goods in 'free' are placed freely)?
   Implemented as: choose the placement of the free goods, and up to r moved goods with new owners. */
static int movable[MAXM], nmov;          /* goods counted by the distance */
static int freeg[MAXM], nfree;           /* goods placed freely (not counted) */
static u8 work[MAXM];
static int found_d_at_w, target_w;

static int try_free(int k) {             /* place free goods, then test */
    if (k == nfree) return efx0(work);
    int g = freeg[k], any = 0;
    for (int j = 0; j < n; j++) {
        if (!agent_on[j]) continue;
        work[g] = (u8)j;
        if (try_free(k + 1)) { any = 1; if (j == target_w) found_d_at_w = 1; }
    }
    work[g] = 255;
    return any;
}

static int try_moves(int start, int left) {
    if (try_free(0)) return 1;
    if (left == 0) return 0;
    for (int k = start; k < nmov; k++) {
        int g = movable[k]; u8 old = work[g];
        for (int j = 0; j < n; j++) {
            if (!agent_on[j] || j == old) continue;
            work[g] = (u8)j;
            if (try_moves(k + 1, left - 1)) { work[g] = old; return 1; }
        }
        work[g] = old;
    }
    return 0;
}

/* Potentials on X' (values in the smaller instance; unassigned goods ignored). Each is maximized.
   0: v_w(X'_w)   1: -v_w(X'_w)   2: -#enviers of w   3: (-#enviers of w, v_w)   4: utilitarian sum_i v_i(X'_i)
   5: Nash welfare (#agents with positive value, then sum of logs)   6: (-#enviers of w, utilitarian)
   7: -#agents that envy someone   For agent removals (A, B) the w-potentials are 0. */
#define NPOT 8
#include <math.h>
static void features(const u8 *own, int w, int wpresent, double *f) {
    long long val[MAXN][MAXN]; int cnt[MAXN];
    for (int i = 0; i < n; i++) { cnt[i] = 0; for (int j = 0; j < n; j++) val[i][j] = 0; }
    for (int g = 0; g < m; g++) if (own[g] != 255) { cnt[own[g]]++; for (int i = 0; i < n; i++) val[i][own[g]] += v[i][g]; }
    int env = 0, enviers_any = 0; double util = 0, lg = 0; int pos = 0;
    for (int i = 0; i < n; i++) {
        if (!small_on[i]) continue;
        util += val[i][i]; if (val[i][i] > 0) { pos++; lg += log((double)val[i][i]); }
        int e = 0;
        for (int j = 0; j < n; j++) if (j != i && small_on[j] && val[i][j] > val[i][i]) e = 1;
        enviers_any += e;
        if (wpresent && i != w && val[i][w] > val[i][i]) env++;
    }
    double vw = wpresent ? (double)val[w][w] : 0;
    f[0] = vw; f[1] = -vw; f[2] = -env; f[3] = -env * 1e6 + vw; f[4] = util; f[5] = pos * 1e6 + lg;
    f[6] = -env * 1e9 + util; f[7] = -enviers_any;
}

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-r")) RMAX = atoi(argv[++a]);
        else if (!strcmp(argv[a], "-q")) QUICK = 1;
        else if (!strcmp(argv[a], "-D")) ONLYD2 = 1;
        else if (!strcmp(argv[a], "-v")) VERBOSE = 1;
    }
    while (scanf("%d %d", &n, &m) == 2) {
        for (int i = 0; i < n; i++) for (int g = 0; g < m; g++) if (scanf("%lld", &v[i][g]) != 1) return 1;
        int t; if (scanf("%d", &t) != 1) return 1;
        u8 *bigE = NULL; long nbig = -1;   /* EFX0 allocations of I, computed lazily */
        for (int q = 0; q < t; q++) {
            char kind[4]; int w, d = -1;
            if (scanf("%3s %d", kind, &w) != 2) return 1;
            if ((kind[0] == 'G' || kind[0] == 'B' || kind[0] == 'H' || kind[0] == 'V') && scanf("%d", &d) != 1) return 1;
            if (kind[0] == 'H') {       /* H w d h: X' in E(I - d) minimizing #enviers(h); does d -> h keep EFX0? */
                int h; if (scanf("%d", &h) != 1) return 1;
                for (int i = 0; i < n; i++) agent_on[i] = 1;
                for (int g = 0; g < m; g++) good_on[g] = 1;
                good_on[d] = 0;
                enumerate(0);
                for (int i = 0; i < n; i++) small_on[i] = 1;
                int best = 1 << 30; long nmin = 0, nok = 0, anyok = 0; double f[NPOT];
                for (long e = 0; e < nstore; e++) { features(store + e * (size_t)m, h, 1, f); int env = (int)(-f[2] + 0.5); if (env < best) best = env; }
                good_on[d] = 1;
                for (long e = 0; e < nstore; e++) {
                    u8 *X = store + e * (size_t)m; features(X, h, 1, f);
                    memcpy(work, X, m); work[d] = (u8)h;
                    int ok = efx0(work);
                    anyok |= ok;
                    if ((int)(-f[2] + 0.5) == best) { nmin++; nok += ok; }
                }
                printf("TASK H %d %d %d | E' %ld | minenv %d | minimizers %ld ok %ld | anyX' %ld\n", w, d, h, nstore, best, nmin, nok, anyok);
                fflush(stdout);
                continue;
            }
            if (kind[0] == 'Q') {       /* Q w [d]: PS by early-exit search on I (or on I - d if d >= 0); all X, then D2 */
                int dd; if (scanf("%d", &dd) != 1) return 1;
                for (int i = 0; i < n; i++) agent_on[i] = 1;
                for (int g = 0; g < m; g++) good_on[g] = 1;
                if (dd >= 0) good_on[dd] = 0;
                int a = ps_search(w, 0);
                int b = a ? ps_search(w, 1) : 0;
                printf("TASK Q %d %d | ps %d psD2 %d\n", w, dd, a, b);
                fflush(stdout);
                continue;
            }
            if (kind[0] == 'P') {       /* PS test: min over EFX0 X of I of #agents envying w (all X, then D2 X) */
                for (int i = 0; i < n; i++) agent_on[i] = 1;
                for (int g = 0; g < m; g++) good_on[g] = 1;
                enumerate(0);
                for (int i = 0; i < n; i++) small_on[i] = 1;
                int best = 1 << 30, bestd2 = 1 << 30; double f[NPOT];
                for (long e = 0; e < nstore; e++) {
                    u8 *X = store + e * (size_t)m; features(X, w, 1, f);
                    int env = (int)(-f[2] + 0.5);
                    if (env < best) best = env;
                    if (is_d2(X) && env < bestd2) bestd2 = env;
                }
                printf("TASK P %d | E %ld | minenv %d minenvD2 %d\n", w, nstore, best, bestd2);
                fflush(stdout);
                continue;
            }
            /* smaller instance */
            for (int i = 0; i < n; i++) agent_on[i] = 1;
            for (int g = 0; g < m; g++) good_on[g] = 1;
            if (kind[0] == 'G' || kind[0] == 'B') good_on[d] = 0;
            if (kind[0] == 'A' || kind[0] == 'B') agent_on[w] = 0;
            long long saved = 0;
            if (kind[0] == 'V') { saved = v[w][d]; v[w][d] = 0; }
            enumerate(ONLYD2);
            for (int i = 0; i < n; i++) small_on[i] = agent_on[i];
            long nE = nstore; u8 *E = malloc((size_t)(nE ? nE : 1) * m); memcpy(E, store, (size_t)nE * m);
            /* distance setup on I */
            nmov = nfree = 0;
            for (int g = 0; g < m; g++) { if (g == d && kind[0] != 'V') freeg[nfree++] = g; else movable[nmov++] = g; }
            target_w = w;
            long hist[8] = {0}, nd2 = 0, dw = 0; int maxr = -1, maxrd2 = -1; long worst = -1; int worstd2 = 0;
            int minr = 1 << 30;
            int *R = malloc(sizeof(int) * (nE ? nE : 1));
            double (*F)[NPOT] = malloc(sizeof(double) * NPOT * (nE ? nE : 1));
            u8 *D2F = malloc(nE ? nE : 1);
            int isV = kind[0] == 'V';
            for (long e = 0; e < nE; e++) features(E + e * (size_t)m, w, kind[0] == 'G' || isV, F[e]);   /* smaller instance */
            if (isV) v[w][d] = saved;
            int dfree = (d >= 0 && !isV) ? d : -1;       /* the good placed freely (not counted by the distance) */
            for (long e = 0; e < nE; e++) {
                u8 *X = E + e * (size_t)m;
                int d2 = is_d2(X); nd2 += d2; D2F[e] = (u8)d2;
                for (int i = 0; i < n; i++) agent_on[i] = 1;
                for (int g = 0; g < m; g++) good_on[g] = 1;
                memcpy(work, X, m); if (dfree >= 0) work[dfree] = 255;
                int r = -1;
                found_d_at_w = 0;
                for (int rr = 0; rr <= RMAX; rr++) {
                    if (rr == 0) { if (try_free(0)) { r = 0; break; } }
                    else if (try_moves(0, rr)) { r = rr; break; }
                }
                if (r == 0 && found_d_at_w) dw++;
                if (r < 0) {
                    if (QUICK) r = RMAX + 1;
                    else {
                        if (nbig < 0) {
                            for (int i = 0; i < n; i++) agent_on[i] = 1;
                            for (int g = 0; g < m; g++) good_on[g] = 1;
                            enumerate(0); nbig = nstore; bigE = malloc((size_t)(nbig ? nbig : 1) * m);
                            memcpy(bigE, store, (size_t)nbig * m);
                        }
                        int best = 1 << 30;
                        for (long f = 0; f < nbig; f++) {
                            u8 *Y = bigE + f * (size_t)m; int dist = 0;
                            for (int g = 0; g < m && dist < best; g++) if (g != dfree && Y[g] != X[g]) dist++;
                            if (dist < best) best = dist;
                        }
                        r = best;           /* 1<<30 if I has no EFX0 allocation at all */
                    }
                }
                hist[r < 7 ? r : 7]++; R[e] = r; if (r < minr) minr = r;
                if (VERBOSE && r >= 1) {
                    printf("  X' r=%d d2=%d :", r, d2);
                    for (int g = 0; g < m; g++) { if (g == dfree) printf(" -"); else printf(" %d", X[g]); }
                    printf("\n");
                }
                if (r > maxr) { maxr = r; if (!worstd2) worst = e; }
                if (d2 && r > maxrd2) { maxrd2 = r; worst = e; worstd2 = 1; }
            }
            printf("TASK %s %d %d | E' %ld D2 %ld | maxr %d maxrD2 %d | hist", kind, w, d, nE, nd2, maxr, maxrd2);
            for (int r = 0; r < 8; r++) printf(" %ld", hist[r]);
            int minenv = 1 << 30; for (long e = 0; e < nE; e++) { int x = (int)(-F[e][2] + 0.5); if (x < minenv) minenv = x; }
            printf(" | d_at_w %ld | minr %d minenvw %d | pot", dw, nE ? minr : -1, nE ? minenv : -1);
            for (int p = 0; p < NPOT; p++) {               /* worst r among the maximizers of potential p (all X', then D2 X') */
                for (int only = 0; only < 2; only++) {
                    double best = -1e300; int wr = -1;
                    for (long e = 0; e < nE; e++) if (!only || D2F[e]) { if (F[e][p] > best + 1e-9) { best = F[e][p]; wr = R[e]; } else if (F[e][p] > best - 1e-9 && R[e] > wr) wr = R[e]; }
                    printf(" %d", wr);
                }
            }
            printf(" | worst");
            if (worst >= 0) for (int g = 0; g < m; g++) { u8 o = E[worst * (size_t)m + g]; if (g == dfree) printf(" -"); else printf(" %d", o); }
            printf("\n");
            free(R); free(F); free(D2F);
            fflush(stdout);
            free(E);
        }
        free(bigE);
    }
    return 0;
}
