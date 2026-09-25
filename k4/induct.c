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
static int agent_on[MAXN], good_on[MAXM];

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
    for (int g = 0; g < m; g++) if (good_on[g]) cnt[own[g]]++;
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

static void push(const u8 *own) {
    if (nstore == capstore) { capstore = capstore ? 2 * capstore : 1 << 16; store = realloc(store, capstore * (size_t)m); }
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

/* enumerate EFX0 allocations of the instance restricted to agent_on / good_on; result in store[0..nstore) */
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
            if ((kind[0] == 'G' || kind[0] == 'B') && scanf("%d", &d) != 1) return 1;
            /* smaller instance */
            for (int i = 0; i < n; i++) agent_on[i] = 1;
            for (int g = 0; g < m; g++) good_on[g] = 1;
            if (kind[0] == 'G' || kind[0] == 'B') good_on[d] = 0;
            if (kind[0] == 'A' || kind[0] == 'B') agent_on[w] = 0;
            enumerate(ONLYD2);
            long nE = nstore; u8 *E = malloc((size_t)(nE ? nE : 1) * m); memcpy(E, store, (size_t)nE * m);
            /* distance setup on I */
            nmov = nfree = 0;
            for (int g = 0; g < m; g++) { if (g == d) freeg[nfree++] = g; else movable[nmov++] = g; }
            target_w = w;
            long hist[8] = {0}, nd2 = 0, dw = 0; int maxr = -1, maxrd2 = -1; long worst = -1; int worstd2 = 0;
            for (long e = 0; e < nE; e++) {
                u8 *X = E + e * (size_t)m;
                int d2 = is_d2(X); nd2 += d2;
                for (int i = 0; i < n; i++) agent_on[i] = 1;
                for (int g = 0; g < m; g++) good_on[g] = 1;
                memcpy(work, X, m); if (d >= 0) work[d] = 255;
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
                            for (int g = 0; g < m && dist < best; g++) if (g != d && Y[g] != X[g]) dist++;
                            if (dist < best) best = dist;
                        }
                        r = best;           /* 1<<30 if I has no EFX0 allocation at all */
                    }
                }
                hist[r < 7 ? r : 7]++;
                if (VERBOSE && r >= 1) {
                    printf("  X' r=%d d2=%d :", r, d2);
                    for (int g = 0; g < m; g++) { if (g == d) printf(" -"); else printf(" %d", X[g]); }
                    printf("\n");
                }
                if (r > maxr) { maxr = r; if (!worstd2) worst = e; }
                if (d2 && r > maxrd2) { maxrd2 = r; worst = e; worstd2 = 1; }
            }
            printf("TASK %s %d %d | E' %ld D2 %ld | maxr %d maxrD2 %d | hist", kind, w, d, nE, nd2, maxr, maxrd2);
            for (int r = 0; r < 8; r++) printf(" %ld", hist[r]);
            printf(" | d_at_w %ld | worst", dw);
            if (worst >= 0) for (int g = 0; g < m; g++) { u8 o = E[worst * (size_t)m + g]; if (g == d) printf(" -"); else printf(" %d", o); }
            printf("\n");
            fflush(stdout);
            free(E);
        }
        free(bigE);
    }
    return 0;
}
