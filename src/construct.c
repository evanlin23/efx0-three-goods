/* Construction LB, the same steps as construct.py (see its docstring and proofs/construction.md), run on every ranking
   profile of each core read from stdin, with every output checked from the raw EFX0 definition.
   Build: gcc -O3 -march=native -o construct construct.c   (construct_run.py compiles and drives it)
   stdin:  "n m K" then K lines of 3n goods (agent i's three goods, as in frontier.py's `sets`).
   stdout, per core: "core <k> fails <f> large <l> hash <h> D <d3> <d4> ... first <profile or ->"
     fails: profiles where the construction fails or the raw check rejects its output;
     large: profiles whose output has a bundle of >= 3 goods; D: how many of those have a large bundle of size 3, 4, ...
     hash:  FNV-1a over the outputs in profile order (agent 0's ranking most significant), compared with construct.py.
   With -c, also "cert <k> <c>" and c lines of m owners: allocations produced by the construction that cover every
   profile (first fit), for tools/check_certs.py.
   Raw check: for three balanced realizations of a > b > c ((4,3,2), (10,9,2), (10,6,5)), no agent i values another
   bundle of >= 2 goods, minus its least valuable good, more than its own; they must agree; at most one bundle of
   >= 3 goods. It does not use the T/P/B/C/E cases. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 9
#define MAXM 20
static int n, m;
static int trip[MAXN][3];          /* ranked goods: trip[i][0] = a_i */
static int rk[MAXN][MAXM];         /* rank of good g for agent i, 3 if irrelevant */
static uint32_t Rm[MAXN];          /* relevant goods of agent i */

static int popc(uint32_t x) { return __builtin_popcount(x); }

/* One R1 step; returns 0 if no remaining agent has <= 2 goods left. */
static int r1_step(uint32_t *A, uint32_t *G, int *Y) {
    int bi = -1, bkey = 1 << 30, bfav = -1;
    for (int i = 0; i < n; i++) if (*A >> i & 1) {
        uint32_t left = Rm[i] & *G; int c = popc(left);
        if (c > 2) continue;
        int r = 3, fav = -1;
        for (int t = 0; t < 3; t++) if (left >> trip[i][t] & 1) { r = t; fav = trip[i][t]; break; }
        int key = (r * 16 + c) * 16 + i;
        if (key < bkey) { bkey = key; bi = i; bfav = fav; }
    }
    if (bi < 0) return 0;
    Y[bi] = bfav; *A &= ~(1u << bi); if (bfav >= 0) *G &= ~(1u << bfav);
    return 1;
}

static int held_of(int k, const int *Y) { return Y[k] >= 0 ? rk[k][Y[k]] : 3; }

static uint32_t need_mask(uint32_t done, uint32_t up, const int *Y) {
    uint32_t NA = 0;
    for (int k = 0; k < n; k++) if ((done >> k & 1) && !(up >> k & 1)) {
        int h = held_of(k, Y);
        for (int t = 0; t < h; t++) NA |= 1u << trip[k][t];
    }
    return NA;
}

/* |NA| over processed agents after the certain upgrades (construct.py: na_count). */
static int na_count(uint32_t A, uint32_t G, const int *Y) {
    uint32_t done = ((1u << n) - 1) & ~A, valued = 0, up = 0;
    for (int k = 0; k < n; k++) if (A >> k & 1) valued |= Rm[k];
    uint32_t junk = G & ~valued;
    for (;;) {
        uint32_t NA = need_mask(done, up, Y);
        int found = -1;
        for (int k = 0; k < n; k++)
            if ((done >> k & 1) && !(up >> k & 1) && held_of(k, Y) == 1 && (junk >> trip[k][2] & 1) && !(NA >> trip[k][1] & 1)) { found = k; break; }
        if (found < 0) return popc(NA);
        up |= 1u << found; junk &= ~(1u << trip[found][2]);
    }
}

static void phase1(int *Y, uint32_t *J) {
    uint32_t A = (1u << n) - 1, G = (m == 32) ? 0xffffffffu : ((1u << m) - 1);
    for (int i = 0; i < n; i++) Y[i] = -1;
    while (A) {
        if (r1_step(&A, &G, Y)) continue;
        int bi = -1, bs = 1 << 30;
        for (int i = 0; i < n; i++) if (A >> i & 1) {
            uint32_t A2 = A & ~(1u << i), G2 = G & ~(1u << trip[i][0]); int Y2[MAXN];
            memcpy(Y2, Y, sizeof(int) * n); Y2[i] = trip[i][0];
            while (A2 && r1_step(&A2, &G2, Y2)) ;
            int s = na_count(A2, G2, Y2) * 16 + i;
            if (s < bs) { bs = s; bi = i; }
        }
        Y[bi] = trip[bi][0]; A &= ~(1u << bi); G &= ~(1u << trip[bi][0]);
    }
    *J = G;
}

/* Phase 2; returns 1 and fills X, or 0 if the construction fails. */
static int phase2(const int *Y, uint32_t J, int *X) {
    int held[MAXN]; uint32_t done = (1u << n) - 1, up = 0;
    for (int k = 0; k < n; k++) held[k] = held_of(k, Y);
    for (;;) {
        uint32_t NA = need_mask(done, up, Y);
        int found = -1;
        for (int k = 0; k < n; k++)
            if (!(up >> k & 1) && held[k] == 1 && (J >> trip[k][2] & 1) && !(NA >> trip[k][1] & 1)) { found = k; break; }
        if (found < 0) break;
        up |= 1u << found; J &= ~(1u << trip[found][2]);
    }
    uint32_t NA = need_mask(done, up, Y);
    int frozen[MAXN], cap[MAXN], sumcap = 0;
    for (int k = 0; k < n; k++) {
        frozen[k] = Y[k] >= 0 && (NA >> Y[k] & 1);
        cap[k] = (frozen[k] || (up >> k & 1)) ? 0 : (Y[k] >= 0 ? 1 : 2);
        sumcap += cap[k];
    }
    int Jl[MAXM], nj = 0;
    for (int g = 0; g < m; g++) if (J >> g & 1) Jl[nj++] = g;
    int owner = -1; uint32_t JL = 0;
    if (nj > sumcap) {
        int ok = 0;
        for (int o = 0; o < n && !ok; o++) {
            if (frozen[o]) continue;
            int need = nj - (sumcap - cap[o]);
            uint32_t L0 = 0;
            if (Y[o] >= 0) L0 |= 1u << Y[o];
            if (up >> o & 1) L0 |= 1u << trip[o][2];
            int idx[MAXM];
            for (int t = 0; t < need; t++) idx[t] = t;
            for (;;) {                                 /* combinations of Jl in lexicographic order */
                uint32_t L = L0, S = 0;
                for (int t = 0; t < need; t++) S |= 1u << Jl[idx[t]];
                L |= S;
                int bad = 0;
                for (int k = 0; k < n && !bad; k++)
                    if (k != o && held[k] == 0 && !(up >> k & 1) && (L >> trip[k][1] & 1) && (L >> trip[k][2] & 1)) bad = 1;
                if (!bad) { ok = 1; owner = o; JL = S; break; }
                int t = need - 1;
                while (t >= 0 && idx[t] == nj - need + t) t--;
                if (t < 0) break;
                idx[t]++;
                for (int u = t + 1; u < need; u++) idx[u] = idx[u - 1] + 1;
            }
        }
        if (!ok) return 0;
    }
    for (int g = 0; g < m; g++) X[g] = -1;
    for (int k = 0; k < n; k++) if (Y[k] >= 0) X[Y[k]] = k;
    for (int k = 0; k < n; k++) if (up >> k & 1) X[trip[k][2]] = k;
    int rest[MAXM], nr = 0;
    for (int t = 0; t < nj; t++) { if (JL >> Jl[t] & 1) X[Jl[t]] = owner; else rest[nr++] = Jl[t]; }
    for (int k = 0; k < n; k++) {
        if (k == owner) continue;
        for (int s = 0; s < cap[k]; s++) if (nr) X[rest[--nr]] = k;
    }
    return 1;
}

static const int REAL[3][3] = {{4, 3, 2}, {10, 9, 2}, {10, 6, 5}};

/* Raw EFX0 check of X for agent i with ranking t (3 goods); returns 1 safe, 0 unsafe, -1 realizations disagree. */
static int raw_agent(const int *X, int i, const int *t) {
    int res = -2;
    for (int r = 0; r < 3; r++) {
        int v[MAXM]; memset(v, 0, sizeof v);
        for (int q = 0; q < 3; q++) v[t[q]] = REAL[r][q];
        int sum[MAXN] = {0}, mn[MAXN], sz[MAXN] = {0};
        for (int j = 0; j < n; j++) mn[j] = 1 << 30;
        for (int g = 0; g < m; g++) { int j = X[g]; sum[j] += v[g]; sz[j]++; if (v[g] < mn[j]) mn[j] = v[g]; }
        int ok = 1;
        for (int j = 0; j < n; j++) if (j != i && sz[j] >= 2 && sum[j] - mn[j] > sum[i]) ok = 0;
        if (res == -2) res = ok; else if (res != ok) return -1;
    }
    return res;
}

static int raw_ok(const int *X) {
    int sz[MAXN] = {0}, big = 0;
    for (int g = 0; g < m; g++) { if (X[g] < 0 || X[g] >= n) return 0; sz[X[g]]++; }
    for (int j = 0; j < n; j++) if (sz[j] >= 3) big++;
    if (big > 1) return 0;
    for (int i = 0; i < n; i++) {
        int r = raw_agent(X, i, trip[i]);
        if (r < 0) { fprintf(stderr, "realizations disagree\n"); exit(2); }
        if (!r) return 0;
    }
    return 1;
}

static const int PERMS[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};

/* first-fit cover (for -c): safety mask of an allocation = bit 6i+k if agent i is safe under its ranking k */
static uint64_t alloc_mask(const int *X, int sets[][3]) {
    uint64_t M = 0;
    for (int i = 0; i < n; i++) for (int k = 0; k < 6; k++) {
        int t[3] = {sets[i][PERMS[k][0]], sets[i][PERMS[k][1]], sets[i][PERMS[k][2]]};
        int r = raw_agent(X, i, t);
        if (r < 0) { fprintf(stderr, "realizations disagree\n"); exit(2); }
        if (r) M |= 1ull << (6 * i + k);
    }
    return M;
}

int main(int argc, char **argv) {
    int cert = argc > 1 && !strcmp(argv[1], "-c");
    int K;
    if (scanf("%d %d %d", &n, &m, &K) != 3 || n > MAXN || m > MAXM || 6 * n > 64) { fprintf(stderr, "bad header\n"); return 1; }
    long total = 1; for (int i = 0; i < n; i++) total *= 6;
    static int covX[4096][MAXM]; static uint64_t covM[4096];
    for (int c = 0; c < K; c++) {
        int sets[MAXN][3];
        for (int i = 0; i < n; i++) for (int q = 0; q < 3; q++) if (scanf("%d", &sets[i][q]) != 1) { fprintf(stderr, "bad input\n"); return 1; }
        for (int i = 0; i < n; i++) { Rm[i] = 0; for (int q = 0; q < 3; q++) Rm[i] |= 1u << sets[i][q]; }
        long fails = 0, large = 0, D[MAXM + 1] = {0}; long firstfail = -1; int ncov = 0;
        uint64_t h = 1469598103934665603ull;
        for (long p = 0; p < total; p++) {
            int prof[MAXN]; long q = p;
            for (int i = n - 1; i >= 0; i--) { prof[i] = q % 6; q /= 6; }
            for (int i = 0; i < n; i++) {
                for (int t = 0; t < 3; t++) trip[i][t] = sets[i][PERMS[prof[i]][t]];
                for (int g = 0; g < m; g++) rk[i][g] = 3;
                for (int t = 0; t < 3; t++) rk[i][trip[i][t]] = t;
            }
            int Y[MAXN], X[MAXM]; uint32_t J;
            phase1(Y, &J);
            int ok = phase2(Y, J, X);
            if (!ok) for (int g = 0; g < m; g++) X[g] = -1;
            for (int g = 0; g < m; g++) { h ^= (uint64_t)(X[g] + 1); h *= 1099511628211ull; }
            if (!ok || !raw_ok(X)) { fails++; if (firstfail < 0) firstfail = p; continue; }
            int sz[MAXN] = {0}, mx = 0;
            for (int g = 0; g < m; g++) sz[X[g]]++;
            for (int j = 0; j < n; j++) if (sz[j] > mx) mx = sz[j];
            if (mx >= 3) { large++; D[mx]++; }
            if (cert) {
                uint64_t P = 0; for (int i = 0; i < n; i++) P |= 1ull << (6 * i + prof[i]);
                int cov = 0;
                for (int t = 0; t < ncov && !cov; t++) if ((covM[t] & P) == P) cov = 1;
                if (!cov) {
                    if (ncov == 4096) { fprintf(stderr, "cover too large\n"); return 1; }
                    memcpy(covX[ncov], X, sizeof(int) * m); covM[ncov] = alloc_mask(X, sets);
                    if (!(covM[ncov] & P) || (covM[ncov] & P) != P) { fprintf(stderr, "mask mismatch\n"); return 1; }
                    ncov++;
                }
            }
        }
        printf("core %d fails %ld large %ld hash %016llx D", c, fails, large, (unsigned long long)h);
        for (int d = 3; d <= m; d++) printf(" %ld", D[d]);
        if (firstfail >= 0) {
            printf(" first");
            long q = firstfail; int prof[MAXN];
            for (int i = n - 1; i >= 0; i--) { prof[i] = q % 6; q /= 6; }
            for (int i = 0; i < n; i++) printf(" %d", prof[i]);
        } else printf(" first -");
        printf("\n");
        if (cert) {
            printf("cert %d %d\n", c, ncov);
            for (int t = 0; t < ncov; t++) { for (int g = 0; g < m; g++) printf("%d ", covX[t][g]); printf("\n"); }
        }
        fflush(stdout);
    }
    return 0;
}
