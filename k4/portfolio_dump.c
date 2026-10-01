/* k4/portfolio_dump.c -- the min-frozen class with its deficits, for the predicate portfolio (compute/k4-portfolio).
EVIDENCE tooling.

Lines 78-196 of k4/dlrt4.c (sha256 fcde494a...; the includes, the subset tables, dl2.c's enumeration of the
min-frozen pre-allocations and dl2.c's removal-only deficit eval_P) are copied here verbatim, and so are the parsing of
the input blocks, the random profile generator and the first half of profile() (up to the deficits). Nothing else of
dlrt4.c is used: no move test, no distance pass. So for the same block and options (-S, the profile list or P random
profiles) this tool evaluates exactly the profiles dlrt4.c evaluates, finds the same min-frozen class and the same
deficits (k4/portfolio.py --selftest compares the per-state deficits with dlrt4.c's -s lines).

Input (stdin): dlrt4.c's blocks (k4/gap.c's format), see dlrt4.c's header.
Options:
  -SS      seed for P > 0 (dlrt4.c's stream: the same profiles as dlrt4.c -SS)
  -fF      dump only profiles whose fewest frozen agents f >= F (default 1)
  -a       dump every evaluated profile with f >= F, also those without a state (def > 0)
Output per dumped profile (omega >= 1, f >= F, and some min-frozen P with def(P) > 0 unless -a), one line:
  "A tag p_0 .. p_{n-1} | f omega npp | b_0.b_1. .. .b_{n-1}:def ..."
  with one item per min-frozen P (b_i the bitmask of agent i's base, def 999999 = +inf), in dlrt4.c's enumeration order.
Per block: "K tag prof N om1 N small N dumped N states N maxnpp N" (profiles; with omega >= 1; with a valid P with
|NA| <= sigma; dumped; min-frozen P with def > 0 in the dumped profiles; the largest class dumped).
Build: gcc -O2 k4/portfolio_dump.c (m <= 32, n <= 16); -DWIDE for m <= 64. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
#define INF 999999
#ifdef WIDE                                         /* 64-bit masks: m <= 64 (H_3 has m = 33) */
#define MAXM 64
typedef uint64_t msk;
#define pc(x) __builtin_popcountll(x)
#define ctz(x) __builtin_ctzll(x)
#else
#define MAXM 32
typedef uint32_t msk;
#define pc(x) __builtin_popcount(x)
#define ctz(x) __builtin_ctz(x)
#endif
#define BIT(g) ((msk)1 << (g))

static int n, m, tag;
static int deg[MAXN], R[MAXN][4];
static msk Rm[MAXN], ALL;
static int K[MAXN], *dom[MAXN];
static int v[MAXN][MAXM], cur[MAXN];
static int VERB = 0, SVERB = 0, RT = 0, RO = 0; static uint64_t SEED = 1;


/* per agent: subset tables over the positions of its goods */
static int ssum[MAXN][16], smin[MAXN][16];
static int topg[MAXN], bigtop[MAXN], rk[MAXN][4];   /* rk: goods by decreasing value */
static inline int sidx(int i, msk X) { int s = 0; for (int k = 0; k < deg[i]; k++) if (X >> R[i][k] & 1) s |= 1 << k; return s; }
static inline int val(int i, msk X) { return ssum[i][sidx(i, X)]; }
/* X threatens i holding a bundle of value h: max over h' in X of v_i(X \ h') > h */
static inline int threat(int i, msk X, int h) {
    if (!X) return 0;
    int s = sidx(i, X);
    if (X & ~Rm[i]) return ssum[i][s] > h;           /* a good of X outside R_i is worth 0: remove it */
    return ssum[i][s] - smin[i][s] > h;
}
static inline msk needs(int i, msk X) {
    int b = val(i, X); msk N = 0;
    for (int k = 0; k < deg[i]; k++) { int g = R[i][k]; if (!(X >> g & 1) && v[i][g] > b) N |= BIT(g); }
    return N;
}

/* ---------- the min-frozen pre-allocations (dl2.c) ---------- */
static msk opt[MAXN][11], optN[MAXN][11]; static int optv[MAXN][11], nopt[MAXN];
static int bestf, sigma;
static unsigned char cidx[MAXN];
static unsigned char *PP = 0; static long npp = 0, capp = 0;

static int found_small;
static void dfs_small(int i, msk used, msk NA, msk S1, msk S2) {   /* is there a valid P with |NA| <= sigma? */
    if (found_small || pc(NA) > sigma || (NA & S2)) return;
    if (i == n) { if (!(NA & ~S1)) found_small = 1; return; }
    for (int t = 0; t < nopt[i] && !found_small; t++) { msk B = opt[i][t]; if (B & used) continue;
        dfs_small(i + 1, used | B, NA | optN[i][t], pc(B) == 1 ? S1 | B : S1, pc(B) == 2 ? S2 | B : S2); }
}
static void dfsP(int i, msk used, msk NA, msk S1, msk S2) {
    if (pc(NA) > bestf || (NA & S2)) return;        /* (V2): a needed good in a pair base stays there */
    if (i == n) {
        if (NA & ~S1) return;                        /* (V1)+(V2): every needed good is a one-good base */
        int f = pc(NA);
        if (f < bestf) { bestf = f; npp = 0; }
        if (npp == capp) { capp = capp ? 2 * capp : 1024; PP = realloc(PP, capp * MAXN); if (!PP) { fprintf(stderr, "oom\n"); exit(2); } }
        memcpy(PP + npp * MAXN, cidx, MAXN); npp++;
        return;
    }
    for (int t = 0; t < nopt[i]; t++) { msk B = opt[i][t]; if (B & used) continue;
        cidx[i] = (unsigned char)t;
        dfsP(i + 1, used | B, NA | optN[i][t], pc(B) == 1 ? S1 | B : S1, pc(B) == 2 ? S2 | B : S2); }
}

/* ---------- per P: deficit, owners, exposures (dl2.c) ---------- */
typedef struct {
    int def;                 /* INF = +inf */
    int bestown[MAXN];       /* per owner: least |C| - S_o(C) (INF if o frozen or no safe bundle) */
    msk frozen, J, NA;
    msk expo[MAXN];          /* agents exposed w.r.t. free owner o */
} pinfo_t;
static pinfo_t *PI = 0; static long capi = 0;

static void eval_P(const unsigned char *ix, pinfo_t *pi) {
    msk B[MAXN], N[MAXN], NA = 0, U = 0; int hv[MAXN];
    for (int i = 0; i < n; i++) { B[i] = opt[i][ix[i]]; N[i] = optN[i][ix[i]]; hv[i] = optv[i][ix[i]]; NA |= N[i]; U |= B[i]; }
    msk J = ALL & ~U, F = 0; int S = 0;
    for (int i = 0; i < n; i++) { if (pc(B[i]) == 1 && (B[i] & NA)) F |= BIT(i); else S += 2 - pc(B[i]); }
    pi->frozen = F; pi->J = J; pi->NA = NA;
    for (int o = 0; o < n; o++) { pi->bestown[o] = INF; pi->expo[o] = 0; }
    if (pc(J) <= S) { pi->def = pc(J) - S; return; }
    int best = INF;
    for (int o = 0; o < n; o++) {
        if (F >> o & 1) continue;
        msk NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= N[j];
        msk Wo = B[o] | J;
        for (int x = 0; x < n; x++) if (x != o && threat(x, Wo, hv[x])) pi->expo[o] |= BIT(x);
        int bo = INF;
        msk C = J;                                       /* every C inside J (removed junk) */
        for (;;) {
            msk X = B[o] | (J & ~C); int ok = 1;
            for (int x = 0; x < n && ok; x++) if (x != o && (pi->expo[o] >> x & 1) && threat(x, X, hv[x])) ok = 0;
            if (ok) {
                msk NA2 = NAo | needs(o, X);
                int sl = 0;
                for (int j = 0; j < n; j++) if (j != o) sl += (pc(B[j]) == 1 && (B[j] & NA2)) ? 0 : 2 - pc(B[j]);
                int d = pc(C) - sl;
                if (d < bo) bo = d;
            }
            if (!C) break;
            C = (C - 1) & J;
        }
        pi->bestown[o] = bo;
        if (bo < best) best = bo;
    }
    pi->def = best;
}

/* chain ends of frozen x: free agents reached from x by need edges (w needs the good of the current agent) */

/* ---------- per profile: the class and its deficits (the first half of dlrt4.c's profile()) ---------- */
static int FMIN = 1, ALLD = 0;
static long C_prof, C_om1, C_small, C_dumped, C_states, C_maxnpp;
static void profile(void) {
    for (int i = 0; i < n; i++) for (int k = 0; k < deg[i]; k++) v[i][R[i][k]] = dom[i][cur[i] * deg[i] + k];
    for (int i = 0; i < n; i++) {
        int d = deg[i];
        for (int s = 0; s < (1 << d); s++) { int su = 0, mn = 1 << 30; for (int k = 0; k < d; k++) if (s >> k & 1) { su += v[i][R[i][k]]; if (v[i][R[i][k]] < mn) mn = v[i][R[i][k]]; } ssum[i][s] = su; smin[i][s] = s ? mn : 0; }
        for (int k = 0; k < d; k++) rk[i][k] = R[i][k];
        for (int a = 0; a < d; a++) for (int b = a + 1; b < d; b++) if (v[i][rk[i][b]] > v[i][rk[i][a]]) { int t = rk[i][a]; rk[i][a] = rk[i][b]; rk[i][b] = t; }
        topg[i] = rk[i][0];
        bigtop[i] = d == 4 && v[i][rk[i][0]] > v[i][rk[i][1]] + v[i][rk[i][2]];
        nopt[i] = 0;
        for (int t = 0; t < (1 << d); t++) if (pc(t) <= 2) {
            msk B = 0; for (int k = 0; k < d; k++) if (t >> k & 1) B |= BIT(R[i][k]);
            opt[i][nopt[i]] = B; optN[i][nopt[i]] = needs(i, B); optv[i][nopt[i]] = val(i, B); nopt[i]++;
        }
    }
    C_prof++;
    sigma = 2 * n - m;
    if (sigma >= 0) { found_small = 0; dfs_small(0, 0, 0, 0, 0); if (found_small) { C_small++; return; } }
    bestf = 1 << 20; npp = 0;
    memset(cidx, 0, sizeof cidx);
    dfsP(0, 0, 0, 0, 0);
    int omega = bestf - sigma;
    if (omega <= 0) { fprintf(stderr, "internal: omega <= 0 after the small test\n"); exit(3); }
    C_om1++;
    if (bestf < FMIN) return;
    if (npp > capi) { capi = npp; PI = realloc(PI, capi * sizeof(pinfo_t)); if (!PI) { fprintf(stderr, "oom\n"); exit(2); } }
    int npos = 0;
    for (long p = 0; p < npp; p++) { eval_P(PP + p * MAXN, &PI[p]); if (PI[p].def > 0) npos++; }
    if (!npos && !ALLD) return;
    C_dumped++; C_states += npos; if (npp > C_maxnpp) C_maxnpp = npp;
    printf("A %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]);
    printf(" | %d %d %ld |", bestf, omega, npp);
    for (long p = 0; p < npp; p++) {
        const unsigned char *ix = PP + p * MAXN;
        putchar(' ');
        for (int i = 0; i < n; i++) printf(i ? ".%llu" : "%llu", (unsigned long long)opt[i][ix[i]]);
        printf(":%d", PI[p].def);
    }
    putchar('\n');
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strncmp(argv[a], "-S", 2)) SEED = strtoull(argv[a] + 2, 0, 10);
        else if (!strncmp(argv[a], "-f", 2)) FMIN = atoi(argv[a] + 2);
        else if (!strcmp(argv[a], "-a")) ALLD = 1;
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 2; }
    }
    (void)VERB; (void)SVERB; (void)RT; (void)RO;
    while (scanf("%d %d %d", &n, &m, &tag) == 3) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "n or m too large\n"); return 2; }
        ALL = m == MAXM ? ~(msk)0 : BIT(m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &deg[i]) != 1) return 2; Rm[i] = 0;
            if (deg[i] < 1 || deg[i] > 4) { fprintf(stderr, "degree\n"); return 2; }
            for (int k = 0; k < deg[i]; k++) { if (scanf("%d", &R[i][k]) != 1) return 2; Rm[i] |= BIT(R[i][k]); } }
        memset(v, 0, sizeof v);
        for (int i = 0; i < n; i++) if (scanf("%d", &K[i]) != 1) return 2;
        for (int i = 0; i < n; i++) { dom[i] = realloc(dom[i], sizeof(int) * K[i] * deg[i]);
            for (int t = 0; t < K[i] * deg[i]; t++) if (scanf("%d", &dom[i][t]) != 1) return 2; }
        long P; if (scanf("%ld", &P) != 1) return 2;
        C_prof = C_om1 = C_small = C_dumped = C_states = C_maxnpp = 0;
        if (P == 0) {
            memset(cur, 0, sizeof cur);
            for (;;) {
                profile();
                int i = n - 1; while (i >= 0 && ++cur[i] == K[i]) cur[i--] = 0;
                if (i < 0) break;
            }
        } else if (P > 0) {
            rs = SEED * 0x9E3779B97F4A7C15ull + (uint64_t)tag * 0xBF58476D1CE4E5B9ull + 1;
            for (long q = 0; q < P; q++) { for (int i = 0; i < n; i++) cur[i] = rnd() % K[i]; profile(); }
        } else {
            for (long q = 0; q < -P; q++) { for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2; profile(); }
        }
        printf("K %d prof %ld om1 %ld small %ld dumped %ld states %ld maxnpp %ld\n", tag, C_prof, C_om1, C_small, C_dumped,
               C_states, C_maxnpp);
        fflush(stdout);
    }
    return 0;
}
