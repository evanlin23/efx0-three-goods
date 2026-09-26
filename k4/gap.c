/* k4/gap.c -- the exposed-frozen gap of conjecture C4min (compute/k4-gap; k4/gap.md). EVIDENCE only.

Written from the definitions of k4/c4min.md sections 1, 3.6 and 4 (PR #41), k4/c4x.md section 1 (PR #36) and
k4/hall.md section 5 (PR #46). It shares no code with k4/c4min.c, k4/hall.c or k4/c4x.c.

For every strict profile of a k = 4 core:
  - P (the valid pre-allocations: disjoint bases B_i in R_i, |B_i| <= 2, value needs N_i(B_i), (V1) J misses NA,
    (V2) no good of a pair base in NA); f = the fewest frozen agents (= min |NA|); omega = f - (2n - m);
  - the keys (F, phi) of the min-frozen P (frozen agent x -> its one-good base phi(x); the needed set N = phi(F));
  - class: f = 0 (Theorem Z), omega <= 0, some key frozen-robust (Theorem F: v_x(U_x) <= v_x(phi(x)) for every
    frozen x, U_x = R_x \ N), or GAP (f >= 1, omega >= 1, every key has an exposed frozen agent).
For a GAP profile, every configuration of every key (c4min.md section 1): free agents y hold disjoint pairs Q_y of
M' = M \ N with Q_y & U_y admissible (every good of U_y outside it is worth less); the pool L = M' \ U Q_y.
For each configuration:
  - the valid owners (c4min.md section 1: C inside X = Q_o + L, X \ C contains an admissible set of o, |C| <= the
    frozen agents unfrozen by o's needs from X \ C, nobody x != o strongly envies X \ C holding H_x), the least |C|;
  - Phi' = (-t, r, Lambda, -p) (c4min.md section 4), pool-optimality;
  - the threat edges o -> x with C = 0, and for frozen x the class of hall.md Lemma H7 in configuration terms:
    J_P = M' minus the free bases Q_y & U_y; G: the plain test of hall.md Lemma H7 as revised in #46 (two or more
    goods of R_x in J_P, worth more to x than phi(x)); G1: not G, o a chain end of x (a free agent reached from x by need edges through frozen
    agents), x big-top (four goods, phi(x) = its top a, a > b + c) with R_x \ {a} in J_P + B_o; L: not G or G1, o not a chain end, and the goods of R_x in
    X \ B_o alone are worth at most v_x(phi(x)) (the threat uses a good of B_o); O: none of these (possible outside
    Pareto-maxima).
With -D, also the removal-only deficit (c4x.md section 1) of every min-frozen P: the profile passes if some P has
deficit <= 0; compared with "some configuration has a valid owner" (Lemma 1 of c4min.md).

Input (stdin), blocks:  n m tag / n lines "d g1 .. gd" / "K_0 .. K_{n-1}" / for each agent K_i lines of d values
(in the order of its goods) / "P" and, if P < 0, -P lines of n domain indices.  P = 0: every profile (the product of
the domains); P > 0: P random profiles (seeded by -S and tag); P < 0: the listed profiles.
Options: -D deficit cross-check; -r R record every gap profile whose index is 0 mod R (and every hard one; R = 0:
hard ones only); -C dump every configuration of every gap profile ("C {json}" lines, after a "P {json}" line);
-S seed; -M max configurations per profile (default 3000000; beyond it the profile is counted as truncated).
Output: "R {json}" profile records, "K tag counters..." per block. Categories of a gap profile: S some Phi'-maximum has
a valid owner with C empty; W not S, some Phi'-maximum has a valid owner; N no Phi'-maximum has one, some configuration
does; X no configuration has one. phibad counts the profiles where some Phi'-maximum has no valid owner (a
counterexample to Conjecture Phi', whatever the category); such profiles are always recorded.  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
#define MAXM 32
#define MAXKEY 4096
#define MAXPP 100000
#define MAXPAIR 512
typedef uint32_t msk;

static int n, m, tag;
static int deg[MAXN], R[MAXN][4];
static msk Rm[MAXN], ALL;
static int K[MAXN], *dom[MAXN];
static int v[MAXN][MAXM], cur[MAXN];
static int top[MAXN], bigtop_agent[MAXN];
static int DEF = 0, REC = 0, DUMP = 0; static long MAXCFG = 3000000; static uint64_t SEED = 1;

static inline int pc(msk x) { return __builtin_popcount(x); }
static inline int val(int i, msk S) { int s = 0; for (int k = 0; k < deg[i]; k++) if (S >> R[i][k] & 1) s += v[i][R[i][k]]; return s; }
static inline msk needs(int i, msk B) {
    int b = val(i, B); msk N = 0;
    for (int k = 0; k < deg[i]; k++) { int g = R[i][k]; if (!(B >> g & 1) && v[i][g] > b) N |= 1u << g; }
    return N;
}
/* agent i holding value h strongly envies X: max over goods of X of v_i(X minus it) > h */
static inline int envies(int i, msk X, int h) {
    if (!X) return 0;
    int s = val(i, X);
    if (X & ~Rm[i]) return s > h;
    int mn = 1 << 30; for (int k = 0; k < deg[i]; k++) if (X >> R[i][k] & 1 && v[i][R[i][k]] < mn) mn = v[i][R[i][k]];
    return s - mn > h;
}
static inline int level(int i, msk S) {
    int s = val(i, S), c = 0;
    for (int t = 0; t < (1 << deg[i]); t++) { int u = 0; for (int k = 0; k < deg[i]; k++) if (t >> k & 1) u += v[i][R[i][k]]; if (u < s) c++; }
    return c;
}
/* A inside U (for agent i) is admissible: every good of U outside A is worth less than A */
static inline int admissible(int i, msk A, msk U) {
    if (!A) return U == 0;
    int a = val(i, A);
    for (int k = 0; k < deg[i]; k++) { int g = R[i][k]; if (U >> g & 1 && !(A >> g & 1) && v[i][g] > a) return 0; }
    return 1;
}
/* the most valuable subset of at most two goods of S (for agent i; goods of S outside R_i are ignored) */
static inline msk best2(int i, msk S) {
    int b1 = -1, b2 = -1;
    for (int k = 0; k < deg[i]; k++) { int g = R[i][k]; if (!(S >> g & 1)) continue;
        if (b1 < 0 || v[i][g] > v[i][b1]) { b2 = b1; b1 = g; } else if (b2 < 0 || v[i][g] > v[i][b2]) b2 = g; }
    return (b1 >= 0 ? 1u << b1 : 0) | (b2 >= 0 ? 1u << b2 : 0);
}

/* ---------- step A: the valid pre-allocations ---------- */
static msk opt[MAXN][11], optN[MAXN][11]; static int nopt[MAXN];
static int bestf; static int nkey; static signed char keys[MAXKEY][MAXN];
static int npp; static msk ppB[MAXPP][MAXN]; static int pp_over;
static msk curB[MAXN];

static int dfs0(int i, msk used) {                 /* is there a P with NA empty? */
    if (i == n) return 1;
    for (int t = 0; t < nopt[i]; t++) if (!optN[i][t] && !(opt[i][t] & used)) if (dfs0(i + 1, used | opt[i][t])) return 1;
    return 0;
}
static void leaf(msk NA, msk S1) {
    if (NA & ~S1) return;                          /* (V1)+(V2): every needed good is a one-good base */
    int f = pc(NA);
    if (f > bestf) return;
    if (f < bestf) { bestf = f; nkey = 0; npp = 0; pp_over = 0; }
    signed char k[MAXN];
    for (int i = 0; i < n; i++) k[i] = (pc(curB[i]) == 1 && (curB[i] & NA)) ? (signed char)__builtin_ctz(curB[i]) : -1;
    int j; for (j = 0; j < nkey; j++) if (!memcmp(keys[j], k, n)) break;
    if (j == nkey) { if (nkey < MAXKEY) memcpy(keys[nkey++], k, n); else { fprintf(stderr, "MAXKEY\n"); exit(2); } }
    if (DEF) { if (npp < MAXPP) memcpy(ppB[npp++], curB, sizeof(msk) * n); else pp_over = 1; }
}
static void dfsP(int i, msk used, msk NA, msk S1) {
    if (pc(NA) > bestf) return;
    if (i == n) { leaf(NA, S1); return; }
    for (int t = 0; t < nopt[i]; t++) { msk B = opt[i][t]; if (B & used) continue;
        curB[i] = B; dfsP(i + 1, used | B, NA | optN[i][t], pc(B) == 1 ? S1 | B : S1); }
}

/* ---------- the removal-only deficit of a pre-allocation (c4x.md section 1) ---------- */
static int P_ok(msk *B) {
    msk NA = 0, U = 0, N[MAXN];
    for (int i = 0; i < n; i++) { N[i] = needs(i, B[i]); NA |= N[i]; U |= B[i]; }
    msk J = ALL & ~U;
    for (int o = 0; o < n; o++) {
        if (pc(B[o]) == 1 && (B[o] & NA)) continue;                /* the owner is free */
        msk C = J;
        for (;;) {                                                  /* every C inside J */
            msk X = B[o] | (J & ~C); int ok = 1;
            for (int x = 0; x < n && ok; x++) if (x != o && envies(x, X, val(x, B[x]))) ok = 0;
            if (ok) {
                msk NAp = needs(o, X);                                 /* the owner's needs from its bundle */
                for (int j = 0; j < n; j++) if (j != o) NAp |= N[j];
                int S = 0;
                for (int j = 0; j < n; j++) if (j != o) S += (pc(B[j]) == 1 && (B[j] & NAp)) ? 0 : 2 - pc(B[j]);
                if (pc(C) <= S) return 1;
            }
            if (!C) break;
            C = (C - 1) & J;
        }
    }
    return 0;
}

/* ---------- configurations ---------- */
typedef struct {
    long ncfg, ncompl, nsimple, nmax, nmax_compl, nmax_simple, nmax_po, nmax_t0, nmax_thr2;
    int phimax[4]; int trunc;
    long h7all[4], h7max[4]; int thrmax_all, thrmax_max;
    char ex[4096];
} pres_t;
static pres_t PR;
static signed char *KY; static msk Nm, Mp, Um[MAXN], Q[MAXN];
static int fr[MAXN], nfr; static msk pairs[MAXN][MAXPAIR]; static int npairs[MAXN];

static int phicmp(const int *a, const int *b) { for (int k = 0; k < 4; k++) if (a[k] != b[k]) return a[k] < b[k] ? -1 : 1; return 0; }

typedef struct { int phi[4], po, t; msk own0, own; int minC[MAXN]; msk Cw[MAXN]; msk thr[MAXN]; int h7[MAXN][MAXN]; msk needers[MAXM]; msk L; } cfg_t;

static void eval(cfg_t *c) {
    msk used = 0; for (int j = 0; j < nfr; j++) used |= Q[fr[j]];
    msk L = Mp & ~used; c->L = L;
    int hv[MAXN]; msk N[MAXN], B[MAXN]; int isfz[MAXN];
    for (int i = 0; i < n; i++) {
        isfz[i] = KY[i] >= 0;
        if (isfz[i]) { B[i] = 1u << KY[i]; hv[i] = v[i][KY[i]]; }
        else { B[i] = Q[i] & Um[i]; hv[i] = val(i, Q[i]); }
        N[i] = needs(i, B[i]);
    }
    for (int g = 0; g < m; g++) { c->needers[g] = 0; if (Nm >> g & 1) for (int i = 0; i < n; i++) if (N[i] >> g & 1) c->needers[g] |= 1u << i; }
    /* Phi' */
    int t = 0, r = 0, Lam = 0, p = 0, po = 1;
    for (int i = 0; i < n; i++) {
        msk U = Rm[i] & ~Nm;
        if (isfz[i]) {
            if (val(i, L & U) > hv[i]) t++;
            if (val(i, U) <= hv[i]) r++;
            Lam += level(i, B[i]); p += pc(L & U);
        } else {
            if (hv[i] >= val(i, U & ~Q[i])) r++;
            Lam += level(i, Q[i] & Rm[i]);
            if (val(i, best2(i, (Q[i] | L) & U)) > hv[i]) po = 0;
        }
    }
    c->phi[0] = -t; c->phi[1] = r; c->phi[2] = Lam; c->phi[3] = -p; c->po = po; c->t = t;
    /* J_P and chain ends (for H7) */
    msk JP = Mp; for (int j = 0; j < nfr; j++) JP &= ~B[fr[j]];
    msk ends[MAXN];
    for (int x = 0; x < n; x++) {
        ends[x] = 0; if (!isfz[x]) continue;
        msk seen = 1u << x, frontier = 1u << x;
        while (frontier) {
            int y = __builtin_ctz(frontier); frontier &= frontier - 1;
            msk z = c->needers[KY[y]];
            for (int w = 0; w < n; w++) if (z >> w & 1 && !(seen >> w & 1)) { seen |= 1u << w; if (isfz[w]) frontier |= 1u << w; else ends[x] |= 1u << w; }
        }
    }
    /* owners */
    c->own0 = 0; c->own = 0;
    for (int j = 0; j < nfr; j++) {
        int o = fr[j]; msk X = Q[o] | L; c->thr[o] = 0; c->minC[o] = -1; c->Cw[o] = 0;
        for (int x = 0; x < n; x++) if (x != o && envies(x, X, hv[x])) {
            c->thr[o] |= 1u << x;
            if (isfz[x]) {
                int a = KY[x], cls;
                msk rest = Rm[x] & ~(1u << a);
                int bt = bigtop_agent[x] && a == top[x];
                msk Bo = Q[o] & Um[o];
                if (pc(JP & Rm[x]) >= 2 && val(x, JP & Rm[x]) > hv[x]) cls = 0;   /* (G): the plain test of hall.md */
                else if ((ends[x] >> o & 1) && bt && !(rest & ~(JP | Bo))) cls = 1;
                else if (!(ends[x] >> o & 1) && val(x, (X & ~Bo) & Rm[x]) <= hv[x]) cls = 2;
                else cls = 3;
                c->h7[x][o] = cls;
            }
        }
        /* valid owner with the least |C| */
        int best = -1; msk bw = 0;
        msk C = 0;
        for (;;) {
            if (best < 0 || pc(C) < best) {
                msk Xp = X & ~C; int ok = 1;
                if (!admissible(o, best2(o, Xp & Um[o]), Um[o])) ok = 0;
                for (int x = 0; x < n && ok; x++) if (x != o && envies(x, Xp, hv[x])) ok = 0;
                if (ok && C) {
                    msk NoX = needs(o, Xp);                             /* o's needs from its bundle */
                    int unf = 0;
                    for (int x = 0; x < n; x++) if (isfz[x]) { int g = KY[x]; if (!(c->needers[g] & ~(1u << o)) && !(NoX >> g & 1)) unf++; }
                    if (pc(C) > unf) ok = 0;
                }
                if (ok) { best = pc(C); bw = C; }
            }
            C = (C - X) & X;                                        /* next submask of X, increasing */
            if (!C) break;
        }
        c->minC[o] = best; c->Cw[o] = bw;
        if (best == 0) c->own0 |= 1u << o;
        if (best >= 0) c->own |= 1u << o;
    }
}

static void pmask(char **s, msk M) { int first = 1; *s += sprintf(*s, "["); for (int g = 0; g < 32; g++) if (M >> g & 1) { *s += sprintf(*s, first ? "%d" : ",%d", g); first = 0; } *s += sprintf(*s, "]"); }

static void cfg_json(char *buf, cfg_t *c) {
    char *s = buf;
    s += sprintf(s, "{\"key\":["); for (int i = 0; i < n; i++) s += sprintf(s, i ? ",%d" : "%d", KY[i]);
    s += sprintf(s, "],\"Q\":["); for (int i = 0; i < n; i++) { if (i) *s++ = ','; if (KY[i] >= 0) s += sprintf(s, "null"); else pmask(&s, Q[i]); }
    s += sprintf(s, "],\"L\":"); pmask(&s, c->L);
    s += sprintf(s, ",\"phi\":[%d,%d,%d,%d],\"po\":%d,\"own\":[", c->phi[0], c->phi[1], c->phi[2], c->phi[3], c->po);
    int first = 1;
    for (int j = 0; j < nfr; j++) { int o = fr[j]; if (c->minC[o] < 0) continue; s += sprintf(s, first ? "[%d," : ",[%d,", o); pmask(&s, c->Cw[o]); *s++ = ']'; first = 0; }
    s += sprintf(s, "],\"thr\":["); first = 1;
    for (int j = 0; j < nfr; j++) { int o = fr[j]; for (int x = 0; x < n; x++) if (c->thr[o] >> x & 1) {
        s += sprintf(s, first ? "[%d,%d,%d]" : ",[%d,%d,%d]", o, x, KY[x] >= 0 ? c->h7[x][o] : -1); first = 0; } }
    s += sprintf(s, "],\"need\":["); first = 1;
    for (int g = 0; g < m; g++) if (Nm >> g & 1) { s += sprintf(s, first ? "[%d," : ",[%d,", g); pmask(&s, c->needers[g]); *s++ = ']'; first = 0; }
    s += sprintf(s, "]}");
}

static long cfg_count;
static cfg_t tmpc;
static void cfg_leaf(void) {
    cfg_t *c = &tmpc; eval(c);
    PR.ncfg++; cfg_count++;
    if (c->own) PR.ncompl++;
    if (c->own0) PR.nsimple++;
    int mult[MAXN] = {0};
    for (int j = 0; j < nfr; j++) { int o = fr[j]; for (int x = 0; x < n; x++) if (c->thr[o] >> x & 1 && KY[x] >= 0) { mult[x]++; PR.h7all[c->h7[x][o]]++; } }
    int mm = 0; for (int x = 0; x < n; x++) if (mult[x] > mm) mm = mult[x];
    if (mm > PR.thrmax_all) PR.thrmax_all = mm;
    int cmp = PR.nmax ? phicmp(c->phi, PR.phimax) : 1;
    if (cmp > 0) { memcpy(PR.phimax, c->phi, sizeof PR.phimax); PR.nmax = PR.nmax_compl = PR.nmax_simple = PR.nmax_po = PR.nmax_t0 = PR.nmax_thr2 = 0;
                   memset(PR.h7max, 0, sizeof PR.h7max); PR.thrmax_max = 0; PR.ex[0] = 0; }
    if (cmp >= 0) {
        PR.nmax++; if (c->own) PR.nmax_compl++; if (c->own0) PR.nmax_simple++; if (c->po) PR.nmax_po++; if (!c->t) PR.nmax_t0++;
        if (mm >= 2) PR.nmax_thr2++;
        if (mm > PR.thrmax_max) PR.thrmax_max = mm;
        for (int j = 0; j < nfr; j++) { int o = fr[j]; for (int x = 0; x < n; x++) if (c->thr[o] >> x & 1 && KY[x] >= 0) PR.h7max[c->h7[x][o]]++; }
        if (!PR.ex[0] || (!c->own && strstr(PR.ex, "\"own\":[]") == NULL)) cfg_json(PR.ex, c);
    }
    if (DUMP) { static char buf[8192]; cfg_json(buf, c); printf("C %s\n", buf); }
}
static void cfg_dfs(int j, msk used) {
    if (cfg_count > MAXCFG) { PR.trunc = 1; return; }
    if (j == nfr) { cfg_leaf(); return; }
    int y = fr[j];
    for (int t = 0; t < npairs[y]; t++) if (!(pairs[y][t] & used)) { Q[y] = pairs[y][t]; cfg_dfs(j + 1, used | pairs[y][t]); }
}
static void configs(void) {
    memset(&PR, 0, sizeof PR); cfg_count = 0;
    for (int k = 0; k < nkey; k++) {
        KY = keys[k]; Nm = 0; nfr = 0;
        for (int i = 0; i < n; i++) if (KY[i] >= 0) Nm |= 1u << KY[i]; else fr[nfr++] = i;
        Mp = ALL & ~Nm;
        for (int j = 0; j < nfr; j++) {
            int y = fr[j]; Um[y] = Rm[y] & ~Nm; npairs[y] = 0;
            for (int g = 0; g < m; g++) if (Mp >> g & 1) for (int h = g + 1; h < m; h++) if (Mp >> h & 1) {
                msk P2 = (1u << g) | (1u << h);
                if (admissible(y, P2 & Um[y], Um[y])) { if (npairs[y] >= MAXPAIR) { fprintf(stderr, "MAXPAIR\n"); exit(2); } pairs[y][npairs[y]++] = P2; }
            }
        }
        cfg_dfs(0, 0);
    }
}

/* ---------- per profile ---------- */
typedef struct { long prof, om1, Z, small, F, gap, gap_f1, gap_f2, cat[4], defmis, defover, trunc,
                 cfg, cfg_compl, cfg_simple, max, max_thr2, max_notpo, max_tpos, h7all[4], h7max[4],
                 exp3, exp4, expbt, keys, thr2prof, phibad; } cnt_t;
static cnt_t CN;
static long gapidx;

static void profile(void) {
    for (int i = 0; i < n; i++) for (int k = 0; k < deg[i]; k++) v[i][R[i][k]] = dom[i][cur[i] * deg[i] + k];
    for (int i = 0; i < n; i++) {
        int b = R[i][0]; for (int k = 1; k < deg[i]; k++) if (v[i][R[i][k]] > v[i][b]) b = R[i][k];
        top[i] = b;
        int s[4], d = deg[i]; for (int k = 0; k < d; k++) s[k] = v[i][R[i][k]];
        for (int a = 0; a < d; a++) for (int b2 = a + 1; b2 < d; b2++) if (s[b2] > s[a]) { int t = s[a]; s[a] = s[b2]; s[b2] = t; }
        bigtop_agent[i] = d == 4 && s[0] > s[1] + s[2];
        nopt[i] = 0;
        for (int t = 0; t < (1 << d); t++) if (__builtin_popcount(t) <= 2) {
            msk B = 0; for (int k = 0; k < d; k++) if (t >> k & 1) B |= 1u << R[i][k];
            opt[i][nopt[i]] = B; optN[i][nopt[i]] = needs(i, B); nopt[i]++;
        }
    }
    CN.prof++;
    int sigma = 2 * n - m;
    if (dfs0(0, 0)) { if (-sigma >= 1) { CN.om1++; CN.Z++; } else CN.small++; return; }
    bestf = 1 << 20; nkey = 0; npp = 0; pp_over = 0;
    dfsP(0, 0, 0, 0);
    int f = bestf, om = f - sigma;
    if (om <= 0) { CN.small++; return; }
    CN.om1++;
    int anyrob = 0;
    for (int k = 0; k < nkey && !anyrob; k++) {
        msk Nk = 0; for (int i = 0; i < n; i++) if (keys[k][i] >= 0) Nk |= 1u << keys[k][i];
        int rob = 1; for (int i = 0; i < n; i++) if (keys[k][i] >= 0 && val(i, Rm[i] & ~Nk) > v[i][keys[k][i]]) rob = 0;
        anyrob |= rob;
    }
    if (anyrob) { CN.F++; return; }
    CN.gap++; if (f == 1) CN.gap_f1++; else CN.gap_f2++;
    CN.keys += nkey;
    for (int k = 0; k < nkey; k++) {
        msk Nk = 0; for (int i = 0; i < n; i++) if (keys[k][i] >= 0) Nk |= 1u << keys[k][i];
        for (int i = 0; i < n; i++) if (keys[k][i] >= 0 && val(i, Rm[i] & ~Nk) > v[i][keys[k][i]]) {
            if (deg[i] == 3) CN.exp3++; else if (bigtop_agent[i] && keys[k][i] == top[i]) CN.expbt++; else CN.exp4++; }
    }
    if (DUMP) {
        printf("P {\"tag\":%d,\"prof\":[", tag); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", cur[i]);
        printf("],\"f\":%d,\"omega\":%d,\"keys\":[", f, om);
        for (int k = 0; k < nkey; k++) { printf(k ? ",[" : "["); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", keys[k][i]); printf("]"); }
        printf("]}\n");
    }
    configs();
    int cat = PR.nmax_simple ? 0 : PR.nmax_compl ? 1 : PR.ncompl ? 2 : 3;
    CN.cat[cat]++;
    CN.cfg += PR.ncfg; CN.cfg_compl += PR.ncompl; CN.cfg_simple += PR.nsimple; CN.max += PR.nmax; CN.max_thr2 += PR.nmax_thr2;
    CN.max_notpo += PR.nmax - PR.nmax_po; CN.max_tpos += PR.nmax - PR.nmax_t0; CN.trunc += PR.trunc;
    if (PR.thrmax_max >= 2) CN.thr2prof++;
    if (PR.nmax_compl < PR.nmax) CN.phibad++;          /* some Phi'-maximum without a valid owner: Conjecture Phi' fails */
    for (int k = 0; k < 4; k++) { CN.h7all[k] += PR.h7all[k]; CN.h7max[k] += PR.h7max[k]; }
    int dres = -1;
    if (DEF) {
        dres = 0; for (int p = 0; p < npp && !dres; p++) dres = P_ok(ppB[p]);
        if (pp_over) CN.defover++;
        if (dres != (PR.ncompl > 0)) CN.defmis++;
    }
    int hard = cat != 0 || PR.nmax_compl < PR.nmax || PR.nmax_thr2 || PR.nmax_po < PR.nmax || PR.nmax_t0 < PR.nmax || (dres >= 0 && dres != (PR.ncompl > 0));
    long gi = gapidx++;
    if (hard || (REC > 0 && gi % REC == 0)) {
        printf("R {\"tag\":%d,\"prof\":[", tag); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", cur[i]);
        printf("],\"f\":%d,\"omega\":%d,\"nkeys\":%d,\"keys\":[", f, om, nkey);
        for (int k = 0; k < nkey && k < 16; k++) { printf(k ? ",[" : "["); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", keys[k][i]); printf("]"); }
        printf("],\"ncfg\":%ld,\"ncompl\":%ld,\"nsimple\":%ld,\"phimax\":[%d,%d,%d,%d],\"nmax\":%ld,\"nmax_compl\":%ld,\"nmax_simple\":%ld,"
               "\"nmax_po\":%ld,\"nmax_t0\":%ld,\"nmax_thr2\":%ld,\"thrmax_all\":%d,\"thrmax_max\":%d,\"h7max\":[%ld,%ld,%ld,%ld],"
               "\"h7all\":[%ld,%ld,%ld,%ld],\"cat\":\"%c\",\"def\":%d,\"trunc\":%d,\"hard\":%d,\"ex\":%s}\n",
               PR.ncfg, PR.ncompl, PR.nsimple, PR.phimax[0], PR.phimax[1], PR.phimax[2], PR.phimax[3], PR.nmax, PR.nmax_compl,
               PR.nmax_simple, PR.nmax_po, PR.nmax_t0, PR.nmax_thr2, PR.thrmax_all, PR.thrmax_max,
               PR.h7max[0], PR.h7max[1], PR.h7max[2], PR.h7max[3], PR.h7all[0], PR.h7all[1], PR.h7all[2], PR.h7all[3],
               "SWNX"[cat], dres, PR.trunc, hard, PR.ex[0] ? PR.ex : "null");
    }
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-D")) DEF = 1;
        else if (!strcmp(argv[a], "-C")) DUMP = 1;
        else if (!strncmp(argv[a], "-r", 2)) REC = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-S", 2)) SEED = strtoull(argv[a] + 2, 0, 10);
        else if (!strncmp(argv[a], "-M", 2)) MAXCFG = atol(argv[a] + 2);
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 2; }
    }
    while (scanf("%d %d %d", &n, &m, &tag) == 3) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "n or m too large\n"); return 2; }
        ALL = m == 32 ? ~0u : (1u << m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &deg[i]) != 1) return 2; Rm[i] = 0;
            for (int k = 0; k < deg[i]; k++) { if (scanf("%d", &R[i][k]) != 1) return 2; Rm[i] |= 1u << R[i][k]; } }
        memset(v, 0, sizeof v);
        for (int i = 0; i < n; i++) if (scanf("%d", &K[i]) != 1) return 2;
        for (int i = 0; i < n; i++) { dom[i] = realloc(dom[i], sizeof(int) * K[i] * deg[i]);
            for (int t = 0; t < K[i] * deg[i]; t++) if (scanf("%d", &dom[i][t]) != 1) return 2; }
        long P; if (scanf("%ld", &P) != 1) return 2;
        memset(&CN, 0, sizeof CN); gapidx = 0;
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
        printf("K %d prof %ld om1 %ld Z %ld small %ld F %ld gap %ld gap_f1 %ld gap_f2 %ld catS %ld catW %ld catN %ld catX %ld "
               "defmis %ld defover %ld trunc %ld cfg %ld cfg_compl %ld cfg_simple %ld max %ld max_thr2 %ld max_notpo %ld max_tpos %ld "
               "h7all %ld %ld %ld %ld h7max %ld %ld %ld %ld exp3 %ld exp4 %ld expbt %ld keys %ld thr2prof %ld phibad %ld\n",
               tag, CN.prof, CN.om1, CN.Z, CN.small, CN.F, CN.gap, CN.gap_f1, CN.gap_f2, CN.cat[0], CN.cat[1], CN.cat[2], CN.cat[3],
               CN.defmis, CN.defover, CN.trunc, CN.cfg, CN.cfg_compl, CN.cfg_simple, CN.max, CN.max_thr2, CN.max_notpo, CN.max_tpos,
               CN.h7all[0], CN.h7all[1], CN.h7all[2], CN.h7all[3], CN.h7max[0], CN.h7max[1], CN.h7max[2], CN.h7max[3],
               CN.exp3, CN.exp4, CN.expbt, CN.keys, CN.thr2prof, CN.phibad);
        fflush(stdout);
    }
    return 0;
}
