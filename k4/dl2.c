/* k4/dl2.c -- Conjecture DL2 of k4/strategy.md section 3 on data (compute/k4-dl2; ledger K4.STRAT.DL2). EVIDENCE only.

Written from the definitions of k4/c4x.md section 1 (the space P, value-based needs, the removal-only deficit),
k4/hall.md sections 1, 2, 5 (Lemma H1's exposures; Lemma H3's free shapes e1-e3; Lemma H7's frozen classes G, G1, L)
and k4/strategy.md section 2.1 (k*). It copies the input format and the profile loop of k4/gap.c (PR #53), and shares
no code with k4/suite/model.py or k4/suite/deficit_local.py, the implementation it is cross-checked against.

Objects, for one strict profile:
  - P: bases B_i inside R_i, |B_i| <= 2, pairwise disjoint; needs N_i = {g in R_i \ B_i : v_i(g) > v_i(B_i)};
    NA = U N_i; valid iff every needed good is a one-good base. Frozen: a one-good base in NA. f = the fewest frozen
    agents; sigma = 2n - m; omega = f - sigma. Only profiles with omega >= 1 are evaluated.
  - def(P) (k4/c4x.md section 1): |J| - S if <= 0; otherwise the least |C| - S_o(C) over the free owners o and the
    C inside J with X = B_o + (J \ C) threatening no x != o holding B_x (max_h v_x(X \ h) > v_x(B_x)), where S_o(C)
    is the number of slots of the agents other than o with frozen status recomputed from o's needs taken from X.
    def(P) = +inf when no agent is free.
  - k*(P), for a min-frozen P with def(P) > 0: the least number of agents whose base differs between P and a
    min-frozen P' with def(P') < def(P) (inf if there is none: a global minimum of def above 0, i.e. C4min fails).
    k* of the profile: the maximum over these P (0 if there is none).
  - for each P with def(P) > 0 (classification for the repair table):
      best owners: the free o attaining def(P) (Lemma H1: the largest |X| + u_o(X));
      exposures (x, o): W_o = B_o + J threatens x holding B_x. Class of (x, o):
        free x: e1 |B_x| = 1, R_x misses J, B_o a pair inside R_x \ B_x;
                e2 x has four goods, B_x = {b_x, c_x}, a_x in B_o, d_x in J, a + d > b + c;
                e3 x has four goods, |B_x| = 2, R_x misses J, R_x \ B_x = B_o;  fO otherwise;
        frozen x (base {g}): G  two or more goods of R_x in J, worth more to x than g together;
                G1 not G, o a chain end of x (a free agent reached from x by need edges through frozen agents),
                   x big-top (four goods, g its top a, a > b + c), R_x \ {a} inside J + B_o;
                L  not G, o not a chain end of x;  O otherwise.
      the signature of P: the classes of the exposures w.r.t. its best owners, plus "D2" if some frozen agent is
      exposed w.r.t. two or more free owners (k4/c4min_reduce.md Lemma D(ii)); "allfrozen" if def = +inf; "PM" if P
      is Pareto-maximal in P (the setting of Lemmas H3 and H7; such P' are min-frozen, k4/hall.md section 2).
      nn(P): the distance to the nearest other min-frozen P' of any deficit (P is isolated if nn(P) >= 3).
      the witness: among the P' at the least distance with def(P') < def(P), the one moving the fewest goods
      (sum of |B_i xor B'_i|), then the smallest def(P'), then the first in the enumeration order of P. Per changed
      agent i: kind
        T trade: a good moves between B_i and another agent's base (gained from some B_j, j != i, or lost into
          some B'_j);  otherwise G grow (B_i inside B'_i), S shrink (B'_i inside B_i), W swap with the pool;
      with the sizes |B_i| > |B'_i|, e.g. "W1>1". The repair type is the sorted list of these codes joined by "+".
      Roles of the changed agents: frozen in P / P' ("F" / "f" before and after, e.g. "F>f"), plus "o" if a best
      owner of P, "x" if exposed w.r.t. a best owner of P.

Input (stdin), blocks as in k4/gap.c:  n m tag / n lines "d g1 .. gd" / "K_0 .. K_{n-1}" / for each agent K_i lines
of d values (in the order of its goods) / "P" and, if P < 0, -P lines of n domain indices.  P = 0: every profile;
P > 0: P random profiles (seeded by -S and tag); P < 0: the listed profiles.
Options:
  -v       one line per evaluated profile: "V tag p_0 .. p_{n-1} kstar nmin npos mindef" (kstar -1 = inf, -2: omega <= 0)
  -w       with -v: one line per min-frozen P: "W bases(masks) def dist nn pm" (def 999999 = inf; dist -1: def <= 0,
           99: none; nn: the distance to the nearest other min-frozen P, 99: none; pm: Pareto-maximal; nn, pm -1 when
           def <= 0)
  -rR      dump "D {json}" records: every profile with k* >= 3 (or inf); the profiles with k* = 1 whose rank among the
           k* = 1 profiles of the block is 0 mod R (the first, the (R+1)-th, ...; R = 0: none)
  -qQ      the same for k* = 2 with Q (default 1: every one)
  -SS      seed for P > 0.
Output per block: "K tag prof N om1 N small N kstar0 N .. kstar3 N kstar4 N kstarinf N kstarn N kiso N ktrap N pos N
pd1 N .. pd4 N pdinf N piso N ptrap N pmpos N pm3 N maxmin N": profiles (all, omega >= 1, omega <= 0); profiles with k* = 0, 1, 2,
3, >= 4, inf, k* = n; profiles with 3 <= k* < inf whose P at distance >= 3 are all isolated (kiso: no other min-frozen
P within distance 2) or not (ktrap); P with def > 0 (pos), by distance (1, 2, 3, >= 4, inf) and, at distance >= 3,
isolated or not (piso, ptrap); the Pareto-maximal P with def > 0 (pmpos), those at distance >= 3 (pm3); the largest
least deficit over the profiles (maxmin). Then
"T sig|type|roles count" (the canonical witness of every P with def > 0) and "A sig|type count" (every repair type
available at the least distance, counted once per P).
Build: gcc -O2 k4/dl2.c (m <= 32, n <= 16); -DWIDE for m <= 64 (H_3). With more than BIGPP (3000) min-frozen P the
neighbours within distance 2 are found by hashing the bases, and every other P is scanned only when none of them has a
smaller deficit; the output is the same as with the plain scan (checked with -DBIGPP=5, both widths).  */
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
static int VERB = 0, WVERB = 0, REC = 0, REC2 = 1; static uint64_t SEED = 1;


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

/* ---------- the min-frozen pre-allocations ---------- */
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

/* ---------- per P: deficit, owners, exposures ---------- */
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
static msk chain_ends(const unsigned char *ix, int x, msk F) {
    msk N[MAXN]; for (int i = 0; i < n; i++) N[i] = optN[i][ix[i]];
    msk seen = BIT(x), fr = BIT(x), ends = 0;
    while (fr) {
        int y = ctz(fr); fr &= fr - 1;
        msk g = opt[y][ix[y]];
        for (int w = 0; w < n; w++) if ((N[w] & g) && !(seen >> w & 1)) { seen |= BIT(w); if (F >> w & 1) fr |= BIT(w); else ends |= BIT(w); }
    }
    return ends;
}

enum { C_E1, C_E2, C_E3, C_FO, C_G, C_G1, C_L, C_O, C_D2, C_ALLF, C_PM, NCLS };
static const char *CLSNAME[NCLS] = {"e1", "e2", "e3", "fO", "G", "G1", "L", "O", "D2", "allfrozen", "PM"};

static int classify(const unsigned char *ix, const pinfo_t *pi, int x, int o) {
    msk Bx = opt[x][ix[x]], Bo = opt[o][ix[o]], J = pi->J;
    if (!(pi->frozen >> x & 1)) {
        if (pc(Bx) == 1 && !(Rm[x] & J) && pc(Bo) == 2 && !(Bo & ~(Rm[x] & ~Bx))) return C_E1;
        if (deg[x] == 4 && pc(Bx) == 2) {
            int a = rk[x][0], b = rk[x][1], c = rk[x][2], d = rk[x][3];
            if (Bx == (BIT(b) | BIT(c)) && (Bo >> a & 1) && (J >> d & 1) && v[x][a] + v[x][d] > v[x][b] + v[x][c]) return C_E2;
            if (!(Rm[x] & J) && (Rm[x] & ~Bx) == Bo) return C_E3;
        }
        return C_FO;
    }
    int g = ctz(Bx);
    msk JR = J & Rm[x];
    if (pc(JR) >= 2 && val(x, JR) > v[x][g]) return C_G;
    msk ends = chain_ends(ix, x, pi->frozen);
    if (ends >> o & 1) {
        if (bigtop[x] && g == topg[x] && !((Rm[x] & ~Bx) & ~(J | Bo))) return C_G1;
        return C_O;
    }
    return C_L;
}

/* ---------- a tiny string -> count map ---------- */
typedef struct { char *k; long c; } kv_t;
static kv_t *HT = 0; static long hcap = 0, hcnt = 0;
static uint64_t hstr(const char *s) { uint64_t h = 1469598103934665603ull; while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ull; } return h; }
static void hadd(const char *k, long c) {
    if (hcnt * 2 >= hcap) {
        long oc = hcap; kv_t *o = HT; hcap = hcap ? 2 * hcap : 1024; HT = calloc(hcap, sizeof(kv_t)); hcnt = 0;
        for (long i = 0; i < oc; i++) if (o[i].k) { uint64_t h = hstr(o[i].k) & (hcap - 1); while (HT[h].k) h = (h + 1) & (hcap - 1); HT[h] = o[i]; hcnt++; }
        free(o);
    }
    uint64_t h = hstr(k) & (hcap - 1);
    while (HT[h].k) { if (!strcmp(HT[h].k, k)) { HT[h].c += c; return; } h = (h + 1) & (hcap - 1); }
    HT[h].k = strdup(k); HT[h].c = c; hcnt++;
}

/* ---------- repair description ---------- */
static int cmpstr(const void *a, const void *b) { return strcmp(*(const char *const *)a, *(const char *const *)b); }
/* type and roles of the change P -> P2 (indices a, b into PP); best: best-owner mask of P; xm: exposed w.r.t. a best owner */
static void describe(long a, long b, msk best, msk xm, char *type, char *roles) {
    const unsigned char *ia = PP + a * MAXN, *ib = PP + b * MAXN;
    msk Ja = PI[a].J, Jb = PI[b].J;
    char codes[MAXN][16], rl[MAXN][16]; char *cp[MAXN], *rp[MAXN]; int nc = 0;
    for (int i = 0; i < n; i++) {
        msk B1 = opt[i][ia[i]], B2 = opt[i][ib[i]];
        if (B1 == B2) continue;
        msk gain = B2 & ~B1, lost = B1 & ~B2;
        msk othA = 0, othB = 0; for (int j = 0; j < n; j++) if (j != i) { othA |= opt[j][ia[j]]; othB |= opt[j][ib[j]]; }
        char kd;
        if ((gain & othA) || (lost & othB)) kd = 'T'; else if (!lost) kd = 'G'; else if (!gain) kd = 'S'; else kd = 'W';
        (void)Ja; (void)Jb;
        sprintf(codes[nc], "%c%d>%d", kd, pc(B1), pc(B2));
        sprintf(rl[nc], "%c>%c%s%s", (PI[a].frozen >> i & 1) ? 'F' : 'f', (PI[b].frozen >> i & 1) ? 'F' : 'f',
                (best >> i & 1) ? "o" : "", (xm >> i & 1) ? "x" : "");
        cp[nc] = codes[nc]; rp[nc] = rl[nc]; nc++;
    }
    qsort(cp, nc, sizeof(char *), cmpstr); qsort(rp, nc, sizeof(char *), cmpstr);
    type[0] = 0; for (int k = 0; k < nc; k++) { if (k) strcat(type, "+"); strcat(type, cp[k]); }
    roles[0] = 0; for (int k = 0; k < nc; k++) { if (k) strcat(roles, "+"); strcat(roles, rp[k]); }
}

/* ---------- neighbours: the min-frozen P within distance 2, by hashing (large classes) ---------- */
#ifndef BIGPP
#define BIGPP 3000                                  /* above this many min-frozen P, use the hash */
#endif
static uint64_t *HK = 0; static long *HV = 0; static long hsz = 0;
static uint64_t pkey(const unsigned char *ix) { uint64_t k = 0; for (int i = 0; i < n; i++) k |= (uint64_t)ix[i] << (4 * i); return k; }
static uint64_t hmix(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdull; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ull; k ^= k >> 33; return k; }
static void hbuild(void) {
    long need = 4; while (need < 2 * npp) need <<= 1;
    if (need > hsz) { hsz = need; HK = realloc(HK, sizeof(uint64_t) * hsz); HV = realloc(HV, sizeof(long) * hsz); }
    for (long i = 0; i < hsz; i++) HV[i] = -1;
    for (long p = 0; p < npp; p++) {
        uint64_t k = pkey(PP + p * MAXN), h = hmix(k) & (hsz - 1);
        while (HV[h] >= 0) h = (h + 1) & (hsz - 1);
        HK[h] = k; HV[h] = p;
    }
}
static long hfind(uint64_t k) {
    uint64_t h = hmix(k) & (hsz - 1);
    while (HV[h] >= 0) { if (HK[h] == k) return HV[h]; h = (h + 1) & (hsz - 1); }
    return -1;
}
static long *cand = 0; static long capc = 0, ncand;
static void cpush(long q) { if (ncand == capc) { capc = capc ? 2 * capc : 1024; cand = realloc(cand, sizeof(long) * capc); } cand[ncand++] = q; }
/* the candidates P' for P = PP[p]: every other min-frozen P (all = 1 or a small class), else those within distance 2 */
static void fill_cand(long p, int all) {
    ncand = 0;
    if (all || npp <= BIGPP) { for (long q = 0; q < npp; q++) if (q != p) cpush(q); return; }
    unsigned char ix[MAXN]; memcpy(ix, PP + p * MAXN, MAXN);
    for (int i = 0; i < n; i++) {
        int ti = ix[i];
        for (int t = 0; t < nopt[i]; t++) if (t != ti) {
            ix[i] = (unsigned char)t; long q = hfind(pkey(ix)); if (q >= 0) cpush(q);
            for (int j = i + 1; j < n; j++) {
                int tj = ix[j];
                for (int u = 0; u < nopt[j]; u++) if (u != tj) { ix[j] = (unsigned char)u; long q2 = hfind(pkey(ix)); if (q2 >= 0) cpush(q2); }
                ix[j] = (unsigned char)tj;
            }
        }
        ix[i] = (unsigned char)ti;
    }
}

/* ---------- per profile ---------- */
typedef struct { long prof, om1, small, ks[6], kn, kiso, ktrap, pos, pd[6], piso, ptrap, pmpos, pm3, maxmin; } cnt_t;
/* ks: profiles with k* = 0, 1, 2, 3, >= 4, inf; kn: with k* = n; kiso / ktrap: with k* >= 3 (finite) where every P
   at distance >= 3 is isolated (no other min-frozen P within distance 2) / some is not; pd: P with def > 0 at
   distance 1, 2, 3, >= 4, inf (index 0 unused); piso / ptrap: P at distance >= 3, isolated / not; pmpos / pm3: P with
   def > 0 that are Pareto-maximal / and at distance >= 3 */
static cnt_t CN;
static long evalidx;

static void pmaskj(FILE *f, msk M) { int first = 1; fputc('[', f); for (int g = 0; g < MAXM; g++) if (M >> g & 1) { fprintf(f, first ? "%d" : ",%d", g); first = 0; } fputc(']', f); }

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
    CN.prof++;
    sigma = 2 * n - m;
    if (sigma >= 0) { found_small = 0; dfs_small(0, 0, 0, 0, 0); if (found_small) { CN.small++; if (VERB) { printf("V %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]); printf(" -2 0 0 0\n"); } return; } }
    bestf = 1 << 20; npp = 0;
    memset(cidx, 0, sizeof cidx);
    dfsP(0, 0, 0, 0, 0);
    int omega = bestf - sigma;
    if (omega <= 0) { fprintf(stderr, "internal: omega <= 0 after the small test\n"); exit(3); }
    CN.om1++;
    if (npp > capi) { capi = npp; PI = realloc(PI, capi * sizeof(pinfo_t)); if (!PI) { fprintf(stderr, "oom\n"); exit(2); } }
    int mindef = INF, npos = 0;
    for (long p = 0; p < npp; p++) { eval_P(PP + p * MAXN, &PI[p]); if (PI[p].def < mindef) mindef = PI[p].def; if (PI[p].def > 0) npos++; }
    /* k* and the witnesses */
    int kstar = 0;
    evalidx++;
    int dumpit = 0;
    char *dbuf = 0; size_t dlen = 0; FILE *df = 0;
    /* first pass: distances */
    static int *dd = 0, *nn = 0, *pmv = 0; static long capd = 0;
    if (npp > capd) { capd = npp; dd = realloc(dd, sizeof(int) * capd); nn = realloc(nn, sizeof(int) * capd); pmv = realloc(pmv, sizeof(int) * capd); }
    int anytrap = 0;
    if (npp > BIGPP) hbuild();
    for (long p = 0; p < npp; p++) {
        dd[p] = -1; nn[p] = -1; pmv[p] = -1;
        if (PI[p].def <= 0) continue;
        int best = 99, near = 99; const unsigned char *ia = PP + p * MAXN;
        for (int pass = 0; pass < 2 && best == 99; pass++) {    /* pass 1 (large classes only): every other P */
            if (pass == 1 && npp <= BIGPP) break;
            fill_cand(p, pass);
            for (long c = 0; c < ncand; c++) {
                long q = cand[c];
                const unsigned char *ib = PP + q * MAXN; int d = 0;
                for (int i = 0; i < n; i++) d += ia[i] != ib[i];
                if (d < near) near = d;
                if (PI[q].def < PI[p].def && d < best) best = d;
            }
        }
        dd[p] = best; nn[p] = near;
        if (best == 99) kstar = 99; else if (kstar != 99 && best > kstar) kstar = best;
        CN.pd[best == 99 ? 5 : best >= 4 ? 4 : best]++;
        if (best >= 3) { if (near >= 3) CN.piso++; else { CN.ptrap++; if (best != 99) anytrap = 1; } }
    }
    if (kstar == 99) CN.ks[5]++; else CN.ks[kstar >= 4 ? 4 : kstar]++;
    if (kstar == n) CN.kn++;
    if (kstar >= 3 && kstar != 99) { if (anytrap) CN.ktrap++; else CN.kiso++; }
    CN.pos += npos;
    if (kstar >= 3) dumpit = 1;                                   /* includes inf (99) */
    else if (kstar == 2) { if (REC2 > 0 && (CN.ks[2] - 1) % REC2 == 0) dumpit = 1; }
    else if (kstar == 1) { if (REC > 0 && (CN.ks[1] - 1) % REC == 0) dumpit = 1; }
    if (dumpit) {
        df = open_memstream(&dbuf, &dlen);
        fprintf(df, "D {\"tag\":%d,\"prof\":[", tag); for (int i = 0; i < n; i++) fprintf(df, i ? ",%d" : "%d", cur[i]);
        fprintf(df, "],\"f\":%d,\"omega\":%d,\"kstar\":%d,\"nmin\":%ld,\"npos\":%d,\"mindef\":%d,\"P\":[", bestf, omega, kstar == 99 ? -1 : kstar, npp, npos, mindef);
    }
    int firstP = 1;
    /* second pass: classification of every P with def > 0 */
    for (long p = 0; p < npp; p++) {
        if (PI[p].def <= 0) continue;
        const unsigned char *ia = PP + p * MAXN;
        /* signature */
        msk best = 0, xm = 0; int sig = 0;
        if (PI[p].def >= INF) sig |= 1 << C_ALLF;
        else for (int o = 0; o < n; o++) if (PI[p].bestown[o] == PI[p].def) best |= BIT(o);
        for (int o = 0; o < n; o++) if (best >> o & 1) for (int x = 0; x < n; x++) if (PI[p].expo[o] >> x & 1) { sig |= 1 << classify(ia, &PI[p], x, o); xm |= BIT(x); }
        for (int x = 0; x < n; x++) if (PI[p].frozen >> x & 1) { int c = 0; for (int o = 0; o < n; o++) if (PI[p].expo[o] >> x & 1) c++; if (c >= 2) sig |= 1 << C_D2; }
        /* Pareto-maximal in P: no P' with v_i(B'_i) >= v_i(B_i) for all i, one strict. Such a P' has NA' inside NA
           (needs shrink when the base value does not drop), so it is min-frozen too and the scan of the class suffices */
        int pm = 1;
        for (long q = 0; q < npp && pm; q++) {
            if (q == p) continue;
            const unsigned char *ib = PP + q * MAXN; int ge = 1, gt = 0;
            for (int i = 0; i < n && ge; i++) { int a = optv[i][ia[i]], b = optv[i][ib[i]]; if (b < a) ge = 0; else if (b > a) gt = 1; }
            if (ge && gt) pm = 0;
        }
        pmv[p] = pm;
        if (pm) { sig |= 1 << C_PM; CN.pmpos++; if (dd[p] >= 3) CN.pm3++; }
        char sigs[128]; sigs[0] = 0;
        for (int c = 0; c < NCLS; c++) if (sig >> c & 1) { if (sigs[0]) strcat(sigs, ","); strcat(sigs, CLSNAME[c]); }
        char key[1024], type[256], roles[256], ctype[256] = "", croles[256] = "";
        long wit = -1; int wmov = 1 << 20, wdef = INF, nwit = 0;
        /* the available types (distinct) */
        char avail[64][256]; int nav = 0;
        if (dd[p] != 99) {
            fill_cand(p, dd[p] > 2);
            for (long c = 0; c < ncand; c++) {
                long q = cand[c];
                if (PI[q].def >= PI[p].def) continue;
                const unsigned char *ib = PP + q * MAXN; int d = 0, mov = 0;
                for (int i = 0; i < n; i++) if (ia[i] != ib[i]) { d++; mov += pc(opt[i][ia[i]] ^ opt[i][ib[i]]); }
                if (d != dd[p]) continue;
                nwit++;
                describe(p, q, best, xm, type, roles);
                int k; for (k = 0; k < nav; k++) if (!strcmp(avail[k], type)) break;
                if (k == nav && nav < 64) { strcpy(avail[nav], type); nav++; }
                if (mov < wmov || (mov == wmov && (PI[q].def < wdef || (PI[q].def == wdef && q < wit)))) { wmov = mov; wdef = PI[q].def; wit = q; strcpy(ctype, type); strcpy(croles, roles); }
            }
        } else { strcpy(ctype, "none"); strcpy(croles, "none"); }
        strcpy(key, "T "); strcat(key, sigs); strcat(key, "|"); strcat(key, ctype); strcat(key, "|"); strcat(key, croles); hadd(key, 1);
        for (int k = 0; k < nav; k++) { strcpy(key, "A "); strcat(key, sigs); strcat(key, "|"); strcat(key, avail[k]); hadd(key, 1); }
        if (dumpit) {
            fprintf(df, firstP ? "{" : ",{"); firstP = 0;
            fprintf(df, "\"B\":["); for (int i = 0; i < n; i++) { if (i) fputc(',', df); pmaskj(df, opt[i][ia[i]]); }
            fprintf(df, "],\"def\":%d,\"own\":[", PI[p].def >= INF ? -1 : PI[p].def);
            int f1 = 1; for (int o = 0; o < n; o++) if (!(PI[p].frozen >> o & 1)) { fprintf(df, f1 ? "[%d,%d]" : ",[%d,%d]", o, PI[p].bestown[o] >= INF ? -1 : PI[p].bestown[o]); f1 = 0; }
            fprintf(df, "],\"exp\":["); f1 = 1;
            for (int o = 0; o < n; o++) for (int x = 0; x < n; x++) if (PI[p].expo[o] >> x & 1) { fprintf(df, f1 ? "[%d,%d,\"%s\"]" : ",[%d,%d,\"%s\"]", o, x, CLSNAME[classify(ia, &PI[p], x, o)]); f1 = 0; }
            fprintf(df, "],\"sig\":\"%s\",\"pm\":%d,\"k\":%d,\"nn\":%d", sigs, pm, dd[p] == 99 ? -1 : dd[p], nn[p] == 99 ? -1 : nn[p]);
            if (wit >= 0) {
                const unsigned char *ib = PP + wit * MAXN;
                fprintf(df, ",\"W\":["); for (int i = 0; i < n; i++) { if (i) fputc(',', df); pmaskj(df, opt[i][ib[i]]); }
                fprintf(df, "],\"defW\":%d,\"type\":\"%s\",\"roles\":\"%s\",\"nwit\":%d,\"avail\":[", PI[wit].def, ctype, croles, nwit);
                for (int k = 0; k < nav; k++) fprintf(df, k ? ",\"%s\"" : "\"%s\"", avail[k]);
                fprintf(df, "]");
            }
            fprintf(df, "}");
        }
    }
    if (dumpit) { fprintf(df, "]}\n"); fclose(df); fputs(dbuf, stdout); free(dbuf); }
    if (CN.om1 == 1 || mindef > CN.maxmin) CN.maxmin = mindef;
    if (VERB) {
        printf("V %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]);
        printf(" %d %ld %d %d\n", kstar == 99 ? -1 : kstar, npp, npos, mindef);
        if (WVERB) for (long p = 0; p < npp; p++) {
            const unsigned char *ia = PP + p * MAXN;
            printf("W"); for (int i = 0; i < n; i++) printf(" %llu", (unsigned long long)opt[i][ia[i]]);
            printf(" %d %d %d %d\n", PI[p].def, dd[p], nn[p], pmv[p]);
        }
    }
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-v")) VERB = 1;
        else if (!strcmp(argv[a], "-w")) WVERB = VERB = 1;
        else if (!strncmp(argv[a], "-r", 2)) REC = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-q", 2)) REC2 = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-S", 2)) SEED = strtoull(argv[a] + 2, 0, 10);
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 2; }
    }
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
        memset(&CN, 0, sizeof CN); evalidx = 0;
        for (long i = 0; i < hcap; i++) if (HT[i].k) { free(HT[i].k); HT[i].k = 0; }
        hcnt = 0;
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
        printf("K %d prof %ld om1 %ld small %ld kstar0 %ld kstar1 %ld kstar2 %ld kstar3 %ld kstar4 %ld kstarinf %ld kstarn %ld "
               "kiso %ld ktrap %ld pos %ld pd1 %ld pd2 %ld pd3 %ld pd4 %ld pdinf %ld piso %ld ptrap %ld pmpos %ld pm3 %ld maxmin %ld\n",
               tag, CN.prof, CN.om1, CN.small, CN.ks[0], CN.ks[1], CN.ks[2], CN.ks[3], CN.ks[4], CN.ks[5], CN.kn,
               CN.kiso, CN.ktrap, CN.pos, CN.pd[1], CN.pd[2], CN.pd[3], CN.pd[4], CN.pd[5], CN.piso, CN.ptrap, CN.pmpos, CN.pm3, CN.maxmin);
        for (long i = 0; i < hcap; i++) if (HT[i].k) printf("%s %ld\n", HT[i].k, HT[i].c);
        fflush(stdout);
    }
    return 0;
}
