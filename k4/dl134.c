/* k4/dl134.c -- Conjecture DL134 (compute/k4-dl134): DL13 (k4/dl2.md section 3, ledger K4.DL2.T13) with the frozen
permutations (T4) added. EVIDENCE only.

A copy of k4/dl13.c (compute/k4-dl13), which stays unchanged (results/k4_dl13 cites it by SHA), with the (T4) test added
and the branch, tables and dumps taken over R_134 = T1 u T3 u T4. Everything dl13.c computes is kept: the "K" line is
dl2.c's "K" line and the "L" line is dl13.c's "L" line on the same input (R_13 only; k4/dl134_ref.py compares both).

Objects (dl2.c's header has the details): for one strict profile, P ranges over the valid pre-allocations with the
fewest frozen agents f (the min-frozen class); def(P) is the removal-only deficit (+inf when every agent is frozen);
only profiles with omega = f - (2n - m) >= 1 are evaluated. A *state* is a min-frozen P with def(P) > 0.

R_134. For min-frozen P, P' let ch be the agents whose base differs, and "nt" mean that some agent outside ch changes its
frozen status. A frozen agent is one whose base is a single good of NA. R_134(P, P') holds iff not nt and
  (T1) |ch| = 1 (dl13.c: one agent y re-bases); or
  (T3) dl13.c's role swap with a needer and at most one helper that gives up a good; or
  (T4) a permutation pi of the frozen agents' singleton bases among the frozen agents: every changed agent is frozen in P
       and in P', NA(P') = NA(P), and the changed agents' bases in P' are their bases in P permuted
       ({B'_i : i in ch} = {B_i : i in ch}); so each frozen i takes B_{pi(i)}, all other bases are unchanged and every
       frozen agent stays frozen. Any cycle structure; |ch| >= 2 (pi has no fixed point on ch).
The three kinds are disjoint (T1: |ch| = 1; T3: an agent unfreezes; T4: |ch| >= 2, nobody changes status).
DL134 at a state P: some min-frozen P' with def(P') < def(P) and R_134(P, P'). DL134 (the conjecture) is about the
profiles with f >= 1; f = 0 states are evaluated too (no T3 or T4 move exists there) and counted apart.

Per state: t1 / t3p / t3h / t4 = some T1 move / T3 move without a helper / T3 move with a helper / T4 move lowers the
deficit. The branch is the list of these that hold ("T1+T3h+T4", ..., "none" = DL134 fails at P). Move types:
  T1, T3: dl13.c's ("rel", "grow", "pool"; "xJ"/"xZ"/"xH" . "h-"/"hR"/"hJ"/"hZ");
  T4: the cycle type of pi on ch, the cycle lengths in decreasing order joined by "+": "2" (a single 2-swap), "3",
      "2+2", "4", ... (CYCNAME below; "other" past 8 moved agents).
  The witness of a state: among its R_134 moves that lower the deficit, the one with the smallest def(P'), then the
  fewest moved goods (sum of |B_i xor B'_i|), then the first in the enumeration order of P.

Input (stdin): dl2.c's blocks (k4/gap.c's format): "n m tag" / n lines "d g1 .. gd" / "K_0 .. K_{n-1}" / per agent K_i
lines of d values / "P" and, if P < 0, -P lines of n domain indices. P = 0: every profile; P > 0: P random profiles
(seeded by -S and tag, the same stream as dl2.c); P < 0: the listed profiles.
Options:
  -v       per evaluated profile dl2.c's line "V tag p_0 .. p_{n-1} kstar nmin npos mindef"
  -s       with -v: per state "S f b_0 .. b_{n-1} def dist r13dist rdist t1 t3p t3h t4 t1mask t3mask t4mask dT1 dT3 dT4
           pm sig" (b_i: masks of the goods; def/dT 999999 = inf; dist, r13dist, rdist 99 = none: the nearest better
           min-frozen P' / R_13 move / R_134 move; bit k of t1mask = T1 type k (rel, grow, pool), bit 4*xs + hk of
           t3mask with xs in (xJ, xZ, xH) and hk in (h-, hR, hJ, hZ), bit c of t4mask = T4 cycle type CYCNAME[c])
  -rR      dump (as "D {json}") every R-th state with f >= 1 that DL134 holds at without a T1 move, counted over the whole
           process (the 1st, (R+1)-th, ...; R = 0: none)
  -oO      the same for the other f >= 1 states that DL134 holds at (with a T1 move), O = 0: none
  -qQ      the same for the f >= 1 states repaired by T4 only (DL13 fails there, DL134 holds), Q = 0: none
           Besides these, every f >= 1 state at which DL134 fails, the first f >= 1 state of each (signature, branch)
           cell and the first 5 f = 0 states at which R_134 fails are dumped (per process).
  -SS      seed for P > 0.
Output per block: dl2.c's "K ..." counters, dl13.c's "L ..." counters (R_13 only: fail0 / fail1 there are the DL13
failures), then
  "M tag fail0 N fail1 N t1 N t3 N t4 N t4only N t4only2 N t4onlyL N t4sw N rdnone N rd1 N rd2 N rd3 N rd4 N"
  (R_134 failures with f = 0 / f >= 1 (DL134 failures); among the f >= 1 states: with some T1 / T3 / T4 move; repaired
  by T4 only; of those, with a 2-swap among the improving T4 moves / with longer cycles only; with an improving 2-swap;
  by the distance of the nearest R_134 move that lowers the deficit (none, 1, 2, 3, >= 4)),
  then the tables (f >= 1 states only; f is the profile's f; branch = the R_134 branch):
  "B f|sig|branch count"       states by signature and branch,
  "G f|k|branch count"         states by the nearest distance k (any move, dl2.c's k(P)) and branch,
  "Y f|branch|type count"      states by branch, counted once for each move type available among their improving
                               R_134 moves,
  "Q f|k|t4types count"        the states repaired by T4 only, by k and the set of T4 cycle types among their
                               improving moves (comma-joined).
Build: gcc -O2 k4/dl134.c (m <= 32, n <= 16); -DWIDE for m <= 64. With more than BIGPP (3000) min-frozen P the
candidates are generated (one agent re-based; or a frozen x, a free needer z of its good taking it, x any base, and at
most one other agent any base; or a bijection of the frozen agents onto their goods) and looked up in a hash of the
class; otherwise every min-frozen P is scanned. Both give the same output (k4/dl134_ref.py compares a -DBIGPP=0
build).  */
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
static int VERB = 0, SVERB = 0, RT = 0, RO = 0, RQ = 0; static uint64_t SEED = 1;


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

/* ---------- a tiny string -> count map (dl2.c) ---------- */
typedef struct { char *k; long c; } kv_t;
typedef struct { kv_t *t; long cap, cnt; } map_t;
static uint64_t hstr(const char *s) { uint64_t h = 1469598103934665603ull; while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ull; } return h; }
static long *mslot(map_t *M, const char *k) {       /* the counter of k (created at 0) */
    if (M->cnt * 2 >= M->cap) {
        long oc = M->cap; kv_t *o = M->t; M->cap = M->cap ? 2 * M->cap : 1024; M->t = calloc(M->cap, sizeof(kv_t)); M->cnt = 0;
        for (long i = 0; i < oc; i++) if (o[i].k) { uint64_t h = hstr(o[i].k) & (M->cap - 1); while (M->t[h].k) h = (h + 1) & (M->cap - 1); M->t[h] = o[i]; M->cnt++; }
        free(o);
    }
    uint64_t h = hstr(k) & (M->cap - 1);
    while (M->t[h].k) { if (!strcmp(M->t[h].k, k)) return &M->t[h].c; h = (h + 1) & (M->cap - 1); }
    M->t[h].k = strdup(k); M->t[h].c = 0; M->cnt++;
    return &M->t[h].c;
}
static void mclear(map_t *M) { for (long i = 0; i < M->cap; i++) if (M->t[i].k) { free(M->t[i].k); M->t[i].k = 0; } M->cnt = 0; }
static map_t TAB = {0, 0, 0};        /* per block: the B, G, Y tables */
static map_t SEEN = {0, 0, 0};       /* per process: the (signature, branch) cells already dumped */

/* ---------- neighbours by hashing (large classes; dl2.c) ---------- */
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
/* the T4 candidates: frozen agents fl[t..nf-1] take the goods left in G (one each, a good of their R_i), in every way */
static void perm_cand(unsigned char *ix, const int *fl, int nf, int t, msk G) {
    if (t == nf) { long q = hfind(pkey(ix)); if (q >= 0) cpush(q); return; }   /* the identity gives P itself (no gain) */
    int i = fl[t], t0 = ix[i];
    for (msk H = G & Rm[i]; H; H &= H - 1) {
        msk g = H & -H; int tg = -1;
        for (int u = 0; u < nopt[i]; u++) if (opt[i][u] == g) tg = u;
        if (tg < 0) continue;
        ix[i] = (unsigned char)tg;
        perm_cand(ix, fl, nf, t + 1, G & ~g);
    }
    ix[i] = (unsigned char)t0;
}
/* the R_134 candidates for P = PP[p] in a large class: one agent re-based; or a frozen x, a free z needing x's good
   taking it, x any other base, and at most one further agent any other base (a superset of the R_13 moves); or the
   frozen agents' goods permuted among them (a superset of the T4 moves) */
static void fill_cand134(long p) {
    ncand = 0;
    unsigned char ix[MAXN]; memcpy(ix, PP + p * MAXN, MAXN);
    msk F = PI[p].frozen;
    for (int i = 0; i < n; i++) {
        int ti = ix[i];
        for (int t = 0; t < nopt[i]; t++) if (t != ti) { ix[i] = (unsigned char)t; long q = hfind(pkey(ix)); if (q >= 0) cpush(q); }
        ix[i] = (unsigned char)ti;
    }
    for (int x = 0; x < n; x++) {
        if (!(F >> x & 1)) continue;
        msk g = opt[x][ix[x]]; int tx0 = ix[x];
        for (int z = 0; z < n; z++) {
            if (z == x || (F >> z & 1) || !(optN[z][ix[z]] & g)) continue;
            int tz0 = ix[z], tz = -1;
            for (int t = 0; t < nopt[z]; t++) if (opt[z][t] == g) tz = t;
            if (tz < 0) continue;
            ix[z] = (unsigned char)tz;
            for (int tx = 0; tx < nopt[x]; tx++) if (tx != tx0) {
                ix[x] = (unsigned char)tx;
                long q = hfind(pkey(ix)); if (q >= 0) cpush(q);
                for (int h = 0; h < n; h++) {
                    if (h == x || h == z) continue;
                    int th0 = ix[h];
                    for (int t = 0; t < nopt[h]; t++) if (t != th0) { ix[h] = (unsigned char)t; long q2 = hfind(pkey(ix)); if (q2 >= 0) cpush(q2); }
                    ix[h] = (unsigned char)th0;
                }
            }
            ix[x] = (unsigned char)tx0; ix[z] = (unsigned char)tz0;
        }
    }
    /* T4: every bijection of the frozen agents onto their goods (each agent i taking a good of R_i), but the identity */
    int fl[MAXN], nf = 0; msk G = 0;
    for (int i = 0; i < n; i++) if (F >> i & 1) { fl[nf++] = i; G |= opt[i][ix[i]]; }
    if (nf >= 2) perm_cand(ix, fl, nf, 0, G);
}

/* ---------- the R_13 test ---------- */
static long ANOM;
/* R_13(P, P') for P = PP[a], P' = PP[b]: 0 (not), 1 (T1), 2 (T3 without helper), 3 (T3 with a helper); *ty: the type
   bit (T1: 0 rel, 1 grow, 2 pool; T3: 4 * xs + hk, xs 0 xJ / 1 xZ / 2 xH, hk 0 h- / 1 hR / 2 hJ / 3 hZ) */
static int r13(long a, long b, int *ty) {
    const unsigned char *ia = PP + a * MAXN, *ib = PP + b * MAXN;
    msk Fa = PI[a].frozen, Fb = PI[b].frozen;
    msk ch = 0;
    for (int i = 0; i < n; i++) if (ia[i] != ib[i]) ch |= BIT(i);
    if ((Fa ^ Fb) & ~ch) return 0;                          /* nt: an unchanged agent changes its frozen status */
    if (pc(ch) == 1) {
        int y = ctz(ch);
        if ((Fa | Fb) >> y & 1) ANOM++;                    /* impossible by Lemma 1(a) */
        msk B = opt[y][ia[y]], B2 = opt[y][ib[y]];
        *ty = !(B2 & ~B) ? 0 : !(B & ~B2) ? 1 : 2;
        return 1;
    }
    msk U = ch & Fa & ~Fb, Z = ch & ~Fa & Fb, W = ch & Fa & Fb, Y = ch & ~Fa & ~Fb;
    if (pc(U) != 1 || pc(Z) != 1 || W || pc(Y) > 1) return 0;
    int x = ctz(U), z = ctz(Z);
    msk g = opt[x][ia[x]];
    if (opt[z][ib[z]] != g) return 0;                       /* z takes x's good */
    if (!(optN[z][ia[z]] & g)) return 0;                    /* z needs it in P */
    msk J = PI[a].J, Bz = opt[z][ia[z]], Bx2 = opt[x][ib[x]];
    int hk = 0, h = -1;
    if (Y) {
        h = ctz(Y);
        msk Bh = opt[h][ia[h]], Bh2 = opt[h][ib[h]];
        if (!(Bh & ~Bh2)) return 0;                         /* the helper gives up a good of its base */
        hk = !(Bh2 & ~Bh) ? 1 : !(Bh2 & ~(Bh | J)) ? 2 : 3;
    }
    int xs = !(Bx2 & ~J) ? 0 : !(Bx2 & ~(J | Bz)) ? 1 : 2;
    *ty = 4 * xs + hk;
    return Y ? 3 : 2;
}
/* ---------- the T4 test ---------- */
#define NCYC 22
static const char *CYCNAME[NCYC] = {"2", "3", "4", "2+2", "5", "3+2", "6", "4+2", "3+3", "2+2+2", "7", "5+2", "4+3",
                                    "3+2+2", "8", "6+2", "5+3", "4+4", "4+2+2", "3+3+2", "2+2+2+2", "other"};
/* T4(P, P') for P = PP[a], P' = PP[b]: 1 iff every changed agent is frozen in P and in P', NA(P') = NA(P), nobody else
   changes its frozen status and the changed agents' bases are permuted among them; *cy: the cycle type (CYCNAME) */
static int t4test(long a, long b, int *cy) {
    const unsigned char *ia = PP + a * MAXN, *ib = PP + b * MAXN;
    msk Fa = PI[a].frozen, Fb = PI[b].frozen, ch = 0, ua = 0, ub = 0;
    for (int i = 0; i < n; i++) if (ia[i] != ib[i]) { ch |= BIT(i); ua |= opt[i][ia[i]]; ub |= opt[i][ib[i]]; }
    if (pc(ch) < 2 || (ch & ~(Fa & Fb)) || Fa != Fb || PI[a].NA != PI[b].NA || ua != ub) return 0;
    int to[MAXN], len[MAXN], nc = 0;                        /* to[i]: the agent j whose base i takes (pi(i) = j) */
    for (int i = 0; i < n; i++) if (ch >> i & 1) { to[i] = -1; for (int j = 0; j < n; j++) if ((ch >> j & 1) && opt[j][ia[j]] == opt[i][ib[i]]) to[i] = j; if (to[i] < 0) return 0; }
    msk seen = 0;
    for (int i = 0; i < n; i++) if ((ch >> i & 1) && !(seen >> i & 1)) {
        int l = 0, j = i;
        while (!(seen >> j & 1)) { seen |= BIT(j); l++; j = to[j]; }
        if (j != i) return 0;                               /* not a permutation (cannot happen when ua = ub) */
        len[nc++] = l;
    }
    for (int x = 0; x < nc; x++) for (int y = x + 1; y < nc; y++) if (len[y] > len[x]) { int t = len[x]; len[x] = len[y]; len[y] = t; }
    char nm[64]; nm[0] = 0;
    for (int x = 0; x < nc; x++) { char w[8]; snprintf(w, sizeof w, x ? "+%d" : "%d", len[x]); strcat(nm, w); }
    *cy = NCYC - 1;
    for (int c = 0; c < NCYC - 1; c++) if (!strcmp(nm, CYCNAME[c])) *cy = c;
    return 1;
}
static const char *T1NAME[3] = {"rel", "grow", "pool"};
static const char *XSNAME[3] = {"xJ", "xZ", "xH"};
static const char *HKNAME[4] = {"h-", "hR", "hJ", "hZ"};

/* ---------- per profile ---------- */
typedef struct { long prof, om1, small, ks[6], kn, kiso, ktrap, pos, pd[6], piso, ptrap, pmpos, pm3, maxmin; } cnt_t;
/* dl2.c's counters: ks: profiles with k* = 0, 1, 2, 3, >= 4, inf; kn: with k* = n; kiso / ktrap: with k* >= 3 (finite)
   where every P at distance >= 3 is isolated / some is not; pd: P with def > 0 at distance 1, 2, 3, >= 4, inf; piso /
   ptrap: P at distance >= 3, isolated / not; pmpos / pm3: P with def > 0 that are Pareto-maximal / and at distance >= 3 */
static cnt_t CN;
typedef struct { long st0, st1, fail0, fail1, t1only, t3only, both, t3p, t3h, t3honly, anom, rd[4]; } cnt13_t;
static cnt13_t CL;                                   /* dl13.c's counters (R_13), the "L" line */
typedef struct { long fail0, fail1, t1, t3, t4, t4only, t4only2, t4onlyL, t4sw, rd[5]; } cnt134_t;
static cnt134_t CM;                                  /* R_134, the "M" line */
static long nT3only = 0, nOther = 0, nT4only = 0, nfail0dump = 0;   /* per process: dump counters */

static void pmaskj(FILE *f, msk M) { int first = 1; fputc('[', f); for (int g = 0; g < MAXM; g++) if (M >> g & 1) { fprintf(f, first ? "%d" : ",%d", g); first = 0; } fputc(']', f); }
static void pbases(FILE *f, const unsigned char *ix) { fputc('[', f); for (int i = 0; i < n; i++) { if (i) fputc(',', f); pmaskj(f, opt[i][ix[i]]); } fputc(']', f); }

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
    int kstar = 0;
    static int *dd = 0, *nn = 0;
    static long capd = 0;
    if (npp > capd) { capd = npp; dd = realloc(dd, sizeof(int) * capd); nn = realloc(nn, sizeof(int) * capd); }
    int anytrap = 0;
    if (npp > BIGPP) hbuild();
    /* first pass (dl2.c): distances */
    for (long p = 0; p < npp; p++) {
        dd[p] = -1; nn[p] = -1;
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
    if (CN.om1 == 1 || mindef > CN.maxmin) CN.maxmin = mindef;
    if (VERB) {
        printf("V %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]);
        printf(" %d %ld %d %d\n", kstar == 99 ? -1 : kstar, npp, npos, mindef);
    }
    /* second pass: R_134 and the signature of every P with def > 0 */
    for (long p = 0; p < npp; p++) {
        if (PI[p].def <= 0) continue;
        const unsigned char *ia = PP + p * MAXN;
        /* R_134 (T1, T3: dl13.c's r13; T4: t4test) */
        int t1 = 0, t3p = 0, t3h = 0, t4 = 0, t1m = 0, t3m = 0, t4m = 0, dT1 = INF, dT3 = INF, dT4 = INF, rd13 = 99, rd = 99;
        long wit = -1; int wdef = INF, wmov = 1 << 20, wk = 0, wcy = 0;
        if (npp <= BIGPP) fill_cand(p, 1); else fill_cand134(p);
        for (long c = 0; c < ncand; c++) {
            long q = cand[c];
            if (PI[q].def >= PI[p].def) continue;
            int ty = 0, k = r13(p, q, &ty);
            if (!k && t4test(p, q, &ty)) k = 4;
            if (!k) continue;
            const unsigned char *ib = PP + q * MAXN; int d = 0, mov = 0;
            for (int i = 0; i < n; i++) if (ia[i] != ib[i]) { d++; mov += pc(opt[i][ia[i]] ^ opt[i][ib[i]]); }
            if (d < rd) rd = d;
            if (k < 4 && d < rd13) rd13 = d;
            if (k == 1) { t1 = 1; t1m |= 1 << ty; if (PI[q].def < dT1) dT1 = PI[q].def; }
            else if (k < 4) { if (k == 2) t3p = 1; else t3h = 1; t3m |= 1 << ty; if (PI[q].def < dT3) dT3 = PI[q].def; }
            else { t4 = 1; t4m |= 1 << ty; if (PI[q].def < dT4) dT4 = PI[q].def; }
            if (PI[q].def < wdef || (PI[q].def == wdef && (mov < wmov || (mov == wmov && q < wit)))) { wdef = PI[q].def; wmov = mov; wit = q; wk = k; wcy = ty; }
        }
        int ok13 = t1 || t3p || t3h, ok = ok13 || t4;
        /* signature (dl2.c) */
        msk best = 0; int sig = 0;
        if (PI[p].def >= INF) sig |= 1 << C_ALLF;
        else for (int o = 0; o < n; o++) if (PI[p].bestown[o] == PI[p].def) best |= BIT(o);
        for (int o = 0; o < n; o++) if (best >> o & 1) for (int x = 0; x < n; x++) if (PI[p].expo[o] >> x & 1) sig |= 1 << classify(ia, &PI[p], x, o);
        for (int x = 0; x < n; x++) if (PI[p].frozen >> x & 1) { int c = 0; for (int o = 0; o < n; o++) if (PI[p].expo[o] >> x & 1) c++; if (c >= 2) sig |= 1 << C_D2; }
        int pm = 1;
        for (long q = 0; q < npp && pm; q++) {
            if (q == p) continue;
            const unsigned char *ib = PP + q * MAXN; int ge = 1, gt = 0;
            for (int i = 0; i < n && ge; i++) { int a = optv[i][ia[i]], b = optv[i][ib[i]]; if (b < a) ge = 0; else if (b > a) gt = 1; }
            if (ge && gt) pm = 0;
        }
        if (pm) { sig |= 1 << C_PM; CN.pmpos++; if (dd[p] >= 3) CN.pm3++; }
        char sigs[128]; sigs[0] = 0;
        for (int c = 0; c < NCLS; c++) if (sig >> c & 1) { if (sigs[0]) strcat(sigs, ","); strcat(sigs, CLSNAME[c]); }
        char br[32]; br[0] = 0;
        if (t1) strcat(br, "T1");
        if (t3p) strcat(br, br[0] ? "+T3p" : "T3p");
        if (t3h) strcat(br, br[0] ? "+T3h" : "T3h");
        if (t4) strcat(br, br[0] ? "+T4" : "T4");
        if (!br[0]) strcpy(br, "none");
        char t4s[256]; t4s[0] = 0;
        for (int c = 0; c < NCYC; c++) if (t4m >> c & 1) { if (t4s[0]) strcat(t4s, ","); strcat(t4s, CYCNAME[c]); }
        if (SVERB) {
            printf("S %d", bestf); for (int i = 0; i < n; i++) printf(" %llu", (unsigned long long)opt[i][ia[i]]);
            printf(" %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %s\n", PI[p].def, dd[p], rd13, rd, t1, t3p, t3h, t4, t1m, t3m,
                   t4m, dT1, dT3, dT4, pm, sigs[0] ? sigs : "-");
        }
        int dumpit = 0;
        if (bestf == 0) {
            CL.st0++;
            if (!ok13) CL.fail0++;
            if (!ok) { CM.fail0++; if (nfail0dump < 5) { nfail0dump++; dumpit = 1; } }
        } else {
            /* dl13.c's counters (R_13) */
            CL.st1++;
            if (!ok13) CL.fail1++;
            if (t1 && !(t3p || t3h)) CL.t1only++;
            if (!t1 && (t3p || t3h)) CL.t3only++;
            if (t1 && (t3p || t3h)) CL.both++;
            if (t3p) CL.t3p++;
            if (t3h) CL.t3h++;
            if (t3h && !t3p && !t1) CL.t3honly++;
            CL.rd[rd13 >= 4 ? 0 : rd13]++;                  /* rd13 99 (none) and >= 4 (impossible) in slot 0 */
            /* R_134 */
            if (!ok) { CM.fail1++; dumpit = 1; }
            if (t1) CM.t1++;
            if (t3p || t3h) CM.t3++;
            if (t4) CM.t4++;
            if (t4m & 1) CM.t4sw++;
            if (t4 && !ok13) { CM.t4only++; if (t4m & 1) CM.t4only2++; else CM.t4onlyL++; }
            CM.rd[rd == 99 ? 0 : rd >= 4 ? 4 : rd]++;
            char key[512];
            snprintf(key, sizeof key, "B %d|%s|%s", bestf, sigs, br); (*mslot(&TAB, key))++;
            snprintf(key, sizeof key, "G %d|%d|%s", bestf, dd[p] == 99 ? -1 : dd[p], br); (*mslot(&TAB, key))++;
            for (int k = 0; k < 3; k++) if (t1m >> k & 1) { snprintf(key, sizeof key, "Y %d|%s|T1:%s", bestf, br, T1NAME[k]); (*mslot(&TAB, key))++; }
            for (int k = 0; k < 12; k++) if (t3m >> k & 1) { snprintf(key, sizeof key, "Y %d|%s|T3:%s.%s", bestf, br, XSNAME[k / 4], HKNAME[k % 4]); (*mslot(&TAB, key))++; }
            for (int k = 0; k < NCYC; k++) if (t4m >> k & 1) { snprintf(key, sizeof key, "Y %d|%s|T4:%s", bestf, br, CYCNAME[k]); (*mslot(&TAB, key))++; }
            if (t4 && !ok13) { snprintf(key, sizeof key, "Q %d|%d|%s", bestf, dd[p] == 99 ? -1 : dd[p], t4s); (*mslot(&TAB, key))++; }
            snprintf(key, sizeof key, "%s|%s", sigs, br);
            long *seen = mslot(&SEEN, key);
            if (!*seen) { *seen = 1; dumpit = 1; }
            if (t4 && !ok13) { nT4only++; if (RQ > 0 && (nT4only - 1) % RQ == 0) dumpit = 1; }
            if (!t1 && ok) { nT3only++; if (RT > 0 && (nT3only - 1) % RT == 0) dumpit = 1; }
            else if (ok) { nOther++; if (RO > 0 && (nOther - 1) % RO == 0) dumpit = 1; }
        }
        if (dumpit) {
            printf("D {\"tag\":%d,\"prof\":[", tag); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", cur[i]);
            printf("],\"f\":%d,\"omega\":%d,\"nmin\":%ld,\"B\":", bestf, omega, npp); pbases(stdout, ia);
            printf(",\"def\":%d,\"k\":%d,\"nn\":%d,\"pm\":%d,\"sig\":\"%s\",\"br\":\"%s\",\"r13d\":%d,\"rd\":%d,\"dT1\":%d,\"dT3\":%d,"
                   "\"dT4\":%d,\"t1types\":[",
                   PI[p].def >= INF ? -1 : PI[p].def, dd[p] == 99 ? -1 : dd[p], nn[p] == 99 ? -1 : nn[p], pm, sigs, br,
                   rd13 == 99 ? -1 : rd13, rd == 99 ? -1 : rd, dT1 >= INF ? -1 : dT1, dT3 >= INF ? -1 : dT3, dT4 >= INF ? -1 : dT4);
            int f1 = 1; for (int k = 0; k < 3; k++) if (t1m >> k & 1) { printf(f1 ? "\"%s\"" : ",\"%s\"", T1NAME[k]); f1 = 0; }
            printf("],\"t3types\":["); f1 = 1;
            for (int k = 0; k < 12; k++) if (t3m >> k & 1) { printf(f1 ? "\"%s.%s\"" : ",\"%s.%s\"", XSNAME[k / 4], HKNAME[k % 4]); f1 = 0; }
            printf("],\"t4types\":["); f1 = 1;
            for (int k = 0; k < NCYC; k++) if (t4m >> k & 1) { printf(f1 ? "\"%s\"" : ",\"%s\"", CYCNAME[k]); f1 = 0; }
            printf("],\"frozen\":"); { msk F = PI[p].frozen; int ff = 1; printf("["); for (int i = 0; i < n; i++) if (F >> i & 1) { printf(ff ? "%d" : ",%d", i); ff = 0; } printf("]"); }
            printf(",\"J\":"); pmaskj(stdout, PI[p].J);
            printf(",\"own\":["); f1 = 1;
            for (int o = 0; o < n; o++) if (!(PI[p].frozen >> o & 1)) { printf(f1 ? "[%d,%d]" : ",[%d,%d]", o, PI[p].bestown[o] >= INF ? -1 : PI[p].bestown[o]); f1 = 0; }
            printf("],\"exp\":["); f1 = 1;
            for (int o = 0; o < n; o++) for (int x = 0; x < n; x++) if (PI[p].expo[o] >> x & 1) { printf(f1 ? "[%d,%d,\"%s\"]" : ",[%d,%d,\"%s\"]", o, x, CLSNAME[classify(ia, &PI[p], x, o)]); f1 = 0; }
            printf("]");
            if (wit >= 0) {
                printf(",\"W\":"); pbases(stdout, PP + wit * MAXN);
                printf(",\"defW\":%d,\"wkind\":\"%s\"", PI[wit].def, wk == 1 ? "T1" : wk == 2 ? "T3p" : wk == 3 ? "T3h" : "T4");
                if (wk == 4) printf(",\"wcycle\":\"%s\"", CYCNAME[wcy]);
            }
            if (t4 && !ok13) {                              /* the improving T4 moves, in the order of P (at most 100) */
                printf(",\"t4moves\":["); f1 = 1; int cnt = 0; long last = -1;
                for (;;) {
                    long nx = -1; int cy = 0;               /* the least candidate after last that is an improving T4 move */
                    for (long c = 0; c < ncand; c++) { long q = cand[c]; if (q > last && (nx < 0 || q < nx) && PI[q].def < PI[p].def && t4test(p, q, &cy)) nx = q; }
                    if (nx < 0 || cnt == 100) break;
                    t4test(p, nx, &cy); last = nx;
                    if (!f1) { printf(","); } f1 = 0;
                    printf("{\"B\":"); pbases(stdout, PP + nx * MAXN); printf(",\"def\":%d,\"cycle\":\"%s\"}", PI[nx].def, CYCNAME[cy]); cnt++;
                }
                printf("]");
            }
            if (!ok) {                                      /* every min-frozen P' with a smaller deficit (at most 400) */
                printf(",\"better\":["); f1 = 1; int cnt = 0;
                for (long q = 0; q < npp && cnt < 400; q++) if (PI[q].def < PI[p].def) { if (!f1) printf(","); f1 = 0; printf("{\"B\":"); pbases(stdout, PP + q * MAXN); printf(",\"def\":%d}", PI[q].def); cnt++; }
                printf("]");
            }
            printf("}\n");
        }
    }
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-v")) VERB = 1;
        else if (!strcmp(argv[a], "-s")) SVERB = VERB = 1;
        else if (!strncmp(argv[a], "-r", 2)) RT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-o", 2)) RO = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-q", 2)) RQ = atoi(argv[a] + 2);
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
        memset(&CN, 0, sizeof CN); memset(&CL, 0, sizeof CL); memset(&CM, 0, sizeof CM); ANOM = 0;
        mclear(&TAB);
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
        CL.anom = ANOM;
        printf("K %d prof %ld om1 %ld small %ld kstar0 %ld kstar1 %ld kstar2 %ld kstar3 %ld kstar4 %ld kstarinf %ld kstarn %ld "
               "kiso %ld ktrap %ld pos %ld pd1 %ld pd2 %ld pd3 %ld pd4 %ld pdinf %ld piso %ld ptrap %ld pmpos %ld pm3 %ld maxmin %ld\n",
               tag, CN.prof, CN.om1, CN.small, CN.ks[0], CN.ks[1], CN.ks[2], CN.ks[3], CN.ks[4], CN.ks[5], CN.kn,
               CN.kiso, CN.ktrap, CN.pos, CN.pd[1], CN.pd[2], CN.pd[3], CN.pd[4], CN.pd[5], CN.piso, CN.ptrap, CN.pmpos, CN.pm3, CN.maxmin);
        printf("L %d st0 %ld st1 %ld fail0 %ld fail1 %ld t1only %ld t3only %ld both %ld t3p %ld t3h %ld t3hOnly %ld anom %ld "
               "r13dnone %ld r13d1 %ld r13d2 %ld r13d3 %ld\n", tag, CL.st0, CL.st1, CL.fail0, CL.fail1, CL.t1only, CL.t3only,
               CL.both, CL.t3p, CL.t3h, CL.t3honly, CL.anom, CL.rd[0], CL.rd[1], CL.rd[2], CL.rd[3]);
        printf("M %d fail0 %ld fail1 %ld t1 %ld t3 %ld t4 %ld t4only %ld t4only2 %ld t4onlyL %ld t4sw %ld rdnone %ld rd1 %ld rd2 %ld "
               "rd3 %ld rd4 %ld\n", tag, CM.fail0, CM.fail1, CM.t1, CM.t3, CM.t4, CM.t4only, CM.t4only2, CM.t4onlyL, CM.t4sw,
               CM.rd[0], CM.rd[1], CM.rd[2], CM.rd[3], CM.rd[4]);
        for (long i = 0; i < TAB.cap; i++) if (TAB.t[i].k) printf("%s %ld\n", TAB.t[i].k, TAB.t[i].c);
        fflush(stdout);
    }
    return 0;
}
