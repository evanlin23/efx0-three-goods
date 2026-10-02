/* k4/oneneeder.c -- the one-needer regime at the T3 stage, f = 1 (workstream proof/k4-oneneeder; k4/oneneeder.md).
EVIDENCE only.

For every strict profile in the input whose fewest frozen agents is f = 1 (and omega = 1 - (2n - m) >= 1), every
min-frozen P (the space of k4/c4x.md section 1: bases of at most two goods inside R_i, value-based needs, every needed
good a one-good base) is evaluated: its frozen agent x with base {g}, its deficit def(P) = omega + 2 - V(P) (Lemma H1 of
k4/hall.md; V(P) = max over free o and safe bundles Z of |Z| + u_o(Z)), and its key (x, g). A state P is *at the T3
stage* if def(P) > 0 and def(P) is the least deficit of the min-frozen P' with the same key (at f = 1 no (T4) move
exists, and (T1), (T2) are exactly the moves inside a key, k4/dl2.md section 3). P is *one-needer* if exactly one agent
z needs g. At every one-needer T3-stage state the tool records:
  bt     x is big-top on g: four goods, g its top, v(g) > v(b) + v(c) (b, c its second and third goods);
  d1     def(P) = 1;
  sx1    some best owner o, some optimal bundle X of o and some c in J minus X such that X + c threatens x holding {g}
         and no other agent w != o holding B_w (an "x-alone triple"); sx1o: such a triple with o != z; sx1z: with o = z;
  u      some best owner has an optimal bundle with u_o = 1 (it unfreezes x);
  c3     Corollary 8.2 of k4/dl13.md applies with at most one helper: x big-top on its top g, L = R_x minus g; a helper
         h (none, or a free agent h != z) with L inside G = J + B_z + B_h, a base B'_h inside (G minus L) cap R_h with
         at most two goods, giving up a good of B_h, N_h(B'_h) inside NA and g not in N_h(B'_h); a bundle Z of x in P'
         (L inside Z inside G minus B'_h) that threatens no agent w holding its P' base (B_w; z: {g}; h: B'_h); and
         |Z| + 1 > V(P). For each such swap with A = {b, c} the swapped P' is looked up in the min-frozen class and
         def(P') <= omega + 1 - |Z| and def(P') < def(P) are asserted (the conclusion of Corollary 8.2). c3h: the
         helper kinds that work ("-": none, "o": a best owner of P, "y": another free agent);
  t3     some (T3) move lowers the deficit (exact scan: a min-frozen P' with def(P') < def(P) in which x is free, z
         holds {g} alone, at most one other agent's base differs and that agent gives up a good, nobody else changes
         frozen status);
  twin   R_z = R_x.
With -t1 the same is done at every *T1-stuck* state (def(P) > 0 and no (T1) move lowers it) instead of the T3-stage
ones (the counters keep their names: "t3stage" then counts T1-stuck states).
Counters per block, and "D {json}" dumps of every one-needer T3-stage state where bt, d1, sx1, c3 or t3 fails, of
every T3-stage state where no (T3) move lowers the deficit, and of every R-th one-needer T3-stage state (-rR).

Input (stdin): k4/dlrt4.c's blocks ("n m tag" / n lines "d g1 .. gd" / "K_0 .. K_{n-1}" / per agent K_i lines of d
values / "P" and, if P < 0, -P lines of n domain indices; P = 0 every profile, P > 0 P random profiles seeded by -S and
tag with dlrt4.c's generator). The min-frozen enumeration (dfsP) and the threat and needs tables are dlrt4.c's code.
Build: gcc -O2 k4/oneneeder.c (m <= 32, n <= 16). Driver: k4/oneneeder_run.py. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
#define MAXM 32
#define INF 999999
typedef uint32_t msk;
#define pc(x) __builtin_popcount(x)
#define ctz(x) __builtin_ctz(x)
#define BIT(g) ((msk)1 << (g))

static int n, m, tag;
static int deg[MAXN], R[MAXN][4];
static msk Rm[MAXN], ALL;
static int K[MAXN], *dom[MAXN];
static int v[MAXN][MAXM], cur[MAXN];
static int RR = 0, T1MODE = 0; static uint64_t SEED = 1;

static int ssum[MAXN][16], smin[MAXN][16];
static int topg[MAXN], bigtop[MAXN], rk[MAXN][4];
static inline int sidx(int i, msk X) { int s = 0; for (int k = 0; k < deg[i]; k++) if (X >> R[i][k] & 1) s |= 1 << k; return s; }
static inline int val(int i, msk X) { return ssum[i][sidx(i, X)]; }
static inline int threat(int i, msk X, int h) {      /* max over h' in X of v_i(X minus h') > h */
    if (!X) return 0;
    int s = sidx(i, X);
    if (X & ~Rm[i]) return ssum[i][s] > h;
    return ssum[i][s] - smin[i][s] > h;
}
static inline msk needs(int i, msk X) {
    int b = val(i, X); msk N = 0;
    for (int k = 0; k < deg[i]; k++) { int g = R[i][k]; if (!(X >> g & 1) && v[i][g] > b) N |= BIT(g); }
    return N;
}

/* ---------- the min-frozen pre-allocations (dlrt4.c / dl2.c) ---------- */
static msk opt[MAXN][11], optN[MAXN][11]; static int optv[MAXN][11], nopt[MAXN];
static int bestf, sigma;
static unsigned char cidx[MAXN];
static unsigned char *PP = 0; static long npp = 0, capp = 0;
static int found_small;
static void dfs_small(int i, msk used, msk NA, msk S1, msk S2) {
    if (found_small || pc(NA) > sigma || (NA & S2)) return;
    if (i == n) { if (!(NA & ~S1)) found_small = 1; return; }
    for (int t = 0; t < nopt[i] && !found_small; t++) { msk B = opt[i][t]; if (B & used) continue;
        dfs_small(i + 1, used | B, NA | optN[i][t], pc(B) == 1 ? S1 | B : S1, pc(B) == 2 ? S2 | B : S2); }
}
static void dfsP(int i, msk used, msk NA, msk S1, msk S2) {
    if (pc(NA) > bestf || (NA & S2)) return;
    if (i == n) {
        if (NA & ~S1) return;
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

/* ---------- per P ---------- */
typedef struct { int def, V, x, g; msk J, NA, F; int val[MAXN]; } pinfo_t;
static pinfo_t *PI = 0; static long capi = 0;
static int omega;

/* u_o(Z) at f = 1: x is counted iff g is in no N_j (j != o) and not in N_o(Z) */
static void eval_P(const unsigned char *ix, pinfo_t *pi) {
    msk B[MAXN], N[MAXN], NA = 0, U = 0; int hv[MAXN];
    for (int i = 0; i < n; i++) { B[i] = opt[i][ix[i]]; N[i] = optN[i][ix[i]]; hv[i] = optv[i][ix[i]]; NA |= N[i]; U |= B[i]; }
    msk J = ALL & ~U, F = 0;
    for (int i = 0; i < n; i++) if (pc(B[i]) == 1 && (B[i] & NA)) F |= BIT(i);
    pi->J = J; pi->NA = NA; pi->F = F;
    pi->x = F ? ctz(F) : -1; pi->g = pi->x >= 0 ? ctz(B[pi->x]) : -1;
    int V = -1;
    for (int o = 0; o < n; o++) {
        pi->val[o] = -1;
        if (F >> o & 1) continue;
        msk NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= N[j];
        int best = -1;
        msk K = J;
        for (;;) {
            msk Z = B[o] | K; int ok = 1;
            for (int w = 0; w < n && ok; w++) if (w != o && threat(w, Z, hv[w])) ok = 0;
            if (ok) {
                msk NA2 = NAo | needs(o, Z); int u = 0;
                for (int j = 0; j < n; j++) if (j != o && (F >> j & 1) && !(B[j] & NA2)) u++;
                if (pc(Z) + u > best) best = pc(Z) + u;
            }
            if (!K) break;
            K = (K - 1) & J;
        }
        pi->val[o] = best;
        if (best > V) V = best;
    }
    pi->V = V;
    pi->def = V < 0 ? INF : omega + 2 - V;
}

/* hash: base indices -> class position */
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
static int optindex(int i, msk B) { for (int t = 0; t < nopt[i]; t++) if (opt[i][t] == B) return t; return -1; }

/* ---------- counters ---------- */
enum { C_PROF, C_F1, C_ST, C_T3S, C_T3S1, C_T3SM, C_BT, C_NBT, C_D1, C_SX1, C_SX1O, C_SX1Z, C_NOSX1, C_U, C_C3, C_NOC3,
       C_C3N, C_C3O, C_C3Y, C_T3, C_NOT3, C_NOT3ANY, C_TWIN, C_ZBT, C_DEF2, C_RC, C_RE, C_RCE, C_RNONE, C_T3BT, C_T3BTD1, NC };
static const char *CNAME[NC] = {"prof", "f1om1", "states", "t3stage", "t3stage_1needer", "t3stage_more_needers", "bt",
    "not_bt", "def1", "sx1", "sx1_o_not_z", "sx1_o_is_z", "no_sx1", "u_at_best", "c3", "no_c3", "c3_nohelper",
    "c3_helper_best", "c3_helper_other", "t3move", "no_t3move_1needer", "no_t3move_any_t3stage", "twin", "z_bigtop",
    "def_ge2", "propC", "escape", "propC_or_escape", "no_rule", "t3stage_x_bigtop", "t3stage_x_bigtop_def1"};
static long CNT[NC];

static void pmaskj(FILE *f, msk M) { int first = 1; fputc('[', f); for (int g = 0; g < MAXM; g++) if (M >> g & 1) { fprintf(f, first ? "%d" : ",%d", g); first = 0; } fputc(']', f); }
static void pbases(FILE *f, const unsigned char *ix) { fputc('[', f); for (int i = 0; i < n; i++) { if (i) fputc(',', f); pmaskj(f, opt[i][ix[i]]); } fputc(']', f); }

/* -t1: P is T1-stuck: no re-base of one free agent y to B' inside (B_y + J) cap R_y, |B'| <= 2, B' != B_y, with
   N_y(B') inside NA (k4/dl2.md Lemma 1(c)), lowers the deficit */
static int t1stuck(long p) {
    const unsigned char *ia = PP + p * MAXN; const pinfo_t *a = &PI[p];
    for (int y = 0; y < n; y++) {
        if (a->F >> y & 1) continue;
        for (int t = 0; t < nopt[y]; t++) {
            if (t == ia[y]) continue;
            msk B = opt[y][t];
            if (B & ~(opt[y][ia[y]] | a->J)) continue;
            if (optN[y][t] & ~a->NA) continue;
            unsigned char ib[MAXN]; memcpy(ib, ia, MAXN); ib[y] = (unsigned char)t;
            long q = hfind(pkey(ib));
            if (q < 0) { fprintf(stderr, "Lemma 1(c) violated (tag %d)\n", tag); exit(3); }
            if (PI[q].def < a->def) return 0;
        }
    }
    return 1;
}

/* is there an improving (T3) move from P = PP[p] (exact scan of the class)? */
static int t3move(long p) {
    const unsigned char *ia = PP + p * MAXN; const pinfo_t *a = &PI[p];
    int x = a->x; msk g = BIT(a->g);
    for (long q = 0; q < npp; q++) {
        const pinfo_t *b = &PI[q];
        if (b->def >= a->def) continue;
        const unsigned char *ib = PP + q * MAXN;
        if (b->NA != a->NA) continue;                       /* the needed set is kept (f = 1: NA = {g}) */
        if (b->F >> x & 1) continue;                        /* x unfreezes */
        int z = b->x; if (z < 0 || z == x || (a->F >> z & 1)) continue;
        if (opt[z][ib[z]] != g || !(optN[z][ia[z]] & g)) continue;   /* z needed g and takes it */
        msk ch = 0; for (int i = 0; i < n; i++) if (ia[i] != ib[i]) ch |= BIT(i);
        msk Y = ch & ~BIT(x) & ~BIT(z);
        if (pc(Y) > 1) continue;
        if (Y) { int h = ctz(Y); if (!(opt[h][ia[h]] & ~opt[h][ib[h]])) continue; }
        return 1;
    }
    return 0;
}

/* Corollary 8.2 with at most one helper; returns a mask of helper kinds that work (1: none, 2: a best owner, 4: other) */
static int c3test(long p, int z, int *bestZ) {
    const unsigned char *ia = PP + p * MAXN; const pinfo_t *a = &PI[p];
    int x = a->x, g = a->g;
    if (!bigtop[x] || topg[x] != g) return 0;
    msk L = Rm[x] & ~BIT(g), B[MAXN]; int hv[MAXN];
    for (int i = 0; i < n; i++) { B[i] = opt[i][ia[i]]; hv[i] = optv[i][ia[i]]; }
    int kinds = 0; *bestZ = -1;
    for (int h = -1; h < n; h++) {
        if (h == x || h == z || (h >= 0 && (a->F >> h & 1))) continue;
        msk G = a->J | B[z] | (h >= 0 ? B[h] : 0);
        if (L & ~G) continue;
        msk cands[64]; int nc = 0;
        if (h < 0) cands[nc++] = 0;
        else {
            msk Hp = (G & ~L) & Rm[h];
            for (msk S = Hp;; S = (S - 1) & Hp) {
                if (pc(S) >= 1 && pc(S) <= 2 && (B[h] & ~S)) {
                    msk Nh = needs(h, S);
                    if (!(Nh & ~a->NA) && !(Nh & BIT(g))) cands[nc++] = S;
                }
                if (!S) break;
            }
        }
        for (int c = 0; c < nc; c++) {
            msk Bh = cands[c];
            int hold[MAXN]; for (int w = 0; w < n; w++) hold[w] = hv[w];
            hold[z] = v[z][g];
            if (h >= 0) hold[h] = val(h, Bh);
            msk W = G & ~Bh, rest = W & ~L;
            int best = -1;
            for (msk K = rest;; K = (K - 1) & rest) {
                msk Z = L | K; int ok = 1;
                if (pc(Z) > best) {
                    for (int w = 0; w < n && ok; w++) if (w != x && threat(w, Z, hold[w])) ok = 0;
                    if (ok) best = pc(Z);
                }
                if (!K) break;
            }
            if (best < 0 || best + 1 <= a->V) continue;
            /* the swap with A = {b, c}: assert Corollary 8.2's conclusion */
            msk A = BIT(rk[x][1]) | BIT(rk[x][2]);
            unsigned char ib[MAXN]; memcpy(ib, ia, MAXN);
            ib[z] = (unsigned char)optindex(z, BIT(g)); ib[x] = (unsigned char)optindex(x, A);
            if (h >= 0) ib[h] = (unsigned char)optindex(h, Bh);
            long q = hfind(pkey(ib));
            if (q < 0) { fprintf(stderr, "Lemma 6 violated: swap not in the class (tag %d)\n", tag); exit(3); }
            if (!(PI[q].def <= omega + 1 - best && PI[q].def < a->def)) { fprintf(stderr, "Corollary 8.2 violated (tag %d)\n", tag); exit(3); }
            int kind = h < 0 ? 1 : (a->val[h] == a->V ? 2 : 4);
            kinds |= kind;
            if (best > *bestZ) *bestZ = best;
        }
    }
    return kinds;
}

/* x-alone triples at best owners: bit 1 some with o != z, bit 2 some with o = z; *uflag: some optimal bundle with u = 1 */
static int sx1test(long p, int z, int *uflag) {
    const unsigned char *ia = PP + p * MAXN; const pinfo_t *a = &PI[p];
    int x = a->x; msk B[MAXN], N[MAXN]; int hv[MAXN];
    for (int i = 0; i < n; i++) { B[i] = opt[i][ia[i]]; N[i] = optN[i][ia[i]]; hv[i] = optv[i][ia[i]]; }
    int res = 0; *uflag = 0;
    for (int o = 0; o < n; o++) {
        if ((a->F >> o & 1) || a->val[o] != a->V) continue;
        msk NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= N[j];
        msk J = a->J;
        for (msk K = J;; K = (K - 1) & J) {
            msk X = B[o] | K; int ok = 1;
            for (int w = 0; w < n && ok; w++) if (w != o && threat(w, X, hv[w])) ok = 0;
            if (ok) {
                msk NA2 = NAo | needs(o, X); int u = 0;
                for (int j = 0; j < n; j++) if (j != o && (a->F >> j & 1) && !(B[j] & NA2)) u++;
                if (pc(X) + u == a->V) {
                    if (u) *uflag = 1;
                    msk C = J & ~X;
                    for (int c = 0; c < MAXM; c++) if (C >> c & 1) {
                        msk Y = X | BIT(c); int onlyx = threat(x, Y, hv[x]);
                        for (int w = 0; w < n && onlyx; w++) if (w != o && w != x && threat(w, Y, hv[w])) onlyx = 0;
                        if (onlyx) res |= (o == z) ? 2 : 1;
                    }
                }
            }
            if (!K) break;
        }
    }
    return res;
}

/* the two constructions of k4/oneneeder.md section 4 at the x-alone triples of P: bit 1 Proposition C (o = z, u = 0, and Y
   safe for z, or z big-top with L_z != L, or L_z = L and omega = 2); bit 2 an escape of o != z (a need-free B' inside
   (Y + Rest) minus L, Rest = (J minus Y) + B_z, with |B' cap Y| <= 1, B' missing a good of B_o or B' = B_o = one good
   outside L, and Y minus B' not threatening o holding B'). Each construction's swap is checked: Z threatens nobody in P'
   and def(P') <= omega + 1 - |Z| for the swapped state looked up in the class. */
static int swapcheck(long p, int x, int z, int h, msk Bh, msk Z) {
    const unsigned char *ia = PP + p * MAXN; int g = PI[p].g;
    int hold[MAXN]; for (int w = 0; w < n; w++) hold[w] = optv[w][ia[w]];
    hold[z] = v[z][g]; if (h >= 0) hold[h] = val(h, Bh);
    for (int w = 0; w < n; w++) if (w != x && threat(w, Z, hold[w])) return 0;
    msk A = BIT(rk[x][1]) | BIT(rk[x][2]);
    unsigned char ib[MAXN]; memcpy(ib, ia, MAXN);
    ib[z] = (unsigned char)optindex(z, BIT(g)); ib[x] = (unsigned char)optindex(x, A);
    if (h >= 0) ib[h] = (unsigned char)optindex(h, Bh);
    long q = hfind(pkey(ib));
    if (q < 0) { fprintf(stderr, "swap not in the class (tag %d)\n", tag); exit(3); }
    if (PI[q].def > omega + 1 - pc(Z)) { fprintf(stderr, "Corollary 8.2 bound violated in rules (tag %d)\n", tag); exit(3); }
    return 1;
}
static int rules(long p, int z) {
    const unsigned char *ia = PP + p * MAXN; const pinfo_t *a = &PI[p];
    int x = a->x, g = a->g; msk B[MAXN], N[MAXN]; int hv[MAXN];
    for (int i = 0; i < n; i++) { B[i] = opt[i][ia[i]]; N[i] = optN[i][ia[i]]; hv[i] = optv[i][ia[i]]; }
    if (!bigtop[x] || topg[x] != g) return 0;
    msk L = Rm[x] & ~BIT(g);
    int res = 0;
    for (int o = 0; o < n; o++) {
        if ((a->F >> o & 1) || a->val[o] != a->V) continue;
        msk NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= N[j];
        msk J = a->J;
        for (msk K = J;; K = (K - 1) & J) {
            msk X = B[o] | K; int ok = 1;
            for (int w = 0; w < n && ok; w++) if (w != o && threat(w, X, hv[w])) ok = 0;
            if (ok) {
                msk NA2 = NAo | needs(o, X); int u = 0;
                for (int j = 0; j < n; j++) if (j != o && (a->F >> j & 1) && !(B[j] & NA2)) u++;
                if (pc(X) + u == a->V) {
                    msk C = J & ~X;
                    for (int c = 0; c < MAXM; c++) if (C >> c & 1) {
                        msk Y = X | BIT(c); int onlyx = threat(x, Y, hv[x]);
                        for (int w = 0; w < n && onlyx; w++) if (w != o && w != x && threat(w, Y, hv[w])) onlyx = 0;
                        if (!onlyx) continue;
                        if (o == z) {
                            if (u) continue;
                            if (!threat(z, Y, v[z][g])) { if (!swapcheck(p, x, z, -1, 0, Y)) { fprintf(stderr, "Prop C (Y) fails (tag %d)\n", tag); exit(3); } res |= 1; continue; }
                            if (!(bigtop[z] && topg[z] == g)) { fprintf(stderr, "Corollary B2 violated (tag %d)\n", tag); exit(3); }
                            msk Lz = Rm[z] & ~BIT(g);
                            if (Lz != L) {
                                int l = ctz(Lz & ~L);
                                if (!swapcheck(p, x, z, -1, 0, Y & ~BIT(l))) { fprintf(stderr, "Prop C (Y - l) fails (tag %d)\n", tag); exit(3); }
                                res |= 1;
                            } else if (omega == 2) {
                                if (!swapcheck(p, x, z, -1, 0, L)) { fprintf(stderr, "Prop C (twin) fails (tag %d)\n", tag); exit(3); }
                                res |= 1;
                            }
                        } else {
                            msk Rest = (J & ~Y) | B[z];
                            msk reg = (Y | Rest) & ~L & Rm[o] & ~BIT(g);
                            for (msk S = reg; S; S = (S - 1) & reg) {
                                if (pc(S) > 2 || pc(S & Y) > 1 || needs(o, S)) continue;
                                int helper = (B[o] & ~S) != 0;
                                if (!helper && !(S == B[o] && !(L & B[o]) && pc(B[o]) == 1)) continue;
                                if (threat(o, Y & ~S, val(o, S))) continue;
                                if (!swapcheck(p, x, z, helper ? o : -1, helper ? S : 0, Y & ~S)) { fprintf(stderr, "escape swap fails (tag %d)\n", tag); exit(3); }
                                res |= 2; break;
                            }
                        }
                    }
                }
            }
            if (!K) break;
        }
    }
    return res;
}

static void dump(long p, int z, const char *why, int fl[8]) {
    const pinfo_t *a = &PI[p];
    printf("D {\"tag\":%d,\"prof\":[", tag); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", cur[i]);
    printf("],\"why\":\"%s\",\"B\":", why); pbases(stdout, PP + p * MAXN);
    printf(",\"def\":%d,\"V\":%d,\"omega\":%d,\"x\":%d,\"g\":%d,\"z\":%d,\"J\":", a->def, a->V, omega, a->x, a->g, z); pmaskj(stdout, a->J);
    printf(",\"bt\":%d,\"sx1\":%d,\"u\":%d,\"c3\":%d,\"c3Z\":%d,\"t3\":%d,\"twin\":%d,\"rules\":%d}\n", fl[0], fl[1], fl[2], fl[3], fl[4], fl[5], fl[6], fl[7]);
}

static long nrep = 0;
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
    CNT[C_PROF]++;
    sigma = 2 * n - m;
    if (sigma >= 1) return;                                  /* f = 1 needs omega = 1 - sigma >= 1 */
    if (sigma >= 0) { found_small = 0; dfs_small(0, 0, 0, 0, 0); if (found_small) return; }
    bestf = 1 << 20; npp = 0; memset(cidx, 0, sizeof cidx);
    dfsP(0, 0, 0, 0, 0);
    if (bestf != 1) return;
    omega = 1 - sigma;
    CNT[C_F1]++;
    if (npp > capi) { capi = npp; PI = realloc(PI, capi * sizeof(pinfo_t)); if (!PI) { fprintf(stderr, "oom\n"); exit(2); } }
    static int keymin[MAXN][MAXM];
    for (int i = 0; i < n; i++) for (int g = 0; g < m; g++) keymin[i][g] = INF + 1;
    for (long p = 0; p < npp; p++) {
        eval_P(PP + p * MAXN, &PI[p]);
        if (PI[p].x < 0 || pc(PI[p].F) != 1) { fprintf(stderr, "internal: f = 1 class with %d frozen\n", pc(PI[p].F)); exit(3); }
        if (PI[p].def < keymin[PI[p].x][PI[p].g]) keymin[PI[p].x][PI[p].g] = PI[p].def;
    }
    hbuild();
    for (long p = 0; p < npp; p++) {
        pinfo_t *a = &PI[p];
        if (a->def <= 0) continue;
        CNT[C_ST]++;
        if (T1MODE ? !t1stuck(p) : a->def != keymin[a->x][a->g]) continue;
        CNT[C_T3S]++;
        const unsigned char *ia = PP + p * MAXN;
        int x = a->x, g = a->g, nneed = 0, z = -1;
        for (int i = 0; i < n; i++) if (optN[i][ia[i]] & BIT(g)) { nneed++; z = i; }
        int t3 = t3move(p);
        if (!t3) { CNT[C_NOT3ANY]++; int fl[8] = {0}; dump(p, nneed == 1 ? z : -1, "no T3 move at a T3-stage state", fl); }
        if (bigtop[x] && topg[x] == g) { CNT[C_T3BT]++; if (a->def == 1) CNT[C_T3BTD1]++; }
        if (nneed != 1) { CNT[C_T3SM]++; continue; }
        CNT[C_T3S1]++;
        int fl[8] = {0};
        fl[0] = bigtop[x] && topg[x] == g;
        CNT[fl[0] ? C_BT : C_NBT]++;
        if (a->def == 1) CNT[C_D1]++; else CNT[C_DEF2]++;
        int uf = 0; fl[1] = sx1test(p, z, &uf); fl[2] = uf;
        if (fl[1]) CNT[C_SX1]++; else CNT[C_NOSX1]++;
        if (fl[1] & 1) CNT[C_SX1O]++;
        if (fl[1] & 2) CNT[C_SX1Z]++;
        if (uf) CNT[C_U]++;
        int bz = -1; fl[3] = c3test(p, z, &bz); fl[4] = bz;
        if (fl[3]) CNT[C_C3]++; else CNT[C_NOC3]++;
        if (fl[3] & 1) CNT[C_C3N]++;
        if (fl[3] & 2) CNT[C_C3O]++;
        if (fl[3] & 4) CNT[C_C3Y]++;
        fl[5] = t3; if (t3) CNT[C_T3]++; else CNT[C_NOT3]++;
        fl[6] = Rm[z] == Rm[x]; if (fl[6]) CNT[C_TWIN]++;
        if (bigtop[z] && topg[z] == g) CNT[C_ZBT]++;
        fl[7] = rules(p, z);
        if (fl[7] & 1) CNT[C_RC]++;
        if (fl[7] & 2) CNT[C_RE]++;
        if (fl[7]) CNT[C_RCE]++; else CNT[C_RNONE]++;
        const char *why = 0;
        if (!fl[0]) why = "x not big-top";
        else if (a->def != 1) why = "def != 1";
        else if (!fl[1]) why = "no x-alone triple";
        else if (!fl[3]) why = "Corollary 8.2 fails";
        else if (!t3) why = "no T3 move";
        else if (fl[6]) why = "twin";
        else if (!fl[7]) why = "no rule";
        else if (RR > 0 && nrep++ % RR == 0) why = "sample";
        if (why) dump(p, z, why, fl);
    }
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strncmp(argv[a], "-r", 2)) RR = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-S", 2)) SEED = strtoull(argv[a] + 2, 0, 10);
        else if (!strcmp(argv[a], "-t1")) T1MODE = 1;
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
        memset(CNT, 0, sizeof CNT);
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
        printf("K %d", tag); for (int c = 0; c < NC; c++) printf(" %s %ld", CNAME[c], CNT[c]); printf("\n");
        fflush(stdout);
    }
    return 0;
}
