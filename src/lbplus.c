/* Construction LB+ (proofs/lb_last_step.md): Phase 1 of construction LB with ANY insertion choices, LB's Phase 2
   upgrades, then the owner r (the last-processed agent that is not upgraded); if r is not a valid owner, one rotation
   along a need path from the last insertion agent k to r, and the owner k. Every allocation is built constructively
   as in the written proof (not by LB's owner search), every lemma of the proof is asserted, and every output is
   checked against the raw EFX0 definition (construct.c's raw_ok: three balanced realizations, at most one bundle of
   >= 3 goods; it does not use the proof's reasoning).
   Build: gcc -O2 -o lbplus lbplus.c           (lbplus.py compiles and drives it)
   stdin: "n m K [mode] [seed]" then K lines of 3n goods (agent i's goods; they need not form a core).
   mode 0: LB's own Phase 1 (lookahead), every ranking profile.
   mode 1: every sequence of insertion choices (a tree of runs), LB's R1 order, every ranking profile.
   mode 2: random insertion choices and random R1 order (seeded), R runs per profile (R = seed's high part... see main).
   stdout per core: "core <k> stat <counters>"; "BAD ..." lines for any assertion failure or raw-check failure. */
#include "lb_common.h"
#include <stdlib.h>

#define NST 12
static const char *STN[NST] = {
    "runs", "c2", "owner_r", "rotated", "rot_c2", "rot_owner_k", "raw_fail", "assert_fail",
    "profiles", "r_E_nonempty", "rot_len_ge2", "max_large"
};
static long st[NST];
static int prof_g[MAXN];
static int nbad;

static void bad(const char *what, const int *Y, const int *ord, int nord) {
    st[7]++;
    if (nbad++ < 5) {
        printf("BAD %s | profile", what);
        for (int i = 0; i < n; i++) printf(" (%d,%d,%d)", trip[i][0], trip[i][1], trip[i][2]);
        printf(" | order"); for (int t = 0; t < nord; t++) printf(" %d", ord[t]);
        printf(" | picks"); for (int i = 0; i < n; i++) printf(" %d", Y[i]);
        printf("\n");
    }
}

/* Smallest set of junk goods meeting every pair in P[0..np) (brute force); returns its size, fills C. */
static int min_hit(const P2 *s, const uint32_t *P, int np, uint32_t *Cout) {
    for (int size = 0; size <= np; size++) {
        int idx[MAXM], nj = s->nj;
        if (size > nj) break;
        for (int t = 0; t < size; t++) idx[t] = t;
        for (;;) {
            uint32_t C = 0;
            for (int t = 0; t < size; t++) C |= 1u << s->Jl[idx[t]];
            int ok = 1;
            for (int t = 0; t < np && ok; t++) if (!(P[t] & C)) ok = 0;
            if (ok) { *Cout = C; return size; }
            int t = size - 1;
            while (t >= 0 && idx[t] == nj - size + t) t--;
            if (t < 0) break;
            idx[t]++;
            for (int u = t + 1; u < size; u++) idx[u] = idx[u - 1] + 1;
        }
    }
    return 1 << 20;
}

/* Exposed agents w.r.t. owner o in state s: k != o, not upgraded, holding its top, b_k and c_k in J u L0(o). Fills
   the pairs' junk parts; sets *inL0 if some pair lies inside L0(o). Returns the mask of exposed agents. */
static uint32_t exposed(const int *Y, const P2 *s, int o, uint32_t *P, int *np, int *inL0) {
    uint32_t L0 = 0, E = 0;
    if (o >= 0 && Y[o] >= 0) L0 |= 1u << Y[o];
    if (o >= 0 && (s->up >> o & 1)) L0 |= 1u << trip[o][2];
    *np = 0; *inL0 = 0;
    for (int k = 0; k < n; k++) {
        if (k == o || (s->up >> k & 1) || Y[k] != trip[k][0]) continue;
        uint32_t Pk = (1u << trip[k][1]) | (1u << trip[k][2]);
        if ((Pk & (s->J | L0)) != Pk) continue;
        E |= 1u << k;
        if ((Pk & L0) == Pk) *inL0 = 1;
        else P[(*np)++] = Pk & s->J;
    }
    return E;
}

/* Completion: frozen agents keep their pick, upgraded agents {b, c}, the goods of C fill the other agents' slots
   (owner excluded), the rest of the junk goes to the owner o (o = -1: no owner, C must be all of the junk). */
static void complete(const int *Y, const P2 *s, int o, uint32_t C, int *X) {
    for (int g = 0; g < m; g++) X[g] = -1;
    for (int k = 0; k < n; k++) if (Y[k] >= 0) X[Y[k]] = k;
    for (int k = 0; k < n; k++) if (s->up >> k & 1) X[trip[k][2]] = k;
    int cl[MAXM], nc = 0;
    for (int g = 0; g < m; g++) if (C >> g & 1) cl[nc++] = g;
    for (int k = 0; k < n; k++) if (k != o) for (int t = 0; t < s->cap[k] && nc; t++) X[cl[--nc]] = k;
    for (int g = 0; g < m; g++) if ((s->J >> g & 1) && X[g] < 0) X[g] = o;
}

/* Pad C (a subset of the junk) with further junk goods up to size want. */
static uint32_t pad(const P2 *s, uint32_t C, int want) {
    for (int t = 0; t < s->nj && __builtin_popcount(C) < want; t++) C |= 1u << s->Jl[t];
    return C;
}

/* LB+ on a finished Phase 1 (picks Y, junk J, processing order ord, insertion flags isr1). */
static void lbplus(const int *Y, uint32_t J, const int *ord, const int *isr1) {
    int pos[MAXN], blk[MAXN], b = -1, X[MAXM];
    for (int t = 0; t < n; t++) { pos[ord[t]] = t; if (!isr1[ord[t]]) b = t; blk[ord[t]] = b; }
    int lastlead = ord[b];
    P2 s; phase2_state(Y, J, &s);
    st[0]++;
    if (!pre_valid(Y, &s)) { bad("LB state invalid", Y, ord, n); return; }
    int omega = s.nj - s.sumcap;
    if (omega <= 0) {
        complete(Y, &s, -1, s.J, X); st[1]++;
        if (!raw_ok(X)) { st[6]++; bad("raw C2", Y, ord, n); }
        return;
    }
    /* r: the last-processed agent that is not upgraded */
    int r = -1;
    for (int t = n - 1; t >= 0; t--) if (!(s.up >> ord[t] & 1)) { r = ord[t]; break; }
    if (r < 0 || s.frozen[r]) { bad("r missing or frozen", Y, ord, n); return; }
    if (blk[r] != b) { bad("r not in last block", Y, ord, n); return; }
    uint32_t P[MAXN]; int np, inL0;
    uint32_t E = exposed(Y, &s, r, P, &np, &inL0);
    if (inL0) { bad("pair inside L0(r)", Y, ord, n); return; }
    if (E) st[9]++;
    for (int k = 0; k < n; k++) if (E >> k & 1) {
        if (isr1[k] || pos[k] > pos[r]) { bad("exposed agent not an earlier insertion agent", Y, ord, n); return; }
        for (int k2 = 0; k2 < k; k2++) if ((E >> k2 & 1) && blk[k2] == blk[k]) { bad("two exposed in a block", Y, ord, n); return; }
    }
    uint32_t C = 0;
    int h = min_hit(&s, P, np, &C), slots = s.sumcap - s.cap[r];
    if (h <= slots) {
        C = pad(&s, C, slots);
        complete(Y, &s, r, C, X); st[2]++;
        if (!raw_ok(X)) { st[6]++; bad("raw owner r", Y, ord, n); }
        int sz[MAXN] = {0}, mx = 0; for (int g = 0; g < m; g++) sz[X[g]]++;
        for (int j = 0; j < n; j++) if (sz[j] > mx) mx = sz[j];
        if (mx > st[11]) st[11] = mx;
        return;
    }
    /* the bad case: the proof says k = leader of the last block is exposed, frozen, != r, every need chain from k
       ends at r, the junk parts of the exposed pairs are pairwise disjoint, and slots = |E| - 1 */
    int k = lastlead;
    if (!(E >> k & 1) || !s.frozen[k] || k == r) { bad("bad case without the structure (k)", Y, ord, n); return; }
    if (h != __builtin_popcount(E) || slots != __builtin_popcount(E) - 1) { bad("bad case counts", Y, ord, n); return; }
    for (int t = 0; t < np; t++) for (int u = 0; u < t; u++) if (P[t] & P[u]) { bad("pairs not disjoint", Y, ord, n); return; }
    /* a need path from k to r: follow the first needer (not upgraded, needs the pick) each time */
    int path[MAXN], plen = 1; path[0] = k;
    while (path[plen - 1] != r) {
        int x = path[plen - 1], nx = -1;
        if (Y[x] < 0 || !s.frozen[x]) { bad("chain reached a terminal other than r", Y, ord, n); return; }
        for (int t = pos[x] + 1; t < n; t++) {
            int j = ord[t];
            if (!(s.up >> j & 1) && rk[j][Y[x]] < s.held[j]) { nx = j; break; }
        }
        if (nx < 0 || blk[nx] != b) { bad("needer missing or outside the block", Y, ord, n); return; }
        path[plen++] = nx;
    }
    if (plen >= 3) st[10]++;
    /* rotation */
    int Y2[MAXN]; memcpy(Y2, Y, sizeof(int) * n);
    for (int t = plen - 1; t >= 1; t--) Y2[path[t]] = Y[path[t - 1]];
    Y2[k] = trip[k][1];
    for (int t = 1; t < plen; t++) if (rk[path[t]][Y2[path[t]]] >= s.held[path[t]]) { bad("rotation not an improvement", Y, ord, n); return; }
    P2 s2; PRE_NOUP = 1; pre_state(Y2, s.up | (1u << k), &s2); PRE_NOUP = 0;
    st[3]++;
    if (!pre_valid(Y2, &s2)) { bad("rotated state invalid", Y, ord, n); return; }
    if (s2.NA & ~s.NA) { bad("NA grew", Y, ord, n); return; }
    int omega2 = s2.nj - s2.sumcap;
    if (omega2 <= 0) {
        complete(Y2, &s2, -1, s2.J, X); st[4]++;
        if (!raw_ok(X)) { st[6]++; bad("raw rotated C2", Y, ord, n); }
        return;
    }
    uint32_t P2p[MAXN]; int np2, inL02;
    uint32_t E2 = exposed(Y2, &s2, k, P2p, &np2, &inL02);
    if (inL02) { bad("pair inside L0(k) after rotation", Y, ord, n); return; }
    if (E2 & ~(E & ~(1u << k))) { bad("new exposed agent after rotation", Y, ord, n); return; }
    if (np2 > s2.sumcap) { bad("too few slots after rotation", Y, ord, n); return; }
    uint32_t C2 = 0;
    for (int t = 0; t < np2; t++) if (!(P2p[t] & C2)) C2 |= 1u << __builtin_ctz(P2p[t]);
    C2 = pad(&s2, C2, s2.sumcap - s2.cap[k]);
    complete(Y2, &s2, k, C2, X); st[5]++;
    if (!raw_ok(X)) { st[6]++; bad("raw rotated owner k", Y, ord, n); }
    int sz[MAXN] = {0}, mx = 0; for (int g = 0; g < m; g++) sz[X[g]]++;
    for (int j = 0; j < n; j++) if (sz[j] > mx) mx = sz[j];
    if (mx > st[11]) st[11] = mx;
}

/* mode 1: every insertion choice; LB's R1 order */
static int ORD1[MAXN], ISR1[MAXN], NORD1;
static void tree(int *Y, uint32_t A, uint32_t G) {
    int Yl[MAXN]; memcpy(Yl, Y, sizeof(int) * n);
    int save = NORD1;
    for (;;) {
        uint32_t A0 = A;
        if (!A || !r1_step(&A, &G, Yl)) break;
        int i = __builtin_ctz(A0 & ~A); ORD1[NORD1] = i; ISR1[i] = 1; NORD1++;
    }
    if (!A) { lbplus(Yl, G, ORD1, ISR1); NORD1 = save; return; }
    for (int i = 0; i < n; i++) if (A >> i & 1) {
        int Y3[MAXN]; memcpy(Y3, Yl, sizeof(int) * n); Y3[i] = trip[i][0];
        ORD1[NORD1] = i; ISR1[i] = 0; NORD1++;
        tree(Y3, A & ~(1u << i), G & ~(1u << trip[i][0]));
        NORD1--;
    }
    NORD1 = save;
}

/* mode 2: random insertion choices and random R1 choices (any eligible agent) */
static uint64_t rng;
static uint32_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint32_t)(rng >> 11); }
static void phase1_random(int *Y, uint32_t *J, int *ord, int *isr1) {
    uint32_t A = (1u << n) - 1, G = (m == 32) ? 0xffffffffu : ((1u << m) - 1);
    int t = 0;
    for (int i = 0; i < n; i++) Y[i] = -1;
    while (A) {
        int el[MAXN], ne = 0;
        for (int i = 0; i < n; i++) if ((A >> i & 1) && popc(Rm[i] & G) <= 2) el[ne++] = i;
        int i, r1 = ne > 0;
        if (r1) i = el[rnd() % ne];
        else { int c = rnd() % popc(A); for (i = 0; i < n; i++) if ((A >> i & 1) && c-- == 0) break; }
        int fav = -1;
        for (int q = 0; q < 3; q++) if (G >> trip[i][q] & 1) { fav = trip[i][q]; break; }
        Y[i] = fav; A &= ~(1u << i); if (fav >= 0) G &= ~(1u << fav);
        ord[t++] = i; isr1[i] = r1;
    }
    *J = G;
}

int main(void) {
    int K, mode = 0; long seed = 1, reps = 1;
    if (scanf("%d %d %d", &n, &m, &K) != 3 || n > MAXN || m > MAXM) { fprintf(stderr, "bad header\n"); return 1; }
    if (scanf("%d", &mode) == 1 && mode == 2) { if (scanf("%ld %ld", &seed, &reps) != 2) return 1; }
    long total = 1; for (int i = 0; i < n; i++) total *= 6;
    printf("names"); for (int t = 0; t < NST; t++) printf(" %s", STN[t]); printf("\n");
    for (int c = 0; c < K; c++) {
        int sets[MAXN][3];
        for (int i = 0; i < n; i++) for (int q = 0; q < 3; q++) if (scanf("%d", &sets[i][q]) != 1) return 1;
        for (int i = 0; i < n; i++) { Rm[i] = 0; for (int q = 0; q < 3; q++) Rm[i] |= 1u << sets[i][q]; }
        memset(st, 0, sizeof st); nbad = 0;
        rng = 0x9e3779b97f4a7c15ull ^ (uint64_t)(seed * 1000003 + c);
        for (long p = 0; p < total; p++) {
            long q = p;
            for (int i = n - 1; i >= 0; i--) { prof_g[i] = q % 6; q /= 6; }
            for (int i = 0; i < n; i++) {
                for (int t = 0; t < 3; t++) trip[i][t] = sets[i][PERMS[prof_g[i]][t]];
                for (int g = 0; g < m; g++) rk[i][g] = 3;
                for (int t = 0; t < 3; t++) rk[i][trip[i][t]] = t;
            }
            st[8]++;
            int Y[MAXN], ord[MAXN], isr1[MAXN], pos[MAXN]; uint32_t J;
            if (mode == 0) { phase1_order(Y, &J, ord, isr1, pos); lbplus(Y, J, ord, isr1); }
            else if (mode == 1) { for (int i = 0; i < n; i++) Y[i] = -1; NORD1 = 0; tree(Y, (1u << n) - 1, (m == 32) ? 0xffffffffu : ((1u << m) - 1)); }
            else for (long t = 0; t < reps; t++) { phase1_random(Y, &J, ord, isr1); lbplus(Y, J, ord, isr1); }
        }
        printf("core %d stat", c);
        for (int t = 0; t < NST; t++) printf(" %ld", st[t]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
