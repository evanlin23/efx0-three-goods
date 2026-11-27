/* rf_oc1.c -- OC1 decision for given bases (workstream compute/k4-rf-indep, k4/rf_indep/README.md).
 *
 * Written from the statements in k4/sdc.md section 29 (improving chain, one-absorber completion) and section 31 end
 * (Conjecture RF, amended), without reading any other checker.  Raw EFX0: for all agents i != j and every good g in
 * X_j, v_i(X_i) >= v_i(X_j - g); goods outside agent i's set are worth 0 to i.
 *
 * OC1 at bases B (junk J = goods in no base):
 *   P  some one-absorber completion of B exists: a complete EFX0 allocation X with B_i subset of X_i, in which one
 *      agent o (the absorber) receives any number of junk goods and every other agent at most one;
 *   C  else some improving chain x_0..x_t (t >= 1, distinct agents) with disjoint H_0 subset of (J u B_{x_t}),
 *      H_i subset of J (i >= 1), each H_i inside R_{x_i}, v_{x_0}(H_0) > v_{x_0}(B_{x_0}) and
 *      v_{x_i}(B_{x_{i-1}} u H_i) > v_{x_i}(B_{x_i}); after it (x_0 holds H_0, x_i holds B_{x_{i-1}} u H_i, the rest
 *      of B_{x_t} is junk) the bases have a one-absorber completion;
 *   F  neither (exhaustive: every chain, every choice of the H_i, every absorber, every placement).
 *
 * Input, one task per line:  id n m  (k g_1 v_1 ... g_k v_k) x n  b_0 ... b_{n-1}   (b_i = base bitmask)
 * Output, one line per task:
 *   id P o X_0 .. X_{n-1}
 *   id C t x_0 .. x_t H_0 .. H_t o X_0 .. X_{n-1}
 *   id F <number of distinct post-chain states tried>
 * P and C are returned at the first success (shorter chains first); F only after the exhaustive search.
 * With argument "count": P as above, else "id N <repairing post-chain states> <post-chain states> <completions>"
 * (exhaustive; completions = (absorber, placement) pairs over all repairing states; N 0 ... means F), one line per
 * task, flushed (for use as a coprocess).  With argument "line": the normal answers, flushed after each line.
 * With argument "countall": as "count", but when the picks complete, "id Q <completions at the picks>".
 *
 *     gcc -O2 -o rf_oc1 rf_oc1.c && ./rf_oc1 < tasks > answers
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
#define MAXM 30

static int n, m;
static int val[MAXN][MAXM];
static uint32_t R[MAXN], ALL;

static inline int vsum(int i, uint32_t S) {
    uint32_t T = S & R[i]; int s = 0;
    while (T) { s += val[i][__builtin_ctz(T)]; T &= T - 1; }
    return s;
}

/* max over g in S of v_i(S - g) = v_i(S) - min_{g in S} v_i(g); 0 when |S| <= 1 */
static inline int thr(int i, uint32_t S) {
    if (__builtin_popcount(S) <= 1) return 0;
    uint32_t T = S & R[i]; int s = 0, mn = 1 << 30;
    while (T) { int x = val[i][__builtin_ctz(T)]; s += x; if (x < mn) mn = x; T &= T - 1; }
    if (S & ~R[i]) mn = 0;
    return s - mn;
}

static int efx0(const uint32_t *X) {
    int own[MAXN];
    for (int i = 0; i < n; i++) own[i] = vsum(i, X[i]);
    for (int j = 0; j < n; j++) {
        if (__builtin_popcount(X[j]) < 2) continue;
        for (int i = 0; i < n; i++) if (i != j && thr(i, X[j]) > own[i]) return 0;
    }
    return 1;
}

/* ---- one-absorber completion ---- */
static uint32_t CB[MAXN], CX[MAXN], WX[MAXN];
static int oth[MAXN], noth, absorber, Wo;
static int count_comp = 0;           /* count every (absorber, placement) completion instead of stopping */
static long ncomp;

static int arec(int k, uint32_t rem) {
    if (k == noth) {
        CX[absorber] = CB[absorber] | rem;
        if (efx0(CX)) {
            if (count_comp) { ncomp++; return 0; }
            memcpy(WX, CX, sizeof(CX)); Wo = absorber; return 1;
        }
        return 0;
    }
    int i = oth[k];
    /* option g = -1: no junk for i; then each junk good in rem */
    for (int g = -1; g < m; g++) {
        uint32_t gb = 0;
        if (g >= 0) { gb = 1u << g; if (!(rem & gb)) continue; }
        CX[i] = CB[i] | gb;
        uint32_t rem2 = rem & ~gb;
        int ok = 1, own_i = vsum(i, CX[i]);
        for (int q = 0; q < k && ok; q++) {          /* final bundles of earlier non-absorbers */
            int j = oth[q];
            if (thr(i, CX[j]) > own_i || thr(j, CX[i]) > vsum(j, CX[j])) ok = 0;
        }
        /* the absorber ends with a subset of CB[o] | rem2: an upper bound on its value */
        if (ok && thr(absorber, CX[i]) > vsum(absorber, CB[absorber] | rem2)) ok = 0;
        if (ok && arec(k + 1, rem2)) return 1;
    }
    return 0;
}

static int one_absorber(const uint32_t *B) {
    uint32_t held = 0;
    for (int i = 0; i < n; i++) { CB[i] = B[i]; held |= B[i]; }
    uint32_t J = ALL & ~held;
    for (int o = 0; o < n; o++) {
        absorber = o; noth = 0;
        for (int i = 0; i < n; i++) if (i != o) oth[noth++] = i;
        if (arec(0, J)) return 1;
    }
    return 0;
}

/* ---- post-chain state dedupe ---- */
#define HBITS 18
#define HSIZE (1u << HBITS)
static uint64_t hkey[HSIZE][2];
static uint32_t hgen[HSIZE], gen = 0;
static long nstates, ninserted;

static int seen(const uint32_t *B) {   /* insert; return 1 if already present (dedupe off when m > 16 or table full) */
    if (m > 16 || ninserted >= (long)(HSIZE / 4 * 3)) return 0;
    uint64_t k0 = 0, k1 = 0;
    for (int i = 0; i < n; i++) { if (i < 4) k0 |= (uint64_t)B[i] << (16 * i); else k1 |= (uint64_t)B[i] << (16 * (i - 4)); }
    uint64_t h = (k0 * 0x9E3779B97F4A7C15ull) ^ (k1 * 0xC2B2AE3D27D4EB4Full);
    uint32_t p = (uint32_t)(h >> (64 - HBITS));
    for (;;) {
        if (hgen[p] != gen) { hgen[p] = gen; hkey[p][0] = k0; hkey[p][1] = k1; ninserted++; return 0; }
        if (hkey[p][0] == k0 && hkey[p][1] == k1) return 1;
        p = (p + 1) & (HSIZE - 1);
    }
}

/* ---- improving chains ---- */
static uint32_t B0[MAXN], J0;
static int seq[MAXN], tlen;          /* seq[0..tlen] */
static uint32_t H[MAXN], NB[MAXN];
static int found;
static int count_mode = 0;           /* argv[1] == "count": count repairing post-chain states, no early exit */
static long nrepair;

static int try_state(void) {
    for (int i = 0; i < n; i++) NB[i] = B0[i];
    NB[seq[0]] = H[0];
    for (int i = 1; i <= tlen; i++) NB[seq[i]] = B0[seq[i - 1]] | H[i];
    if (seen(NB)) return 0;
    nstates++;
    if (!count_mode) return one_absorber(NB);
    long before = ncomp;
    count_comp = 1; one_absorber(NB); count_comp = 0;
    if (ncomp > before) nrepair++;
    return 0;
}

static int hrec(int i, uint32_t used) {   /* choose H_i, i >= 1 */
    if (i > tlen) return try_state();
    int x = seq[i];
    uint32_t C = J0 & R[x] & ~used;
    int need = vsum(x, B0[x]), base = vsum(x, B0[seq[i - 1]]);
    for (uint32_t S = C;; S = (S - 1) & C) {
        H[i] = S;
        if (base + vsum(x, S) > need && hrec(i + 1, used | S)) return 1;
        if (S == 0) break;
    }
    return 0;
}

static int chain_for_seq(void) {
    int x0 = seq[0];
    uint32_t C = (J0 | B0[seq[tlen]]) & R[x0];
    int need = vsum(x0, B0[x0]);
    for (uint32_t S = C; S; S = (S - 1) & C) {
        if (vsum(x0, S) <= need) continue;
        H[0] = S;
        if (hrec(1, S)) return 1;
    }
    return 0;
}

static int srec(int k, uint32_t usedag) {  /* build seq of length tlen + 1 */
    if (k > tlen) return chain_for_seq();
    for (int a = 0; a < n; a++) {
        if (usedag >> a & 1) continue;
        seq[k] = a;
        if (srec(k + 1, usedag | 1u << a)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    char id[256];
    if (argc > 1 && !strcmp(argv[1], "count")) count_mode = 1;
    int line_mode = argc > 1 && !strcmp(argv[1], "line");     /* normal answers, flushed after each line */
    int countall = argc > 1 && !strcmp(argv[1], "countall");  /* count mode, and P also counts the picks' completions */
    if (countall) count_mode = 1;
    while (scanf("%255s %d %d", id, &n, &m) == 3) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "too large\n"); return 1; }
        ALL = (m == 32) ? 0xffffffffu : ((1u << m) - 1);
        for (int i = 0; i < n; i++) {
            int k; if (scanf("%d", &k) != 1) return 1;
            R[i] = 0; for (int g = 0; g < m; g++) val[i][g] = 0;
            for (int q = 0; q < k; q++) {
                int g, v; if (scanf("%d %d", &g, &v) != 2) return 1;
                val[i][g] = v; R[i] |= 1u << g;
                if (v <= 0) { fprintf(stderr, "nonpositive value\n"); return 1; }
            }
        }
        for (int i = 0; i < n; i++) { unsigned b; if (scanf("%u", &b) != 1) return 1; B0[i] = b; }
        uint32_t held = 0; for (int i = 0; i < n; i++) held |= B0[i];
        J0 = ALL & ~held;
        if (countall && one_absorber(B0)) {
            ncomp = 0; count_comp = 1; one_absorber(B0); count_comp = 0;
            printf("%s Q %ld\n", id, ncomp); fflush(stdout);
            continue;
        }
        if (one_absorber(B0)) {
            printf("%s P %d", id, Wo);
            for (int i = 0; i < n; i++) printf(" %u", WX[i]);
            printf("\n"); if (count_mode || line_mode) fflush(stdout);
            continue;
        }
        gen++; if (gen == 0) { memset(hgen, 0, sizeof(hgen)); gen = 1; }
        nstates = 0; ninserted = 0; found = 0;
        if (count_mode) {
            nrepair = 0; ncomp = 0;
            for (tlen = 1; tlen < n; tlen++) srec(0, 0);
            printf("%s N %ld %ld %ld\n", id, nrepair, nstates, ncomp); fflush(stdout);
            continue;
        }
        for (tlen = 1; tlen < n && !found; tlen++) found = srec(0, 0);
        if (found) {
            tlen--;    /* the loop incremented past the successful length */
            printf("%s C %d", id, tlen);
            for (int i = 0; i <= tlen; i++) printf(" %d", seq[i]);
            for (int i = 0; i <= tlen; i++) printf(" %u", H[i]);
            printf(" %d", Wo);
            for (int i = 0; i < n; i++) printf(" %u", WX[i]);
            printf("\n");
        } else printf("%s F %ld\n", id, nstates);
        if (line_mode) fflush(stdout);
    }
    (void)argc; (void)argv;   /* count mode is set at the top of main */
    return 0;
}
