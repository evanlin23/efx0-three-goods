/* Extension search for k4/reduce4.py reductions, in C (driver: k4/reduce4c.py).

   For each admissible local state of Y it enumerates exactly the extensions reduce4.Reduction.extensions enumerates
   (moved items to agents of S or to free outside bundles; interior goods to agents of S or to outside bundles holding
   gadget goods or the unenvied bundle; the same domination tests of Lemma M1 / M1(b)), computes every agent's view, and
   prints one representative extension per distinct tuple of views whose safe sets are all nonempty.  The Python
   driver rebuilds each representative, recomputes its views, safe masks and domination with reduce4's own code, and
   only then uses it, so this program is a search accelerator: an error here can lose coverage, never add any.

   Input (stdin, whitespace separated):
     NGOODS UMASK IMASK IPMASK                 (64-bit masks over the good indices: U goods = boundary goods and markers;
                                                I = interior goods; I' = gadget goods)
     NIG ig_0 .. ig_{NIG-1}                    (interior goods, in reduce4's order: sorted names)
     NA, then per agent of S: d g_0..g_{d-1} NT and NT rows of d values
     then per state:  NY y_0..   NO o_0..   SK SI      (gadget bundles in sorted name order, outside bundles, unenvied
                                                       bundle: SK = -1 none, 0 gadget bundle SI, 1 outside bundle SI)
                      NMV mv_0..                       (moved items: good indices, reduce4's order)
   Output, per state:  "E k" then k lines "dest_0 .. dest_{NMV-1} | ch_0 .. ch_{NIG-1}" with dest j < NA an agent of S,
   else free[j - NA]; ch j < NA an agent, else ipblocks[j - NA] (both lists as reduce4 computes them). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
#define MAXA 5
#define MAXT 288
#define TW 5
#define MAXB 24

static int NG, NIG, NA, IG[16];
static u64 UMASK, IMASK, IPMASK;
static int D[MAXA], G[MAXA][4], NT[MAXA];
static int VAL[MAXA][MAXT][4];
static u64 RMASK[MAXA];
/* safe[a][own][pair] : bitset over types; pair = T * 2 + flag, T in [1, 2^d) */
static u64 SAFE[MAXA][16][32][TW];

static int popc(u64 x) { return __builtin_popcountll(x); }

static void precompute(void) {
    for (int a = 0; a < NA; a++) {
        int d = D[a];
        RMASK[a] = 0;
        for (int i = 0; i < d; i++) RMASK[a] |= 1ULL << G[a][i];
        for (int own = 0; own < (1 << d); own++)
            for (int T = 1; T < (1 << d); T++)
                for (int fl = 0; fl < 2; fl++) {
                    u64 *m = SAFE[a][own][T * 2 + fl];
                    memset(m, 0, sizeof(u64) * TW);
                    for (int t = 0; t < NT[a]; t++) {
                        int ov = 0, s = 0, mn = 1 << 30;
                        for (int i = 0; i < d; i++) {
                            if (own >> i & 1) ov += VAL[a][t][i];
                            if (T >> i & 1) { s += VAL[a][t][i]; if (VAL[a][t][i] < mn) mn = VAL[a][t][i]; }
                        }
                        int thr = fl ? s : s - mn;
                        if (ov >= thr) m[t >> 6] |= 1ULL << (t & 63);
                    }
                }
    }
}

static int local_bits(int a, u64 X) {
    int r = 0;
    for (int i = 0; i < D[a]; i++) if (X >> G[a][i] & 1) r |= 1 << i;
    return r;
}

/* ----- one state ----- */
static int NY, NO, SK, SI, NMV, MV[16];
static u64 Y[MAXB], O[MAXB];
static u64 YALL[2 * MAXB]; static int NYALL;
static u64 UDOM[2 * MAXB + 1]; static int NUDOM;
static u64 YSRC; static int HAVESRC;
static int IPB[MAXB], NIPB, FREE[MAXB], NFREE;
static u64 IBASE[MAXB];

static int dominated(u64 B) {
    if (popc(B) <= 1) return 1;
    u64 u = B & UMASK;
    if (!u) return 1;
    if (HAVESRC && (u & ~(YSRC & UMASK)) == 0) return 1;
    int inn = (B & (IMASK | IPMASK)) != 0;
    for (int k = 0; k < NYALL; k++) {
        u64 B2 = YALL[k], u2 = B2 & UMASK;
        if ((u & ~u2) == 0 && (!inn || (B2 & (IMASK | IPMASK)) || u != u2)) return 1;
    }
    return 0;
}

/* hash set of view tuples */
#define HS (1 << 16)
static u64 HK[HS][MAXA]; static int HUSED[HS]; static int hstamp = 1;
static int hcount;
static int hs_insert(u64 *key) {
    u64 h = 1469598103934665603ULL;
    for (int a = 0; a < NA; a++) { h ^= key[a]; h *= 1099511628211ULL; }
    for (u64 i = h & (HS - 1);; i = (i + 1) & (HS - 1)) {
        if (HUSED[i] != hstamp) {
            if (++hcount > HS / 2) { fprintf(stderr, "too many distinct views in one state\n"); exit(3); }
            HUSED[i] = hstamp; memcpy(HK[i], key, sizeof(u64) * NA); return 1;
        }
        if (!memcmp(HK[i], key, sizeof(u64) * NA)) return 0;
    }
}

static u64 XS[MAXA], OX[MAXB];
static int DEST[16], CH[16];
static char *OUT; static size_t OUTN, OUTCAP; static int NOUT;
static void emit(void) {
    char buf[256]; int p = 0;
    for (int i = 0; i < NMV; i++) p += sprintf(buf + p, "%d ", DEST[i]);
    p += sprintf(buf + p, "|");
    for (int i = 0; i < NIG; i++) p += sprintf(buf + p, " %d", CH[i]);
    buf[p++] = '\n';
    if (OUTN + p + 1 > OUTCAP) { OUTCAP = 2 * OUTCAP + p + 1024; OUT = realloc(OUT, OUTCAP); }
    memcpy(OUT + OUTN, buf, p); OUTN += p; NOUT++;
}

static void evaluate(void) {
    u64 key[MAXA];
    for (int a = 0; a < NA; a++) {
        u64 pairs = 0;
        for (int b = 0; b < NA; b++) {
            if (b == a || popc(XS[b]) < 2) continue;
            int T = local_bits(a, XS[b]);
            if (T) pairs |= 1ULL << (T * 2 + ((XS[b] & ~RMASK[a]) != 0));
        }
        for (int k = 0; k < NO; k++) {
            if (popc(OX[k]) < 2) continue;
            int T = local_bits(a, OX[k]);
            if (T) pairs |= 1ULL << (T * 2 + ((OX[k] & ~RMASK[a]) != 0));
        }
        key[a] = (u64)local_bits(a, XS[a]) | (pairs << 4);
    }
    if (!hs_insert(key)) return;
    for (int a = 0; a < NA; a++) {
        int own = key[a] & 15; u64 pairs = key[a] >> 4;
        u64 m[TW];
        for (int w = 0; w < TW; w++) m[w] = ~0ULL;
        for (int p = 0; p < 32; p++) if (pairs >> p & 1) for (int w = 0; w < TW; w++) m[w] &= SAFE[a][own][p][w];
        int any = 0;
        for (int w = 0; w < TW; w++) {
            u64 valid = (NT[a] >= 64 * (w + 1)) ? ~0ULL : (NT[a] > 64 * w ? ((1ULL << (NT[a] - 64 * w)) - 1) : 0);
            if (m[w] & valid) any = 1;
        }
        if (!any) return;
    }
    emit();
}

static void place_interior(int i) {
    if (i == NIG) {
        for (int a = 0; a < NA; a++) if (!dominated(XS[a])) return;
        for (int j = 0; j < NIPB; j++) if (!dominated(OX[IPB[j]])) return;
        evaluate();
        return;
    }
    u64 g = 1ULL << IG[i];
    for (int c = 0; c < NA + NIPB; c++) {
        CH[i] = c;
        if (c < NA) { XS[c] |= g; place_interior(i + 1); XS[c] &= ~g; }
        else { int k = IPB[c - NA]; OX[k] |= g; place_interior(i + 1); OX[k] &= ~g; }
    }
}

static void place_moved(int i) {
    if (i == NMV) {
        for (int a = 0; a < NA; a++) {
            u64 u = XS[a] & UMASK;
            if (popc(u) >= 2) { int ok = 0; for (int k = 0; k < NUDOM; k++) if ((u & ~UDOM[k]) == 0) { ok = 1; break; } if (!ok) return; }
        }
        for (int k = 0; k < NO; k++) {
            u64 u = OX[k] & UMASK;
            if (popc(u) >= 2) { int ok = 0; for (int j = 0; j < NUDOM; j++) if ((u & ~UDOM[j]) == 0) { ok = 1; break; } if (!ok) return; }
        }
        place_interior(0);
        return;
    }
    u64 g = 1ULL << MV[i];
    for (int dd = 0; dd < NA + NFREE; dd++) {
        DEST[i] = dd;
        if (dd < NA) { XS[dd] |= g; place_moved(i + 1); XS[dd] &= ~g; }
        else { int k = FREE[dd - NA]; OX[k] |= g; place_moved(i + 1); OX[k] &= ~g; }
    }
}

static u64 rd(void) { unsigned long long x; if (scanf("%llu", &x) != 1) { fprintf(stderr, "bad input\n"); exit(2); } return x; }

int main(void) {
    NG = rd(); UMASK = rd(); IMASK = rd(); IPMASK = rd();
    NIG = rd(); for (int i = 0; i < NIG; i++) IG[i] = rd();
    NA = rd();
    if (NA > MAXA) { fprintf(stderr, "too many agents\n"); return 2; }
    for (int a = 0; a < NA; a++) {
        D[a] = rd(); for (int i = 0; i < D[a]; i++) G[a][i] = rd();
        NT[a] = rd(); if (NT[a] > MAXT) { fprintf(stderr, "too many types\n"); return 2; }
        for (int t = 0; t < NT[a]; t++) for (int i = 0; i < D[a]; i++) VAL[a][t][i] = rd();
    }
    precompute();
    unsigned long long ny;
    while (scanf("%llu", &ny) == 1) {
        NY = ny; for (int i = 0; i < NY; i++) Y[i] = rd();
        NO = rd(); for (int i = 0; i < NO; i++) O[i] = rd();
        SK = (int)(long long)rd(); SI = rd();
        NMV = rd(); for (int i = 0; i < NMV; i++) MV[i] = rd();
        NYALL = 0; for (int i = 0; i < NY; i++) YALL[NYALL++] = Y[i]; for (int i = 0; i < NO; i++) YALL[NYALL++] = O[i];
        HAVESRC = SK >= 0; YSRC = SK == 0 ? Y[SI] : (SK == 1 ? O[SI] : 0);
        NUDOM = 0; for (int k = 0; k < NYALL; k++) UDOM[NUDOM++] = YALL[k] & UMASK; if (HAVESRC) UDOM[NUDOM++] = YSRC & UMASK;
        NIPB = 0; NFREE = 0;
        for (int k = 0; k < NO; k++) {
            int hasip = (O[k] & IPMASK) != 0;
            if (hasip || (SK == 1 && SI == k)) IPB[NIPB++] = k;
            IBASE[k] = O[k] & ~IPMASK;
        }
        for (int j = 0; j < NIPB; j++) { int k = IPB[j]; if (!(O[k] & UMASK) && (O[k] & IPMASK)) FREE[NFREE++] = k; }
        for (int a = 0; a < NA; a++) XS[a] = 0;
        for (int k = 0; k < NO; k++) OX[k] = IBASE[k];
        hstamp++; hcount = 0; if (hstamp == 0x7fffffff) { memset(HUSED, 0, sizeof HUSED); hstamp = 1; }
        OUTN = 0; NOUT = 0;
        place_moved(0);
        printf("E %d\n", NOUT);
        fwrite(OUT, 1, OUTN, stdout);
    }
    return 0;
}
