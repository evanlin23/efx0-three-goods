/* Construction LB with every possible choice at every insertion step (ledger S2.LB; proofs/lb_last_step.md).
   Phase 1 of LB is serial dictatorship where, at each insertion step (every unprocessed agent still has its three
   goods), LB inserts the agent with the smallest lookahead count (construct.c: na_count). Here every unprocessed agent
   is tried at every insertion step (a tree of runs); R1 steps are LB's. For each complete run: Phase 2 state, whether
   r (the last-processed agent that is not upgraded) is a valid owner when the overflow bundle is needed, and whether
   the choice made at the LAST insertion step had the minimal lookahead count there (ties allowed).
   Build: gcc -O2 -o lb_tree lb_tree.c        (lb_owner.py --bin=lb_tree compiles and drives it) */
#include "lb_common.h"

#define NST 20
static const char *STN[NST] = {
    "runs", "over", "r_bad", "r_bad_lastmin", "any_bad", "any_bad_lastmin", "lb_runs_r_bad",
    "r_bad_allmin", "profiles", "profiles_some_r_bad", "over_lastmin", "r_bad_lastmin_strict",
    "rb_alt_r_better", "rb_alt_j1_better", "rb_alt_ar_better", "rb_some_better", "rb_alt_r_le", "rb_k_frozen", "rb_r_needs_ak", "rb_single_block"
};
static long st[NST];
static int nex;
static int prof_g[MAXN];

/* run state: Y, A (unprocessed), G (available); ins = insertion log: chooser flags */
static void finish(const int *Y, uint32_t J, int lastmin, int lastmin_strict, int allmin, int islb) {
    P2 s; phase2_state(Y, J, &s);
    st[0]++;
    if (s.nj <= s.sumcap) return;
    st[1]++;
    if (lastmin) st[10]++;
    /* order is not tracked here; r = last non-upgraded agent needs the order: recomputed by caller */
}

static int ORD[MAXN], NORD;
static int LCNT[MAXN], LLEAD = -1, LPOS = -1; static uint32_t LA;
static void rec(int *Y, uint32_t A, uint32_t G, int lastmin, int lastmin_strict, int allmin, int islb) {
    /* R1 steps */
    int Yl[MAXN]; memcpy(Yl, Y, sizeof(int) * n);
    int saveN = NORD;
    for (;;) {
        uint32_t A0 = A;
        if (!A) break;
        if (!r1_step(&A, &G, Yl)) break;
        ORD[NORD++] = __builtin_ctz(A0 & ~A);
    }
    if (!A) {
        P2 s; phase2_state(Yl, G, &s);
        st[0]++;
        if (s.nj > s.sumcap) {
            st[1]++;
            if (lastmin) st[10]++;
            int r = -1;
            for (int t = n - 1; t >= 0; t--) if (!(s.up >> ORD[t] & 1)) { r = ORD[t]; break; }
            int rok = owner_ok(Yl, &s, r), any = rok;
            for (int o = 0; o < n && !any; o++) any |= owner_ok(Yl, &s, o);
            if (!rok) {
                /* alternatives at the last insertion step: leader LLEAD, counts LCNT over LA */
                int k = LLEAD, j1 = -1, ar = -1;
                for (int t = LPOS + 1; t < n; t++) { int j = ORD[t]; if (!(s.up >> j & 1) && rk[j][trip[k][0]] < s.held[j]) { j1 = j; break; } }
                for (int j = 0; j < n; j++) if (Yl[j] == trip[r][0]) ar = j;
                if (LCNT[r] < LCNT[k]) st[12]++;
                if (j1 >= 0 && (LA >> j1 & 1) && LCNT[j1] < LCNT[k]) st[13]++;
                if (ar >= 0 && (LA >> ar & 1) && LCNT[ar] < LCNT[k]) st[14]++;
                int some = 0; for (int i = 0; i < n; i++) if ((LA >> i & 1) && LCNT[i] < LCNT[k]) some = 1;
                if (some) st[15]++;
                if (LCNT[r] <= LCNT[k]) st[16]++;
                if (s.frozen[k]) st[17]++;
                if (rk[r][trip[k][0]] < s.held[r]) st[18]++;
                if (LPOS == 0) st[19]++;
                st[2]++; if (lastmin) st[3]++; if (islb) st[6]++; if (allmin) st[7]++; if (lastmin_strict) st[11]++;
                if (lastmin && nex < 4) {
                    nex++; printf("ex");
                    for (int i = 0; i < n; i++) printf(" %d", prof_g[i]);
                    printf(" | order"); for (int t = 0; t < n; t++) printf(" %d", ORD[t]);
                    printf(" | picks"); for (int i = 0; i < n; i++) printf(" %d", Yl[i]);
                    printf(" allmin %d lb %d\n", allmin, islb);
                }
            }
            if (!any) { st[4]++; if (lastmin) st[5]++; }
        }
        NORD = saveN;
        return;
    }
    /* insertion step: lookahead counts */
    int cnt[MAXN], mn = 1 << 30, lbch = -1;
    for (int i = 0; i < n; i++) cnt[i] = 1 << 20;
    for (int i = 0; i < n; i++) if (A >> i & 1) {
        uint32_t A2 = A & ~(1u << i), G2 = G & ~(1u << trip[i][0]); int Y2[MAXN];
        memcpy(Y2, Yl, sizeof(int) * n); Y2[i] = trip[i][0];
        while (A2 && r1_step(&A2, &G2, Y2)) ;
        cnt[i] = na_count(A2, G2, Y2);
        if (cnt[i] < mn) { mn = cnt[i]; lbch = i; }
    }
    int nmin = 0; for (int i = 0; i < n; i++) if ((A >> i & 1) && cnt[i] == mn) nmin++;
    int sC[MAXN], sL = LLEAD, sP = LPOS; uint32_t sA = LA; memcpy(sC, LCNT, sizeof sC);
    for (int i = 0; i < n; i++) if (A >> i & 1) {
        memcpy(LCNT, cnt, sizeof(int) * n); LLEAD = i; LPOS = NORD; LA = A;
        int Y3[MAXN]; memcpy(Y3, Yl, sizeof(int) * n); Y3[i] = trip[i][0];
        ORD[NORD++] = i;
        rec(Y3, A & ~(1u << i), G & ~(1u << trip[i][0]), cnt[i] == mn, cnt[i] == mn && nmin == 1,
            allmin && cnt[i] == mn, islb && i == lbch);
        NORD--;
    }
    memcpy(LCNT, sC, sizeof sC); LLEAD = sL; LPOS = sP; LA = sA;
    NORD = saveN;
}

int main(void) {
    int K;
    if (scanf("%d %d %d", &n, &m, &K) != 3 || n > MAXN || m > MAXM) { fprintf(stderr, "bad header\n"); return 1; }
    long total = 1; for (int i = 0; i < n; i++) total *= 6;
    printf("names"); for (int t = 0; t < NST; t++) printf(" %s", STN[t]); printf("\n");
    for (int c = 0; c < K; c++) {
        int sets[MAXN][3];
        for (int i = 0; i < n; i++) for (int q = 0; q < 3; q++) if (scanf("%d", &sets[i][q]) != 1) return 1;
        for (int i = 0; i < n; i++) { Rm[i] = 0; for (int q = 0; q < 3; q++) Rm[i] |= 1u << sets[i][q]; }
        memset(st, 0, sizeof st); nex = 0;
        for (long p = 0; p < total; p++) {
            long q = p;
            for (int i = n - 1; i >= 0; i--) { prof_g[i] = q % 6; q /= 6; }
            for (int i = 0; i < n; i++) {
                for (int t = 0; t < 3; t++) trip[i][t] = sets[i][PERMS[prof_g[i]][t]];
                for (int g = 0; g < m; g++) rk[i][g] = 3;
                for (int t = 0; t < 3; t++) rk[i][trip[i][t]] = t;
            }
            long before = st[2];
            int Y[MAXN]; for (int i = 0; i < n; i++) Y[i] = -1;
            NORD = 0;
            rec(Y, (1u << n) - 1, (1u << m) - 1, 1, 1, 1, 1);
            st[8]++; if (st[2] > before) st[9]++;
        }
        printf("core %d stat", c);
        for (int t = 0; t < NST; t++) printf(" %ld", st[t]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
