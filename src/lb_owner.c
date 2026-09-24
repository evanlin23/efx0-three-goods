/* Instrumentation of construction LB's last step (ledger S2.LB; proofs/lb_last_step.md). Reuses construct.c verbatim
   (included below with its main renamed), re-runs Phase 1 recording the processing order, and, on every profile where
   LB needs its overflow bundle, tests which agents are valid owners and a list of candidate owner rules.
   Build: gcc -O2 -o lb_owner lb_owner.c        (lb_owner.py compiles and drives it)
   stdin: as construct.c ("n m K", then K lines of 3n goods).
   stdout, per core: "core <k> over <o> stat <counters...>" and up to 3 "ex <profile> <info>" lines for violations of
   rule 0 (the last-processed agent is a valid owner). */
#include "lb_common.h"

#define NST 16
static const char *STN[NST] = {
    "over",            /* 0 profiles where the overflow bundle is needed */
    "last_ok",         /* 1 the last-processed agent is a valid owner */
    "last_frozen",     /* 2 the last-processed agent is frozen (should never happen) */
    "any_ok",          /* 3 some owner valid (LB succeeds) */
    "lastins_ok",      /* 4 the last insertion agent is valid */
    "nopick_exists",   /* 5 some agent has no pick */
    "nopick_ok",       /* 6 some agent without a pick is valid */
    "last_r1",         /* 7 the last-processed agent is an R1 agent */
    "last_up",         /* 8 the last-processed agent is upgraded */
    "last_nopick",     /* 9 the last-processed agent has no pick */
    "last_holds_c",    /* 10 the last-processed agent holds its c */
    "last_holds_b",    /* 11 */
    "last_holds_a",    /* 12 */
    "omega1",          /* 13 overflow omega = 1 */
    "omega2",          /* 14 omega = 2 */
    "omega3p",         /* 15 omega >= 3 */
};

int main(void) {
    int K;
    if (scanf("%d %d %d", &n, &m, &K) != 3 || n > MAXN || m > MAXM) { fprintf(stderr, "bad header\n"); return 1; }
    long total = 1; for (int i = 0; i < n; i++) total *= 6;
    printf("names"); for (int t = 0; t < NST; t++) printf(" %s", STN[t]); printf("\n");
    for (int c = 0; c < K; c++) {
        int sets[MAXN][3];
        for (int i = 0; i < n; i++) for (int q = 0; q < 3; q++) if (scanf("%d", &sets[i][q]) != 1) return 1;
        for (int i = 0; i < n; i++) { Rm[i] = 0; for (int q = 0; q < 3; q++) Rm[i] |= 1u << sets[i][q]; }
        long st[NST] = {0}; int nex = 0;
        for (long p = 0; p < total; p++) {
            int prof[MAXN]; long q = p;
            for (int i = n - 1; i >= 0; i--) { prof[i] = q % 6; q /= 6; }
            for (int i = 0; i < n; i++) {
                for (int t = 0; t < 3; t++) trip[i][t] = sets[i][PERMS[prof[i]][t]];
                for (int g = 0; g < m; g++) rk[i][g] = 3;
                for (int t = 0; t < 3; t++) rk[i][trip[i][t]] = t;
            }
            int Y[MAXN], Y1[MAXN], order[MAXN], isr1[MAXN], pos[MAXN]; uint32_t J, J1;
            phase1(Y1, &J1);
            phase1_order(Y, &J, order, isr1, pos);
            if (J != J1 || memcmp(Y, Y1, sizeof(int) * n)) { fprintf(stderr, "phase1 mismatch\n"); return 2; }
            P2 s; phase2_state(Y, J, &s);
            if (s.nj <= s.sumcap) continue;
            int omega = s.nj - s.sumcap;
            st[0]++;
            int z = order[n - 1], lastins = -1, anyok = 0, nopick_ok = 0, nopick = 0;
            for (int t = n - 1; t >= 0; t--) if (!isr1[order[t]]) { lastins = order[t]; break; }
            int ok[MAXN];
            for (int o = 0; o < n; o++) { ok[o] = owner_ok(Y, &s, o); anyok |= ok[o]; if (Y[o] < 0) { nopick = 1; nopick_ok |= ok[o]; } }
            if (ok[z]) st[1]++;
            if (s.frozen[z]) st[2]++;
            if (anyok) st[3]++;
            if (lastins >= 0 && ok[lastins]) st[4]++;
            if (nopick) st[5]++;
            if (nopick_ok) st[6]++;
            if (isr1[z]) st[7]++;
            if (s.up >> z & 1) st[8]++;
            if (Y[z] < 0) st[9]++;
            if (Y[z] >= 0 && s.held[z] == 2) st[10]++;
            if (Y[z] >= 0 && s.held[z] == 1) st[11]++;
            if (Y[z] >= 0 && s.held[z] == 0) st[12]++;
            st[omega == 1 ? 13 : omega == 2 ? 14 : 15]++;
            if (!ok[z] && nex < 3) {
                nex++;
                printf("ex");
                for (int i = 0; i < n; i++) printf(" %d", prof[i]);
                printf(" | order");
                for (int t = 0; t < n; t++) printf(" %d%s", order[t], isr1[order[t]] ? "r" : "i");
                printf(" | picks");
                for (int i = 0; i < n; i++) printf(" %d", Y[i]);
                printf(" | junk");
                for (int t = 0; t < s.nj; t++) printf(" %d", s.Jl[t]);
                printf(" | up %x frozen", s.up);
                for (int i = 0; i < n; i++) printf("%d", s.frozen[i]);
                printf(" ok");
                for (int i = 0; i < n; i++) printf("%d", ok[i]);
                printf(" omega %d\n", omega);
            }
        }
        printf("core %d stat", c);
        for (int t = 0; t < NST; t++) printf(" %ld", st[t]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
