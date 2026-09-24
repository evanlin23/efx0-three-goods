/* Construction LB's Phase 1 as blocks (ledger S2.LB; proofs/lb_last_step.md): a block is an insertion step followed
   by its cascade of R1 steps. Tests, on every profile (not only those needing the overflow bundle), the block
   lemmas of the written proof. r = the last-processed agent that is not upgraded.
   Build: gcc -O2 -o lb_block lb_block.c        (lb_owner.py --bin=lb_block compiles and drives it) */
#include "lb_common.h"

#define NST 12
static const char *STN[NST] = {
    "profiles", "over", "r_in_last_block", "after_r_all_up", "lastleader_exposed", "C2_holds",
    "C2_holds_over", "lastleader_exp_frozen", "C2_fail", "C2_fail_over", "every_block_has_terminal", "r_ok_over"
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
            int Y[MAXN], order[MAXN], isr1[MAXN], pos[MAXN]; uint32_t J;
            phase1_order(Y, &J, order, isr1, pos);
            P2 s; phase2_state(Y, J, &s);
            int over = s.nj > s.sumcap;
            st[0]++; if (over) st[1]++;
            int blk[MAXN], b = -1, lastlead = -1;
            for (int t = 0; t < n; t++) { if (!isr1[order[t]]) { b = t; lastlead = order[t]; } blk[order[t]] = b; }
            int r = -1;
            for (int t = n - 1; t >= 0; t--) if (!(s.up >> order[t] & 1)) { r = order[t]; break; }
            if (blk[r] == b) st[2]++;
            int allup = 1; for (int t = pos[r] + 1; t < n; t++) if (!(s.up >> order[t] & 1)) allup = 0;
            if (allup) st[3]++;
            /* exposed w.r.t. r: holds exactly its top, b and c in J' u {Y_r} */
            uint32_t avail = s.J | (Y[r] >= 0 ? 1u << Y[r] : 0);
            int k = lastlead;
            int kexp = k != r && s.held[k] == 0 && (avail >> trip[k][1] & 1) && (avail >> trip[k][2] & 1);
            int term2 = 0;
            for (int j = 0; j < n; j++) if (blk[j] == b && j != r && !s.frozen[j] && !(s.up >> j & 1)) term2 = 1;
            if (kexp) { st[4]++; if (s.frozen[k]) st[7]++; }
            int c2 = !kexp || term2;
            if (c2) { st[5]++; if (over) st[6]++; }
            else { st[8]++; if (over) st[9]++; }
            int allterm = 1;
            for (int bb = 0; bb < n; bb++) if (!isr1[order[bb]]) {
                int has = 0;
                for (int j = 0; j < n; j++) if (blk[j] == bb && !s.frozen[j] && !(s.up >> j & 1)) has = 1;
                if (!has) allterm = 0;
            }
            if (allterm) st[10]++;
            if (over && owner_ok(Y, &s, r)) st[11]++;
            if (!c2 && nex < 4) {
                nex++;
                printf("ex%s", over ? " OVER" : "");
                for (int i = 0; i < n; i++) printf(" %d", prof[i]);
                printf(" | order");
                for (int t = 0; t < n; t++) printf(" %d%s", order[t], isr1[order[t]] ? "r" : "i");
                printf(" | picks");
                for (int i = 0; i < n; i++) printf(" %d", Y[i]);
                printf(" | junk");
                for (int t = 0; t < s.nj; t++) printf(" %d", s.Jl[t]);
                printf(" | up %x frozen", s.up);
                for (int i = 0; i < n; i++) printf("%d", s.frozen[i]);
                printf(" r %d\n", r);
            }
        }
        printf("core %d stat", c);
        for (int t = 0; t < NST; t++) printf(" %ld", st[t]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
