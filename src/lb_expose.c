/* Construction LB's last step (ledger S2.LB; proofs/lb_last_step.md): the owner rules of the written proof, tested on
   every profile where LB needs its overflow bundle, with the counting quantities the proof uses.
   Build: gcc -O2 -o lb_expose lb_expose.c     (lb_owner.py --bin=lb_expose compiles and drives it)
   stdin: as construct.c. stdout: "names ...", then per core "core <k> stat <counters>", plus "ex" lines for failures
   of the owner rule under test. */
#include "lb_common.h"

/* For owner o: the exposed agents (k != o holding exactly its top, not upgraded, with b_k and c_k both in
   J' u L0(o)), whether one has both inside L0(o), and the size of a smallest set of junk goods meeting every exposed
   pair (brute force; pairs with a good in L0 must use the other good). Returns the number of exposed agents. */
static int exposure(const int *Y, const P2 *s, int o, int *inL0, int *hit, uint32_t *expmask) {
    uint32_t L0 = 0;
    if (Y[o] >= 0) L0 |= 1u << Y[o];
    if (s->up >> o & 1) L0 |= 1u << trip[o][2];
    uint32_t avail = s->J | L0;
    uint32_t pr[MAXN]; int np = 0, ne = 0; *inL0 = 0; *expmask = 0;
    for (int k = 0; k < n; k++) {
        if (k == o || s->held[k] != 0 || (s->up >> k & 1)) continue;
        uint32_t P = (1u << trip[k][1]) | (1u << trip[k][2]);
        if ((P & avail) != P) continue;
        ne++; *expmask |= 1u << k;
        if ((P & L0) == P) { *inL0 = 1; continue; }
        pr[np++] = P & ~L0;          /* the junk part: must contain a good sent elsewhere */
    }
    /* smallest hitting set among junk goods (at most MAXM choose small; np <= n) */
    int best = np;
    for (int size = 0; size < np && best == np; size++) {
        int idx[MAXM]; int nj = s->nj;
        if (size > nj) break;
        for (int t = 0; t < size; t++) idx[t] = t;
        for (;;) {
            uint32_t C = 0;
            for (int t = 0; t < size; t++) C |= 1u << s->Jl[idx[t]];
            int okc = 1;
            for (int t = 0; t < np && okc; t++) if (!(pr[t] & C)) okc = 0;
            if (okc) { best = size; break; }
            int t = size - 1;
            while (t >= 0 && idx[t] == nj - size + t) t--;
            if (t < 0) break;
            idx[t]++;
            for (int u = t + 1; u < size; u++) idx[u] = idx[u - 1] + 1;
        }
    }
    *hit = best;
    return ne;
}

#define NST 26
static const char *STN[NST] = {
    "over", "z_ok", "z_up", "z_up_fail", "z_inL0", "z_hit_gt_slots", "z_exposed_not_insertion",
    "z_simple_ok", "z_hitcrit_eq_ok", "rule1_ok", "rule1_frozen", "rule1_is_z",
    "exposed0", "exposed1", "exposed2p", "slots0", "slots1", "slots2p", "exp_frozen_ge1", "any_ok",
    "r_exposed_all_ins", "r_simple_ok", "chain_ok", "chain_only_r", "r_exposed_2_same_block", "chain_only_r_but_ok"
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
            if (s.nj <= s.sumcap) continue;
            st[0]++;
            int z = order[n - 1], zok = owner_ok(Y, &s, z);
            int inL0, hit; uint32_t em;
            int ne = exposure(Y, &s, z, &inL0, &hit, &em);
            int slots = s.sumcap - s.cap[z];
            if (zok) st[1]++;
            if (s.up >> z & 1) { st[2]++; if (!zok) st[3]++; }
            if (inL0) st[4]++;
            if (!inL0 && hit > slots) st[5]++;
            for (int k = 0; k < n; k++) if ((em >> k & 1) && isr1[k]) { st[6]++; break; }
            if (!inL0 && ne <= slots) st[7]++;
            if (zok == (!inL0 && hit <= slots)) st[8]++;
            /* rule 1: the last-processed agent that is not upgraded */
            int r1 = -1;
            for (int t = n - 1; t >= 0; t--) if (!(s.up >> order[t] & 1)) { r1 = order[t]; break; }
            int r1ok = r1 >= 0 && owner_ok(Y, &s, r1);
            if (r1ok) st[9]++;
            if (r1 >= 0 && s.frozen[r1]) st[10]++;
            if (r1 == z) st[11]++;
            st[ne == 0 ? 12 : ne == 1 ? 13 : 14]++;
            st[slots == 0 ? 15 : slots == 1 ? 16 : 17]++;
            for (int k = 0; k < n; k++) if ((em >> k & 1) && s.frozen[k]) { st[18]++; break; }
            int any = 0; for (int o = 0; o < n; o++) any |= owner_ok(Y, &s, o);
            if (any) st[19]++;
            /* rule 1 analysis: exposed agents w.r.t. r = r1, needer chains */
            if (r1 >= 0) {
                int inL0r, hitr; uint32_t emr;
                int ner = exposure(Y, &s, r1, &inL0r, &hitr, &emr);
                int allins = 1; for (int k = 0; k < n; k++) if ((emr >> k & 1) && isr1[k]) allins = 0;
                if (allins) st[20]++;
                if (!inL0r && ner <= s.sumcap - s.cap[r1]) st[21]++;
                /* block of each agent: index of the last insertion agent at or before it in the order */
                int blk[MAXN], b = -1;
                for (int t = 0; t < n; t++) { if (!isr1[order[t]]) b = t; blk[order[t]] = b; }
                int chainok = 1, onlyr = 0, same = 0;
                for (int k = 0; k < n; k++) if (emr >> k & 1) {
                    for (int k2 = 0; k2 < k; k2++) if ((emr >> k2 & 1) && blk[k2] == blk[k]) same = 1;
                    /* reachable set via needer edges x -> j (j not upgraded, values Y_x more than its pick) */
                    uint32_t reach = 1u << k, frontier = 1u << k;
                    while (frontier) {
                        int x = __builtin_ctz(frontier); frontier &= frontier - 1;
                        if (!s.frozen[x] || Y[x] < 0) continue;
                        for (int j = 0; j < n; j++) if (j != x && !(s.up >> j & 1) && !(reach >> j & 1) && rk[j][Y[x]] < s.held[j]) { reach |= 1u << j; frontier |= 1u << j; }
                    }
                    uint32_t term = 0;
                    for (int j = 0; j < n; j++) if ((reach >> j & 1) && !s.frozen[j] && !(s.up >> j & 1)) term |= 1u << j;
                    if (!(term & ~(1u << r1))) { chainok = 0; if (term == (1u << r1)) onlyr = 1; }
                }
                if (chainok) st[22]++;
                if (onlyr) { st[23]++; if (r1ok) st[25]++; }
                if (same) st[24]++;
                if (onlyr && nex < 5) {
                    nex++;
                    printf("ex ONLYR");
                    for (int i = 0; i < n; i++) printf(" %d", prof[i]);
                    printf(" | order");
                    for (int t = 0; t < n; t++) printf(" %d%s", order[t], isr1[order[t]] ? "r" : "i");
                    printf(" | picks");
                    for (int i = 0; i < n; i++) printf(" %d", Y[i]);
                    printf(" | junk");
                    for (int t = 0; t < s.nj; t++) printf(" %d", s.Jl[t]);
                    printf(" | up %x frozen", s.up);
                    for (int i = 0; i < n; i++) printf("%d", s.frozen[i]);
                    printf(" r %d exposed %x\n", r1, emr);
                }
            }
            if (!r1ok && nex < 5) {
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
                for (int i = 0; i < n; i++) printf("%d", owner_ok(Y, &s, i));
                printf("\n");
            }
        }
        printf("core %d stat", c);
        for (int t = 0; t < NST; t++) printf(" %ld", st[t]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
