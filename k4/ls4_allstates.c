/* ls4_allstates.c: conjecture TP4 (k4/local_search4.md §4) over EVERY stable state, not only those LS4 reaches.
 * For each profile: enumerate every junk-free partial allocation (each good in the pool or with an agent valuing it),
 * keep those that are EFX0 (for V), have a nonempty pool, and admit no M1, R or X move; check that Phase 2 (a), (b)
 * or (c) of LS4 applies, and that its output is EFX0 by the raw definition (representative and tied preimages).
 * Same input format as ls4alg.c.  Output: RESULT runs=profiles states=... stable=... fail=... */
#define LS4_NO_MAIN
#include "ls4alg.c"

static long st_states, st_efx, st_stable, st_fail, st_p2[5];
static int gv[MAXM][MAXN + 1], ngv[MAXM];
static void check_state(void) {
    st_states++;
    mask a = 0; for (int i = 0; i < n; i++) a |= Y[i];
    U = ALL & ~a;
    if (!U || !efx0(Y)) return;
    st_efx++;
    mask save[MAXN]; memcpy(save, Y, sizeof save); mask su = U;
    int mv = move_M1(); if (!mv) mv = move_R();
#ifndef NOX
    if (!mv) mv = move_X();
#endif
    memcpy(Y, save, sizeof save); U = su;
    if (mv) return;
    st_stable++;
    int c = phase2();
    if (!c || c == 4) { st_fail++; if (st_fail <= 5) report(c ? "stable state needs the exact search" : "stable state without placement"); return; }
    st_p2[c]++;
    if (!efx0(P2)) report("placement not EFX0 (V)");
    for (int i = 0; i < n; i++) {
        if (!raw_safe(i, rep[i][cur_idx[i]], P2)) report("placement not EFX0 (raw)");
        for (int p = 0; p < np_[i][cur_idx[i]]; p++) if (!raw_safe(i, pre[i][cur_idx[i]][p], P2)) report("placement not EFX0 (raw, tied)");
    }
}
static void rec(int g) {
    if (g == m) { check_state(); return; }
    for (int k = 0; k < ngv[g]; k++) {
        int i = gv[g][k];
        if (i >= 0) Y[i] |= 1u << g;
        rec(g + 1);
        if (i >= 0) Y[i] &= ~(1u << g);
    }
}
int main(void) {
    int anyfail = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        ALL = (1u << m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &d[i]) != 1) return 3; R[i] = 0;
            for (int t = 0; t < d[i]; t++) { if (scanf("%d", &rg[i][t]) != 1) return 3; R[i] |= 1u << rg[i][t]; } }
        for (int i = 0; i < n; i++) {
            if (scanf("%d", &T[i]) != 1 || T[i] > MAXT) return 3;
            for (int t = 0; t < T[i]; t++) {
                if (scanf("%d", &np_[i][t]) != 1 || np_[i][t] > MAXP) return 3;
                for (int q = 0; q < d[i]; q++) if (scanf("%d", &rep[i][t][q]) != 1) return 3;
                for (int p = 0; p < np_[i][t]; p++) for (int q = 0; q < d[i]; q++) if (scanf("%d", &pre[i][t][p][q]) != 1) return 3;
            }
        }
        int mode; long K; unsigned long long seed;
        if (scanf("%d %ld %llu", &mode, &K, &seed) != 3) return 3;
        rs = seed * 2654435761ULL + 12345;
        for (int g = 0; g < m; g++) { ngv[g] = 0; gv[g][ngv[g]++] = -1; for (int i = 0; i < n; i++) if (R[i] >> g & 1) gv[g][ngv[g]++] = i; }
        long runs = 0; st_states = st_efx = st_stable = st_fail = 0; memset(st_p2, 0, sizeof st_p2); cnt_fail = 0;
        memset(cur_idx, 0, sizeof cur_idx);
        for (long r = 0;; r++) {
            if (mode == 1) { if (r >= K) break; for (int i = 0; i < n; i++) cur_idx[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) for (int t = 0; t < d[i]; t++) V[i][rg[i][t]] = 32L * rep[i][cur_idx[i]][t] + (1L << t);
            for (int i = 0; i < n; i++) Y[i] = 0;
            rec(0); runs++;
            if (mode == 0) { int i = 0; while (i < n && ++cur_idx[i] == T[i]) { cur_idx[i] = 0; i++; } if (i == n) break; }
        }
        printf("RESULT runs=%ld states=%ld efx0_nonempty_pool=%ld stable=%ld fail=%ld empty=%ld dump=%ld dm=%ld\n",
               runs, st_states, st_efx, st_stable, st_fail + cnt_fail, st_p2[1], st_p2[2], st_p2[3]);
        fflush(stdout);
        if (st_fail || cnt_fail) anyfail = 1;
    }
    return anyfail;
}
