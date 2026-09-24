/* Shared by lb_owner.c and lb_expose.c: construct.c included verbatim (its main renamed), Phase 1 re-run with the
   processing order recorded, the Phase 2 state up to the owner search, and the owner test. */
#define main construct_main_unused
#include "construct.c"
#undef main

/* Phase 1 again, recording the processing order and whether each agent was an R1 agent (1) or an insertion agent (0).
   Identical steps to construct.c's phase1 (checked against it on every profile). */
static void phase1_order(int *Y, uint32_t *J, int *order, int *isr1, int *pos) {
    uint32_t A = (1u << n) - 1, G = (m == 32) ? 0xffffffffu : ((1u << m) - 1);
    int t = 0;
    for (int i = 0; i < n; i++) Y[i] = -1;
    while (A) {
        uint32_t A0 = A;
        if (r1_step(&A, &G, Y)) {
            int i = __builtin_ctz(A0 & ~A); order[t] = i; pos[i] = t++; isr1[i] = 1; continue;
        }
        int bi = -1, bs = 1 << 30;
        for (int i = 0; i < n; i++) if (A >> i & 1) {
            uint32_t A2 = A & ~(1u << i), G2 = G & ~(1u << trip[i][0]); int Y2[MAXN];
            memcpy(Y2, Y, sizeof(int) * n); Y2[i] = trip[i][0];
            while (A2 && r1_step(&A2, &G2, Y2)) ;
            int s = na_count(A2, G2, Y2) * 16 + i;
            if (s < bs) { bs = s; bi = i; }
        }
        Y[bi] = trip[bi][0]; A &= ~(1u << bi); G &= ~(1u << trip[bi][0]);
        order[t] = bi; pos[bi] = t++; isr1[bi] = 0;
    }
    *J = G;
}

/* Phase 2 state (the same computation as construct.c's phase2 up to the owner search). */
typedef struct { int held[MAXN], frozen[MAXN], cap[MAXN], sumcap, nj, Jl[MAXM]; uint32_t up, NA, J; } P2;

static void phase2_state(const int *Y, uint32_t J, P2 *s) {
    uint32_t done = (1u << n) - 1, up = 0;
    for (int k = 0; k < n; k++) s->held[k] = held_of(k, Y);
    for (;;) {
        uint32_t NA = need_mask(done, up, Y);
        int found = -1;
        for (int k = 0; k < n; k++)
            if (!(up >> k & 1) && s->held[k] == 1 && (J >> trip[k][2] & 1) && !(NA >> trip[k][1] & 1)) { found = k; break; }
        if (found < 0) break;
        up |= 1u << found; J &= ~(1u << trip[found][2]);
    }
    s->up = up; s->NA = need_mask(done, up, Y); s->J = J; s->sumcap = 0; s->nj = 0;
    for (int k = 0; k < n; k++) {
        s->frozen[k] = Y[k] >= 0 && (s->NA >> Y[k] & 1);
        s->cap[k] = (s->frozen[k] || (up >> k & 1)) ? 0 : (Y[k] >= 0 ? 1 : 2);
        s->sumcap += s->cap[k];
    }
    for (int g = 0; g < m; g++) if (J >> g & 1) s->Jl[s->nj++] = g;
}

/* Is o a valid owner (some overflow set passes the owner constraint)? */
static int owner_ok(const int *Y, const P2 *s, int o) {
    if (s->frozen[o]) return 0;
    int need = s->nj - (s->sumcap - s->cap[o]);
    uint32_t L0 = 0;
    if (Y[o] >= 0) L0 |= 1u << Y[o];
    if (s->up >> o & 1) L0 |= 1u << trip[o][2];
    int idx[MAXM];
    if (need > s->nj) return 0;
    for (int t = 0; t < need; t++) idx[t] = t;
    for (;;) {
        uint32_t L = L0;
        for (int t = 0; t < need; t++) L |= 1u << s->Jl[idx[t]];
        int bad = 0;
        for (int k = 0; k < n && !bad; k++)
            if (k != o && s->held[k] == 0 && !(s->up >> k & 1) && (L >> trip[k][1] & 1) && (L >> trip[k][2] & 1)) bad = 1;
        if (!bad) return 1;
        int t = need - 1;
        while (t >= 0 && idx[t] == s->nj - need + t) t--;
        if (t < 0) return 0;
        idx[t]++;
        for (int u = t + 1; u < need; u++) idx[u] = idx[u - 1] + 1;
    }
}

