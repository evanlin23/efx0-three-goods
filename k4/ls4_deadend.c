/* ls4_deadend.c: dead ends of Pareto local search (attempts/k4-ls-dead-end.md).
 * A DEAD END is a junk-free EFX0 partial allocation Y such that no complete EFX0 allocation X has V_i(X_i) >= V_i(Y_i)
 * for every agent i.  From a dead end no sequence of Pareto moves followed by a placement of the pool can succeed.
 * For each profile: all n^m complete allocations are tested for EFX0 (their value vectors kept), every junk-free
 * partial allocation is tested for EFX0 and for being a dead end; if a dead end exists, a breadth-first search from
 * the empty allocation over ALL valid single-agent rebundles (M1 moves: one agent takes Z subset R cap (Y_h cup U),
 * strictly better, result EFX0) decides whether some dead end is reachable with M1 moves alone.
 * Same input format as ls4alg.c.  Output: RESULT runs=profiles deadprof=... m1reach=... */
#define LS4_NO_MAIN
#include "ls4alg.c"

#define MAXS (1 << 22)
static long fr[4096][MAXN]; static int nfr;
static int gvv[MAXM][MAXN + 1], ngvv[MAXM];
static long dead_prof, reach_prof, dead_states;
static unsigned char *isdead, *seen;
static long pw[MAXM + 1];
static long code(const mask *X) {                 /* mixed radix: good g -> index in gvv[g] */
    long c = 0;
    for (int g = m - 1; g >= 0; g--) { int k = 0; for (int q = 1; q < ngvv[g]; q++) if (X[gvv[g][q]] >> g & 1) k = q; c = c * ngvv[g] + k; }
    return c;
}
static void decode(long c, mask *X) {
    for (int i = 0; i < n; i++) X[i] = 0;
    for (int g = 0; g < m; g++) { int k = c % ngvv[g]; c /= ngvv[g]; if (k) X[gvv[g][k]] |= 1u << g; }
}
static int dominated(const mask *X) {
    for (int f = 0; f < nfr; f++) { int ok = 1; for (int i = 0; i < n && ok; i++) if (fr[f][i] < vs(i, X[i])) ok = 0; if (ok) return 1; }
    return 0;
}
int main(int argc, char **argv) {
    long *queue = malloc(sizeof(long) * MAXS); isdead = malloc(MAXS); seen = malloc(MAXS);
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
        long NS = 1;
        for (int g = 0; g < m; g++) { ngvv[g] = 0; gvv[g][ngvv[g]++] = -1; for (int i = 0; i < n; i++) if (R[i] >> g & 1) gvv[g][ngvv[g]++] = i; NS *= ngvv[g]; }
        if (NS > MAXS) { printf("SKIP too many states\n"); continue; }
        long ncomp = 1; for (int g = 0; g < m; g++) ncomp *= n;
        long runs = 0; dead_prof = reach_prof = dead_states = 0; int printed = 0;
        memset(cur_idx, 0, sizeof cur_idx);
        for (long r = 0;; r++) {
            if (mode == 1) { if (r >= K) break; for (int i = 0; i < n; i++) cur_idx[i] = rnd() % T[i]; }
            for (int i = 0; i < n; i++) for (int t = 0; t < d[i]; t++) V[i][rg[i][t]] = 32L * rep[i][cur_idx[i]][t] + (1L << t);
            /* frontier of complete EFX0 allocations */
            nfr = 0;
            for (long c = 0; c < ncomp; c++) {
                mask X[MAXN] = {0}; long cc = c; for (int g = 0; g < m; g++) { X[cc % n] |= 1u << g; cc /= n; }
                if (!efx0(X)) continue;
                long v[MAXN]; for (int i = 0; i < n; i++) v[i] = vs(i, X[i]);
                int dom = 0; for (int f = 0; f < nfr && !dom; f++) { int ge = 1; for (int i = 0; i < n; i++) if (fr[f][i] < v[i]) ge = 0; dom = ge; }
                if (dom) continue;
                int w = 0; for (int f = 0; f < nfr; f++) { int le = 1; for (int i = 0; i < n; i++) if (fr[f][i] > v[i]) le = 0; if (!le) { memcpy(fr[w], fr[f], sizeof fr[0]); w++; } }
                nfr = w; if (nfr < 4096) { memcpy(fr[nfr], v, sizeof v); nfr++; }
            }
            long nd = 0;
            for (long c = 0; c < NS; c++) {
                mask X[MAXN]; decode(c, X); isdead[c] = 0;
                if (!efx0(X) || dominated(X)) continue;
                isdead[c] = 1; nd++;
            }
            if (nd) {
                dead_prof++; dead_states += nd;
                memset(seen, 0, NS); long qh = 0, qt = 0; mask E[MAXN] = {0}; long c0 = code(E); queue[qt++] = c0; seen[c0] = 1; long hit = -1;
                while (qh < qt && hit < 0) {
                    long c = queue[qh++]; decode(c, Y); mask a = 0; for (int i = 0; i < n; i++) a |= Y[i]; U = ALL & ~a;
                    if (isdead[c]) { hit = c; break; }
                    for (int h = 0; h < n; h++) {
                        long cur = vs(h, Y[h]); mask av = (Y[h] | U) & R[h];
                        for (int z = 1; z < (1 << d[h]); z++) {
                            mask Z = loc(h, z); if ((Z & ~av) || vs(h, Z) <= cur) continue;
                            int ok = 1; for (int x = 0; x < n && ok; x++) if (x != h && threat(x, Z) > vs(x, Y[x])) ok = 0;
                            if (!ok) continue;
                            mask S = Y[h]; Y[h] = Z; long c2 = code(Y); Y[h] = S;
                            if (!seen[c2]) { seen[c2] = 1; queue[qt++] = c2; }
                        }
                    }
                }
                if (hit >= 0) {
                    reach_prof++;
                    if (printed++ < 3) { decode(hit, Y); mask a = 0; for (int i = 0; i < n; i++) a |= Y[i];
                        printf("DEADEND reachable by M1: n=%d m=%d", n, m);
                        for (int i = 0; i < n; i++) { printf(" ["); for (int t = 0; t < d[i]; t++) printf(t ? " %d:%d" : "%d:%d", rg[i][t], rep[i][cur_idx[i]][t]); printf("]"); }
                        printf(" Y:"); for (int i = 0; i < n; i++) printf(" %x", Y[i]); printf(" U:%x\n", ALL & ~a); }
                }
            }
            runs++;
            if (mode == 0) { int i = 0; while (i < n && ++cur_idx[i] == T[i]) { cur_idx[i] = 0; i++; } if (i == n) break; }
        }
        printf("RESULT runs=%ld deadprof=%ld deadstates=%ld m1reach=%ld\n", runs, dead_prof, dead_states, reach_prof);
        fflush(stdout);
        if (reach_prof) anyfail = 1;
    }
    return 0;
}
