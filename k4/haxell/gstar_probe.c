/* Start-based test of CONN_2 for instances too large for the full census (k4/haxell.md §5).

   Input (stdin): one instance per line as in gstar.c ("n m" then per agent "d g v ..."), followed on the same line by
   "S" then the number of start states and each start as m holders (-1 = pool).
   For each start s (it must be a partial EFX0 allocation): best-first search through partial EFX0 allocations with
   at most as many pooled goods as the current state, each step a composite of at most two generic local moves (move
   one good to another agent; swap the holders of two goods, the pool counting as a holder; trade two bundles),
   preferring single moves and states with fewer pooled goods, until a complete EFX0 allocation is reached ("reached
   d" = number of steps on the path found), the search space is exhausted ("TRAP": s refutes CONN_2), or CAP states
   are expanded ("cap").  With WALK > 0, from each start also WALK random walks of LEN single EFX0-preserving moves
   are taken, and every state visited is tested the same way (probes for traps near the start).

   cc -O2 -o gstar_probe gstar_probe.c
   ./gstar_probe CAP WALK LEN SEED [RADIUS=2] < input   (RADIUS=1: single moves only, i.e. traps of G_1) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 12
#define MAXM 20
static int n, m;
static long val[MAXN][MAXM];
static long CAP; static int WALK, LEN, RADIUS = 2;
typedef unsigned long long u64;

static u64 enc(const int *o) { u64 s = 0; for (int g = m - 1; g >= 0; g--) s = s * (n + 1) + (o[g] < 0 ? n : o[g]); return s; }
static void dec(u64 s, int *o) { for (int g = 0; g < m; g++) { int x = s % (n + 1); s /= (n + 1); o[g] = x == n ? -1 : x; } }
static int pool(const int *o) { int c = 0; for (int g = 0; g < m; g++) c += o[g] < 0; return c; }
static int efx0(const int *own) {
    long tot[MAXN][MAXN], mn[MAXN][MAXN]; int cnt[MAXN];
    for (int j = 0; j < n; j++) { cnt[j] = 0; for (int i = 0; i < n; i++) { tot[i][j] = 0; mn[i][j] = -1; } }
    for (int g = 0; g < m; g++) { int j = own[g]; if (j < 0) continue; cnt[j]++;
        for (int i = 0; i < n; i++) { long x = val[i][g]; tot[i][j] += x; if (mn[i][j] < 0 || x < mn[i][j]) mn[i][j] = x; } }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        if (j != i && cnt[j] >= 2 && tot[i][j] - mn[i][j] > tot[i][i]) return 0;
    return 1;
}
/* generic local moves from o into buffer */
static int moves(const int *o, int out[][MAXM], int maxout) {
    int c = 0;
    for (int g = 0; g < m; g++) for (int b = 0; b < n; b++) if (b != o[g] && c < maxout) { memcpy(out[c], o, sizeof(int) * m); out[c][g] = b; c++; }
    for (int g = 0; g < m; g++) for (int h = g + 1; h < m; h++) if (o[g] != o[h] && c < maxout) {
        memcpy(out[c], o, sizeof(int) * m); out[c][g] = o[h]; out[c][h] = o[g]; c++; }
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (c < maxout) {
        for (int g = 0; g < m; g++) out[c][g] = o[g] == a ? b : o[g] == b ? a : o[g]; c++; }
    return c;
}
/* open-addressing hash set of u64 (value 0 reserved: shift by 1) */
static u64 *H; static long HS, HN; static int overflow;
static void hclear(long size) { HS = size; H = calloc(HS, sizeof(u64)); }
static int hput(u64 k) { if (HN > HS / 2) { overflow = 1; return 0; }
    k += 1; long i = (long)((k * 11400714819323198485ull) % (u64)HS);
    while (H[i]) { if (H[i] == k) return 0; i = (i + 1) % HS; } H[i] = k; HN++; return 1; }
#define MAXMV 1200
static int M1[MAXMV][MAXM], M2[MAXMV][MAXM];
/* buckets by pool size: a simple multi-queue */
static u64 *Q[MAXM + 1]; static long qh[MAXM + 1], qt[MAXM + 1], qcap;
static const char *search(const int *start, long *expanded, int *steps) {
    memset(H, 0, sizeof(u64) * HS); HN = 0; overflow = 0;
    for (int p = 0; p <= m; p++) { qh[p] = qt[p] = 0; }
    int o[MAXM]; memcpy(o, start, sizeof(int) * m);
    if (pool(o) == 0) { *steps = 0; *expanded = 0; return "reached"; }
    hput(enc(o)); Q[pool(o)][qt[pool(o)]++] = enc(o);
    long ex = 0;
    while (1) {
        int p = -1; for (int t = 0; t <= m; t++) if (qh[t] < qt[t]) { p = t; break; }
        if (p < 0) { *expanded = ex; return overflow ? "cap" : "TRAP"; }
        if (ex >= CAP || overflow) { *expanded = ex; return "cap"; }
        u64 s = Q[p][qh[p]++]; dec(s, o); ex++;
        int c1 = moves(o, M1, MAXMV);
        for (int pass = 0; pass < RADIUS; pass++)
        for (int t = 0; t < c1; t++) {
            if (pass == 0) {
                int *u = M1[t]; int pu = pool(u); if (pu > p || !efx0(u)) continue;
                if (pu == 0) { *expanded = ex; *steps = 1; return "reached"; }
                u64 e = enc(u); if (hput(e)) { if (qt[pu] < qcap) Q[pu][qt[pu]++] = e; else overflow = 1; }
            } else {
                int c2 = moves(M1[t], M2, MAXMV);
                for (int w = 0; w < c2; w++) { int *u = M2[w]; int pu = pool(u); if (pu > p || !efx0(u)) continue;
                    if (pu == 0) { *expanded = ex; *steps = 2; return "reached"; }
                    u64 e = enc(u); if (hput(e)) { if (qt[pu] < qcap) Q[pu][qt[pu]++] = e; else overflow = 1; } }
            }
        }
    }
}
static unsigned long rs = 88172645463325252ull;
static unsigned long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    CAP = argc > 1 ? atol(argv[1]) : 20000; WALK = argc > 2 ? atoi(argv[2]) : 0; LEN = argc > 3 ? atoi(argv[3]) : 0;
    if (argc > 4) rs ^= (unsigned long)atol(argv[4]) * 2654435761ull;
    if (argc > 5) RADIUS = atoi(argv[5]);
    qcap = 4000000; for (int p = 0; p <= MAXM; p++) Q[p] = malloc(sizeof(u64) * qcap);
    hclear(1 << 24);
    while (scanf("%d %d", &n, &m) == 2) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "instance too large: n %d m %d\n", n, m); return 2; }
        memset(val, 0, sizeof val);
        for (int i = 0; i < n; i++) { int d; if (scanf("%d", &d) != 1) return 1;
            for (int t = 0; t < d; t++) { int g; long v; if (scanf("%d %ld", &g, &v) != 2) return 1; val[i][g] = v; } }
        char tag[8]; int ns; if (scanf("%7s %d", tag, &ns) != 2) return 1;
        long tested = 0, reached = 0, traps = 0, caps = 0, maxex = 0; int worst = 0;
        for (int k = 0; k < ns; k++) {
            int st[MAXM]; for (int g = 0; g < m; g++) if (scanf("%d", &st[g]) != 1) return 1;
            if (!efx0(st)) { printf("start %d is not partial EFX0\n", k); continue; }
            for (int w = -1; w < WALK; w++) {
                int cur[MAXM]; memcpy(cur, st, sizeof(int) * m);
                for (int stepi = 0; stepi < (w < 0 ? 1 : LEN); stepi++) {
                    if (w >= 0) { /* one random EFX0-preserving single move with pool not growing */
                        int c1 = moves(cur, M1, MAXMV); int tries = 0;
                        while (tries++ < 4 * c1 + 8) { int *u = M1[rnd() % c1]; if (pool(u) <= pool(cur) && efx0(u)) { memcpy(cur, u, sizeof(int) * m); break; } }
                    }
                    if (pool(cur) == 0) continue;
                    long ex; int steps = 0; const char *r = search(cur, &ex, &steps);
                    tested++; if (ex > maxex) maxex = ex;
                    if (r[0] == 'r') reached++; else if (r[0] == 'T') { traps++; printf("TRAP"); for (int g = 0; g < m; g++) printf(" %d", cur[g]); printf("\n"); }
                    else { caps++; }
                }
            }
        }
        printf("instance n %d m %d probes %ld reached %ld traps %ld cap %ld max_expanded %ld\n", n, m, tested, reached, traps, caps, maxex);
        fflush(stdout);
        (void)worst;
    }
    return 0;
}
