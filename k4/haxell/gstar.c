/* Traps of the EFX0-preserving local-move graph G* (k4/haxell.md §3.4), second implementation, written
   independently of ht_gstar.py (shares only the definitions).

   Input (stdin), one instance per line:  n m  then for each agent: d g_1 v_1 ... g_d v_d
   (goods 0..m-1, values nonnegative integers; goods not listed are worth 0 to that agent).
   A state assigns each good to an agent 0..n-1 or to the pool (coded n); it is a partial EFX0 allocation when for
   all agents i != j and every good h of X_j: v_i(X_j minus h) <= v_i(X_i) (raw definition; the pool is no bundle).
   G*: from a partial EFX0 state, a generic local move (move one good to another agent; swap the holders of two goods
   with different holders, the pool counting as a holder; trade the bundles of two agents) leads to another partial
   EFX0 state with no more pooled goods.  A trap: a partial EFX0 state from which no complete EFX0 allocation is
   reachable.  A radius-2 trap: a trap from which no non-trap partial EFX0 state with no more pooled goods is
   reachable by composites of two generic moves, iterated to the fixpoint (as ht_gstar.radius2_traps).

   Output per instance: n m states complete traps radius2traps minpool, and, if any, one trap state.
   cc -O2 -o gstar gstar.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 6
#define MAXM 13
static int n, m;
static long val[MAXN][MAXM];
static long pw[MAXM + 1];
static long NS;
static unsigned char *ok;       /* partial EFX0 */
static unsigned char *good;     /* reaches a complete EFX0 allocation */

static void decode(long s, int *own) { for (int g = 0; g < m; g++) { own[g] = s % (n + 1); s /= (n + 1); } }
static long encode(const int *own) { long s = 0; for (int g = m - 1; g >= 0; g--) s = s * (n + 1) + own[g]; return s; }
static int poolsz(const int *own) { int c = 0; for (int g = 0; g < m; g++) c += own[g] == n; return c; }

static int efx0(const int *own) {
    /* tot[i][j] = v_i(X_j), mn[i][j] = min over X_j of v_i, cnt[j] = |X_j|; then the raw EFX0 test
       v_i(X_j) - min_{h in X_j} v_i(h) <= v_i(X_i) for every j != i with |X_j| >= 2 (bundles of one good are never
       strongly envied; the pool, coded n, is no bundle) */
    long tot[MAXN][MAXN], mn[MAXN][MAXN]; int cnt[MAXN];
    for (int j = 0; j < n; j++) { cnt[j] = 0; for (int i = 0; i < n; i++) { tot[i][j] = 0; mn[i][j] = -1; } }
    for (int g = 0; g < m; g++) { int j = own[g]; if (j == n) continue; cnt[j]++;
        for (int i = 0; i < n; i++) { long x = val[i][g]; tot[i][j] += x; if (mn[i][j] < 0 || x < mn[i][j]) mn[i][j] = x; } }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        if (j != i && cnt[j] >= 2 && tot[i][j] - mn[i][j] > tot[i][i]) return 0;
    return 1;
}

/* neighbours of own: calls f(state) for each generic move result */
static int nb_count;
static long nb_buf[4096];
static void neighbours(const int *own) {
    int o[MAXM]; nb_count = 0;
    for (int g = 0; g < m; g++)
        for (int b = 0; b < n; b++) if (b != own[g]) { memcpy(o, own, sizeof(int) * m); o[g] = b; nb_buf[nb_count++] = encode(o); }
    for (int g = 0; g < m; g++) for (int h = g + 1; h < m; h++) if (own[g] != own[h]) {
        memcpy(o, own, sizeof(int) * m); o[g] = own[h]; o[h] = own[g]; nb_buf[nb_count++] = encode(o); }
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        for (int g = 0; g < m; g++) o[g] = own[g] == a ? b : own[g] == b ? a : own[g];
        nb_buf[nb_count++] = encode(o); }
}

int main(void) {
    while (scanf("%d %d", &n, &m) == 2) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "instance too large: n %d m %d (MAXN %d MAXM %d)\n", n, m, MAXN, MAXM); return 2; }
        memset(val, 0, sizeof val);
        for (int i = 0; i < n; i++) { int d; if (scanf("%d", &d) != 1) return 1;
            for (int t = 0; t < d; t++) { int g; long v; if (scanf("%d %ld", &g, &v) != 2) return 1; val[i][g] = v; } }
        pw[0] = 1; for (int g = 1; g <= m; g++) pw[g] = pw[g - 1] * (n + 1);
        NS = pw[m];
        ok = calloc(NS, 1); good = calloc(NS, 1);
        int own[MAXM];
        long states = 0, complete = 0;
        for (long s = 0; s < NS; s++) { decode(s, own); if (efx0(own)) { ok[s] = 1; states++; if (poolsz(own) == 0) { good[s] = 1; complete++; } } }
        /* reverse BFS from the complete EFX0 allocations.  The generic moves are symmetric (move back, swap again,
           trade again) except a placement from the pool, whose reverse returns a good to the pool; so the
           predecessors of u are its generic neighbours plus u with one allocated good returned to the pool,
           kept when EFX0 with at least as many pooled goods as u. */
        long *q = malloc(sizeof(long) * (states + 1)); long qh = 0, qt = 0;
        for (long s2 = 0; s2 < NS; s2++) if (good[s2]) q[qt++] = s2;
        while (qh < qt) {
            long u = q[qh++]; int ou[MAXM]; decode(u, ou); int pu = poolsz(ou);
            neighbours(ou);
            int o[MAXM];
            for (int g = 0; g < m; g++) if (ou[g] != n) { memcpy(o, ou, sizeof(int) * m); o[g] = n; nb_buf[nb_count++] = encode(o); }
            for (int t = 0; t < nb_count; t++) { long w = nb_buf[t]; int ow[MAXM];
                if (!ok[w] || good[w]) continue; decode(w, ow); if (poolsz(ow) < pu) continue;
                good[w] = 1; q[qt++] = w; }
        }
        free(q);
        long traps = 0; int minpool = 99; long ex = -1;
        for (long s = 0; s < NS; s++) if (ok[s] && !good[s]) { traps++; decode(s, own); int p = poolsz(own); if (p < minpool) { minpool = p; ex = s; } }
        /* radius-2: remove traps with a radius-2 neighbour (EFX0, pool not larger) outside the trap set; fixpoint */
        long r2 = 0;
        if (traps) {
            unsigned char *tr = calloc(NS, 1);
            for (long s = 0; s < NS; s++) if (ok[s] && !good[s]) tr[s] = 1;
            int ch = 1;
            while (ch) { ch = 0;
                for (long s = 0; s < NS; s++) { if (!tr[s]) continue;
                    decode(s, own); int p = poolsz(own); int esc = 0;
                    neighbours(own); int c1 = nb_count; long first[4096]; memcpy(first, nb_buf, sizeof(long) * c1);
                    for (int t = 0; t < c1 && !esc; t++) { int o1[MAXM]; decode(first[t], o1);
                        if (ok[first[t]] && !tr[first[t]] && poolsz(o1) <= p) { esc = 1; break; }
                        neighbours(o1);
                        for (int u = 0; u < nb_count; u++) { long w = nb_buf[u]; int o2[MAXM];
                            if (!ok[w] || tr[w]) continue; decode(w, o2); if (poolsz(o2) > p) continue; esc = 1; break; } }
                    if (esc) { tr[s] = 0; ch = 1; } } }
            for (long s = 0; s < NS; s++) r2 += tr[s];
            free(tr);
        }
        printf("%d %d states %ld complete %ld traps %ld radius2traps %ld minpool %d", n, m, states, complete, traps, r2, traps ? minpool : -1);
        if (ex >= 0) { decode(ex, own); printf(" example"); for (int g = 0; g < m; g++) printf(" %d", own[g] == n ? -1 : own[g]); }
        printf("\n"); fflush(stdout);
        free(ok); free(good);
    }
    return 0;
}
