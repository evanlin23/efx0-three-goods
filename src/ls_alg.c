/* Algorithm LS2 of proofs/local_search.md (Theorem C): two-phase local search that computes an EFX0 allocation of a
   core. Run on every ranking profile of every core read on stdin, with every Phase-1 step and the final allocation
   checked, and the distinct final allocations of each core written as a certificate record (one JSON line per core,
   to be gzipped into the format of tools/check_certs.py by src/local_search.py).

   Phase 1 (junk-free partial allocation Y, unallocated goods U; each step keeps Y EFX0 and raises the sum of levels):
     1  an agent envies a good u of U: it swaps its bundle for {u}                         (M1)
     2  the envy graph has a cycle: each agent on it takes its own goods of the next bundle (M3, rotation)
     3  an a-holder has b and c in U: it takes {b, c}, a goes to U                        (M1)
     4  an a-holder has one of b, c in U and nobody envies a: it adds that good            (M1)
     5  a one-good source values a good of U: it adds that good                            (M1)
     6  a one-good source s is dirty for u through a-holder i (bottom pair {u, y_s}) and there is an envy path
        from s to i: champion move along the path, i takes {u, y_s}                        (M2)
     7  the dirty sets D(s) of the one-good sources have a system of distinct representatives: follow one
        representative edge out of every source (Gamma), take a cycle, unfold it into an augmented envy cycle and
        apply it                                                                             (M3)
   Phase 2 (none of 1-7 applies): an agent with an empty bundle takes all of U; otherwise a maximum matching of
   one-good sources to their dirty goods leaves a source s* unmatched; with T the sources reachable from s* by
   alternating paths, every good of D(T) goes alone to its matched source and every other good of U goes to s*.
   Checks: after every Phase-1 step, Y is EFX0 (ordinal rule), junk-free, has no bundle of more than two goods, and
   the sum of levels increased; the final allocation is complete, EFX0 under the RAW definition for two balanced
   realizations of every ranking, and has at most one bundle of more than two goods (conjecture D's shape, Claim 5).
   Any failure aborts.
   Usage: ls_alg [-c] < cores     (-c: print the certificate lines "CERT {json}") */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 9
#define MAXM 18
static int n, m;
static int G[MAXN][3];
static int ra[MAXN], rb[MAXN], rc[MAXN];
static unsigned Rm[MAXN];
static const int IDX[8] = {0, 1, 2, 4, 3, 5, 6, 7};
static const int PERM[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static const int REAL[2][3] = {{4, 3, 2}, {10, 9, 2}};
static long long cnt_step[16], cnt_runs, max_iter;
static int cert = 0;

static inline int popc(unsigned x) { return __builtin_popcount(x); }
static int o[MAXM];                 /* owner, -1 = unallocated */
static unsigned bm[MAXN], pool;
static void rebuild(void) {
    for (int j = 0; j < n; j++) bm[j] = 0;
    pool = 0;
    for (int g = 0; g < m; g++) { if (o[g] < 0) pool |= 1u << g; else bm[o[g]] |= 1u << g; }
}
static inline int levm(int i, unsigned mask) {
    int b = ((mask >> ra[i] & 1) << 2) | ((mask >> rb[i] & 1) << 1) | (mask >> rc[i] & 1);
    return IDX[b];
}
static inline int ownbits(int i, unsigned mask) {
    return ((mask >> ra[i] & 1) << 2) | ((mask >> rb[i] & 1) << 1) | (mask >> rc[i] & 1);
}
static int isfree(int g) { return o[g] < 0 || popc(bm[o[g]]) == 1; }
static int safe_i(int i) {
    int b = ownbits(i, bm[i]);
    if (popc(b) >= 2) return 1;
    if (b == 4) { int x = o[rb[i]], y = o[rc[i]]; return !(x >= 0 && x == y && popc(bm[x]) >= 3); }
    if (b == 2) return isfree(ra[i]);
    if (b == 1) return isfree(ra[i]) && isfree(rb[i]);
    return isfree(ra[i]) && isfree(rb[i]) && isfree(rc[i]);
}
static int efx0(void) { for (int i = 0; i < n; i++) if (!safe_i(i)) return 0; return 1; }
static int sumlev(void) { int s = 0; for (int i = 0; i < n; i++) s += levm(i, bm[i]); return s; }
static int raw_efx0_complete(void) {
    for (int g = 0; g < m; g++) if (o[g] < 0) return 0;
    for (int r = 0; r < 2; r++)
        for (int i = 0; i < n; i++) {
            int w[MAXM] = {0}; w[ra[i]] = REAL[r][0]; w[rb[i]] = REAL[r][1]; w[rc[i]] = REAL[r][2];
            int own = 0; for (int g = 0; g < m; g++) if (o[g] == i) own += w[g];
            for (int j = 0; j < n; j++) if (j != i) {
                int sum = 0, mn = 1 << 30, cnt = 0;
                for (int g = 0; g < m; g++) if (o[g] == j) { sum += w[g]; if (w[g] < mn) mn = w[g]; cnt++; }
                if (cnt >= 2 && sum - mn > own) return 0;
            }
        }
    return 1;
}
static void die(const char *msg) {
    fprintf(stderr, "FAILURE: %s\n rankings:", msg);
    for (int i = 0; i < n; i++) fprintf(stderr, " (%d,%d,%d)", ra[i], rb[i], rc[i]);
    fprintf(stderr, "\n owners:"); for (int g = 0; g < m; g++) fprintf(stderr, " %d", o[g]);
    fprintf(stderr, "\n"); exit(3);
}

static int env[MAXN][MAXN], reach[MAXN][MAXN], indeg[MAXN];
static void envy_graph(void) {
    for (int j = 0; j < n; j++) indeg[j] = 0;
    for (int i = 0; i < n; i++) { int L = levm(i, bm[i]);
        for (int j = 0; j < n; j++) { env[i][j] = i != j && levm(i, bm[j]) > L; indeg[j] += env[i][j]; } }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) reach[i][j] = env[i][j];
    for (int k = 0; k < n; k++) for (int i = 0; i < n; i++) if (reach[i][k])
        for (int j = 0; j < n; j++) if (reach[k][j]) reach[i][j] = 1;
}
/* shortest envy path from s to t (s != t); returns length (number of vertices) into path[] */
static int envy_path(int s, int t, int *path) {
    int par[MAXN], q[MAXN], h = 0, tl = 0, seen = 1 << s; q[tl++] = s; par[s] = -1;
    while (h < tl) { int v = q[h++]; if (v == t) break;
        for (int w = 0; w < n; w++) if (env[v][w] && !(seen >> w & 1)) { seen |= 1 << w; par[w] = v; q[tl++] = w; } }
    if (!(seen >> t & 1)) return 0;
    int L = 0; for (int v = t; v >= 0; v = par[v]) path[L++] = v;
    for (int a = 0, b = L - 1; a < b; a++, b--) { int x = path[a]; path[a] = path[b]; path[b] = x; }
    return L;
}
/* apply a cycle/path of "takes": agent who[k] gets new bundle Z[k]; every good of the bundles of the agents in
   `dissolve` that is not in some Z goes to U. (All Z consist of the taker's own goods, so Y stays junk-free.) */
static void apply_takes(int K, const int *who, const unsigned *Z, unsigned dissolve_agents) {
    unsigned freed = 0, taken = 0;
    for (int j = 0; j < n; j++) if (dissolve_agents >> j & 1) freed |= bm[j];
    for (int k = 0; k < K; k++) taken |= Z[k];
    for (int g = 0; g < m; g++) if ((freed >> g & 1) && !(taken >> g & 1)) o[g] = -1;
    for (int k = 0; k < K; k++) for (int g = 0; g < m; g++) if (Z[k] >> g & 1) o[g] = who[k];
    rebuild();
}

/* dirty triples at one-good sources: (i, u, s) with {b_i, c_i} = {u, y_s}, i an a-holder, u in U */
static int nd, dI[64], dU[64], dS[64];
static void dirty_triples(const int *oneg) {
    nd = 0;
    for (int s = 0; s < n; s++) if (oneg[s]) {
        int y = __builtin_ctz(bm[s]);
        for (int i = 0; i < n; i++) if (i != s && ownbits(i, bm[i]) == 4 && popc(bm[i]) == 1) {
            int u = -1;
            if (rb[i] == y) u = rc[i]; else if (rc[i] == y) u = rb[i];
            if (u >= 0 && (pool >> u & 1)) { if (nd >= 64) die("too many dirty triples"); dI[nd] = i; dU[nd] = u; dS[nd] = s; nd++; }
        }
    }
}
/* Kuhn's matching: one-good sources (left) to goods (right) along dirty triples */
static int matchS[MAXN], matchU[MAXM], vis[MAXM];
static int try_kuhn(int s) {
    for (int t = 0; t < nd; t++) {
        if (dS[t] != s) continue;
        int u = dU[t];
        if (vis[u]) continue;
        vis[u] = 1;
        if (matchU[u] < 0 || try_kuhn(matchU[u])) { matchU[u] = s; matchS[s] = u; return 1; }
    }
    return 0;
}

static int step(void) {   /* one Phase-1 step; returns its number (1..7) or 0 if none applies */
    envy_graph();
    /* 1 envied pool good */
    for (int i = 0; i < n; i++) { int L = levm(i, bm[i]);
        for (int u = 0; u < m; u++) if ((pool >> u & 1) && (Rm[i] >> u & 1) && levm(i, 1u << u) > L) {
            for (int g = 0; g < m; g++) if (o[g] == i) o[g] = -1;
            o[u] = i; rebuild(); return 1; } }
    /* 2 envy cycle: find one by DFS from each vertex */
    for (int s = 0; s < n; s++) if (reach[s][s]) {
        int cyc[MAXN], L = 0, v = s, seen = 0;
        /* walk along envy edges staying inside vertices that reach s */
        while (!(seen >> v & 1)) { seen |= 1 << v; cyc[L++] = v;
            int nx = -1; for (int w = 0; w < n; w++) if (env[v][w] && (w == s || reach[w][s])) { nx = w; break; }
            v = nx; }
        int start = 0; while (cyc[start] != v) start++;
        int K = L - start, who[MAXN]; unsigned Z[MAXN], dis = 0;
        for (int k = 0; k < K; k++) { int a = cyc[start + k], nx = cyc[start + (k + 1) % K];
            who[k] = a; Z[k] = bm[nx] & Rm[a]; dis |= 1u << a; }
        apply_takes(K, who, Z, dis); return 2;
    }
    /* 3, 4 a-holders with a bottom good in U */
    for (int i = 0; i < n; i++) if (ownbits(i, bm[i]) == 4) {
        if ((pool >> rb[i] & 1) && (pool >> rc[i] & 1)) {
            for (int g = 0; g < m; g++) if (o[g] == i) o[g] = -1;
            o[rb[i]] = i; o[rc[i]] = i; rebuild(); return 3; }
        int u = (pool >> rb[i] & 1) ? rb[i] : (pool >> rc[i] & 1) ? rc[i] : -1;
        if (u >= 0) { int envied = 0; for (int k = 0; k < n; k++) if (env[k][i]) envied = 1;
            if (!envied) { o[u] = i; rebuild(); return 4; } }
    }
    int oneg[MAXN];
    for (int s = 0; s < n; s++) oneg[s] = indeg[s] == 0 && popc(bm[s]) == 1;
    /* 5 a one-good source values a good of U */
    for (int s = 0; s < n; s++) if (oneg[s] && (pool & Rm[s])) { o[__builtin_ctz(pool & Rm[s])] = s; rebuild(); return 5; }
    for (int j = 0; j < n; j++) if (!bm[j]) return 0;      /* Phase 2 (empty bundle) */
    /* 6 dirty triple whose a-holder is reachable from its own source: champion path */
    dirty_triples(oneg);
    for (int t = 0; t < nd; t++) if (reach[dS[t]][dI[t]]) {
        int path[MAXN], L = envy_path(dS[t], dI[t], path), who[MAXN]; unsigned Z[MAXN], dis = 0;
        for (int k = 0; k + 1 < L; k++) { who[k] = path[k]; Z[k] = bm[path[k + 1]] & Rm[path[k]]; dis |= 1u << path[k]; }
        who[L - 1] = dI[t]; Z[L - 1] = (1u << dU[t]) | bm[dS[t]]; dis |= 1u << dI[t];
        apply_takes(L, who, Z, dis); return 6;
    }
    /* 7 SDR of the dirty sets -> rainbow cycle in Gamma -> augmented envy cycle */
    for (int s = 0; s < n; s++) matchS[s] = -1;
    for (int u = 0; u < m; u++) matchU[u] = -1;
    int sat = 1;
    for (int s = 0; s < n; s++) if (oneg[s]) { memset(vis, 0, sizeof vis); if (!try_kuhn(s)) sat = 0; }
    if (!sat) return 0;
    int nonempty = 0; for (int s = 0; s < n; s++) if (oneg[s]) nonempty = 1;
    if (!nonempty) die("no one-good source");
    int f[MAXN], ftrip[MAXN];
    for (int s = 0; s < n; s++) if (oneg[s]) {
        int t0 = -1; for (int t = 0; t < nd; t++) if (dS[t] == s && dU[t] == matchS[s]) { t0 = t; break; }
        if (t0 < 0) die("matched good without triple");
        int s2 = -1; for (int s1 = 0; s1 < n; s1++) if (oneg[s1] && s1 != s && reach[s1][dI[t0]]) { s2 = s1; break; }
        if (s2 < 0) die("Lemma: dirty a-holder not reachable from another one-good source");
        f[s] = s2; ftrip[s] = t0;
    }
    /* cycle of f */
    int s0 = -1; for (int s = 0; s < n; s++) if (oneg[s]) { s0 = s; break; }
    int seenf = 0, v = s0; while (!(seenf >> v & 1)) { seenf |= 1 << v; v = f[v]; }
    int fc[MAXN], K = 0; int w = v; do { fc[K++] = w; w = f[w]; } while (w != v);
    /* closed walk: s_1 ~> i_k -> s_k ~> i_{k-1} -> ... ~> i_1 -> s_1 where f(s_j) = s_{j+1} */
    int walk[4 * MAXN * MAXN], wtype[4 * MAXN * MAXN], wtrip[4 * MAXN * MAXN], WL = 0;
    int cur = fc[0];
    for (int step_ = 0; step_ < K; step_++) {
        /* go backwards around the f-cycle: s_{j+1} = cur ~> i_j -> s_j */
        /* find the source whose f is cur: that is s_j with f(s_j) = s_{j+1} = cur */
        int sjj = -1; for (int q = 0; q < K; q++) if (f[fc[q]] == cur) { sjj = fc[q]; break; }
        int t = ftrip[sjj], path[MAXN], L = envy_path(cur, dI[t], path);
        if (!L) die("no envy path");
        for (int k = 0; k + 1 < L; k++) { walk[WL] = path[k]; wtype[WL] = 0; wtrip[WL] = -1; WL++; }
        walk[WL] = dI[t]; wtype[WL] = 1; wtrip[WL] = t; WL++;       /* dirty edge i_j -> s_j */
        cur = sjj;
    }
    walk[WL] = cur; wtype[WL] = 0; wtrip[WL] = -1;
    if (cur != fc[0]) die("walk not closed");
    /* extract a simple cycle: first repeated vertex */
    int pos[MAXN]; for (int a = 0; a < n; a++) pos[a] = -1;
    int p = -1, q = -1;
    for (int k = 0; k <= WL; k++) { if (pos[walk[k]] >= 0) { p = pos[walk[k]]; q = k; break; } pos[walk[k]] = k; }
    if (p < 0) die("no repetition");
    int who[MAXN], Kc = 0; unsigned Z[MAXN], dis = 0; int hasdirty = 0;
    for (int k = p; k < q; k++) { int a = walk[k], nx = walk[k + 1];
        who[Kc] = a; dis |= 1u << a;
        if (wtype[k] == 1) { int t = wtrip[k]; if (dS[t] != nx) die("dirty edge target"); Z[Kc] = (1u << dU[t]) | bm[nx]; hasdirty = 1; }
        else { if (!env[a][nx]) die("not an envy edge"); Z[Kc] = bm[nx] & Rm[a]; }
        Kc++; }
    if (!hasdirty) die("cycle without dirty edge");
    for (int a = 0; a < Kc; a++) for (int b = a + 1; b < Kc; b++) if (Z[a] & Z[b]) die("overlapping takes");
    apply_takes(Kc, who, Z, dis);
    return 7;
}

static void phase2(void) {
    envy_graph();
    for (int j = 0; j < n; j++) if (!bm[j]) { for (int g = 0; g < m; g++) if (o[g] < 0) o[g] = j; rebuild(); cnt_step[8]++; return; }
    int oneg[MAXN]; for (int s = 0; s < n; s++) oneg[s] = indeg[s] == 0 && popc(bm[s]) == 1;
    dirty_triples(oneg);
    for (int s = 0; s < n; s++) matchS[s] = -1;
    for (int u = 0; u < m; u++) matchU[u] = -1;
    for (int s = 0; s < n; s++) if (oneg[s]) { memset(vis, 0, sizeof vis); try_kuhn(s); }
    int star = -1; for (int s = 0; s < n; s++) if (oneg[s] && matchS[s] < 0) { star = s; break; }
    if (star < 0) die("phase 2 reached with a saturating matching");
    /* T: sources reachable from star by alternating paths (dirty edge to u, then matching edge back) */
    int inT[MAXN] = {0}, qq[MAXN], h = 0, tl = 0; inT[star] = 1; qq[tl++] = star;
    unsigned DT = 0;
    while (h < tl) { int s = qq[h++];
        for (int t = 0; t < nd; t++) if (dS[t] == s) { int u = dU[t]; DT |= 1u << u;
            int s2 = matchU[u]; if (s2 < 0) die("Hall: dirty good of T unmatched");
            if (!inT[s2]) { inT[s2] = 1; qq[tl++] = s2; } } }
    for (int u = 0; u < m; u++) if (o[u] < 0) o[u] = (DT >> u & 1) ? matchU[u] : star;
    rebuild(); cnt_step[9]++;
}

static void run(void) {
    for (int g = 0; g < m; g++) o[g] = -1;
    rebuild();
    int it = 0;
    while (pool) {
        int L0 = sumlev();
        int st = step();
        if (!st) break;
        cnt_step[st]++; it++;
        if (!efx0()) die("Phase-1 step broke EFX0");
        if (sumlev() <= L0) die("Phase-1 step did not raise the sum of levels");
        for (int g = 0; g < m; g++) if (o[g] >= 0 && !(Rm[o[g]] >> g & 1)) die("junk in Phase 1");
        for (int j = 0; j < n; j++) if (popc(bm[j]) > 2) die("Phase-1 bundle with more than two goods");
    }
    if (it > max_iter) max_iter = it;
    if (pool) phase2();
    if (!raw_efx0_complete()) die("final allocation not EFX0 (raw definition) or not complete");
    { int big = 0; for (int j = 0; j < n; j++) big += popc(bm[j]) > 2;
      if (big > 1) die("two bundles with more than two goods (conjecture D shape violated)"); }
    cnt_runs++;
}

/* certificate: distinct final allocations per core */
#define MAXALLOC 200000
static unsigned long long *akey; static int nalloc;
static int **alist;
int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) if (!strcmp(argv[a], "-c")) cert = 1;
    akey = malloc(sizeof *akey * MAXALLOC); alist = malloc(sizeof *alist * MAXALLOC);
    int core_id = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        for (int i = 0; i < n; i++) for (int k = 0; k < 3; k++) if (scanf("%d", &G[i][k]) != 1) return 2;
        long long nprof = 1; for (int i = 0; i < n; i++) nprof *= 6;
        nalloc = 0;
        for (long long pc = 0; pc < nprof; pc++) {
            long long c = pc;
            for (int i = 0; i < n; i++) { int p = (int)(c % 6); c /= 6;
                ra[i] = G[i][PERM[p][0]]; rb[i] = G[i][PERM[p][1]]; rc[i] = G[i][PERM[p][2]];
                Rm[i] = (1u << ra[i]) | (1u << rb[i]) | (1u << rc[i]); }
            run();
            if (cert) {
                unsigned long long k = 0; for (int g = 0; g < m; g++) k = k * n + (unsigned long long)o[g];
                int found = 0; for (int q = 0; q < nalloc; q++) if (akey[q] == k) { found = 1; break; }
                if (!found) { if (nalloc >= MAXALLOC) { fprintf(stderr, "too many allocations\n"); return 4; }
                    akey[nalloc] = k; alist[nalloc] = malloc(sizeof(int) * m); memcpy(alist[nalloc], o, sizeof(int) * m); nalloc++; }
            }
        }
        if (cert) {
            printf("CERT {\"n\": %d, \"m\": %d, \"sets\": [", n, m);
            for (int i = 0; i < n; i++) printf("%s[%d, %d, %d]", i ? ", " : "", G[i][0], G[i][1], G[i][2]);
            printf("], \"mode\": \"LS2\", \"allocations\": [");
            for (int q = 0; q < nalloc; q++) { printf("%s[", q ? ", " : "");
                for (int g = 0; g < m; g++) printf("%s%d", g ? ", " : "", alist[q][g]);
                printf("]"); free(alist[q]); }
            printf("]}\n");
        }
        core_id++;
    }
    printf("TOTAL cores %d, runs %lld (every one ends in a complete EFX0 allocation, raw definition, with at most one "
           "bundle of more than two goods), max Phase-1 steps %lld; "
           "steps: 1=%lld 2=%lld 3=%lld 4=%lld 5=%lld 6=%lld 7=%lld; phase 2: empty-bundle=%lld matching=%lld\n",
           core_id, cnt_runs, max_iter, cnt_step[1], cnt_step[2], cnt_step[3], cnt_step[4], cnt_step[5], cnt_step[6],
           cnt_step[7], cnt_step[8], cnt_step[9]);
    return 0;
}
