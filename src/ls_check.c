/* Local search for EFX0 in cores: exhaustive "no stuck state" check (workstream proof/local-search).
   See proofs/local_search.md and src/local_search.py (driver, core enumeration, second implementation).

   Model (ordinal; proofs/local_search.md, Lemma 1): a partial allocation gives each good an owner or leaves it in
   the pool. Agent i with ranking a > b > c is safe iff, with "free" meaning "in the pool or alone in its bundle":
     holds >= 2 of its goods; or holds exactly a (of its goods) and b, c are not together in a bundle of >= 3 goods;
     or holds exactly b and a is free; or holds exactly c and a, b are free; or holds none and a, b, c are free.
   Level of i: index of v_i(own goods held) in the chain 0 < c < b < a < b+c < a+c < a+b < a+b+c.
   Potential: (sum of levels, number of allocated goods), lexicographic. Every move must raise it.

   Input on stdin: lines "n m g00 g01 g02 g10 ... " (one core per line, agent i values g_i0, g_i1, g_i2).
   For each core, every ranking profile (6^n) and every partial allocation ((n+1)^m) is examined, or only those
   reachable from the empty allocation (-r). Output: per core, counts, and every stuck state (up to a limit).
   Usage: ls_check [-r] [-m MOVES] [-v]
     MOVES: letters from "ESRAUCK" (default "ESRAUC"): E fill an empty bundle, S swap for an envied pool good,
       R envy-cycle rotation, A add a pool good to a bundle, U single-agent rebundle (pool + own bundle + goods
       worthless to their holders), C champion along an envy path (Z from the start bundle and the pool),
       K like C but Z may also take goods worthless to their holders. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 7
#define MAXM 14
static int n, m;
static int G[MAXN][3];                  /* agent's goods (unordered, as in the core) */
static int bitv[MAXN][MAXM];            /* bit of good g for agent i under the current profile: a=4 b=2 c=1 */
static int ra[MAXN], rb[MAXN], rc[MAXN];
static const int IDX[8] = {0, 1, 2, 4, 3, 5, 6, 7};  /* bits (a=4,b=2,c=1) -> chain index */
static const int PERM[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static char moves_on[16] = "ESRAUC";
static int use[128];
static long long cnt_move[128], cnt_hard, cnt_states, cnt_stuck;
static int verbose = 0, reach_only = 0;
static long long stuck_print_limit = 20;

typedef struct { int o[MAXM]; } State;

static inline int popc(unsigned x) { return __builtin_popcount(x); }

static void masks(const State *s, unsigned *bm, unsigned *pool) {
    for (int j = 0; j < n; j++) bm[j] = 0;
    *pool = 0;
    for (int g = 0; g < m; g++) { if (s->o[g] < 0) *pool |= 1u << g; else bm[s->o[g]] |= 1u << g; }
}
static inline int levm(int i, unsigned mask) {
    int b = 0;
    if (mask >> ra[i] & 1) b |= 4;
    if (mask >> rb[i] & 1) b |= 2;
    if (mask >> rc[i] & 1) b |= 1;
    return IDX[b];
}
static inline int ownbits(int i, unsigned mask) {
    return ((mask >> ra[i] & 1) << 2) | ((mask >> rb[i] & 1) << 1) | (mask >> rc[i] & 1);
}
static int safe_i(const State *s, const unsigned *bm, int i) {
    int b = ownbits(i, bm[i]);
    if (popc(b) >= 2) return 1;
#define FREE(g) (s->o[g] < 0 || popc(bm[s->o[g]]) == 1)
    if (b == 4) { int x = s->o[rb[i]], y = s->o[rc[i]]; return !(x >= 0 && x == y && popc(bm[x]) >= 3); }
    if (b == 2) return FREE(ra[i]);
    if (b == 1) return FREE(ra[i]) && FREE(rb[i]);
    return FREE(ra[i]) && FREE(rb[i]) && FREE(rc[i]);
#undef FREE
}
static int efx0(const State *s) {
    unsigned bm[MAXN], pool; masks(s, bm, &pool);
    for (int i = 0; i < n; i++) if (!safe_i(s, bm, i)) return 0;
    return 1;
}
static void potential(const State *s, int *lev, int *alloc) {
    unsigned bm[MAXN], pool; masks(s, bm, &pool);
    int L = 0; for (int i = 0; i < n; i++) L += levm(i, bm[i]);
    *lev = L; *alloc = m - popc(pool);
}
static int better(const State *a, const State *b) { /* potential(a) > potential(b) */
    int la, aa, lb, ab; potential(a, &la, &aa); potential(b, &lb, &ab);
    return la > lb || (la == lb && aa > ab);
}
/* envy: v_i(X_j) > v_i(X_i) */
static void envy(const unsigned *bm, int adj[MAXN][MAXN]) {
    for (int i = 0; i < n; i++) { int L = levm(i, bm[i]);
        for (int j = 0; j < n; j++) adj[i][j] = (i != j) && levm(i, bm[j]) > L; }
}

/* successor collection: in check mode we only need existence; in reach mode we collect all */
#define MAXSUCC 4096
static State succ[MAXSUCC]; static int nsucc; static int collect_all;
static int push(const State *t, const State *from) {
    if (!better(t, from) || !efx0(t)) return 0;
    if (nsucc < MAXSUCC) succ[nsucc++] = *t;
    return 1;
}

static int path[MAXN], plen;
static int try_C_path(const State *s, const unsigned *bm, unsigned pool, int withjunk, unsigned junk) {
    /* path[0] = j (start, bundle dissolved) -> ... -> path[plen-1] = k (champion) */
    int j = path[0], k = path[plen - 1];
    unsigned avail = bm[j] | pool | (withjunk ? (junk & ~bm[k]) : 0);
    int Lk = levm(k, bm[k]); int found = 0;
    /* Z ranges over subsets of avail; only its goods in R_k matter for the level, but we allow any subset */
    for (unsigned Z = avail;; Z = (Z - 1) & avail) {
        if (Z && levm(k, Z) > Lk) {
            State t = *s;
            for (int g = 0; g < m; g++) if (bm[j] >> g & 1) t.o[g] = -1;
            for (int q = 0; q + 1 < plen; q++)
                for (int g = 0; g < m; g++) if (bm[path[q + 1]] >> g & 1) t.o[g] = path[q];
            for (int g = 0; g < m; g++) if (Z >> g & 1) t.o[g] = k;
            if (push(&t, s)) { found = 1; if (!collect_all) return 1; }
        }
        if (Z == 0) break;
    }
    return found;
}
static int dfs_C(const State *s, const unsigned *bm, unsigned pool, int adj[MAXN][MAXN], int used, int withjunk,
                 unsigned junk) {
    int found = 0;
    if (plen >= 2) { if (try_C_path(s, bm, pool, withjunk, junk)) { found = 1; if (!collect_all) return 1; } }
    int v = path[plen - 1];
    for (int w = 0; w < n; w++) if (adj[v][w] && !(used >> w & 1)) {
        path[plen++] = w;
        int f = dfs_C(s, bm, pool, adj, used | 1 << w, withjunk, junk);
        plen--;
        if (f) { found = 1; if (!collect_all) return 1; }
    }
    return found;
}
static int cyc[MAXN], clen;
static int dfs_R(const State *s, const unsigned *bm, int adj[MAXN][MAXN], int used) {
    int v = cyc[clen - 1], found = 0;
    for (int w = 0; w < n; w++) if (adj[v][w]) {
        if (w == cyc[0] && clen >= 2) {
            State t = *s;
            for (int q = 0; q < clen; q++) { int nx = cyc[(q + 1) % clen];
                for (int g = 0; g < m; g++) if (bm[nx] >> g & 1) t.o[g] = cyc[q]; }
            if (push(&t, s)) { found = 1; if (!collect_all) return 1; }
        } else if (w > cyc[0] && !(used >> w & 1)) {
            cyc[clen++] = w; int f = dfs_R(s, bm, adj, used | 1 << w); clen--;
            if (f) { found = 1; if (!collect_all) return 1; }
        }
    }
    return found;
}

/* returns the letter of the first move type that applies, or 0 if stuck; with collect_all, fills succ[] */
static int find_moves(const State *s) {
    unsigned bm[MAXN], pool; masks(s, bm, &pool);
    int first = 0; nsucc = 0;
    if (!pool) return 0;
    if (use['E']) for (int j = 0; j < n; j++) if (!bm[j])
        for (int g = 0; g < m; g++) if (pool >> g & 1) {
            State t = *s; t.o[g] = j; if (push(&t, s)) { if (!first) first = 'E'; if (!collect_all) return first; } }
    if (use['S']) for (int i = 0; i < n; i++) { int L = levm(i, bm[i]);
        for (int g = 0; g < m; g++) if ((pool >> g & 1) && bitv[i][g] && levm(i, 1u << g) > L) {
            State t = *s;
            for (int h = 0; h < m; h++) if (bm[i] >> h & 1) t.o[h] = -1;
            t.o[g] = i; if (push(&t, s)) { if (!first) first = 'S'; if (!collect_all) return first; } } }
    int adj[MAXN][MAXN]; envy(bm, adj);
    if (use['R']) for (int v = 0; v < n; v++) { cyc[0] = v; clen = 1;
        if (dfs_R(s, bm, adj, 1 << v)) { if (!first) first = 'R'; if (!collect_all) return first; } }
    if (use['A']) for (int g = 0; g < m; g++) if (pool >> g & 1) for (int j = 0; j < n; j++) if (bm[j]) {
        State t = *s; t.o[g] = j; if (push(&t, s)) { if (!first) first = 'A'; if (!collect_all) return first; } }
    unsigned junk = 0;
    for (int g = 0; g < m; g++) if (s->o[g] >= 0 && !bitv[s->o[g]][g]) junk |= 1u << g;
    if (use['U']) for (int i = 0; i < n; i++) {
        unsigned avail = bm[i] | pool | (junk & ~bm[i]);
        for (unsigned Y = avail;; Y = (Y - 1) & avail) {
            State t = *s;
            for (int g = 0; g < m; g++) if (bm[i] >> g & 1) t.o[g] = -1;
            for (int g = 0; g < m; g++) if (Y >> g & 1) t.o[g] = i;
            if (memcmp(&t, s, sizeof t) && push(&t, s)) { if (!first) first = 'U'; if (!collect_all) return first; }
            if (Y == 0) break;
        }
    }
    if (use['C']) for (int v = 0; v < n; v++) { path[0] = v; plen = 1;
        if (dfs_C(s, bm, pool, adj, 1 << v, 0, junk)) { if (!first) first = 'C'; if (!collect_all) return first; } }
    if (use['K']) for (int v = 0; v < n; v++) { path[0] = v; plen = 1;
        if (dfs_C(s, bm, pool, adj, 1 << v, 1, junk)) { if (!first) first = 'K'; if (!collect_all) return first; } }
    return first;
}

static void print_state(const State *s) {
    unsigned bm[MAXN], pool; masks(s, bm, &pool);
    printf("   rankings(a,b,c):");
    for (int i = 0; i < n; i++) printf(" (%d,%d,%d)", ra[i], rb[i], rc[i]);
    printf("\n   bundles:");
    for (int j = 0; j < n; j++) { printf(" {"); int f = 1;
        for (int g = 0; g < m; g++) if (bm[j] >> g & 1) { printf(f ? "%d" : ",%d", g); f = 0; } printf("}"); }
    printf("  pool {"); int f = 1;
    for (int g = 0; g < m; g++) if (pool >> g & 1) { printf(f ? "%d" : ",%d", g); f = 0; }
    printf("}\n");
}

/* reach-only exploration: hash set of visited states */
#define HBITS 24
static unsigned long long *htab; static size_t hsize;
static unsigned long long enc(const State *s) { unsigned long long k = 0;
    for (int g = 0; g < m; g++) k = k * (n + 1) + (unsigned long long)(s->o[g] + 1); return k + 1; }
static int hins(unsigned long long k) {
    size_t h = (k * 0x9E3779B97F4A7C15ULL) >> (64 - HBITS);
    while (htab[h]) { if (htab[h] == k) return 0; h = (h + 1) & (hsize - 1); }
    htab[h] = k; return 1;
}
static void dec(unsigned long long k, State *s) { k -= 1;
    for (int g = m - 1; g >= 0; g--) { s->o[g] = (int)(k % (n + 1)) - 1; k /= n + 1; } }

static long long run_profile(void) {
    long long stuck = 0;
    if (!reach_only) {
        State s; long long total = 1; for (int g = 0; g < m; g++) total *= n + 1;
        for (long long code = 0; code < total; code++) {
            long long c = code; int haspool = 0;
            for (int g = 0; g < m; g++) { s.o[g] = (int)(c % (n + 1)) - 1; c /= n + 1; if (s.o[g] < 0) haspool = 1; }
            if (!haspool || !efx0(&s)) continue;
            cnt_states++;
            collect_all = 0;
            int f = find_moves(&s);
            if (f) { cnt_move[f]++; if (f != 'E' && f != 'S' && f != 'A') cnt_hard++; }
            else { stuck++; if (cnt_stuck + stuck <= stuck_print_limit) { printf("  STUCK\n"); print_state(&s); } }
        }
        return stuck;
    }
    /* reachable closure from the empty allocation */
    memset(htab, 0, hsize * sizeof *htab);
    static State stack[1 << 20]; int sp = 0;
    State s0; for (int g = 0; g < m; g++) s0.o[g] = -1;
    hins(enc(&s0)); stack[sp++] = s0;
    while (sp) {
        State s = stack[--sp]; cnt_states++;
        collect_all = 1;
        int f = find_moves(&s);
        int haspool = 0; for (int g = 0; g < m; g++) if (s.o[g] < 0) haspool = 1;
        if (!haspool) continue;
        if (!f) { stuck++; if (cnt_stuck + stuck <= stuck_print_limit) { printf("  STUCK (reachable)\n"); print_state(&s); } continue; }
        cnt_move[f]++;
        int ns = nsucc; State loc[MAXSUCC]; memcpy(loc, succ, ns * sizeof(State));
        for (int q = 0; q < ns; q++) if (hins(enc(&loc[q]))) {
            if (sp >= (1 << 20)) { fprintf(stderr, "stack overflow\n"); exit(1); }
            stack[sp++] = loc[q];
        }
    }
    return stuck;
}

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-r")) reach_only = 1;
        else if (!strcmp(argv[a], "-v")) verbose = 1;
        else if (!strcmp(argv[a], "-m") && a + 1 < argc) { strncpy(moves_on, argv[++a], 15); }
        else if (!strcmp(argv[a], "-l") && a + 1 < argc) stuck_print_limit = atoll(argv[++a]);
    }
    for (const char *p = moves_on; *p; p++) use[(int)*p] = 1;
    hsize = (size_t)1 << HBITS; htab = calloc(hsize, sizeof *htab);
    int core_id = 0; long long grand_stuck = 0;
    while (scanf("%d %d", &n, &m) == 2) {
        for (int i = 0; i < n; i++) for (int k = 0; k < 3; k++) scanf("%d", &G[i][k]);
        long long nprof = 1; for (int i = 0; i < n; i++) nprof *= 6;
        long long stuck_core = 0, stuck_profiles = 0;
        for (long long pc = 0; pc < nprof; pc++) {
            long long c = pc;
            for (int i = 0; i < n; i++) { int p = (int)(c % 6); c /= 6;
                ra[i] = G[i][PERM[p][0]]; rb[i] = G[i][PERM[p][1]]; rc[i] = G[i][PERM[p][2]];
                for (int g = 0; g < m; g++) bitv[i][g] = 0;
                bitv[i][ra[i]] = 4; bitv[i][rb[i]] = 2; bitv[i][rc[i]] = 1; }
            long long st = run_profile();
            if (st) { stuck_profiles++; stuck_core += st; cnt_stuck += st; }
        }
        printf("core %d n=%d m=%d goods", core_id, n, m);
        for (int i = 0; i < n; i++) printf(" (%d,%d,%d)", G[i][0], G[i][1], G[i][2]);
        printf(": stuck states %lld in %lld profiles\n", stuck_core, stuck_profiles);
        fflush(stdout);
        grand_stuck += stuck_core; core_id++;
    }
    printf("TOTAL cores %d, %s states examined %lld, stuck %lld; first applicable move:", core_id,
           reach_only ? "reachable" : "partial EFX0 (pool nonempty)", cnt_states, grand_stuck);
    for (const char *p = "ESRAUCK"; *p; p++) if (use[(int)*p]) printf(" %c=%lld", *p, cnt_move[(int)*p]);
    printf("\n");
    return grand_stuck ? 1 : 0;
}
