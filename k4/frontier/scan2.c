/* Uncovered-profile finder with subsumption (k4/frontier/search.py; replaces k4/scan.c's plain walk).
   Rows: M[(base[i] + t) * W + w] is word w of the bitset of allocations under which agent i is safe with type t.
   A profile (t_0..t_{n-1}) is covered iff the AND of its rows is nonzero. Three sound prunings:
   (1) per agent, only inclusion-minimal rows matter: if row_t contains row_u, every profile using t is covered
       as soon as the same profile with u is (the AND with row_t contains the AND with row_u);
   (2) F[l]: allocations safe for agents order[l..] with every type; a prefix set meeting it covers its subtree;
   (3) a store of prefix sets proved covered at each level: a later prefix set containing one is covered. Rows only
       gain bits as allocations are added, so the store stays valid across calls (ctx keeps it).
   Returns 1 and writes an uncovered profile (indexed by agent) to `out`, or 0 if every profile is covered.
   Build: gcc -O2 -shared -fPIC -o scan2.so scan2.c */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 12
typedef struct { int cap, len, w; uint64_t *data; int *pop; int *wd; } store_t;
typedef struct { int n; store_t st[MAXN + 1]; long nodes; } ctx_t;

static int N, W, ORD[MAXN];
static const uint64_t *M, *F;
static const long *B;
static int *A[MAXN], NA[MAXN];               /* antichain of minimal rows per level (type indices) */
static int *OUT;
static ctx_t *C;
static uint64_t *CH[MAXN];                    /* children buffers per level */
static int *CP[MAXN], *CI[MAXN];

void *ctx_new(int n, int cap) {
    ctx_t *c = calloc(1, sizeof(ctx_t)); c->n = n;
    for (int l = 0; l <= n; l++) { c->st[l].cap = cap; }
    return c;
}
void ctx_free(void *p) {
    ctx_t *c = p; for (int l = 0; l <= c->n; l++) { free(c->st[l].data); free(c->st[l].pop); free(c->st[l].wd); } free(c);
}
long ctx_nodes(void *p) { return ((ctx_t *)p)->nodes; }

static inline int popc(const uint64_t *x, int w) { int s = 0; for (int i = 0; i < w; i++) s += __builtin_popcountll(x[i]); return s; }
static inline int meets(const uint64_t *a, const uint64_t *b) { for (int w = 0; w < W; w++) if (a[w] & b[w]) return 1; return 0; }
static inline const uint64_t *row(int l, int t) { return M + (B[ORD[l]] + (long)t) * W; }

static int dominated(int l, const uint64_t *cur, int pc) {
    store_t *s = &C->st[l];
    for (int k = 0; k < s->len; k++) {
        if (s->pop[k] > pc) continue;
        const uint64_t *x = s->data + (long)k * s->w;
        int ok = 1, wd = s->wd[k];
        for (int w = 0; w < wd && ok; w++) if (x[w] & ~cur[w]) ok = 0;
        if (ok) return 1;
    }
    return 0;
}
static void insert(int l, const uint64_t *cur, int pc) {
    store_t *s = &C->st[l];
    if (s->cap <= 0) return;
    if (s->w < W) {                           /* widen every entry (zero-extend) */
        uint64_t *nd = calloc((size_t)s->cap * W, 8);
        for (int k = 0; k < s->len; k++) memcpy(nd + (long)k * W, s->data + (long)k * s->w, 8 * s->w);
        free(s->data); s->data = nd; s->w = W;
        if (!s->pop) { s->pop = calloc(s->cap, sizeof(int)); s->wd = calloc(s->cap, sizeof(int)); }
    }
    int k;
    if (s->len < s->cap) k = s->len++;
    else { k = 0; for (int j = 1; j < s->len; j++) if (s->pop[j] > s->pop[k]) k = j; if (s->pop[k] <= pc) return; }
    memcpy(s->data + (long)k * s->w, cur, 8 * W); s->pop[k] = pc; s->wd[k] = W;
}

static void fill_rest(int l) { for (int k = l; k < N; k++) OUT[ORD[k]] = A[k][0]; }

static int rec(int l, const uint64_t *cur) {
    C->nodes++;
    if (meets(cur, F + (long)l * W)) return 0;
    int pc = popc(cur, W);
    if (l > 0 && dominated(l, cur, pc)) return 0;
    if (l == N - 1) {
        for (int k = 0; k < NA[l]; k++) if (!meets(cur, row(l, A[l][k]))) { OUT[ORD[l]] = A[l][k]; return 1; }
        return 0;
    }
    uint64_t *ch = CH[l]; int *cp = CP[l], *ci = CI[l];
    for (int k = 0; k < NA[l]; k++) {
        const uint64_t *r = row(l, A[l][k]); uint64_t *x = ch + (long)k * W; int any = 0;
        for (int w = 0; w < W; w++) { x[w] = cur[w] & r[w]; any |= x[w] != 0; }
        if (!any) { OUT[ORD[l]] = A[l][k]; fill_rest(l + 1); return 1; }
        cp[k] = popc(x, W); ci[k] = k;
    }
    for (int a = 1; a < NA[l]; a++) {         /* smallest children first (insertion sort by popcount) */
        int v = ci[a], b = a - 1;
        while (b >= 0 && cp[ci[b]] > cp[v]) { ci[b + 1] = ci[b]; b--; }
        ci[b + 1] = v;
    }
    for (int a = 0; a < NA[l]; a++) {
        int k = ci[a];
        if (rec(l + 1, ch + (long)k * W)) { OUT[ORD[l]] = A[l][k]; return 1; }
    }
    insert(l, cur, pc);
    return 0;
}

/* order[l]: agent at level l; F[l*W..]: allocations safe for agents order[l..n-1] with every type (F[n] = all). */
int find(void *ctx, int n, const int *order, const int *dom, int words, const uint64_t *masks, const long *base,
         const uint64_t *full, int *out) {
    N = n; W = words; M = masks; B = base; F = full; OUT = out; C = ctx;
    for (int l = 0; l < n; l++) ORD[l] = order[l];
    int ret = 0;
    for (int l = 0; l < n; l++) {             /* minimal rows; a zero row is an uncovered profile at once */
        int i = ORD[l], D = dom[i];
        A[l] = malloc(sizeof(int) * D); NA[l] = 0;
        int *pc = malloc(sizeof(int) * D);
        for (int t = 0; t < D; t++) pc[t] = popc(M + (B[i] + (long)t) * W, W);
        for (int t = 0; t < D && !ret; t++) {
            const uint64_t *r = M + (B[i] + (long)t) * W;
            if (pc[t] == 0) { ret = 1; for (int k = 0; k < n; k++) out[k] = 0; out[i] = t; break; }
            int dom_ = 0;
            for (int u = 0; u < D && !dom_; u++) {
                if (u == t || pc[u] > pc[t] || (pc[u] == pc[t] && u > t)) continue;   /* u strictly smaller, or equal and earlier */
                const uint64_t *q = M + (B[i] + (long)u) * W; int sub = 1;
                for (int w = 0; w < W && sub; w++) if (q[w] & ~r[w]) sub = 0;
                dom_ = sub;
            }
            if (!dom_) A[l][NA[l]++] = t;
        }
        free(pc);
    }
    if (!ret) {
        for (int l = 0; l < n; l++) { CH[l] = malloc(8L * NA[l] * W); CP[l] = malloc(sizeof(int) * NA[l]); CI[l] = malloc(sizeof(int) * NA[l]); }
        uint64_t *all = malloc(8L * W); memset(all, 0xff, 8L * W);
        ret = rec(0, all);
        free(all);
        for (int l = 0; l < n; l++) { free(CH[l]); free(CP[l]); free(CI[l]); }
    }
    for (int l = 0; l < n; l++) free(A[l]);
    return ret;
}

/* Sizes of the minimal-row antichains (for diagnostics), written to na[agent]. */
void antichain_sizes(int n, const int *dom, int words, const uint64_t *masks, const long *base, int *na) {
    for (int i = 0; i < n; i++) {
        int D = dom[i], c = 0;
        for (int t = 0; t < D; t++) {
            const uint64_t *r = masks + (base[i] + (long)t) * words; int d = 0;
            for (int u = 0; u < D && !d; u++) {
                if (u == t) continue;
                const uint64_t *q = masks + (base[i] + (long)u) * words; int sub = 1, eq = 1;
                for (int w = 0; w < words && sub; w++) { if (q[w] & ~r[w]) sub = 0; if (q[w] != r[w]) eq = 0; }
                d = sub && (!eq || u < t);
            }
            c += !d;
        }
        na[i] = c;
    }
}
