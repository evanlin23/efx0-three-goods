/* First profile not covered by any allocation, in lexicographic order from `start` (used by search4.py).
   masks[(base[i] + t)*W + w]: word w of the bitset of allocations under which agent i is safe with type t.
   A profile (t_0..t_{n-1}) is covered iff the AND over i of these bitsets is nonzero.
   full[l*W + w]: allocations under which agents l..n-1 are safe with every type (a prefix set meeting it covers
   the whole subtree). Returns 1 and writes the profile to `out` if one is uncovered, else 0.
   Build: gcc -O2 -shared -fPIC -o scan.so scan.c */
#include <stdint.h>
#include <string.h>

static int N, W;
static const int *D;
static const uint64_t *M;
static const long *B;
static const uint64_t *F;
static int *S, *OUT;

static int rec(int l, const uint64_t *pre, int tight) {
    uint64_t cur[W];
    int t0 = tight ? S[l] : 0;
    for (int t = t0; t < D[l]; t++) {
        const uint64_t *m = M + (B[l] + (long)t) * W;          /* row base[l] + t, W words per row */
        int any = 0;
        for (int w = 0; w < W; w++) { cur[w] = pre[w] & m[w]; any |= cur[w] != 0; }
        OUT[l] = t;
        if (!any) { for (int k = l + 1; k < N; k++) OUT[k] = 0; return 1; }
        if (l + 1 < N) {
            int cov = 0;
            for (int w = 0; w < W && !cov; w++) cov = (cur[w] & F[(l + 1) * W + w]) != 0;
            if (cov) continue;
        }
        if (l + 1 < N && rec(l + 1, cur, tight && t == t0)) return 1;
    }
    return 0;
}

int scan(int n, const int *dom, int words, const uint64_t *masks, const long *base, int *start, int *out,
         const uint64_t *full) {
    N = n; W = words; D = dom; M = masks; B = base; S = start; OUT = out; F = full;
    uint64_t all[words];
    memset(all, 0xff, sizeof(all));
    return rec(0, all, 1);
}
