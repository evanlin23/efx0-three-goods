/* Backtracking search for a complete EFX0 allocation, for monotone valuations given on subsets of each
 * agent's relevant set (monotone/synth.py uses it through ctypes as the inner step of CEGAR; a returned
 * allocation is re-checked in Python with the raw definition before it is used).
 *
 * Inputs: n agents, m goods; pos[i*m + g] = index of good g in R_i, or -1 if g is not relevant to i;
 * off[i] = offset of agent i's table in vals, which has 2^|R_i| entries indexed by local bitmask;
 * order[0..m-1] = order in which goods are assigned. Output: owner[g]. Returns 1 if found, 0 if none.
 *
 * Pruning: agent i's value can only grow up to v_i(X_i + all unassigned goods); the threat
 * max_{g in X_j} v_i(X_j - g) only grows as X_j grows. A threat above that bound is final.
 */
#include <string.h>

#define MAXN 8
#define MAXM 24

static int N, M;
static const int *POS, *OFF, *VALS, *ORD;
static int L[MAXN][MAXN];      /* L[i][j] = local_i(X_j) */
static int OUTC[MAXN][MAXN];   /* number of goods of X_j outside R_i */
static int SZ[MAXN];           /* |X_j| */
static int U[MAXN];            /* local_i(unassigned goods) */
static int *OWN;

static inline int val(int i, int mask) { return VALS[OFF[i] + mask]; }

static inline int threat(int i, int j) {
    if (SZ[j] <= 1) return 0;
    int lm = L[i][j];
    if (OUTC[i][j] > 0) return val(i, lm);
    int best = 0, x = lm;
    while (x) {
        int b = x & (-x);
        int v = val(i, lm ^ b);
        if (v > best) best = v;
        x ^= b;
    }
    return best;
}

static int feasible(int final) {
    for (int i = 0; i < N; i++) {
        int bound = final ? val(i, L[i][i]) : val(i, L[i][i] | U[i]);
        for (int j = 0; j < N; j++) {
            if (j == i) continue;
            if (threat(i, j) > bound) return 0;
        }
    }
    return 1;
}

static int rec(int k) {
    if (k == M) return feasible(1);
    int g = ORD[k];
    for (int j = 0; j < N; j++) {
        for (int i = 0; i < N; i++) {
            int p = POS[i * M + g];
            if (p >= 0) { L[i][j] |= (1 << p); U[i] &= ~(1 << p); }
            else OUTC[i][j]++;
        }
        SZ[j]++;
        OWN[g] = j;
        if (feasible(0) && rec(k + 1)) return 1;
        SZ[j]--;
        for (int i = 0; i < N; i++) {
            int p = POS[i * M + g];
            if (p >= 0) { L[i][j] &= ~(1 << p); U[i] |= (1 << p); }
            else OUTC[i][j]--;
        }
    }
    return 0;
}

int find_efx0(int n, int m, const int *pos, const int *off, const int *vals, const int *order, int *owner) {
    if (n > MAXN || m > MAXM) return -1;
    N = n; M = m; POS = pos; OFF = off; VALS = vals; ORD = order; OWN = owner;
    memset(L, 0, sizeof L); memset(OUTC, 0, sizeof OUTC); memset(SZ, 0, sizeof SZ);
    for (int i = 0; i < n; i++) {
        U[i] = 0;
        for (int g = 0; g < m; g++) if (pos[i * m + g] >= 0) U[i] |= 1 << pos[i * m + g];
    }
    return rec(0);
}
