/* Independent check of a claimed failure (no SAT, no order types, no code shared with the search): does the instance
   have an EFX₀ allocation (--any) or one with at most one bundle of more than 2 goods (default, D2)?
   Input (stdin), one instance per line, as in tester.py's pipe protocol: "n m" then per agent "d g_1..g_d v_1..v_d"
   (integer values; v_i = 0 on goods outside R_i). Enumerates owner assignments good by good (depth-first) and
   checks the raw definition v_i(X_i) >= v_i(X_j) - v_i(h) for all i != j, h in X_j on every complete assignment.
   Pruning (sound): with D2, stop when two bundles already have more than 2 goods; for EFX₀, stop when some agent's
   bundle plus all its unassigned relevant goods is worth less than v_i(X_j) - v_i(h) for an assigned h in X_j
   (goods only add value, and X_j minus h only grows). Prints per line: "EXISTS <owners>" or "NONE (<count> leaves)".
   Build: gcc -O2 -o verify_fail verify_fail.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MN 16
#define MM 48
static int n, m, anyshape, v[MN][MM], own[MM], cnt[MN], found;
static long leaves;
static int ok_full(void) {
    for (int i = 0; i < n; i++) {
        int mine = 0; for (int g = 0; g < m; g++) if (own[g] == i) mine += v[i][g];
        for (int j = 0; j < n; j++) if (j != i) {
            int tot = 0; for (int g = 0; g < m; g++) if (own[g] == j) tot += v[i][g];
            for (int h = 0; h < m; h++) if (own[h] == j && mine < tot - v[i][h]) return 0;
        }
    }
    return 1;
}
static int hopeless(int upto) {                 /* goods 0..upto-1 assigned */
    for (int i = 0; i < n; i++) {
        int best = 0; for (int g = 0; g < m; g++) if (g >= upto || own[g] == i) best += (g >= upto || own[g] == i) ? v[i][g] : 0;
        for (int j = 0; j < n; j++) if (j != i) {
            int tot = 0, mn = 1 << 30, any = 0;
            for (int g = 0; g < upto; g++) if (own[g] == j) { tot += v[i][g]; if (v[i][g] < mn) mn = v[i][g]; any = 1; }
            if (any && best < tot - mn) return 1;
        }
    }
    return 0;
}
static void rec(int g) {
    if (found) return;
    if (g == m) { leaves++; if (ok_full()) found = 1; return; }
    for (int j = 0; j < n && !found; j++) {
        own[g] = j; cnt[j]++;
        int big = 0; for (int k = 0; k < n; k++) big += cnt[k] > 2;
        if ((anyshape || big <= 1) && !hopeless(g + 1)) rec(g + 1);
        cnt[j]--;
        if (!found) own[g] = -1;
    }
}
int main(int argc, char **argv) {
    anyshape = argc > 1 && !strcmp(argv[1], "--any");
    while (scanf("%d %d", &n, &m) == 2) {
        memset(v, 0, sizeof v);
        for (int i = 0; i < n; i++) {
            int d, gs[8]; if (scanf("%d", &d) != 1 || d > 8) return 2;
            for (int k = 0; k < d; k++) if (scanf("%d", &gs[k]) != 1) return 2;
            for (int k = 0; k < d; k++) if (scanf("%d", &v[i][gs[k]]) != 1) return 2;
        }
        for (int g = 0; g < m; g++) own[g] = -1;
        memset(cnt, 0, sizeof cnt); found = 0; leaves = 0;
        rec(0);
        if (found) { printf("EXISTS"); for (int g = 0; g < m; g++) printf(" %d", own[g]); printf("\n"); }
        else printf("NONE (%ld leaves, %s)\n", leaves, anyshape ? "any shape" : "D2");
        fflush(stdout);
    }
    return 0;
}
