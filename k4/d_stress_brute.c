/* Brute force for k4/d_stress.md (PR #42 review, item N2): every allocation of the m goods to the n agents with at
   most one bundle of more than 2 goods, checked against the plain EFX0 definition
       v_i(X_i) >= v_i(X_j) - v_i(g)   for all agents i != j and every good g in X_j
   (a good outside R_i is worth 0 to i). Plain enumeration: no SAT, no code shared with d_stress.py or
   d_stress_check.py.
   Input (stdin), repeated until EOF: a line "n m", then n lines "k g_1 .. g_k v_1 .. v_k" (goods 0-based).
   Output, one line per instance: "total T; by owner c_0 .. c_{n-1}; none c", where c_o counts the EFX0 allocations in
   which o's bundle is the one with more than 2 goods, and "none" those in which every bundle has at most 2 goods.
   Build: cc -O2 -o d_stress_brute d_stress_brute.c */
#include <stdio.h>
#include <string.h>

#define MAXN 16
#define MAXM 40
static int n, m, val[MAXN][MAXM], A[MAXM], cnt[MAXN];
static long long byown[MAXN + 1];

static int efx0(void)
{
    for (int i = 0; i < n; i++) {
        long tot[MAXN];
        int mn[MAXN];
        for (int j = 0; j < n; j++) { tot[j] = 0; mn[j] = 1 << 30; }
        for (int g = 0; g < m; g++) {
            int j = A[g];
            tot[j] += val[i][g];
            if (val[i][g] < mn[j]) mn[j] = val[i][g];
        }
        for (int j = 0; j < n; j++)          /* worst g in X_j is its least valuable one for i */
            if (j != i && cnt[j] > 0 && tot[j] - mn[j] > tot[i]) return 0;
    }
    return 1;
}

static void rec(int g, int big)
{
    if (g == m) {
        if (efx0()) byown[big < 0 ? n : big]++;
        return;
    }
    for (int j = 0; j < n; j++) {
        if (cnt[j] == 2 && big >= 0) continue;   /* j would be a second bundle above 2 goods */
        A[g] = j;
        cnt[j]++;
        rec(g + 1, cnt[j] == 3 ? j : big);
        cnt[j]--;
    }
}

int main(void)
{
    while (scanf("%d %d", &n, &m) == 2) {
        if (n > MAXN || m > MAXM) return 2;
        memset(val, 0, sizeof val);
        for (int i = 0; i < n; i++) {
            int k, gs[MAXM];
            if (scanf("%d", &k) != 1) return 2;
            for (int t = 0; t < k; t++) if (scanf("%d", &gs[t]) != 1) return 2;
            for (int t = 0; t < k; t++) if (scanf("%d", &val[i][gs[t]]) != 1) return 2;
        }
        memset(byown, 0, sizeof byown);
        memset(cnt, 0, sizeof cnt);
        rec(0, -1);
        long long tot = 0;
        for (int o = 0; o <= n; o++) tot += byown[o];
        printf("total %lld; by owner", tot);
        for (int o = 0; o < n; o++) printf(" %lld", byown[o]);
        printf("; none %lld\n", byown[n]);
        fflush(stdout);
    }
    return 0;
}
