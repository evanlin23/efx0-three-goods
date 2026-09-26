/* Plain brute force for Output(s, o, X) (lean/EFX/LB4R.lean Output, PreAllocK Completion/OC/ownerNeeds).
 * Independent of the SAT encoding: recomputes needsOf, NA, Frozen, omega from the raw state and enumerates
 * every assignment of the junk goods, with only two restrictions read directly off Completion:
 *   (a) a non-owner j receives at most max(0, 2 - |B_j|) junk goods (Completion.free / Completion.frozen);
 *   (b) a non-owner j whose one-good base is needed by some agent other than o receives none (it is Frozen
 *       under the owner's needs whatever X is, since those agents' needs are unchanged).
 * Every leaf is checked against the full definition (both restrictions are re-checked there).
 * stdin: n m / n rows of m values / m base entries (-1 junk) / n picks / n marked / o (-1 none) conv (1 bundle, 0 base)
 * stdout: "SAT <X...>" or "UNSAT", then the number of leaves checked.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int n, m, v[64][64], base[64], pick_[64], marked[64], o, conv;
static uint64_t needs[64], B[64];
static int nB[64], J[64], nJ, cap[64], X[64], used[64];
static long long leaves;
static long long omega_;

static int popc(uint64_t x) { return __builtin_popcountll(x); }
static int val(int i, uint64_t S) { int s = 0; for (int g = 0; g < m; g++) if (S >> g & 1) s += v[i][g]; return s; }

static int check(void) {
  uint64_t bund[64] = {0};
  for (int g = 0; g < m; g++) bund[X[g]] |= 1ULL << g;
  uint64_t N2[64];
  for (int i = 0; i < n; i++) N2[i] = needs[i];
  if (o >= 0 && conv == 1) {
    int vo = val(o, bund[o]);
    N2[o] = 0;
    for (int g = 0; g < m; g++) if (X[g] != o && vo < v[o][g]) N2[o] |= 1ULL << g;
  }
  uint64_t NA = 0;
  for (int i = 0; i < n; i++) NA |= N2[i];
  int fr[64];
  for (int i = 0; i < n; i++) fr[i] = (nB[i] == 1) && (B[i] & NA);
  if (o >= 0 && fr[o]) return 0;
  for (int j = 0; j < n; j++) {
    if (j == o) continue;
    int cj = popc(bund[j] & ~B[j]);
    if (fr[j] && cj) return 0;
    if (!fr[j] && cj + nB[j] > 2) return 0;
  }
  if (o >= 0) {
    for (int j = 0; j < n; j++) {
      if (j == o) continue;
      int vj = val(j, bund[j]), vo = val(j, bund[o]);
      for (int h = 0; h < m; h++) if (bund[o] >> h & 1) if (vo - v[j][h] > vj) return 0;
    }
  }
  int allsmall = 1;
  for (int i = 0; i < n; i++) if (nB[i] > 2) allsmall = 0;
  if (allsmall && ((o < 0) != (omega_ <= 0))) return 0;
  return 1;
}

static int dfs(int k) {
  if (k == nJ) { leaves++; return check(); }
  int g = J[k];
  for (int a = 0; a < n; a++) {
    if (a != o) { if (used[a] >= cap[a]) continue; used[a]++; }
    X[g] = a;
    if (dfs(k + 1)) return 1;
    if (a != o) used[a]--;
  }
  return 0;
}

int main(void) {
  if (scanf("%d %d", &n, &m) != 2) return 2;
  for (int i = 0; i < n; i++) for (int g = 0; g < m; g++) scanf("%d", &v[i][g]);
  for (int g = 0; g < m; g++) scanf("%d", &base[g]);
  for (int i = 0; i < n; i++) scanf("%d", &pick_[i]);
  for (int i = 0; i < n; i++) scanf("%d", &marked[i]);
  scanf("%d %d", &o, &conv);
  for (int i = 0; i < n; i++) { B[i] = 0; nB[i] = 0; }
  nJ = 0;
  for (int g = 0; g < m; g++) { if (base[g] >= 0) { B[base[g]] |= 1ULL << g; nB[base[g]]++; X[g] = base[g]; } else J[nJ++] = g; }
  /* needsOf */
  for (int i = 0; i < n; i++) {
    needs[i] = 0;
    if (marked[i]) { int vb = val(i, B[i]); for (int g = 0; g < m; g++) if (!(B[i] >> g & 1) && vb < v[i][g]) needs[i] |= 1ULL << g; }
    else if (pick_[i] < 0) { for (int g = 0; g < m; g++) if (v[i][g] > 0) needs[i] |= 1ULL << g; }
    else { for (int g = 0; g < m; g++) if (v[i][g] > 0 && v[i][pick_[i]] < v[i][g]) needs[i] |= 1ULL << g; }
  }
  uint64_t NA = 0; for (int i = 0; i < n; i++) NA |= needs[i];
  long long capsum = 0;
  for (int i = 0; i < n; i++) { int f = (nB[i] == 1) && (B[i] & NA); capsum += f ? 0 : 2 - nB[i]; }
  omega_ = nJ - capsum;
  for (int j = 0; j < n; j++) {
    cap[j] = 2 - nB[j]; if (cap[j] < 0) cap[j] = 0;
    if (nB[j] == 1) { uint64_t oth = 0; for (int i = 0; i < n; i++) if (i != o) oth |= needs[i]; if (B[j] & oth) cap[j] = 0; }
    used[j] = 0;
  }
  int r = dfs(0);
  if (r) { printf("SAT"); for (int g = 0; g < m; g++) printf(" %d", X[g]); printf("\n"); } else printf("UNSAT\n");
  printf("%lld\n", leaves);
  return 0;
}
