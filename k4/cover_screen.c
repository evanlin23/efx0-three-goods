/* k4/cover_screen.c -- the profiles with a non-completable key, at any f (workstream compute/k4-cover). EVIDENCE tooling.

   A screen for k4/cover_check.py: it finds the strict profiles that have a key κ with def*(κ) > 0, which by Lemma 0 of
   k4/sx.md (PR #80; the per-key form of k4/c4min.md Lemma 1) are the keys none of whose configurations is completable.
   The objects are those of k4/c4min.c (PR #41), whose code this file copies for the valid pre-allocations (genP), the
   keys of the min-frozen class, the configurations of a key (configs_for_key) and the owner test (owner_ok_u):
   - P: bases B_i ⊆ R_i, |B_i| <= 2, disjoint; needs N_i = {g in R_i \ B_i : v_i(g) > v_i(B_i)}; valid iff every needed
     good is a one-good base; f = the fewest frozen agents; omega = f - (2n - m); a key = (NA, phi) of a min-frozen P.
   - configurations at a key: free y holds a pair Q_y ⊆ M \ NA with Q_y ∩ U_y admissible (U_y = R_y \ NA), disjoint;
     pool L = the rest. Completable: some free o is a valid owner (C ⊆ Q_o ∪ L given to frozen agents that unfreeze).
   New here: the enumeration stops at the first completable configuration of a key, and nothing else is computed.

   stdin as k4/red.c (so k4/red_run.py's core_input feeds it): n m; per agent: d g_0 .. g_{d-1} T, then T lines of d
   values; then "R seed" (R = 0: every profile; R > 0: R random profiles with red.c's generator and seeding, so at f = 1
   this sees exactly red.c's profiles). Several such blocks may follow each other (each random block restarts the
   generator from its own seed); a list of single profiles is a list of blocks with T = 1 and R = 0.
   options: -f a:b  only profiles with a <= f <= b (default 1:99); -x N  print at most N HIT lines (default unlimited).
   Output: per hit "HIT f omega nkeys nbad [g:v,...] [g:v,...] ..." (the profile, agent by agent), then counters
   "C name value": profiles, omega>=1 per f, keys per f, noncompletable keys per f, profiles with one per f. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 10
#define MAXM 40
#define MAXT 300
typedef uint64_t mask_t;
static inline int pc(mask_t x) { return __builtin_popcountll(x); }

static int n, m, d[MAXN], gl[MAXN][4], nt[MAXN], tv[MAXN][MAXT][4], cur[MAXN];
static mask_t Rm[MAXN];
static int vv[MAXN][MAXM];
static int fa = 1, fb = 99; static long long maxhits = -1, nhits = 0;

static int val(int i, mask_t S) { int s = 0; mask_t r = S & Rm[i]; while (r) { int g = __builtin_ctzll(r); s += vv[i][g]; r &= r - 1; } return s; }
static int minval(int i, mask_t S) {
  if (S & ~Rm[i]) return 0;
  int mn = 1 << 30; mask_t r = S; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] < mn) mn = vv[i][g]; r &= r - 1; } return mn;
}
static int threat(int i, mask_t X, mask_t H) { if (!X) return 0; return val(i, X) - minval(i, X) > val(i, H); }
static mask_t needs(int i, mask_t B) { int b = val(i, B); mask_t N = 0, r = Rm[i] & ~B; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] > b) N |= (mask_t)1 << g; r &= r - 1; } return N; }

/* ---- valid pre-allocations and the keys of the min-frozen class (k4/c4min.c) ---- */
static int nopt[MAXN]; static mask_t opt[MAXN][11];
static mask_t curB[MAXN];
typedef struct { mask_t NA; mask_t phi[MAXN]; } nkey_t;
static nkey_t *keys; static int nkeys, capkeys, fmin;
static void add_key(mask_t NA, int nf) {
  if (nf > fmin) return;
  if (nf < fmin) { fmin = nf; nkeys = 0; }
  nkey_t k; memset(&k, 0, sizeof k); k.NA = NA;
  for (int i = 0; i < n; i++) if (pc(curB[i]) == 1 && (curB[i] & NA)) k.phi[i] = curB[i];
  for (int q = 0; q < nkeys; q++) if (keys[q].NA == NA && !memcmp(keys[q].phi, k.phi, sizeof(mask_t) * n)) return;
  if (nkeys == capkeys) { capkeys = capkeys ? 2 * capkeys : 64; keys = realloc(keys, capkeys * sizeof(nkey_t)); }
  keys[nkeys++] = k;
}
static void genP(int i, mask_t used, mask_t sing, mask_t two, mask_t NA) {
  if (i == n) {
    if (NA & ~sing) return;
    int nf = 0; for (int k = 0; k < n; k++) if (pc(curB[k]) == 1 && (curB[k] & NA)) nf++;
    add_key(NA, nf);
    return;
  }
  for (int k = 0; k < nopt[i]; k++) {
    mask_t B = opt[i][k]; if (B & used) continue;
    mask_t N = needs(i, B), NA2 = NA | N, two2 = pc(B) == 2 ? two | B : two;
    if (NA2 & two2) continue;
    curB[i] = B; genP(i + 1, used | B, pc(B) == 1 ? sing | B : sing, two2, NA2);
  }
}

/* ---- configurations of one key, stopping at the first completable one (k4/c4min.c) ---- */
static int isfree[MAXN], freel[MAXN], nfree;
static mask_t U[MAXN], Mp, H[MAXN], Lc;
static int nfopt[MAXN]; static mask_t fopt[MAXN][1200];

static int owner_ok_u(int o) {          /* k4/c4min.c owner_ok_u with allow_unf = 1, on the holdings H and pool Lc */
  mask_t Xo = H[o] | Lc, NAo = 0; int cand[MAXN], ncand = 0;
  for (int j = 0; j < n; j++) if (j != o) NAo |= needs(j, isfree[j] ? H[j] & U[j] : H[j]);
  for (int x = 0; x < n; x++) if (!isfree[x] && !(H[x] & NAo)) cand[ncand++] = x;
  for (mask_t C = 0;; C = (C - Xo) & Xo) {
    if (pc(C) <= ncand) {
      mask_t X = Xo & ~C; int ok = 1;
      { int adm = 0; mask_t S = X & U[o];
        if (!S) adm = !U[o];
        for (mask_t B = S; B && !adm; B = (B - 1) & S) if (pc(B) <= 2 && !(needs(o, B) & U[o])) adm = 1;
        ok = adm; }
      if (ok && C) { mask_t No = needs(o, X & Rm[o]); int unf = 0; for (int k = 0; k < ncand; k++) if (!(H[cand[k]] & No)) unf++; if (unf < pc(C)) ok = 0; }
      for (int x = 0; x < n && ok; x++) if (x != o && threat(x, X, isfree[x] ? H[x] & U[x] : H[x])) ok = 0;
      if (ok) return 1;
    }
    if (C == Xo) break;
  }
  return 0;
}
static long long ncfg;
static int genC(int k, mask_t used) {   /* 1 iff some configuration extending the current one is completable */
  if (k == nfree) {
    ncfg++;
    Lc = Mp & ~used;
    for (int q = 0; q < nfree; q++) if (owner_ok_u(freel[q])) return 1;
    return 0;
  }
  int i = freel[k];
  for (int q = 0; q < nfopt[i]; q++) { mask_t S = fopt[i][q]; if (S & used) continue; H[i] = S; if (genC(k + 1, used | S)) return 1; }
  return 0;
}
static int key_completable(const nkey_t *K) {
  mask_t all = (((mask_t)1 << m) - 1);
  Mp = all & ~K->NA; nfree = 0;
  for (int i = 0; i < n; i++) {
    U[i] = Rm[i] & Mp; isfree[i] = !K->phi[i]; H[i] = K->phi[i];
    if (!isfree[i]) continue;
    freel[nfree++] = i; nfopt[i] = 0;
    for (int g = 0; g < m; g++) if (Mp >> g & 1) for (int h = g + 1; h < m; h++) if (Mp >> h & 1) {
      mask_t S = ((mask_t)1 << g) | ((mask_t)1 << h);
      if (needs(i, S & U[i]) & U[i]) continue;
      if (nfopt[i] >= 1200) { fprintf(stderr, "too many pairs\n"); exit(3); }
      fopt[i][nfopt[i]++] = S;
    }
  }
  if (!nfree) return 0;
  return genC(0, 0);
}

static long long cprof, com[16], ckeys[16], cbad[16], cpbad[16];
static void do_profile(void) {
  for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) vv[i][gl[i][k]] = tv[i][cur[i]][k];
  cprof++;
  fmin = 1 << 20; nkeys = 0;
  genP(0, 0, 0, 0, 0);
  int omega = fmin - (2 * n - m);
  if (omega <= 0 || fmin < fa || fmin > fb) return;
  int f = fmin < 15 ? fmin : 15;
  com[f]++; ckeys[f] += nkeys;
  int nbad = 0;
  for (int q = 0; q < nkeys; q++) if (!key_completable(&keys[q])) nbad++;
  cbad[f] += nbad;
  if (!nbad) return;
  cpbad[f]++;
  if (maxhits >= 0 && nhits >= maxhits) return;
  nhits++;
  printf("HIT %d %d %d %d", fmin, omega, nkeys, nbad);
  for (int i = 0; i < n; i++) { printf(" ["); for (int k = 0; k < d[i]; k++) printf("%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); printf("]"); }
  printf("\n");
}

static uint64_t rs = 88172645463325252ULL;           /* k4/red.c's generator */
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
  for (int a = 1; a < argc; a++) {
    if (!strcmp(argv[a], "-f") && a + 1 < argc) { if (sscanf(argv[++a], "%d:%d", &fa, &fb) != 2) return 2; }
    else if (!strcmp(argv[a], "-x") && a + 1 < argc) maxhits = atoll(argv[++a]);
    else { fprintf(stderr, "unknown option %s\n", argv[a]); return 2; }
  }
  int blocks = 0;
  for (;;) {                                   /* one or more blocks (a core with its types, then "R seed") */
    if (scanf("%d %d", &n, &m) != 2) break;
    if (n > MAXN || m > MAXM - 2) { fprintf(stderr, "too large\n"); return 1; }
    for (int i = 0; i < n; i++) {
      if (scanf("%d", &d[i]) != 1) return 1;
      Rm[i] = 0; for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 1; Rm[i] |= (mask_t)1 << gl[i][k]; }
      if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) return 1;
      for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 1;
      nopt[i] = 0; opt[i][nopt[i]++] = 0;
      for (int a = 0; a < d[i]; a++) opt[i][nopt[i]++] = (mask_t)1 << gl[i][a];
      for (int a = 0; a < d[i]; a++) for (int b = a + 1; b < d[i]; b++) opt[i][nopt[i]++] = ((mask_t)1 << gl[i][a]) | ((mask_t)1 << gl[i][b]);
    }
    memset(vv, 0, sizeof vv);
    long long R = 0, seed = 1;
    if (scanf("%lld %lld", &R, &seed) != 2) { R = 0; }
    blocks++;
    if (R > 0) {
      rs = 88172645463325252ULL;
      rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int w = 0; w < 10; w++) rnd();
      for (long long it = 0; it < R; it++) { for (int i = 0; i < n; i++) cur[i] = rnd() % nt[i]; do_profile(); }
    } else {
      memset(cur, 0, sizeof cur);
      for (;;) {
        do_profile();
        int i = 0; while (i < n && ++cur[i] == nt[i]) { cur[i] = 0; i++; }
        if (i == n) break;
      }
    }
  }
  if (!blocks) return 1;
  printf("C profiles %lld\n", cprof);
  printf("C configs_visited %lld\n", ncfg);
  for (int f = 0; f < 16; f++) if (com[f]) {
    printf("C f%d_omega>=1 %lld\nC f%d_keys %lld\nC f%d_keys_noncompletable %lld\nC f%d_profiles_with_noncompletable %lld\n",
           f, com[f], f, ckeys[f], f, cbad[f], f, cpbad[f]);
  }
  return 0;
}
