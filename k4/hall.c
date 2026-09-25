/* hall.c: the covering ("Hall") structure of owner validity for k = 4 pre-allocations (k4/hall.md).

   Written independently of k4/c4x.c (branch proof/k4-c4x), from the definitions of k4/c4x.md §1 and
   k4/lb4.md §1, and cross-checked against it (k4/hall_run.py --xcheck).

   For every strict profile of one core, enumerate the space P of valid pre-allocations (bases B_i ⊆ R_i with
   |B_i| <= 2, pairwise disjoint; value-based needs N_i = {g in R_i \ B_i : v_i(g) > v_i(B_i)}; junk J = goods in
   no base; valid iff every needed good is the whole base of one agent), find the fewest frozen agents, and for the
   pre-allocations with the fewest frozen agents compute the removal-only deficit exactly:
     def(P) = |J| - S                           if that is <= 0 (no owner);
            = min over free owners o and K ⊆ J with B_o ∪ K threatening nobody (every x != o holding B_x alone)
              of |J \ K| - S_o(K),               otherwise,
   where S_o(K) = the slots of the agents other than o, frozen status recomputed with the owner's needs taken from
   X_o = B_o ∪ K (lean/EFX/PreAllocK.lean's ownerNeeds). A set X ⊆ W threatens x holding B_x iff
   max_{h in X} v_x(X \ h) > v_x(B_x).

   The Hall form (k4/hall.md §2): K ⊆ J is safe iff it is independent in the threat hypergraph H_o on W_o = B_o ∪ J,
   whose edges are the minimal threatening sets; every edge has 2 or 3 goods, all in R_x \ B_x of one agent x.
   So o is a removal-only owner iff alpha_o(forced B_o) + u_o >= |J| - (S - cap(o)), and the counters below check
   the characterization and record, at every min-frozen P with omega >= 1, the minimal violators.

   stdin (the format of k4/c4x.c): n m, then per agent: d g_0 .. g_{d-1} T, then T lines of d values;
          then lo hi (range of agent 0's type index).
   options: -r N random profiles (seed -S), -x N examples, -1 one profile (type 0 of every agent, the -d dump),
            -d dump the min-frozen pre-allocations with their deficits and exposure data, -X cross-check mode (print
            per profile: #valid, min frozen, #min-frozen, #min-frozen with deficit <= 0, least deficit). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 40
#define MAXM 64
#define MAXT 300
#define MAXO 11
typedef uint64_t mask_t;
static inline int pc(mask_t x) { return __builtin_popcountll(x); }

static int n, m, d[MAXN], gl[MAXN][4], nt[MAXN], tv[MAXN][MAXT][4], cur[MAXN];
static mask_t R[MAXN];
static int nex = 0, dump = 0, xcheck = 0;

/* per profile */
static int nop[MAXN]; static mask_t opB[MAXN][MAXO], opN[MAXN][MAXO]; static int opV[MAXN][MAXO];

static int val(int i, mask_t X) {                /* v_i(X) for a global set X */
  int s = 0; for (int k = 0; k < d[i]; k++) if (X >> gl[i][k] & 1) s += tv[i][cur[i]][k]; return s;
}

static void setup(void) {
  for (int i = 0; i < n; i++) {
    nop[i] = 0;
    for (int s = 0; s < (1 << d[i]); s++) {
      if (pc(s) > 2) continue;
      mask_t B = 0; int v = 0;
      for (int k = 0; k < d[i]; k++) if (s >> k & 1) { B |= (mask_t)1 << gl[i][k]; v += tv[i][cur[i]][k]; }
      mask_t N = 0;
      for (int k = 0; k < d[i]; k++) if (!(s >> k & 1) && tv[i][cur[i]][k] > v) N |= (mask_t)1 << gl[i][k];
      opB[i][nop[i]] = B; opN[i][nop[i]] = N; opV[i][nop[i]] = v; nop[i]++;
    }
  }
}

/* a set X threatens x holding a bundle worth vx */
static int threatens(int x, mask_t X, int vx) {
  mask_t q = X & R[x];
  if (pc(q) < 2) return 0;
  int th = val(x, q);
  if (!(X & ~R[x])) { int mn = 1 << 30; for (int k = 0; k < d[x]; k++) if (q >> gl[x][k] & 1) if (tv[x][cur[x]][k] < mn) mn = tv[x][cur[x]][k]; th -= mn; }
  return th > vx;
}

/* ---------------- enumeration of valid pre-allocations ---------------- */
typedef struct { unsigned char o[MAXN]; } pa_t;
static pa_t *L; static long long nL, capL;
static mask_t valuedfrom[MAXN + 1];
static int best_frozen;
static void push(const unsigned char *o) {
  if (nL == capL) { capL = capL ? 2 * capL : 4096; L = realloc(L, capL * sizeof(pa_t)); }
  memcpy(L[nL].o, o, MAXN); nL++;
}
static long long nvalid;
static void gen(int i, mask_t used, mask_t sing, mask_t two, mask_t needU, unsigned char *o) {
  if (i == n) {
    if (needU & ~sing) return;
    nvalid++;
    int F = pc(needU);                           /* every needed good is one frozen agent's base */
    if (F < best_frozen) { best_frozen = F; nL = 0; }
    if (F == best_frozen) push(o);
    return;
  }
  for (int k = 0; k < nop[i]; k++) {
    mask_t B = opB[i][k];
    if (B & used) continue;
    mask_t s2 = sing, t2 = two;
    if (pc(B) == 1) s2 |= B; else if (pc(B) == 2) t2 |= B;
    mask_t nu = needU | opN[i][k], u2 = used | B;
    if (nu & t2) continue;                       /* a needed good in a two-good base */
    if (nu & ~u2 & ~valuedfrom[i + 1]) continue; /* a needed good no later agent can take */
    o[i] = k; gen(i + 1, u2, s2, t2, nu, o);
  }
}

/* ---------------- one pre-allocation ---------------- */
typedef struct {
  mask_t B[MAXN], N[MAXN], NA, J; int fz[MAXN], cap[MAXN], S, omega;
} st_t;
static void mkst(const unsigned char *o, st_t *s) {
  mask_t used = 0; s->NA = 0;
  for (int i = 0; i < n; i++) { s->B[i] = opB[i][o[i]]; s->N[i] = opN[i][o[i]]; s->NA |= s->N[i]; used |= s->B[i]; }
  s->J = (((mask_t)1 << m) - 1) & ~used; s->S = 0;
  for (int i = 0; i < n; i++) { s->fz[i] = pc(s->B[i]) == 1 && (s->B[i] & s->NA); s->cap[i] = s->fz[i] ? 0 : 2 - pc(s->B[i]); s->S += s->cap[i]; }
  s->omega = pc(s->J) - s->S;
}
/* slots of the agents other than o when o's needs are taken from X_o */
static int slots_o(const st_t *s, int o, mask_t Xo) {
  int vxo = val(o, Xo); mask_t no = 0;
  for (int k = 0; k < d[o]; k++) { mask_t g = (mask_t)1 << gl[o][k]; if (!(g & Xo) && tv[o][cur[o]][k] > vxo) no |= g; }
  mask_t NAp = no; for (int j = 0; j < n; j++) if (j != o) NAp |= s->N[j];
  int S = 0; for (int j = 0; j < n; j++) if (j != o) S += (pc(s->B[j]) == 1 && (s->B[j] & NAp)) ? 0 : 2 - pc(s->B[j]);
  return S;
}
static int safe(const st_t *s, int o, mask_t Xo) {
  for (int x = 0; x < n; x++) if (x != o && threatens(x, Xo, val(x, s->B[x]))) return 0;
  return 1;
}
/* exact removal-only deficit of owner o (1<<20 if no safe K) */
static int def_owner(const st_t *s, int o, mask_t *bestK) {
  int best = 1 << 20; mask_t J = s->J;
  for (mask_t K = J;; K = (K - 1) & J) {
    mask_t Xo = s->B[o] | K;
    if (safe(s, o, Xo)) { int dd = pc(J & ~K) - slots_o(s, o, Xo); if (dd < best) { best = dd; if (bestK) *bestK = K; } }
    if (!K) break;
  }
  return best;
}
static int deficit(const st_t *s, int *who) {
  if (s->omega <= 0) { if (who) *who = -1; return s->omega; }
  int best = 1 << 20;
  for (int o = 0; o < n; o++) if (!s->fz[o]) { int dd = def_owner(s, o, 0); if (dd < best) { best = dd; if (who) *who = o; } }
  return best;
}

/* ---------------- the Hall structure ----------------
   For owner o: the exposed agents E_o (threatened by W_o = B_o ∪ J holding their base), each with its minimal
   threatening sets inside W_o (the edges of H_o). Removal-only validity with the owner's needs from the base
   (w0) is  tau_o := min{|C| : C ⊆ J, W_o \ C threatens nobody} <= S - cap(o).
   We record the edges and check: (1) the characterization (def_o computed from tau_o and the unfreezing gain
   agrees with def_owner); (2) the kinds of exposure. */
enum { K_E1 = 0, K_TOP4_BIG, K_TOP4_BC, K_TOP4_MID, K_TOP4_FLAT, K_B4, K_PAIR4, K_OTHER, NK };
static const char *kname[NK] = {"3-good top", "4-good top a>b+c", "4-good top b+d<a<b+c", "4-good top c+d<a<b+d", "4-good top flat", "4-good {b}", "4-good pair", "other"};
static int kind_of(int x, mask_t Bx) {
  int v[4], k; for (k = 0; k < d[x]; k++) v[k] = tv[x][cur[x]][k];
  /* sort local goods by value */
  int ord[4] = {0, 1, 2, 3};
  for (int a = 0; a < d[x]; a++) for (int b = a + 1; b < d[x]; b++) if (v[ord[b]] > v[ord[a]]) { int t = ord[a]; ord[a] = ord[b]; ord[b] = t; }
  mask_t top = (mask_t)1 << gl[x][ord[0]];
  if (pc(Bx) == 2) return d[x] == 4 ? K_PAIR4 : K_OTHER;
  if (Bx == top) {
    if (d[x] == 3) return K_E1;
    int a = v[ord[0]], b = v[ord[1]], c = v[ord[2]], dd = v[ord[3]];
    if (a > b + c) return K_TOP4_BIG;
    if (a > b + dd) return K_TOP4_BC;
    if (a > c + dd) return K_TOP4_MID;
    return K_TOP4_FLAT;
  }
  if (d[x] == 4 && Bx == ((mask_t)1 << gl[x][ord[1]])) return K_B4;
  return K_OTHER;
}

static long long cnt_prof, cnt_valid, cnt_minF, cnt_minF_om1, cnt_def_le0_prof, cnt_bad_char, cnt_minF_pos;
static long long kexp[NK][2], kexp_unhit[NK][2], kfail_owner, kfail_owner_unhit, kviol_size[8], nviol;
static long long tauhist[8];

static void print_profile(void) {
  printf(" types");
  for (int i = 0; i < n; i++) { printf(" ["); for (int k = 0; k < d[i]; k++) printf("%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); printf("]"); }
}
static void print_pa(const st_t *s) {
  printf(" bases");
  for (int i = 0; i < n; i++) { printf(" {"); int f = 1; for (int g = 0; g < m; g++) if (s->B[i] >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}%s", s->fz[i] ? "F" : ""); }
  printf(" J {"); int f = 1; for (int g = 0; g < m; g++) if (s->J >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}");
}

/* the owner analysis at one min-frozen P with omega >= 1 */
static void analyze(const st_t *s) {
  for (int o = 0; o < n; o++) {
    if (s->fz[o]) continue;
    mask_t W = s->B[o] | s->J;
    int dO = def_owner(s, o, 0);
    /* (1) characterization: tau with w0 slots vs def with ownerNeeds; the unfreezing gain is >= 0 */
    int tau = 1 << 20; mask_t J = s->J;
    for (mask_t C = J;; C = (C - 1) & J) { if (pc(C) < tau && safe(s, o, W & ~C)) tau = pc(C); if (!C) break; }
    int d0 = tau - (s->S - s->cap[o]);
    if (tau < (1 << 20) && dO > d0) cnt_bad_char++;          /* unfreezing can only help */
    if (dO > 0) {
      kfail_owner++;
      int unhit = 0;
      for (int x = 0; x < n; x++) if (x != o && threatens(x, W, val(x, s->B[x]))) {
        int kd = kind_of(x, s->B[x]);
        int uh = threatens(x, s->B[o] | (J & ~R[x]), val(x, s->B[x]));
        kexp[kd][s->fz[x]]++; if (uh) { kexp_unhit[kd][s->fz[x]]++; unhit = 1; }
      }
      if (unhit) kfail_owner_unhit++;
      else if (tau < 8) tauhist[tau]++;
      /* a minimal violator: fewest exposed agents whose protection alone needs more than S - cap(o) removals */
      if (!unhit) {
        int ex[MAXN], ne = 0;
        for (int x = 0; x < n; x++) if (x != o && threatens(x, W, val(x, s->B[x]))) ex[ne++] = x;
        int found = 0;
        for (int sz = 1; sz <= ne && sz < 8 && !found; sz++) {
          /* subsets of size sz of the exposed agents */
          int idx[8]; for (int q = 0; q < sz; q++) idx[q] = q;
          for (;;) {
            int t2 = 1 << 20;
            for (mask_t C = J;; C = (C - 1) & J) {
              if (pc(C) < t2) {
                int ok = 1; for (int q = 0; q < sz && ok; q++) { int x = ex[idx[q]]; if (threatens(x, W & ~C, val(x, s->B[x]))) ok = 0; }
                if (ok) t2 = pc(C);
              }
              if (!C) break;
            }
            if (t2 > s->S - s->cap[o]) { found = sz; break; }
            int q = sz - 1; while (q >= 0 && idx[q] == ne - sz + q) q--;
            if (q < 0) break;
            idx[q]++; for (int r = q + 1; r < sz; r++) idx[r] = idx[r - 1] + 1;
          }
        }
        kviol_size[found < 8 ? found : 7]++; nviol++;
      }
    }
  }
}

static void do_profile(void) {
  setup();
  valuedfrom[n] = 0; for (int i = n - 1; i >= 0; i--) valuedfrom[i] = valuedfrom[i + 1] | R[i];
  nL = 0; nvalid = 0; best_frozen = 1 << 20;
  unsigned char o[MAXN] = {0};
  gen(0, 0, 0, 0, 0, o);
  cnt_prof++; cnt_valid += nvalid; cnt_minF += nL;
  int any = 0, least = 1 << 20; long long nle0 = 0;
  for (long long k = 0; k < nL; k++) {
    st_t s; mkst(L[k].o, &s);
    int who = -1, dd = deficit(&s, &who);
    if (dd < least) least = dd;
    if (dd <= 0) { any = 1; nle0++; }
    if (s.omega >= 1) { cnt_minF_om1++; analyze(&s); }
    if (dd > 0) cnt_minF_pos++;
    if (dump) { printf("P"); print_pa(&s); printf(" omega %d def %d owner %d\n", s.omega, dd, who); }
  }
  if (any) cnt_def_le0_prof++;
  else if (nex-- > 0) { printf("EX C4min fails:"); print_profile(); printf("\n"); }
  if (xcheck) { printf("X"); for (int i = 0; i < n; i++) printf(" %d", cur[i]); printf(" valid %lld minfrozen %d count %lld le0 %lld least %d\n", nvalid, best_frozen, nL, nle0, least); }
}

int main(int argc, char **argv) {
  long long nrand = 0; unsigned long long seed = 1; int single = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-r")) nrand = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-S")) seed = strtoull(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "-x")) nex = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-d")) dump = 1;
    else if (!strcmp(argv[i], "-1")) single = 1;
    else if (!strcmp(argv[i], "-X")) xcheck = 1;
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
  }
  if (scanf("%d %d", &n, &m) != 2) return 2;
  if (n > MAXN || m > MAXM) { fprintf(stderr, "too large\n"); return 2; }
  for (int i = 0; i < n; i++) {
    if (scanf("%d", &d[i]) != 1) return 2;
    R[i] = 0;
    for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 2; R[i] |= (mask_t)1 << gl[i][k]; }
    if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) return 2;
    for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 2;
  }
  int lo, hi; if (scanf("%d %d", &lo, &hi) != 2) { lo = 0; hi = nt[0]; }
  if (single) { for (int i = 0; i < n; i++) cur[i] = 0; do_profile(); }
  else if (nrand) {
    uint64_t s = seed * 0x9E3779B97F4A7C15ULL + 12345;   /* the sampler of k4/c4x.c, so -X lines can be compared */
    for (long long r = 0; r < nrand; r++) {
      for (int i = 0; i < n; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; cur[i] = (int)(s % (uint64_t)nt[i]); }
      do_profile();
    }
  } else {
    for (cur[0] = lo; cur[0] < hi; cur[0]++) {
      for (int i = 1; i < n; i++) cur[i] = 0;
      for (;;) {
        do_profile();
        int i = n - 1;
        while (i >= 1 && ++cur[i] == nt[i]) { cur[i] = 0; i--; }
        if (i < 1) break;
      }
    }
  }
  printf("RESULT profiles %lld valid %lld minfrozen %lld minfrozen_omega1 %lld minfrozen_posdef %lld profiles_c4min_ok %lld bad_char %lld\n",
         cnt_prof, cnt_valid, cnt_minF, cnt_minF_om1, cnt_minF_pos, cnt_def_le0_prof, cnt_bad_char);
  printf("FAILOWNERS %lld unhittable %lld tau", kfail_owner, kfail_owner_unhit);
  for (int t = 0; t < 8; t++) printf(" %lld", tauhist[t]);
  printf(" violsize"); for (int t = 0; t < 8; t++) printf(" %lld", kviol_size[t]); printf("\n");
  for (int k = 0; k < NK; k++) printf("KIND %d free %lld (unhit %lld) frozen %lld (unhit %lld) %s\n", k, kexp[k][0], kexp_unhit[k][0], kexp[k][1], kexp_unhit[k][1], kname[k]);
  return 0;
}
