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
static int nex = 0, dump = 0, xcheck = 0, paretomode = 0, pex = 0, cyclemode = 0, paretoonly = 0, btmode = 0;
static long long pm_prof[4], pm_every[4], pm_some[4], pm_n[4];
static int potmode = 0; static long long *potv, potbest;
static int level(int i, mask_t B);
static int bigtop_type(int i);

/* per profile */
static int nop[MAXN]; static mask_t opB[MAXN][MAXO], opN[MAXN][MAXO]; static int opV[MAXN][MAXO];

static int val(int i, mask_t X) {                /* v_i(X) for a global set X */
  int s = 0; for (int k = 0; k < d[i]; k++) if (X >> gl[i][k] & 1) s += tv[i][cur[i]][k]; return s;
}
static int level(int i, mask_t B) { int v = val(i, B), l = 0; for (int t = 0; t < (1 << d[i]); t++) { int x = 0; for (int k = 0; k < d[i]; k++) if (t >> k & 1) x += tv[i][cur[i]][k]; if (x < v) l++; } return l; }

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

/* F = 0 (no frozen agent) at a Pareto-maximum with omega >= 1 (k4/hall.md §3). f0c counters:
   0 maxima; 1 Lemma U violated (a single-good holder values a junk good); 2 Lemma U2 violated (a pair-holder has a
   better pair inside its base and the junk); 3 no single-good holder (T = 0); 4 exposure of another kind than e1-e3;
   5 the label criterion disagrees with the exact removal-only test; 6 some single-good holder is a valid owner;
   7 some pair-holder is a valid owner; 8 no valid owner; 9 every single-good holder is valid; 10 a single-good holder
   is invalid because of an unhittable exposure; 11 e2 exposures (total), 12 e1, 13 e3 */
static long long f0c[20];
static void f0_analyze(const st_t *s) {
  f0c[0]++;
  int T = 0, anyt = 0, anyp = 0, allt = 1;
  for (int x = 0; x < n; x++) {
    if (pc(s->B[x]) == 1) { T++; if (R[x] & s->J) f0c[1]++; }
    if (pc(s->B[x]) == 2) {
      mask_t av = s->B[x] | (R[x] & s->J); int bv = val(x, s->B[x]);
      for (int g = 0; g < m; g++) for (int h = g + 1; h < m; h++) if ((av >> g & 1) && (av >> h & 1)) { mask_t Pq = ((mask_t)1 << g) | ((mask_t)1 << h); if (val(x, Pq) > bv) f0c[2]++; }
    }
  }
  if (!T) f0c[3]++;
  for (int o = 0; o < n; o++) {
    mask_t W = s->B[o] | s->J, Z = 0; int unhit = 0;
    for (int x = 0; x < n; x++) if (x != o && threatens(x, W, val(x, s->B[x]))) {
      mask_t low = R[x] & ~s->B[x];
      if (pc(s->B[x]) == 1 && pc(low & s->B[o]) == 2) { unhit = 1; f0c[12]++; }
      else if (pc(s->B[x]) == 2 && d[x] == 4 && (low & ~s->B[o]) == 0) { unhit = 1; f0c[13]++; }
      else if (pc(s->B[x]) == 2 && d[x] == 4 && pc(low & s->B[o]) == 1 && pc(low & s->J) == 1) { Z |= low & s->J; f0c[11]++; if (pc(s->B[o]) == 1) { f0c[14]++; if (pex > 0) { pex--; printf("EXF0 e2 at single owner %d x %d:", o, x); print_profile(); print_pa(s); printf("\n"); } } }
      else f0c[4]++;
    }
    int crit = !unhit && pc(Z) <= s->S - s->cap[o];
    int ok = def_owner(s, o, 0) <= 0;
    if (crit != ok) f0c[5]++;
    if (ok) { if (pc(s->B[o]) == 1) anyt = 1; else anyp = 1; }
    else if (pc(s->B[o]) == 1) { allt = 0; if (unhit) f0c[10]++; }
  }
  f0c[6] += anyt; f0c[7] += anyp; f0c[8] += !anyt && !anyp; f0c[9] += allt && T;
}

/* -G: the cycle argument of Theorem H0 (k4/hall.md §3) on every pre-allocation with no frozen agent and omega >= 1
   that satisfies the local conditions U and U2 and has no valid owner. g0c: 0 such P; 1 an agent exposed w.r.t. two
   owners; 2 some owner exposes nobody; 3 T >= 2; 4 the exposure map is not a bijection; 5 the rotation rule of the
   proof gives a valid Pareto improvement; 6 it fails; 7 it fails for want of distinct labels. */
static long long g0c[10]; static int gex = 0;
static int f0_local_ok(const st_t *s) {
  for (int x = 0; x < n; x++) {
    if (pc(s->B[x]) == 1 && (R[x] & s->J)) return 0;
    if (pc(s->B[x]) == 2) {
      mask_t av = s->B[x] | (R[x] & s->J); int bv = val(x, s->B[x]);
      for (int g = 0; g < m; g++) for (int h = g + 1; h < m; h++) if ((av >> g & 1) && (av >> h & 1)) { mask_t Pq = ((mask_t)1 << g) | ((mask_t)1 << h); if (val(x, Pq) > bv) return 0; }
    }
  }
  return 1;
}
static mask_t best1(int y, mask_t A) { int bv = -1; mask_t b = 0; for (int g = 0; g < m; g++) if ((A >> g & 1) && val(y, (mask_t)1 << g) > bv) { bv = val(y, (mask_t)1 << g); b = (mask_t)1 << g; } return b; }
static void f0_cycle_check(const st_t *s) {
  for (int o = 0; o < n; o++) if (def_owner(s, o, 0) <= 0) return;
  g0c[0]++;
  int T = 0; for (int x = 0; x < n; x++) T += pc(s->B[x]) == 1;
  if (T >= 2) g0c[3]++;
  int expby[MAXN], nexp[MAXN], cnt[MAXN];
  for (int x = 0; x < n; x++) { expby[x] = -1; cnt[x] = 0; }
  for (int o = 0; o < n; o++) { nexp[o] = 0; mask_t W = s->B[o] | s->J;
    for (int x = 0; x < n; x++) if (x != o && threatens(x, W, val(x, s->B[x]))) { nexp[o]++; cnt[x]++; expby[x] = o; } }
  int bij = 1;
  for (int x = 0; x < n; x++) { if (cnt[x] > 1) { g0c[1]++; bij = 0; } if (cnt[x] != 1) bij = 0; }
  for (int o = 0; o < n; o++) { if (!nexp[o]) g0c[2]++; if (nexp[o] != 1) bij = 0; }
  if (!bij) { g0c[4]++; return; }
  /* pred(y) = expby[y]; successor of o = the agent o exposes */
  int succ[MAXN]; for (int x = 0; x < n; x++) succ[expby[x]] = x;
  mask_t In[MAXN], lg[MAXN];
  for (int y = 0; y < n; y++) { In[y] = s->B[expby[y]] & R[y]; lg[y] = best1(y, In[y]); }
  int H[MAXN] = {0}, ch = 1;
  while (ch) { ch = 0;
    for (int y = 0; y < n; y++) if (!H[y]) {
      int sy = succ[y]; mask_t taken = H[sy] ? In[sy] : lg[sy], keep = s->B[y] & ~taken;
      if (!keep || val(y, lg[y] | best1(y, keep)) <= val(y, s->B[y])) { H[y] = 1; ch = 1; }
    } }
  mask_t NB[MAXN], usedlab = 0; int fail = 0, labfail = 0;
  for (int y = 0; y < n && !fail; y++) {
    if (H[y]) { NB[y] = In[y];
      if (pc(In[y]) == 1) { mask_t lab = best1(y, R[y] & s->J & ~usedlab); if (!lab) { fail = labfail = 1; break; } NB[y] |= lab; usedlab |= lab; } }
    else { int sy = succ[y]; mask_t taken = H[sy] ? In[sy] : lg[sy]; NB[y] = lg[y] | best1(y, s->B[y] & ~taken); }
  }
  if (!fail) {   /* verify: disjoint, strictly better, valid (no needed good outside one-good bases) */
    mask_t all = 0, sing = 0, NAn = 0;
    for (int y = 0; y < n && !fail; y++) {
      if (NB[y] & all) fail = 1;
      all |= NB[y];
      if (pc(NB[y]) > 2 || val(y, NB[y]) <= val(y, s->B[y])) fail = 1;
      if (pc(NB[y]) == 1) sing |= NB[y];
      for (int k = 0; k < d[y]; k++) { mask_t g = (mask_t)1 << gl[y][k]; if (!(g & NB[y]) && tv[y][cur[y]][k] > val(y, NB[y])) NAn |= g; }
    }
    if (NAn & ~sing) fail = 1;
  }
  if (fail) { g0c[6]++; g0c[7] += labfail; if (gex > 0) { gex--; printf("EXG rule fails%s:", labfail ? " (labels)" : ""); print_profile(); print_pa(s); printf("\n"); } }
  else g0c[5]++;
}

/* frozen agents at a Pareto-maximum with frozen agents (k4/hall.md §5). fc counters: 0 maxima with F >= 1 and
   omega >= 1; 1 ... with a globally exposed frozen agent (J alone threatens it, plain threat); 2 global exposures not of
   the shape "4-good, a > b + c, all three lower goods junk"; 3 no global exposure and no valid owner; 4 global exposure
   and no valid owner; 5 Lemma R violations (a frozen agent x and a chain end tau with a need-free improving set of
   <= 2 goods of R_x inside J ∪ B_tau, other than x's needs); 6 frozen exposed agents w.r.t. two or more owners;
   7 maxima where some owner is valid */
static long long fc[10], fzcls[5], btc[4];   /* btc: 0 profiles with a non-completable Pareto-maximum with frozen agents, 1 ... with a completable min-frozen P owned by a big-top-type agent, 2 ... with any completable min-frozen P */
static void frozen_analyze(const st_t *s) {
  fc[0]++;
  mask_t reach[MAXN];
  for (int x = 0; x < n; x++) {   /* chain ends: free agents reachable from x through frozen agents in the need digraph */
    reach[x] = 0; if (!s->fz[x]) continue;
    int seen = 1 << x, st[4 * MAXN], sp = 0; st[sp++] = x;
    while (sp) { int y = st[--sp]; for (int z = 0; z < n; z++) if (z != y && (s->B[y] & s->N[z])) { if (s->fz[z]) { if (!(seen >> z & 1)) { seen |= 1 << z; st[sp++] = z; } } else reach[x] |= (mask_t)1 << z; } }
  }
  int glob = 0;
  for (int x = 0; x < n; x++) if (s->fz[x]) {
    mask_t q = s->J & R[x];
    if (pc(q) >= 2 && val(x, q) > val(x, s->B[x])) {
      glob = 1;
      /* shape: 4-good, base = top, a > b + c, q = the three lower goods */
      int ok = d[x] == 4 && pc(q) == 3 && (q | s->B[x]) == R[x];
      if (ok) { int mx = 0; for (int k = 0; k < 4; k++) if (tv[x][cur[x]][k] > mx) mx = tv[x][cur[x]][k];
        ok = val(x, s->B[x]) == mx; int best2 = 0;
        for (int g = 0; g < m; g++) for (int h = g + 1; h < m; h++) if ((q >> g & 1) && (q >> h & 1)) { int w = val(x, ((mask_t)1 << g) | ((mask_t)1 << h)); if (w > best2) best2 = w; }
        if (best2 > mx) ok = 0; }
      if (!ok) fc[2]++;
    }
    /* Lemma H6: for every chain end tau, no set O ⊆ R_x ∩ (J ∪ B_tau), 1 <= |O| <= 2, with v(O) > v(B_x) */
    for (int tau = 0; tau < n; tau++) if (reach[x] >> tau & 1) {
      mask_t av = R[x] & (s->J | s->B[tau]);
      for (mask_t O = av; O; O = (O - 1) & av)
        if (pc(O) <= 2 && val(x, O) > val(x, s->B[x])) { fc[5]++; tau = n; break; }
    }
  }
  if (glob) fc[1]++;
  int anyok = 0, cntexp[MAXN] = {0};
  for (int o = 0; o < n; o++) if (!s->fz[o]) {
    if (def_owner(s, o, 0) <= 0) anyok = 1;
    mask_t W = s->B[o] | s->J;
    for (int x = 0; x < n; x++) if (x != o && s->fz[x] && threatens(x, W, val(x, s->B[x]))) {
      cntexp[x]++;
      mask_t q = s->J & R[x];
      int cls;
      if (pc(q) >= 2 && val(x, q) > val(x, s->B[x])) cls = 0;                 /* G */
      else if (reach[x] >> o & 1) cls = 1;                                        /* G1-type: o is a chain end of x */
      else {                                                                      /* L: labels needed */
        int r = 99;
        for (mask_t C = q;; C = (C - 1) & q) { if (pc(C) < r && !threatens(x, W & ~C, val(x, s->B[x]))) r = pc(C); if (!C) break; }
        cls = r == 1 ? 2 : r == 2 ? 3 : 4;
      }
      fzcls[cls]++;
    }
  }
  for (int x = 0; x < n; x++) if (cntexp[x] >= 2) fc[6]++;
  /* a G1 configuration: a frozen 4-good agent x holding its top, a > b + c, and a chain end tau of x with
     R_x \ B_x ⊆ J ∪ B_tau (the rotation that repairs x gives it three goods: x must become the owner) */
  int g1 = 0;
  for (int x = 0; x < n && !g1; x++) if (s->fz[x] && d[x] == 4) {
    int v4[4], mx = 0; for (int k = 0; k < 4; k++) { v4[k] = tv[x][cur[x]][k]; if (v4[k] > mx) mx = v4[k]; }
    if (val(x, s->B[x]) != mx) continue;
    int tot = v4[0] + v4[1] + v4[2] + v4[3], mn = 1 << 30; for (int k = 0; k < 4; k++) if (v4[k] < mn) mn = v4[k];
    if (mx <= tot - mx - mn) continue;                     /* a > b + c */
    mask_t low = R[x] & ~s->B[x];
    for (int tau = 0; tau < n; tau++) if ((reach[x] >> tau & 1) && !(low & ~(s->J | s->B[tau]))) g1 = 1;
  }
  if (!anyok && !g1) fc[8]++;
  /* 9: no valid owner and no frozen 4-good agent holding its top with a > b + c ("big-top") */
  if (!anyok) {
    int bigtop = 0;
    for (int x = 0; x < n; x++) if (s->fz[x] && d[x] == 4) {
      int v4[4], mx = 0, tot = 0, mn = 1 << 30; for (int k = 0; k < 4; k++) { v4[k] = tv[x][cur[x]][k]; tot += v4[k]; if (v4[k] > mx) mx = v4[k]; if (v4[k] < mn) mn = v4[k]; }
      if (val(x, s->B[x]) == mx && mx > tot - mx - mn) bigtop = 1;
    }
    if (!bigtop) { fc[9]++; if (pex > 0) { pex--; printf("EXFROZEN no owner, no frozen big-top:"); print_profile(); print_pa(s); printf("\n"); } }
  }
  if (anyok) fc[7]++;
  else if (glob) fc[4]++;
  else fc[3]++;
}

static int bigtop_type(int i) {   /* four goods and a > b + c */
  if (d[i] != 4) return 0;
  int v4[4], mx = 0, tot = 0, mn = 1 << 30; for (int k = 0; k < 4; k++) { v4[k] = tv[i][cur[i]][k]; tot += v4[k]; if (v4[k] > mx) mx = v4[k]; if (v4[k] < mn) mn = v4[k]; }
  return mx > tot - mx - mn;
}

/* ---- the big-top owner step (k4/hall_bt.md): exchange cycles through a frozen big-top agent ---- */
static void mkst_masks(const mask_t *B, st_t *s) {
  mask_t used = 0; s->NA = 0;
  for (int i = 0; i < n; i++) {
    s->B[i] = B[i]; used |= B[i]; int v = val(i, B[i]); mask_t N = 0;
    for (int k = 0; k < d[i]; k++) { mask_t g = (mask_t)1 << gl[i][k]; if (!(g & B[i]) && tv[i][cur[i]][k] > v) N |= g; }
    s->N[i] = N; s->NA |= N;
  }
  s->J = (((mask_t)1 << m) - 1) & ~used; s->S = 0;
  for (int i = 0; i < n; i++) { s->fz[i] = pc(s->B[i]) == 1 && (s->B[i] & s->NA); s->cap[i] = s->fz[i] ? 0 : 2 - pc(s->B[i]); s->S += s->cap[i]; }
  s->omega = pc(s->J) - s->S;
}
static int valid_st(const st_t *s) {   /* every needed good is a one-good base */
  mask_t sing = 0; for (int i = 0; i < n; i++) if (pc(s->B[i]) == 1) sing |= s->B[i];
  return !(s->NA & ~sing);
}
static long long btx[10]; static int btex = 0, bt_anymode = 0;
static int cyc[MAXN + 1], cyclen, bt_ok_owner, bt_ok_any, bt_tried;
static int bt_edge(const st_t *s, int u, int w) {   /* 1 threat edge u -> w, 2 need edge u -> w, 0 none */
  if (u == w) return 0;
  if (s->fz[u]) return (s->B[u] & s->N[w]) ? 2 : 0;
  return threatens(w, s->B[u] | s->J, val(w, s->B[w])) ? 1 : 0;
}
/* move holdings along cyc[0..cyclen-1] (cyc[0] = x) and test x as the owner. A need edge u -> w: w takes u's frozen
   good. A threat edge u -> w: w takes an admissible set (needs inside NA) of at most two goods from u's base, its own
   base and the junk; all choices are tried (backtracking), goods used at most once. */
static mask_t bt_B[MAXN];
static void bt_try(const st_t *s, int x, int q, mask_t used) {
  if (bt_ok_owner || (bt_anymode && bt_ok_any)) return;
  if (q == cyclen) {
    mask_t B[MAXN]; for (int i = 0; i < n; i++) B[i] = s->B[i];
    for (int r = 0; r < cyclen; r++) B[cyc[r]] = bt_B[cyc[r]];
    for (int i = 0; i < n; i++) if (i != x) { int on = 0; for (int r = 0; r < cyclen; r++) if (cyc[r] == i) on = 1; if (!on && (B[i] & used)) return; }
    st_t t; mkst_masks(B, &t);
    if (!valid_st(&t) || pc(t.NA) != best_frozen) return;
    bt_tried = 1;
    if (!bt_anymode && !t.fz[x] && (t.omega <= 0 || def_owner(&t, x, 0) <= 0)) bt_ok_owner = 1;
    if (!bt_ok_any && deficit(&t, 0) <= 0) bt_ok_any = 1;
    return;
  }
  int u = cyc[q], w = cyc[(q + 1) % cyclen];
  if (s->fz[u]) { if (s->B[u] & used) return; bt_B[w] = s->B[u]; bt_try(s, x, q + 1, used | s->B[u]); return; }
  mask_t pool = (s->B[u] | s->B[w] | s->J) & R[w] & ~s->NA & ~used;
  for (mask_t A = pool; A; A = (A - 1) & pool) {
    if (pc(A) > 2) continue;
    int v = val(w, A); mask_t nd = 0;
    for (int k = 0; k < d[w]; k++) { mask_t g = (mask_t)1 << gl[w][k]; if (!(g & A) && tv[w][cur[w]][k] > v) nd |= g; }
    if (nd & ~s->NA) continue;
    bt_B[w] = A; bt_try(s, x, q + 1, used | A);
    if (bt_ok_owner) return;
  }
}
static void bt_apply(const st_t *s, int x) { bt_try(s, x, 0, 0); }
static void bt_dfs(const st_t *s, int x, int u, int used) {
  if (bt_ok_owner || (bt_anymode && bt_ok_any)) return;
  for (int w = 0; w < n; w++) {
    int e = bt_edge(s, u, w); if (!e) continue;
    if (w == x) { if (e == 1) bt_apply(s, x); continue; }   /* x's in-edge must be a threat edge */
    if (used >> w & 1) continue;
    cyc[cyclen++] = w; bt_dfs(s, x, w, used | 1 << w); cyclen--;
  }
}
static void bt_analyze(const st_t *s) {   /* s: a Pareto-maximum inside the min-frozen set with no valid owner, F >= 1 */
  btx[0]++;
  int anybt = 0, expbt = 0, owner = 0, any = 0;
  for (int x = 0; x < n; x++) if (s->fz[x] && bigtop_type(x)) {
    int top = 1; for (int k = 0; k < d[x]; k++) if (tv[x][cur[x]][k] > val(x, s->B[x])) top = 0;
    if (!top) continue;
    anybt = 1;
    for (int o = 0; o < n; o++) if (!s->fz[o] && threatens(x, s->B[o] | s->J, val(x, s->B[x]))) expbt = 1;
    bt_ok_owner = bt_ok_any = bt_tried = 0; cyc[0] = x; cyclen = 1;
    bt_dfs(s, x, x, 1 << x);
    owner |= bt_ok_owner; any |= bt_ok_any;
  }
  btx[1] += anybt; btx[2] += expbt; btx[3] += owner; btx[4] += any;
  /* 5: some cycle through any exposed frozen agent (big-top or not) gives a completable pre-allocation (any owner) */
  int anyfz = any;
  for (int x = 0; x < n && !anyfz; x++) if (s->fz[x]) {
    int ex = 0; for (int o = 0; o < n; o++) if (!s->fz[o] && threatens(x, s->B[o] | s->J, val(x, s->B[x]))) ex = 1;
    if (!ex) continue;
    bt_ok_owner = bt_ok_any = bt_tried = 0; cyc[0] = x; cyclen = 1;
    bt_anymode = 1; bt_dfs(s, x, x, 1 << x); bt_anymode = 0;
    anyfz |= bt_ok_any;
  }
  btx[5] += anyfz;
  if (!owner && btex > 0) { btex--; printf("EXBTC no big-top owner cycle%s:", anybt ? "" : " (no frozen big-top)"); print_profile(); print_pa(s); printf("\n"); }
}

static int gdemand(const st_t *s) {
  mask_t J = s->J; int best = 1 << 20;
  for (mask_t C = J;; C = (C - 1) & J) {
    if (pc(C) < best) {   /* plain threat v_x(Q) > v_x(B_x), |Q| >= 2: an owner's bundle also holds goods outside R_x */
      int ok = 1; for (int x = 0; x < n && ok; x++) { mask_t q = J & ~C & R[x]; if (s->fz[x] && pc(q) >= 2 && val(x, q) > val(x, s->B[x])) ok = 0; }
      if (ok) best = pc(C); }
    if (!C) break;
  }
  return best;
}

static void do_profile(void) {
  setup();
  valuedfrom[n] = 0; for (int i = n - 1; i >= 0; i--) valuedfrom[i] = valuedfrom[i + 1] | R[i];
  nL = 0; nvalid = 0; best_frozen = 1 << 20;
  unsigned char o[MAXN] = {0};
  gen(0, 0, 0, 0, 0, o);
  cnt_prof++; cnt_valid += nvalid; cnt_minF += nL;
  int any = 0, least = 1 << 20; long long nle0 = 0;
  for (long long k = 0; k < nL && !paretoonly; k++) {
    st_t s; mkst(L[k].o, &s);
    int who = -1, dd = deficit(&s, &who);
    if (dd < least) least = dd;
    if (dd <= 0) { any = 1; nle0++; }
    if (s.omega >= 1) { cnt_minF_om1++; if (!cyclemode) analyze(&s); }
    if (cyclemode && best_frozen == 0 && s.omega >= 1 && f0_local_ok(&s)) f0_cycle_check(&s);
    if (dd > 0) cnt_minF_pos++;
    if (dump) { printf("P"); print_pa(&s); printf(" omega %d def %d owner %d\n", s.omega, dd, who); }
  }
  if (paretoonly) any = 1;   /* -N: the min-frozen deficits are not computed */
  if (any) cnt_def_le0_prof++;
  else if (nex-- > 0) { printf("EX C4min fails:"); print_profile(); printf("\n"); }
  if (paretomode) {   /* -P: Pareto-maxima (base values) inside the min-frozen set, by the fewest frozen agents
                         (-Q1: the maxima of the level sum instead; -Q2: of leximin over the levels) */
    int fb = best_frozen > 3 ? 3 : best_frozen, ev = 1, so = 0; long long npm = 0;
    long long *gkey = 0, gbest = -(1LL << 62);
    if (potmode >= 3) {   /* -Q3: (-G, level sum); -Q4: (-G, Pareto); G = the frozen agents' junk demand (gdemand) */
      gkey = malloc(nL * sizeof(long long));
      for (long long k = 0; k < nL; k++) { st_t s; mkst(L[k].o, &s); gkey[k] = -gdemand(&s); if (gkey[k] > gbest) gbest = gkey[k]; }
    }
    if (potmode) {
      potv = realloc(potv, nL * sizeof(long long)); potbest = -(1LL << 62);
      for (long long k = 0; k < nL; k++) {
        long long pv = 0;
        for (int i = 0; i < n; i++) { int l = level(i, opB[i][L[k].o[i]]);
          if (potmode == 5) pv += bigtop_type(i) ? l : 1000LL * l;   /* -Q5: level sum of the other agents first, then of the big-top types */
          else if (potmode == 6) pv += bigtop_type(i) ? -l : 1000LL * l;   /* -Q6: ... then the big-top types' level sum minimized */
          else if (potmode == 7) pv += bigtop_type(i) ? 100LL * (2 - pc(opB[i][L[k].o[i]])) + l : 100000LL * l;   /* -Q7: ... then -|B| of big-tops, then their levels */
          else if (potmode == 1 || potmode == 3) pv += l; else pv -= 1LL << (4 * (15 - l)); }
        if (potmode >= 3 && gkey[k] != gbest) pv = -(1LL << 61);
        potv[k] = pv; if (pv > potbest) potbest = pv;
      }
    }
    for (long long k = 0; k < nL; k++) {
      int dom = 0;
      if (potmode == 4 && gkey[k] != gbest) continue;
      if (potmode == 0 || potmode == 4)
        for (long long q = 0; q < nL && !dom; q++) {
          if (potmode == 4 && gkey[q] != gbest) continue;
          int ge = 1, gt = 0;
          for (int i = 0; i < n; i++) { int a = opV[i][L[k].o[i]], b = opV[i][L[q].o[i]]; if (b < a) { ge = 0; break; } if (b > a) gt = 1; }
          dom = ge && gt;
        }
      else dom = potv[k] != potbest;
      if (dom) continue;
      npm++;
      st_t s; mkst(L[k].o, &s);
      int dd = deficit(&s, 0);
      if (best_frozen == 0 && s.omega >= 1) f0_analyze(&s);
      if (best_frozen >= 1 && s.omega >= 1) frozen_analyze(&s);
      if (dump) { int T = 0; for (int i = 0; i < n; i++) T += pc(s.B[i]) == 1; printf("PM"); print_pa(&s); printf(" T %d omega %d def %d\n", T, s.omega, dd); }
      if (dd > 0 && btmode && best_frozen >= 1 && s.omega >= 1) bt_analyze(&s);
      if (dd <= 0) so = 1; else { ev = 0; if (pex > 0) { pex--; printf("EXPARETO F=%d:", best_frozen); print_profile(); print_pa(&s); printf(" omega %d def %d\n", s.omega, dd); } }
    }
    pm_prof[fb]++; pm_every[fb] += ev; pm_some[fb] += so; pm_n[fb] += npm;
    if (!ev && best_frozen >= 1) {   /* a failing Pareto-maximum: is some min-frozen P completable with a big-top-type owner? */
      btc[0]++; int okbt = 0, okany = 0;
      for (long long k = 0; k < nL && !okbt; k++) {
        st_t s; mkst(L[k].o, &s);
        for (int o = 0; o < n && !okbt; o++) if (!s.fz[o]) { if (s.omega <= 0) { okany = 1; continue; } int dd = def_owner(&s, o, 0); if (dd <= 0) { okany = 1; if (bigtop_type(o)) okbt = 1; } }
      }
      btc[1] += okbt; btc[2] += okany;
      if (!okbt && pex > 0) { pex--; printf("EXBT no big-top owner:"); print_profile(); printf("\n"); }
    }
    free(gkey);
  }
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
    else if (!strcmp(argv[i], "-P")) { paretomode = 1; }
    else if (!strcmp(argv[i], "-G")) cyclemode = 1;
    else if (!strcmp(argv[i], "-B")) { btmode = 1; paretoonly = 1; paretomode = 1; }
    else if (!strcmp(argv[i], "-Bx")) { btmode = 1; paretoonly = 1; paretomode = 1; btex = atoi(argv[++i]); }
    else if (!strcmp(argv[i], "-N")) { paretoonly = 1; paretomode = 1; }
    else if (!strcmp(argv[i], "-Q1")) potmode = 1;
    else if (!strcmp(argv[i], "-Q2")) potmode = 2;
    else if (!strcmp(argv[i], "-Q3")) potmode = 3;
    else if (!strcmp(argv[i], "-Q4")) potmode = 4;
    else if (!strcmp(argv[i], "-Q5")) potmode = 5;
    else if (!strcmp(argv[i], "-Q6")) potmode = 6;
    else if (!strcmp(argv[i], "-Q7")) potmode = 7;
    else if (!strcmp(argv[i], "-Gx")) { cyclemode = 1; gex = atoi(argv[++i]); }
    else if (!strcmp(argv[i], "-Px")) { paretomode = 1; pex = atoi(argv[++i]); }
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
  if (btmode) printf("BTX %lld %lld %lld %lld %lld %lld\n", btx[0], btx[1], btx[2], btx[3], btx[4], btx[5]);
  if (paretomode) printf("BTC %lld %lld %lld\n", btc[0], btc[1], btc[2]);
  if (paretomode) { printf("FZ"); for (int q = 0; q < 10; q++) printf(" %lld", fc[q]); for (int q = 0; q < 5; q++) printf(" %lld", fzcls[q]); printf("\n"); }
  if (cyclemode) { printf("G0"); for (int q = 0; q < 8; q++) printf(" %lld", g0c[q]); printf("\n"); }
  if (paretomode) { printf("F0"); for (int q = 0; q < 15; q++) printf(" %lld", f0c[q]); printf("\n"); }
  if (paretomode) for (int f = 0; f < 4; f++) printf("PARETO minfrozen %d%s profiles %lld every_ok %lld some_ok %lld maxima %lld\n", f, f == 3 ? "+" : "", pm_prof[f], pm_every[f], pm_some[f], pm_n[f]);
  for (int k = 0; k < NK; k++) printf("KIND %d free %lld (unhit %lld) frozen %lld (unhit %lld) %s\n", k, kexp[k][0], kexp_unhit[k][0], kexp[k][1], kexp_unhit[k][1], kname[k]);
  return 0;
}
