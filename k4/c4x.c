/* c4x.c: extremal valid pre-allocations for k = 4 cores (k4/c4x.md).

   For every strict profile of one core (agents' goods and their strict types from stdin), enumerate the set P of
   all valid pre-allocations (k4/lb4.md §1): bases B_i ⊆ R_i with |B_i| <= 2, pairwise disjoint; needs value-based,
   N_i = {g in R_i \ B_i : v_i(g) > v_i(B_i)} (the smallest needs the Definition allows; with strict types they are
   the pick needs for a one-good base and R_i for an empty base); J = the goods in no base; NA = ∪ N_i;
   valid iff (V1) J ∩ NA = ∅ and (V2) no good of a two-good base is in NA.
   A P in P is *completable* if some completion (owner o, or none) satisfies (OC4), in the sense of
   lean/EFX/PreAllocK.lean (SoundCompletion): frozen agents other than o get no junk, a free agent j != o gets at
   most 2 - |B_j| junk goods, o gets the rest; the owner's needs are taken from its bundle (-w0: from its base);
   (OC4): v_j(X_o \ h) <= v_j(X_j) for all j != o, h in X_o. The test is exact: every owner, every set K ⊆ J of
   junk goods left to the owner, and a search for disjoint protecting sets for the threatened agents.

   For each potential Φ (maximized), it counts the profiles where some Φ-maximum is not completable ("every" form
   fails) and where no Φ-maximum is completable ("some" form fails), and the profiles where no P in P is
   completable at all.

   stdin:  n m, then per agent: d g_0 .. g_{d-1} T, then T lines of d values (a strict type, values of g_0..);
           then lo hi (range of agent 0's type index).
   options: -w0 owner's needs from its base; -x N print up to N examples per potential and kind;
            -a also count, for every profile, whether any P is completable (always done when a "some" form fails);
            -s K R: only profiles whose index mod K == R (sampling / splitting); -r N random sample of N profiles
            (seed from -S); -3 allow one base of 3 or 4 goods (its agent must be the owner). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 6
#define MAXM 16
#define MAXT 300
#define MAXOPT 16


static int n, m, d[MAXN], gl[MAXN][4], nt[MAXN];
static int tv[MAXN][MAXT][4];            /* type values, local good order */
static int loc[MAXN][MAXM];              /* local index of global good g in R_i, or -1 */
static uint32_t Rmask[MAXN];
static int rodef_on = 0, efonly = 0;
static int wbase = 1, nex = 0, anyall = 0, allow3 = 0, verbose = 0, dump = 0;

/* base options per agent: local masks with popcount <= 2 (or <= 4 with -3) */
static int nopt[MAXN], optl[MAXN][MAXOPT], optsz[MAXN][MAXOPT];
static uint32_t optg[MAXN][MAXOPT];

/* assignments */
typedef struct { unsigned char o[MAXN]; uint32_t sing, J, two, big; } asg_t;
static asg_t *A; static int nA, capA;

/* per profile tables */
static int val[MAXN][16];                /* v_i(local subset) */
static uint32_t need[MAXN][MAXOPT];      /* global mask */
static int lev[MAXN][MAXOPT];
static int bval[MAXN][MAXOPT];
static int cur[MAXN];                    /* current type of each agent */

static inline int pc(uint32_t x) { return __builtin_popcount(x); }

static uint32_t tolocal(int i, uint32_t g) {
  uint32_t s = 0;
  for (int k = 0; k < d[i]; k++) if (g >> gl[i][k] & 1) s |= 1u << k;
  return s;
}
static inline int vg(int i, uint32_t g) { return val[i][tolocal(i, g)]; }   /* v_i of a global set */

static void gen_asg(int i, uint32_t used, unsigned char *o, int nbig) {
  if (i == n) {
    if (nA == capA) { capA = capA ? 2 * capA : 1024; A = realloc(A, capA * sizeof(asg_t)); }
    asg_t *a = &A[nA++]; memcpy(a->o, o, MAXN);
    uint32_t sing = 0, two = 0, big = 0, all = 0;
    for (int k = 0; k < n; k++) {
      uint32_t g = optg[k][o[k]]; all |= g;
      if (pc(g) == 1) sing |= g; else if (pc(g) == 2) two |= g; else if (pc(g) >= 3) big |= g;
    }
    a->sing = sing; a->two = two; a->big = big; a->J = ((1u << m) - 1) & ~all;
    return;
  }
  for (int k = 0; k < nopt[i]; k++) {
    if (optg[i][k] & used) continue;
    int b = optsz[i][k] >= 3;
    if (nbig + b > 1) continue;
    o[i] = k; gen_asg(i + 1, used | optg[i][k], o, nbig + b);
  }
}

static void setup_profile(void) {
  for (int i = 0; i < n; i++) {
    int *v = tv[i][cur[i]];
    for (int s = 0; s < (1 << d[i]); s++) { int x = 0; for (int k = 0; k < d[i]; k++) if (s >> k & 1) x += v[k]; val[i][s] = x; }
    for (int o = 0; o < nopt[i]; o++) {
      int s = optl[i][o], bv = val[i][s];
      bval[i][o] = bv;
      uint32_t nd = 0;
      for (int k = 0; k < d[i]; k++) if (!(s >> k & 1) && v[k] > bv) nd |= 1u << gl[i][k];
      need[i][o] = nd;
      if (efonly && pc(s) >= 2 && 2 * bv < val[i][(1 << d[i]) - 1]) need[i][o] = 0xFFFFFFFFu;   /* -E: multi-good bases must be envy-free */
      int l = 0; for (int t = 0; t < (1 << d[i]); t++) if (val[i][t] < bv) l++;
      lev[i][o] = l;
    }
  }
}

/* ---- the exact completability test ---- */
static int thr_n, thr_j[MAXN], thr_cap[MAXN], thr_th[MAXN];
static uint32_t thr_base[MAXN];
static int prot_search(int k, uint32_t rest) {
  if (k == thr_n) return 1;
  int j = thr_j[k]; uint32_t avail = rest & Rmask[j];
  int bj = vg(j, thr_base[k]);
  /* subsets C of avail with |C| <= cap and bj + v_j(C) >= th */
  for (uint32_t c = avail;; c = (c - 1) & avail) {
    if (c && pc(c) <= thr_cap[k] && bj + vg(j, c) >= thr_th[k] && prot_search(k + 1, rest & ~c)) return 1;
    if (!c) break;
  }
  return 0;
}

static int how_owner, how_K;
/* returns 1 if the assignment a is completable (a valid P assumed) */
static int completable(const asg_t *a) {
  uint32_t B[MAXN], NA = 0, NAo[MAXN];
  int frozen[MAXN], S = 0;
  for (int i = 0; i < n; i++) { B[i] = optg[i][a->o[i]]; NA |= need[i][a->o[i]]; }
  for (int i = 0; i < n; i++) {
    NAo[i] = 0; for (int j = 0; j < n; j++) if (j != i) NAo[i] |= need[j][a->o[j]];
    frozen[i] = pc(B[i]) == 1 && (B[i] & NA);
    if (!frozen[i] && pc(B[i]) <= 2) S += 2 - pc(B[i]);
  }
  uint32_t J = a->J;
  if (!a->big && pc(J) <= S) { how_owner = -1; how_K = 0; return 1; }
  for (int o = 0; o < n; o++) {
    if (frozen[o]) continue;
    if (a->big && pc(B[o]) < 3) continue;     /* a base of >= 3 goods must be the owner's */
    int vbo = vg(o, B[o]);
    for (uint32_t K = J;; K = (K - 1) & J) {
      uint32_t Xo = B[o] | K, rest = J & ~K;
      int vxo = vbo + vg(o, K & Rmask[o]);
      uint32_t NAp;
      if (wbase) {
        uint32_t no = 0;
        for (int k = 0; k < d[o]; k++) { uint32_t g = 1u << gl[o][k]; if (!(g & Xo) && tv[o][cur[o]][k] > vxo) no |= g; }
        NAp = NAo[o] | no;
      } else NAp = NA;
      int capsum = 0, capj[MAXN];
      for (int j = 0; j < n; j++) {
        if (j == o) continue;
        int fz = pc(B[j]) == 1 && (B[j] & NAp);
        capj[j] = fz ? 0 : 2 - pc(B[j]);
        capsum += capj[j];
      }
      if (pc(rest) <= capsum) {
        thr_n = 0; int bad = 0;
        for (int j = 0; j < n && !bad; j++) {
          if (j == o) continue;
          uint32_t q = Xo & Rmask[j];
          if (pc(q) < 2) continue;                      /* one relevant good is worth <= v_j(B_j) by validity */
          int th = vg(j, q);
          if (!(Xo & ~Rmask[j])) {                      /* X_o ⊆ R_j: remove j's least good of X_o */
            int mn = 1 << 30; for (int k = 0; k < d[j]; k++) if (q >> gl[j][k] & 1) if (tv[j][cur[j]][k] < mn) mn = tv[j][cur[j]][k];
            th -= mn;
          }
          if (th > vg(j, B[j])) {
            if (capj[j] == 0) { bad = 1; break; }
            thr_j[thr_n] = j; thr_cap[thr_n] = capj[j]; thr_th[thr_n] = th; thr_base[thr_n] = B[j]; thr_n++;
          }
        }
        if (!bad && prot_search(0, rest)) { how_owner = o; how_K = K; return 1; }
      }
      if (!K) break;
    }
  }
  return 0;
}

/* removal-only test (a sufficient condition): owner's needs from its base, all slots interchangeable, every agent
   other than the owner judged with its base alone: some C ⊆ J with |C| = min(|J|, S_o) leaves no agent threatened
   by X_o = B_o ∪ (J \ C). Returns 1 and sets ro_def = 0, or 0 and sets ro_def = min over owners of (the least
   number of goods to keep out of W_o = B_o ∪ J so that nobody is threatened) - S_o. */
static int ro_def;
static int threatened_by(int j, uint32_t Xo, uint32_t Bj) {
  uint32_t q = Xo & Rmask[j];
  if (pc(q) < 2) return 0;
  int th = vg(j, q);
  if (!(Xo & ~Rmask[j])) { int mn = 1 << 30; for (int k = 0; k < d[j]; k++) if (q >> gl[j][k] & 1) if (tv[j][cur[j]][k] < mn) mn = tv[j][cur[j]][k]; th -= mn; }
  return th > vg(j, Bj);
}
static int completable_ro(const asg_t *a) {
  uint32_t B[MAXN], NA = 0;
  int frozen[MAXN], cap[MAXN], S = 0;
  for (int i = 0; i < n; i++) { B[i] = optg[i][a->o[i]]; NA |= need[i][a->o[i]]; }
  for (int i = 0; i < n; i++) {
    frozen[i] = pc(B[i]) == 1 && (B[i] & NA);
    cap[i] = (frozen[i] || pc(B[i]) > 2) ? 0 : 2 - pc(B[i]); S += cap[i];
  }
  uint32_t J = a->J;
  if (!a->big && pc(J) <= S) { ro_def = pc(J) - S; return 1; }
  int bestdef = 1 << 20;
  for (int o = 0; o < n; o++) {
    if (frozen[o]) continue;
    if (a->big && pc(B[o]) < 3) continue;
    int So = S - cap[o], beta = 1 << 20;
    for (uint32_t C = J;; C = (C - 1) & J) {
      if (pc(C) < beta) {
        uint32_t Xo = B[o] | (J & ~C); int ok = 1;
        for (int j = 0; j < n && ok; j++) if (j != o && threatened_by(j, Xo, B[j])) ok = 0;
        if (ok) beta = pc(C);
      }
      if (!C) break;
    }
    int def = beta - So;
    if (def < bestdef) bestdef = def;
  }
  ro_def = bestdef;
  return bestdef <= 0;
}

/* ---- potentials: lexicographic lists of features (all maximized) ---- */
#define NFEAT 18
static const char *featname[NFEAT] = {
  "sumlev", "sum2lev", "leximax", "leximin", "sumval", "sumvalnorm", "-frozen", "upgraded", "slots", "-exposed",
  "-empty", "junk", "-upgraded", "frozen-sumlev", "frozen-leximin", "free-sumlev", "-exposed0", "-rodef"
};
#define MAXPHI 64
static int nphi, phil[MAXPHI], phif[MAXPHI][6];
static char phiname[MAXPHI][96];
static const char *default_phis =
  "0;1;2;3;4;5;6;7;8;9;6,0;6,3;6,2;6,1;0,6;6,9;6,9,0;6,4;3,6;6,10,0;6,7,0;6,12,0;6,8;6,8,0;6,8,3;6,8,2;"
  "6,8,9;6,9,8;6,11;6,13;6,14;6,15;6,8,13;6,8,14;6,8,15;8,6;6,16;6,8,16;6,16,8;6,8,16,0;6,8,16,3";
static long long every_fail[MAXPHI], some_fail[MAXPHI], nprof, nocomp, nvalid, ncompl_tested;
static int exc_e[MAXPHI], exc_s[MAXPHI];

static void parse_phis(const char *spec) {
  nphi = 0; const char *p = spec;
  while (*p && nphi < MAXPHI) {
    int k = 0; char *name = phiname[nphi]; name[0] = 0;
    for (;;) {
      int f = (int)strtol(p, (char **)&p, 10);
      phif[nphi][k++] = f;
      strcat(name, k == 1 ? "(" : ","); strcat(name, featname[f]);
      if (*p == ',') { p++; continue; }
      break;
    }
    strcat(name, ")"); phil[nphi] = k; nphi++;
    if (*p == ';') p++;
  }
}

static void features(const asg_t *a, long long *F) {
  long long sl = 0, s2 = 0, lmx = 0, lmn = 0, sv = 0, svn = 0, fsl = 0, flmn = 0, gsl = 0;
  int nF = 0, nU = 0, nE = 0, S = 0, D = 0, D0 = 0;
  uint32_t NA = 0;
  for (int i = 0; i < n; i++) NA |= need[i][a->o[i]];
  long long totprod = 1; int tot[MAXN];
  for (int i = 0; i < n; i++) { tot[i] = val[i][(1 << d[i]) - 1]; totprod *= tot[i]; }
  for (int i = 0; i < n; i++) {
    int o = a->o[i], l = lev[i][o]; uint32_t B = optg[i][o];
    sl += l; s2 += 1LL << l; lmx += 1LL << (4 * l); lmn += 1LL << (4 * (15 - l)); sv += bval[i][o];
    svn += (long long)bval[i][o] * (totprod / tot[i]);
    int fz = pc(B) == 1 && (B & NA);
    nF += fz; nU += pc(B) == 2; nE += pc(B) == 0;
    if (fz) { fsl += l; flmn += 1LL << (4 * (15 - l)); } else gsl += l;
    if (!fz && pc(B) <= 2) S += 2 - pc(B);
    /* exposed: threatened by the whole junk with its base */
    uint32_t q = a->J & Rmask[i];
    if (pc(q) >= 2) {
      int th = vg(i, q);
      if (!(a->J & ~Rmask[i])) { int mn = 1 << 30; for (int k = 0; k < d[i]; k++) if (q >> gl[i][k] & 1) if (tv[i][cur[i]][k] < mn) mn = tv[i][cur[i]][k]; th -= mn; }
      if (th > bval[i][o]) { D++; if (fz || pc(B) == 2) D0++; }
    }
  }
  F[16] = -D0;
  F[17] = 0;   /* -rodef: filled in by do_profile for the pre-allocations with the fewest frozen agents (-R) */
  F[0] = sl; F[1] = s2; F[2] = lmx; F[3] = -lmn; F[4] = sv; F[5] = svn; F[6] = -nF; F[7] = nU; F[8] = S; F[9] = -D;
  F[10] = -nE; F[11] = pc(a->J); F[12] = -nU; F[13] = fsl; F[14] = -flmn; F[15] = gsl;
}

static int cmpphi(const long long *x, const long long *y, int p) {   /* >0 if x better */
  for (int k = 0; k < phil[p]; k++) { long long a = x[phif[p][k]], b = y[phif[p][k]]; if (a != b) return a > b ? 1 : -1; }
  return 0;
}

static void print_profile(void) {
  printf(" types");
  for (int i = 0; i < n; i++) { printf(" ["); for (int k = 0; k < d[i]; k++) printf("%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); printf("]"); }
}
static void print_asg(const asg_t *a) {
  printf(" bases");
  for (int i = 0; i < n; i++) { uint32_t B = optg[i][a->o[i]]; printf(" {"); int f = 1; for (int g = 0; g < m; g++) if (B >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}"); }
  printf(" J {"); int f = 1; for (int g = 0; g < m; g++) if (a->J >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}");
}

static int *validlist; static long long *feat; static signed char *comp;

static void do_profile(void) {
  setup_profile();
  int nv = 0;
  for (int x = 0; x < nA; x++) {
    const asg_t *a = &A[x]; uint32_t ok = ~a->sing;
    int good = 1;
    for (int i = 0; i < n; i++) if (need[i][a->o[i]] & ok) { good = 0; break; }
    if (good) validlist[nv++] = x;
  }
  nprof++; nvalid += nv;
  for (int k = 0; k < nv; k++) { features(&A[validlist[k]], &feat[(size_t)k * NFEAT]); comp[k] = -1; }
  if (rodef_on) {   /* the deficit only on the pre-allocations with the fewest frozen agents; the others get -1000 */
    long long mf = -1000;
    for (int k = 0; k < nv; k++) if (feat[(size_t)k * NFEAT + 6] > mf) mf = feat[(size_t)k * NFEAT + 6];
    for (int k = 0; k < nv; k++) {
      if (feat[(size_t)k * NFEAT + 6] == mf) { completable_ro(&A[validlist[k]]); feat[(size_t)k * NFEAT + 17] = -ro_def; }
      else feat[(size_t)k * NFEAT + 17] = -1000;
    }
  }
  int anysomefail = 0;
  for (int p = 0; p < nphi; p++) {
    int best = 0;
    for (int k = 1; k < nv; k++) if (cmpphi(&feat[(size_t)k * NFEAT], &feat[(size_t)best * NFEAT], p) > 0) best = k;
    int ef = 0, sok = 0, efk = -1;
    for (int k = 0; k < nv; k++) {
      if (cmpphi(&feat[(size_t)k * NFEAT], &feat[(size_t)best * NFEAT], p) != 0) continue;
      if (comp[k] < 0) { comp[k] = completable(&A[validlist[k]]); ncompl_tested++; }
      if (comp[k]) sok = 1; else { ef = 1; if (efk < 0) efk = k; }
    }
    if (ef) {
      every_fail[p]++;
      if (exc_e[p] < nex) { exc_e[p]++; printf("EX every %s:", phiname[p]); print_profile(); print_asg(&A[validlist[efk]]); printf("\n"); }
    }
    if (!sok) {
      some_fail[p]++; anysomefail = 1;
      if (exc_s[p] < nex) { exc_s[p]++; printf("EX some %s:", phiname[p]); print_profile(); print_asg(&A[validlist[efk]]); printf("\n"); }
    }
  }
  if (dump) {
    for (int k = 0; k < nv; k++) {
      const asg_t *a = &A[validlist[k]];
      int c = completable(a);
      uint32_t NA = 0; for (int i = 0; i < n; i++) NA |= need[i][a->o[i]];
      printf("P"); print_asg(a); printf(" lev");
      for (int i = 0; i < n; i++) printf(" %d", lev[i][a->o[i]]);
      printf(" frozen");
      for (int i = 0; i < n; i++) { uint32_t B = optg[i][a->o[i]]; if (pc(B) == 1 && (B & NA)) printf(" %d", i); }
      printf(" | %s", c ? "COMPLETABLE" : "stuck");
      if (c) { printf(" owner %d K {", how_owner); for (int g = 0; g < m; g++) if (how_K >> g & 1) printf(" %d", g); printf(" }"); }
      printf("\n");
    }
  }
  if (verbose) {
    int nc = 0;
    for (int k = 0; k < nv; k++) { if (comp[k] < 0) { comp[k] = completable(&A[validlist[k]]); ncompl_tested++; } nc += comp[k]; }
    printf("PROF"); for (int i = 0; i < n; i++) printf(" %d", cur[i]); printf(" %d %d", nv, nc);
    for (int p = 0; p < nphi; p++) {
      int best = 0, ev = 1, so = 0;
      for (int k = 1; k < nv; k++) if (cmpphi(&feat[(size_t)k * NFEAT], &feat[(size_t)best * NFEAT], p) > 0) best = k;
      for (int k = 0; k < nv; k++) if (cmpphi(&feat[(size_t)k * NFEAT], &feat[(size_t)best * NFEAT], p) == 0) { if (comp[k]) so = 1; else ev = 0; }
      printf(" %d%d", ev, so);
    }
    printf("\n");
  }
  if (anysomefail || anyall) {
    int any = 0;
    for (int k = 0; k < nv && !any; k++) { if (comp[k] < 0) { comp[k] = completable(&A[validlist[k]]); ncompl_tested++; } any = comp[k]; }
    if (!any) { nocomp++; if (nocomp <= nex) { printf("EX nocomp:"); print_profile(); printf("\n"); } }
  }
}

int main(int argc, char **argv) {
  long long smod = 1, srem = 0, nrand = 0; unsigned long long seed = 1; const char *phis = default_phis;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-w0")) wbase = 0;
    else if (!strcmp(argv[i], "-x")) nex = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-a")) anyall = 1;
    else if (!strcmp(argv[i], "-v")) verbose = 1;
    else if (!strcmp(argv[i], "-d")) dump = 1;
    else if (!strcmp(argv[i], "-p")) phis = argv[++i];
    else if (!strcmp(argv[i], "-R")) rodef_on = 1;
    else if (!strcmp(argv[i], "-E")) efonly = 1;
    else if (!strcmp(argv[i], "-3")) allow3 = 1;
    else if (!strcmp(argv[i], "-s")) { smod = atoll(argv[++i]); srem = atoll(argv[++i]); }
    else if (!strcmp(argv[i], "-r")) nrand = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-S")) seed = strtoull(argv[++i], 0, 10);
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
  }
  if (scanf("%d %d", &n, &m) != 2) return 2;
  for (int i = 0; i < n; i++) {
    if (scanf("%d", &d[i]) != 1) return 2;
    for (int k = 0; k < d[i]; k++) if (scanf("%d", &gl[i][k]) != 1) return 2;
    if (scanf("%d", &nt[i]) != 1) return 2;
    for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 2;
    Rmask[i] = 0; for (int g = 0; g < m; g++) loc[i][g] = -1;
    for (int k = 0; k < d[i]; k++) { Rmask[i] |= 1u << gl[i][k]; loc[i][gl[i][k]] = k; }
    nopt[i] = 0;
    for (int s = 0; s < (1 << d[i]); s++) {
      if (pc(s) > 2 && !allow3) continue;
      if (pc(s) > 4) continue;
      optl[i][nopt[i]] = s; optsz[i][nopt[i]] = pc(s);
      uint32_t g = 0; for (int k = 0; k < d[i]; k++) if (s >> k & 1) g |= 1u << gl[i][k];
      optg[i][nopt[i]] = g; nopt[i]++;
    }
  }
  int lo, hi; if (scanf("%d %d", &lo, &hi) != 2) { lo = 0; hi = nt[0]; }
  unsigned char o[MAXN] = {0};
  gen_asg(0, 0, o, 0);
  parse_phis(phis);
  validlist = malloc(sizeof(int) * nA); feat = malloc(sizeof(long long) * (size_t)nA * NFEAT); comp = malloc(nA);
  int K;
  if (verbose && scanf("%d", &K) == 1) {
    for (int r = 0; r < K; r++) { for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2; do_profile(); }
  } else if (nrand) {
    uint64_t s = seed * 0x9E3779B97F4A7C15ULL + 12345;
    for (long long r = 0; r < nrand; r++) {
      for (int i = 0; i < n; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; cur[i] = (int)(s % (uint64_t)nt[i]); }
      do_profile();
    }
  } else {
    long long idx = 0;
    for (cur[0] = lo; cur[0] < hi; cur[0]++) {
      for (int i = 1; i < n; i++) cur[i] = 0;
      for (;;) {
        if (idx % smod == srem) do_profile();
        idx++;
        int i = n - 1;
        while (i >= 1 && ++cur[i] == nt[i]) { cur[i] = 0; i--; }
        if (i < 1) break;
      }
    }
  }
  printf("RESULT asg %d profiles %lld valid %lld tested %lld nocomp %lld\n", nA, nprof, nvalid, ncompl_tested, nocomp);
  for (int p = 0; p < nphi; p++) printf("PHI %s every_fail %lld some_fail %lld\n", phiname[p], every_fail[p], some_fail[p]);
  return 0;
}
