/* c4min.c: all-pairs configurations at the fewest frozen agents (k4/c4min.md §1-§2).

   For every strict profile of one k = 4 core:
   1. enumerate the valid pre-allocations of k4/c4x.md §1 (bases B_i ⊆ R_i, |B_i| <= 2, disjoint; value-based needs
      N_i = {g in R_i \ B_i : v_i(g) > v_i(B_i)}; valid iff every needed good is a one-good base); f = the fewest frozen
      agents; omega = f - (2n - m). If omega <= 0 the profile is trivially fine (no owner needed).
   2. for every key (NA, phi) of a pre-allocation with f frozen agents (NA its needed set, phi the frozen agents' goods),
      enumerate the all-pairs configurations: every free agent y holds a pair Q_y ⊆ M' = M \ NA whose part in
      U_y = R_y \ NA is admissible (every good of U_y outside Q_y is worth less than v_y(Q_y)), pairwise disjoint; the
      pool L = M' \ ∪ Q_y has omega goods. A configuration is completable if some free agent o (the owner, bundle
      Q_o ∪ L) threatens nobody: no x != o with max_h v_x((Q_o ∪ L) \ h) > v_x(H_x), H_x = {phi(x)} or Q_y ∩ U_y.
      (k4/c4min.md Lemma 1: C4min holds on the profile iff some configuration is completable.)
   3. features of each configuration, and for each potential (a lexicographic list of features, maximized) whether
      every / some maximum is completable.
   Cross-check (-X): the deficit of every min-frozen pre-allocation computed directly (removal-only test of
   k4/c4x.md §1), compared with the configuration test.

   stdin as k4/c4x.c: n m, per agent: d g_0 .. g_{d-1} T, then T lines of d values; then lo hi (agent 0's types).
   options: -p "f,f;f" potentials; -r N random profiles (seed -S); -x N examples; -X deficit cross-check;
            -D distance analysis (for each non-completable configuration, the least number of agents whose holding
            changes in a configuration better for the first potential). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
#define MAXM 48
#define MAXT 300
typedef uint64_t mask_t;
static inline int pc(mask_t x) { return __builtin_popcountll(x); }

static int n, m, d[MAXN], gl[MAXN][4], nt[MAXN], tv[MAXN][MAXT][4], cur[MAXN];
static mask_t Rm[MAXN];
static int vv[MAXN][MAXM];                   /* v_i(g) for the current profile, 0 if g not in R_i */
static int nex = 0, xcheck = 0, dist = 0, onlyf = -1, pareto = 0, onlyr0 = 0, nounf = 0, onlyA = 0;
static long long nA1, cov[4];
static long long nr0;
static long long par_every, par_some, par_n;

static int val(int i, mask_t S) { int s = 0; mask_t r = S & Rm[i]; while (r) { int g = __builtin_ctzll(r); s += vv[i][g]; r &= r - 1; } return s; }
static int minval(int i, mask_t S) {          /* least v_i over S (0 if S has a good outside R_i) */
  if (S & ~Rm[i]) return 0;
  int mn = 1 << 30; mask_t r = S; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] < mn) mn = vv[i][g]; r &= r - 1; } return mn;
}
/* agent i holding H strongly envies bundle X */
static int threat(int i, mask_t X, mask_t H) { if (!X) return 0; return val(i, X) - minval(i, X) > val(i, H); }
#define FOREIGN ((mask_t)1 << (MAXM - 1))    /* a good no agent values (m < MAXM - 1) */
static mask_t needs(int i, mask_t B) { int b = val(i, B); mask_t N = 0, r = Rm[i] & ~B; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] > b) N |= (mask_t)1 << g; r &= r - 1; } return N; }

/* ---- step 1: valid pre-allocations ---- */
static int nopt[MAXN]; static mask_t opt[MAXN][11];
static mask_t curB[MAXN];
typedef struct { mask_t NA; mask_t phi[MAXN]; } nkey_t;    /* phi[i] = frozen good or 0 */
static nkey_t *keys; static int nkeys, capkeys, fmin;
static long long nvalidP;
typedef struct { mask_t B[MAXN]; } pa_t;
static pa_t *minP; static int nminP, capminP;
static void add_key(mask_t NA, int nf) {
  if (nf > fmin) return;
  if (nf < fmin) { fmin = nf; nkeys = 0; nminP = 0; }
  nkey_t k; memset(&k, 0, sizeof k); k.NA = NA;
  for (int i = 0; i < n; i++) if (pc(curB[i]) == 1 && (curB[i] & NA)) k.phi[i] = curB[i];
  if (xcheck) { if (nminP == capminP) { capminP = capminP ? 2 * capminP : 256; minP = realloc(minP, capminP * sizeof(pa_t)); } memcpy(minP[nminP++].B, curB, sizeof(mask_t) * MAXN); }
  for (int q = 0; q < nkeys; q++) if (keys[q].NA == NA && !memcmp(keys[q].phi, k.phi, sizeof(mask_t) * n)) return;
  if (nkeys == capkeys) { capkeys = capkeys ? 2 * capkeys : 64; keys = realloc(keys, capkeys * sizeof(nkey_t)); }
  keys[nkeys++] = k;
}
static void genP(int i, mask_t used, mask_t sing, mask_t two, mask_t NA) {
  if (i == n) {
    if (NA & ~sing) return;
    nvalidP++;
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

/* ---- step 2: configurations ---- */
#define NF 24
static const char *fname[NF] = {"robF", "robfree", "-rhoF", "-poolexp", "safeall", "nvalid", "-poolthr1", "-rhoL",
  "-thrL", "rob", "-exposedL1", "toppairs", "-rhoLQ", "-poolvalF", "robfree+robF", "-maxrhoLQ", "sumlev", "leximin", "sumlevfree", "sumlevF", "poolopt", "-frozthr", "nvalid_nounf", "allrobF"};
typedef struct { mask_t H[MAXN]; mask_t L; int comp; int F[NF]; int v[MAXN]; } cfg_t;
static cfg_t *cf; static int ncf, capcf;
static int isfree[MAXN], freel[MAXN], nfree;
static mask_t U[MAXN], Mp;
static int nfopt[MAXN]; static mask_t fopt[MAXN][1200];

static int level(int i, mask_t S) {        /* #{T ⊆ R_i : v_i(T) < v_i(S)} */
  int x = val(i, S), l = 0, k = d[i];
  for (int t = 0; t < (1 << k); t++) { int s2 = 0; for (int q = 0; q < k; q++) if (t >> q & 1) s2 += vv[i][gl[i][q]]; l += s2 < x; }
  return l;
}
static int rho_of(int i, mask_t X, mask_t H) {   /* least number of goods of X ∩ U_i to remove so that (X minus them) with a foreign good no longer threatens H */
  mask_t S = X & U[i]; int best = 99;
  for (mask_t D = S;; D = (D - 1) & S) { if (pc(D) < best && !threat(i, (S & ~D) | FOREIGN, H)) best = pc(D); if (!D) break; }
  return best;
}

/* Is o a valid owner of configuration c?  The owner keeps X' = (Q_o ∪ L) \ C, which must contain an admissible base
   of o; the goods of C go one each to frozen agents that are no longer frozen once the owner's needs are taken from
   X' (their good is needed by nobody else); nobody x != o may be threatened by X' holding H_x (removal-only). */
static int owner_ok_u(const cfg_t *c, int o, int allow_unf) {
  mask_t Xo = c->H[o] | c->L, NAo = 0; int cand[MAXN], ncand = 0;
  for (int j = 0; j < n; j++) if (j != o) NAo |= needs(j, isfree[j] ? c->H[j] & U[j] : c->H[j]);
  if (allow_unf) for (int x = 0; x < n; x++) if (!isfree[x] && !(c->H[x] & NAo)) cand[ncand++] = x;
  for (mask_t C = 0;; C = (C - Xo) & Xo) {          /* every subset C of Xo, in increasing order */
    if (pc(C) <= ncand) {
      mask_t X = Xo & ~C; int ok = 1;
      /* admissible base of o inside X: some B ⊆ X ∩ U_o, |B| <= 2, with no good of U_o outside B worth more */
      { int adm = 0; mask_t S = X & U[o];
        if (!S) adm = !U[o];
        for (mask_t B = S; B && !adm; B = (B - 1) & S) if (pc(B) <= 2 && !(needs(o, B) & U[o])) adm = 1;
        ok = adm; }
      if (ok && C) { mask_t No = needs(o, X & Rm[o]); int unf = 0; for (int k = 0; k < ncand; k++) if (!(c->H[cand[k]] & No)) unf++; if (unf < pc(C)) ok = 0; }
      for (int x = 0; x < n && ok; x++) if (x != o && threat(x, X, isfree[x] ? c->H[x] & U[x] : c->H[x])) ok = 0;
      if (ok) return 1;
    }
    if (C == Xo) break;
  }
  return 0;
}
static int owner_ok(const cfg_t *c, int o) { return owner_ok_u(c, o, !nounf); }

static void features(cfg_t *c) {
  int robF = 0, robfree = 0, rhoF = 0, pe = 0, safe = 0, nv = 0, pt1 = 0, rl = 0, thrL = 0, ex1 = 0, tp = 0, rlq = 0, pvf = 0, mrlq = 0;
  mask_t L = c->L;
  for (int i = 0; i < n; i++) {
    mask_t H = c->H[i];
    if (!isfree[i]) {
      int r = rho_of(i, U[i], H); rhoF += r; robF += r == 0;
      pe += pc(L & U[i]); pvf += val(i, L & U[i]);
      rl += rho_of(i, L, H);
      if (threat(i, L | FOREIGN, H)) thrL++;
      /* threatened by L plus one more good of M' */
      { int t1 = 0; mask_t r2 = Mp & ~L; while (r2 && !t1) { int g = __builtin_ctzll(r2); if (threat(i, L | ((mask_t)1 << g) | FOREIGN, H)) t1 = 1; r2 &= r2 - 1; } pt1 += t1; }
      /* least over free owners o of the removal needed from Q_o ∪ L; max over frozen */
      { int best = 99; for (int q = 0; q < nfree; q++) { int o = freel[q]; int r2 = rho_of(i, c->H[o] | L, H); if (r2 < best) best = r2; } rlq += best; if (best > mrlq) mrlq = best; }
    } else {
      mask_t B = H & U[i];
      int rb = !threat(i, (U[i] & ~H) | FOREIGN, B); robfree += rb;
      if (threat(i, L | FOREIGN, B)) ex1++;
      /* holds its two best goods of U_i */
      { int b1 = -1, b2 = -1, g1 = -1, g2 = -1; mask_t r2 = U[i]; while (r2) { int g = __builtin_ctzll(r2); if (vv[i][g] > b1) { b2 = b1; g2 = g1; b1 = vv[i][g]; g1 = g; } else if (vv[i][g] > b2) { b2 = vv[i][g]; g2 = g; } r2 &= r2 - 1; }
        mask_t top = 0; if (g1 >= 0) top |= (mask_t)1 << g1; if (g2 >= 0) top |= (mask_t)1 << g2; tp += (H & U[i]) == top; }
    }
  }
  for (int x = 0; x < n; x++) {
    mask_t Hx = isfree[x] ? c->H[x] & U[x] : c->H[x]; int ok = 1;
    for (int q = 0; q < nfree && ok; q++) { int o = freel[q]; if (o != x && threat(x, c->H[o] | L, Hx)) ok = 0; }
    safe += ok;
  }
  for (int q = 0; q < nfree; q++) nv += owner_ok(c, freel[q]);
  { int ft = 0, nvn = 0;
    for (int x = 0; x < n; x++) if (!isfree[x]) { int th = 0; for (int q = 0; q < nfree && !th; q++) if (threat(x, c->H[freel[q]] | c->L, c->H[x])) th = 1; ft += th; }
    for (int q = 0; q < nfree; q++) nvn += owner_ok_u(c, freel[q], 0);
    c->F[21] = -ft; c->F[22] = nvn; }
  { int nf = 0; for (int x = 0; x < n; x++) nf += !isfree[x]; c->F[23] = robF == nf; }
  c->comp = nv > 0;
  for (int i = 0; i < n; i++) c->v[i] = val(i, isfree[i] ? c->H[i] & U[i] : c->H[i]);
  int *F = c->F;
  { int sl = 0, slf = 0, slF = 0, lv[MAXN];
    for (int i = 0; i < n; i++) { int l = level(i, isfree[i] ? c->H[i] & U[i] : c->H[i]); lv[i] = l; sl += l; if (isfree[i]) slf += l; else slF += l; }
    /* leximin as a number: sorted increasing, base 16, compared lexicographically = the vector sorted ascending */
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (lv[b] < lv[a]) { int t = lv[a]; lv[a] = lv[b]; lv[b] = t; }
    int lm = 0; for (int a = 0; a < n && a < 7; a++) lm = lm * 16 + lv[a];
    F[16] = sl; F[17] = lm; F[18] = slf; F[19] = slF; }
  { /* pool-optimal: no free agent has a pair inside Q_i ∪ L worth more to it */
    int po = 1;
    for (int q = 0; q < nfree && po; q++) {
      int i = freel[q]; mask_t S = (c->H[i] | c->L) & U[i]; int vi = val(i, c->H[i]);
      for (mask_t a = S; a && po; a &= a - 1) { int g = __builtin_ctzll(a); for (mask_t b = a & (a - 1); b; b &= b - 1) { int h = __builtin_ctzll(b); if (vv[i][g] + vv[i][h] > vi) { po = 0; break; } } if (vv[i][g] > vi) po = 0; }
    }
    F[20] = po; }
  F[0] = robF; F[1] = robfree; F[2] = -rhoF; F[3] = -pe; F[4] = safe; F[5] = nv; F[6] = -pt1; F[7] = -rl; F[8] = -thrL;
  F[9] = robF + robfree; F[10] = -ex1; F[11] = tp; F[12] = -rlq; F[13] = -pvf; F[14] = robF + robfree; F[15] = -mrlq;
}

static mask_t curH[MAXN];
static void genC(int k, mask_t used) {
  if (k == nfree) {
    if (ncf == capcf) { capcf = capcf ? 2 * capcf : 1024; cf = realloc(cf, (size_t)capcf * sizeof(cfg_t)); }
    cfg_t *c = &cf[ncf++]; memcpy(c->H, curH, sizeof curH); c->L = Mp & ~used;
    return;
  }
  int i = freel[k];
  for (int q = 0; q < nfopt[i]; q++) { mask_t S = fopt[i][q]; if (S & used) continue; curH[i] = S; genC(k + 1, used | S); }
}
static void configs_for_key(const nkey_t *K) {
  mask_t all = (m == 64) ? ~(mask_t)0 : (((mask_t)1 << m) - 1);
  Mp = all & ~K->NA; nfree = 0;
  for (int i = 0; i < n; i++) {
    U[i] = Rm[i] & Mp; isfree[i] = !K->phi[i]; curH[i] = K->phi[i];
    if (!isfree[i]) continue;
    freel[nfree++] = i; nfopt[i] = 0;
    for (int g = 0; g < m; g++) if (Mp >> g & 1) for (int h = g + 1; h < m; h++) if (Mp >> h & 1) {
      mask_t S = ((mask_t)1 << g) | ((mask_t)1 << h);
      if (needs(i, S & U[i]) & U[i]) continue;                       /* admissible: needs inside NA */
      if (nfopt[i] >= 1200) { fprintf(stderr, "too many pairs\n"); exit(3); }
      fopt[i][nfopt[i]++] = S;
    }
  }
  genC(0, 0);
}

/* ---- deficit cross-check (k4/c4x.md §1, removal-only) ---- */
static int deficitP(const mask_t *B) {
  mask_t NA = 0, all = (((mask_t)1 << m) - 1), used = 0; int fz[MAXN], S = 0;
  for (int i = 0; i < n; i++) { NA |= needs(i, B[i]); used |= B[i]; }
  mask_t J = all & ~used;
  for (int i = 0; i < n; i++) { fz[i] = pc(B[i]) == 1 && (B[i] & NA); S += fz[i] ? 0 : 2 - pc(B[i]); }
  if (pc(J) <= S) return pc(J) - S;
  int best = 1 << 20;
  for (int o = 0; o < n; o++) {
    if (fz[o]) continue;
    mask_t NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= needs(j, B[j]);
    for (mask_t C = J;; C = (C - 1) & J) {
      mask_t Xo = B[o] | (J & ~C); int ok = 1;
      for (int x = 0; x < n && ok; x++) if (x != o && threat(x, Xo, B[x])) ok = 0;
      if (ok) {
        mask_t NAp = NAo | needs(o, Xo & Rm[o]);
        int So = 0; for (int j = 0; j < n; j++) if (j != o) So += (pc(B[j]) == 1 && (B[j] & NAp)) ? 0 : 2 - pc(B[j]);
        if (pc(C) - So < best) best = pc(C) - So;
      }
      if (!C) break;
    }
  }
  return best;
}

/* ---- potentials ---- */
#define MAXPHI 48
static int nphi, phil[MAXPHI], phif[MAXPHI][6]; static char phin[MAXPHI][128];
static long long everyf[MAXPHI], somef[MAXPHI], nprof, nom, ncomp_none, nxbad, ncfg, nkeyfail, distcnt[MAXPHI][8];
static int exe[MAXPHI];
static void parse(const char *s) {
  nphi = 0;
  while (*s && nphi < MAXPHI) {
    int k = 0; phin[nphi][0] = 0;
    for (;;) { int f = (int)strtol(s, (char **)&s, 10); phif[nphi][k++] = f; strcat(phin[nphi], k == 1 ? "(" : ","); strcat(phin[nphi], fname[f]); if (*s == ',') { s++; continue; } break; }
    strcat(phin[nphi], ")"); phil[nphi++] = k; if (*s == ';') s++;
  }
}
static int cmpc(const cfg_t *a, const cfg_t *b, int p) { for (int k = 0; k < phil[p]; k++) { int f = phif[p][k]; if (a->F[f] != b->F[f]) return a->F[f] > b->F[f] ? 1 : -1; } return 0; }
static void print_prof(void) { for (int i = 0; i < n; i++) { printf(" ["); for (int k = 0; k < d[i]; k++) printf("%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); printf("]"); } }
static const nkey_t *print_key;
static void print_cfg(const cfg_t *c) {
  printf(" |"); for (int i = 0; i < n; i++) { printf(" %s{", (print_key ? !print_key->phi[i] : isfree[i]) ? "" : "F"); int f = 1; for (int g = 0; g < m; g++) if (c->H[i] >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}"); }
  printf(" L{"); int f = 1; for (int g = 0; g < m; g++) if (c->L >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}");
}

static void do_profile(void) {
  for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) vv[i][gl[i][k]] = tv[i][cur[i]][k];
  nprof++;
  fmin = 1 << 20; nkeys = 0; nminP = 0;
  genP(0, 0, 0, 0, 0);
  int omega = fmin - (2 * n - m);
  if (omega <= 0) return;
  if (onlyf >= 0 && fmin != onlyf) return;
  nom++;
  ncf = 0;
  int anycomp = 0;
  /* configurations of all keys together (the potentials compare across keys) */
  int *keyof = NULL; int capk = 0;
  for (int q = 0; q < nkeys; q++) {
    int before = ncf; configs_for_key(&keys[q]);
    int kc = 0;
    for (int c = before; c < ncf; c++) { features(&cf[c]); if (cf[c].comp) kc = 1; }
    if (ncf > capk) { capk = ncf + 1024; keyof = realloc(keyof, capk * sizeof(int)); }
    for (int c = before; c < ncf; c++) keyof[c] = q;
    anycomp |= kc;
    if (!kc) nkeyfail++;
  }
  if (onlyA) { int ok = 0; for (int c = 0; c < ncf; c++) if (cf[c].F[23]) ok = 1; if (!ok) { free(keyof); return; } nA1++; }
  if (onlyr0) { int mr = 0; for (int c = 0; c < ncf; c++) if (cf[c].F[9] > mr) mr = cf[c].F[9]; if (mr > 0) { free(keyof); return; } nr0++; if (nex) { printf("R0PROF %d %d", n, m); for (int i = 0; i < n; i++) { printf(" |"); for (int k = 0; k < d[i]; k++) printf(" %d:%d", gl[i][k], tv[i][cur[i]][k]); } printf("\n"); } }
  { int ar = 0; for (int c = 0; c < ncf; c++) if (cf[c].F[23]) ar = 1;
    if (fmin == 0) cov[0]++; else if (ar) cov[1]++; else if (fmin == 1) cov[2]++; else cov[3]++; }
  ncfg += ncf;
  if (!anycomp) { ncomp_none++; if (nex) { printf("NONE"); print_prof(); printf("\n"); } }
  if (xcheck) {
    int dmin = 1 << 20; for (int q = 0; q < nminP; q++) { int dd = deficitP(minP[q].B); if (dd < dmin) dmin = dd; }
    if ((dmin <= 0) != anycomp) { nxbad++; printf("XCHECK mismatch deficit %d configs %d:", dmin, anycomp); print_prof(); printf("\n"); }
  }
  if (pareto) {   /* every / some Pareto-maximal configuration (values of the holdings) completable? */
    int ev = 1, so = 0, badc = -1;
    for (int c = 0; c < ncf; c++) {
      int dom = 0;
      for (int e = 0; e < ncf && !dom; e++) {
        int ge = 1, gt = 0;
        for (int i = 0; i < n; i++) { if (cf[e].v[i] < cf[c].v[i]) { ge = 0; break; } if (cf[e].v[i] > cf[c].v[i]) gt = 1; }
        dom = ge && gt;
      }
      if (dom) continue;
      par_n++;
      if (cf[c].comp) so = 1; else { ev = 0; if (badc < 0) badc = c; }
    }
    if (!ev) { par_every++; if (nex && par_every <= nex) { printf("EX pareto:"); print_prof(); print_key = &keys[keyof[badc]]; print_cfg(&cf[badc]); print_key = NULL; printf("\n"); } }
    if (!so) par_some++;
  }
  for (int p = 0; p < nphi; p++) {
    int best = -1;
    for (int c = 0; c < ncf; c++) if (best < 0 || cmpc(&cf[c], &cf[best], p) > 0) best = c;
    int ev = 1, so = 0, bad = -1;
    for (int c = 0; c < ncf; c++) if (cmpc(&cf[c], &cf[best], p) == 0) { if (cf[c].comp) so = 1; else { ev = 0; if (bad < 0) bad = c; } }
    if (!ev) { everyf[p]++; if (exe[p] < nex) { exe[p]++; printf("EX every %s:", phin[p]); print_prof(); print_key = &keys[keyof[bad]]; print_cfg(&cf[bad]); print_key = NULL; printf("\n"); } }
    if (!so) somef[p]++;
    if (dist && p == 0) {
      for (int c = 0; c < ncf; c++) {
        if (cf[c].comp) continue;
        int bd = 7;
        for (int e = 0; e < ncf; e++) {
          if (cmpc(&cf[e], &cf[c], p) <= 0) continue;
          int h = 0; for (int i = 0; i < n; i++) h += cf[e].H[i] != cf[c].H[i];
          if (h < bd) bd = h;
        }
        distcnt[p][bd]++;
      }
    }
  }
  free(keyof);
}

int main(int argc, char **argv) {
  long long nr = 0; unsigned long long seed = 1; const char *phis = "9;1;2,1,3;2,1,4;4;2,1,7";
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-p")) phis = argv[++i];
    else if (!strcmp(argv[i], "-r")) nr = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-S")) seed = strtoull(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "-x")) nex = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-X")) xcheck = 1;
    else if (!strcmp(argv[i], "-D")) dist = 1;
    else if (!strcmp(argv[i], "-f")) onlyf = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-Q")) pareto = 1;
    else if (!strcmp(argv[i], "-R0")) onlyr0 = 1;
    else if (!strcmp(argv[i], "-U0")) nounf = 1;
    else if (!strcmp(argv[i], "-A")) onlyA = 1;
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
  }
  parse(phis);
  if (scanf("%d %d", &n, &m) != 2 || n > MAXN || m > MAXM - 2) return 2;
  for (int i = 0; i < n; i++) {
    if (scanf("%d", &d[i]) != 1) return 2;
    Rm[i] = 0; for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 2; Rm[i] |= (mask_t)1 << gl[i][k]; }
    if (scanf("%d", &nt[i]) != 1) return 2;
    for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 2;
    nopt[i] = 0; opt[i][nopt[i]++] = 0;
    for (int a = 0; a < d[i]; a++) opt[i][nopt[i]++] = (mask_t)1 << gl[i][a];
    for (int a = 0; a < d[i]; a++) for (int b = a + 1; b < d[i]; b++) opt[i][nopt[i]++] = ((mask_t)1 << gl[i][a]) | ((mask_t)1 << gl[i][b]);
  }
  int lo, hi; if (scanf("%d %d", &lo, &hi) != 2) { lo = 0; hi = nt[0]; }
  memset(vv, 0, sizeof vv);
  if (nr) {
    uint64_t s = seed * 0x9E3779B97F4A7C15ULL + 7;
    for (long long r = 0; r < nr; r++) { for (int i = 0; i < n; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; cur[i] = (int)(s % (uint64_t)nt[i]); } do_profile(); }
  } else {
    for (cur[0] = lo; cur[0] < hi; cur[0]++) {
      for (int i = 1; i < n; i++) cur[i] = 0;
      for (;;) { do_profile(); int i = n - 1; while (i >= 1 && ++cur[i] == nt[i]) { cur[i] = 0; i--; } if (i < 1) break; }
    }
  }
  printf("RESULT profiles %lld omega>=1 %lld configs %lld none %lld keyfail %lld xbad %lld paretomax %lld paretoevery %lld paretosome %lld rmax0 %lld allrobF %lld covZ %lld covF %lld f1 %lld uncovered %lld\n", nprof, nom, ncfg, ncomp_none, nkeyfail, nxbad, par_n, par_every, par_some, nr0, nA1, cov[0], cov[1], cov[2], cov[3]);
  for (int p = 0; p < nphi; p++) {
    printf("PHI %s every_fail %lld some_fail %lld", phin[p], everyf[p], somef[p]);
    if (dist && p == 0) { printf(" dist"); for (int k = 1; k < 8; k++) printf(" %lld", distcnt[p][k]); }
    printf("\n");
  }
  return 0;
}
