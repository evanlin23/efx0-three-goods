/* red.c: configurations with one frozen agent (f = 1) as all-pairs allocations of the reduced instance
   I' = I - x - g (k4/c4min_reduce.md). Written from the definitions of k4/c4min.md §1 and k4/c4x.md §1; shares no code
   with k4/c4min.c (the Python twin is k4/red_lib.py).

   For every strict profile of one k = 4 core:
   - f = 0 iff the agents have pairwise disjoint admissible sets (A ⊆ R_i, 1 <= |A| <= 2, every good of R_i \ A worth
     less than A). Otherwise the keys (g, x): g = top of x, and the agents y != x have pairwise disjoint admissible sets
     for U_y = R_y \ {g} avoiding g. f = 1 iff some key exists (then omega = m - 2n + 1); else f >= 2.
   - configurations at a key: pairs Q_y ⊆ M \ {g} (y != x), pairwise disjoint, Q_y ∩ U_y admissible for U_y; the pool L
     is the rest (omega goods).
   - owner test (k4/c4min.md §1): owner o free; C ⊆ X = Q_o ∪ L with |C| <= 1, and |C| = 1 only if x unfreezes (no free
     y != o has v_y(g) > v_y(Q_y), and not g ∈ R_o with v_o(g) > v_o(X \ C)); X \ C contains an admissible set of o; no
     agent other than o strongly envies X \ C holding its holding ({g} for x, Q_y for free y).
   Features of a configuration: r = robust free agents (v_y(Q_y ∩ U_y) >= v_y(U_y \ Q_y)); lamU = sum of levels over
   U_y; lamR = sum of levels over R_y plus the level of {g} in R_x; t = [v_x(L ∩ U_x) > v_x(g)]; p = |L ∩ U_x|;
   terminals = free y with g ∈ R_y and v_y(g) > v_y(Q_y); pool-optimal = no free y has a pair S ⊆ Q_y ∪ L worth more
   than Q_y.

   stdin: n m; per agent: d g_0 .. g_{d-1} T, then T lines of d values; then "R seed" (R = 0: every profile; R > 0:
   R random profiles). Output: one line of counters "name value". Option -x N prints up to N examples per failure. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
#define MAXM 24
#define MAXT 300
typedef uint32_t mask_t;
static inline int pc(mask_t x) { return __builtin_popcount(x); }

static int n, m, d[MAXN], gl[MAXN][4], nt[MAXN], tv[MAXN][MAXT][4], cur[MAXN];
static mask_t Rm[MAXN];
static int vv[MAXN][MAXM], top[MAXN];
static int nex = 0;

static int val(int i, mask_t S) { int s = 0; mask_t r = S & Rm[i]; while (r) { int h = __builtin_ctz(r); s += vv[i][h]; r &= r - 1; } return s; }
static int threat(int i, mask_t X, int hv) {         /* agent i with holding value hv strongly envies X */
  if (!X) return 0;
  int s = 0, mn = 1 << 30; mask_t r = X;
  while (r) { int h = __builtin_ctz(r); int w = (Rm[i] >> h & 1) ? vv[i][h] : 0; s += w; if (w < mn) mn = w; r &= r - 1; }
  return s - mn > hv;
}
static int admissible(int i, mask_t A, mask_t U) {
  if (!A || (A & ~U) || pc(A) > 2) return 0;
  int a = val(i, A); mask_t r = U & ~A;
  while (r) { int h = __builtin_ctz(r); if (vv[i][h] >= a) return 0; r &= r - 1; }
  return 1;
}
static int has_adm(int i, mask_t Y, mask_t U) {      /* Y ∩ U contains an admissible set of i (for U) */
  mask_t S = Y & U, r1 = S;
  while (r1) { int a = __builtin_ctz(r1); mask_t A = (mask_t)1 << a;
    if (admissible(i, A, U)) return 1;
    mask_t r2 = r1 & (r1 - 1);
    while (r2) { int b = __builtin_ctz(r2); if (admissible(i, A | ((mask_t)1 << b), U)) return 1; r2 &= r2 - 1; }
    r1 &= r1 - 1; }
  return 0;
}
static int level(int i, mask_t S, mask_t U) {         /* #{T ⊆ U : v_i(T) < v_i(S)} */
  int w = val(i, S), c = 0; mask_t T = 0;
  do { if (val(i, T) < w) c++; T = (T - U) & U; } while (T);
  return c;
}

/* ---- disjoint admissible systems ---- */
static int nso[MAXN]; static mask_t so[MAXN][64];
static int sys_rec(int k, int na, const int *ag, mask_t used) {
  if (k == na) return 1;
  int y = ag[k];
  for (int q = 0; q < nso[y]; q++) if (!(so[y][q] & used) && sys_rec(k + 1, na, ag, used | so[y][q])) return 1;
  return 0;
}
static int disjoint_system(int na, const int *ag, const mask_t *U, mask_t avoid) {
  for (int k = 0; k < na; k++) {
    int y = ag[k]; nso[y] = 0; mask_t S = U[y] & ~avoid, r1 = S;
    while (r1) { int a = __builtin_ctz(r1); mask_t A = (mask_t)1 << a;
      if (admissible(y, A, U[y])) so[y][nso[y]++] = A;
      mask_t r2 = r1 & (r1 - 1);
      while (r2) { int b = __builtin_ctz(r2); mask_t B = A | ((mask_t)1 << b); if (admissible(y, B, U[y])) so[y][nso[y]++] = B; r2 &= r2 - 1; }
      r1 &= r1 - 1; }
    if (!nso[y]) return 0;
  }
  return sys_rec(0, na, ag, 0);
}

/* ---- configurations at a key ---- */
typedef struct {
  mask_t Q[MAXN], L;
  int r, lamU, lamR, t, p, nterm, poolopt, nfv, ndx, comp, inj, lx, vp;
  mask_t terms, fv, dx, compo, npo, rob;  /* bitsets of agents (npo: not pool-optimal) */
} cfg_t;
typedef struct { int g, x, omega, nfree, free[MAXN], lx; mask_t U[MAXN], Mp; cfg_t *c; int nc, cap; } rkey_t;
static rkey_t keys[MAXN]; static int nkeys;
static int npairs[MAXN]; static mask_t pairs[MAXN][300];
static mask_t curQ[MAXN];

static void eval_cfg(rkey_t *K, cfg_t *c) {
  int x = K->x, g = K->g; mask_t gb = (mask_t)1 << g;
  c->r = c->lamU = 0; c->lamR = K->lx; c->nterm = 0; c->terms = 0; c->poolopt = 1; c->npo = 0; c->rob = 0;
  for (int k = 0; k < K->nfree; k++) {
    int y = K->free[k]; mask_t Q = c->Q[y], U = K->U[y];
    int vq = val(y, Q);
    if (vq >= val(y, U & ~Q)) { c->r++; c->rob |= 1u << y; }
    c->lamU += level(y, Q, U); c->lamR += level(y, Q, Rm[y]);
    if ((Rm[y] & gb) && vv[y][g] > vq) { c->nterm++; c->terms |= 1u << y; }
    /* pool-optimality in I' */
    mask_t W = Q | c->L, r1 = W; int po = 1;
    while (r1 && po) { int a = __builtin_ctz(r1); mask_t r2 = r1 & (r1 - 1);
      while (r2) { int b = __builtin_ctz(r2); if (val(y, ((mask_t)1 << a) | ((mask_t)1 << b)) > vq) { po = 0; break; } r2 &= r2 - 1; }
      r1 &= r1 - 1; }
    if (!po) { c->poolopt = 0; c->npo |= 1u << y; }
  }
  int vg = vv[x][g];
  c->vp = val(x, c->L & K->U[x]); c->lx = K->lx;
  c->t = c->vp > vg;
  c->p = pc(c->L & K->U[x]);
  c->nfv = c->ndx = 0; c->fv = c->dx = 0; c->comp = 0; c->compo = 0;
  { int nthr[MAXN] = {0};                /* threat-injectivity: every free agent threatened by at most one owner */
    for (int k = 0; k < K->nfree; k++) { int o = K->free[k]; mask_t X = c->Q[o] | c->L;
      for (int j = 0; j < K->nfree; j++) { int y = K->free[j]; if (y != o && threat(y, X, val(y, c->Q[y]))) nthr[y]++; } }
    c->inj = 1; for (int j = 0; j < K->nfree; j++) if (nthr[K->free[j]] > 1) c->inj = 0; }
  for (int k = 0; k < K->nfree; k++) {
    int o = K->free[k]; mask_t X = c->Q[o] | c->L;
    int fvalid = 1;
    for (int j = 0; j < K->nfree && fvalid; j++) { int y = K->free[j]; if (y != o && threat(y, X, val(y, c->Q[y]))) fvalid = 0; }
    int xt = threat(x, X, vg);
    if (fvalid) { c->nfv++; c->fv |= 1u << o; }
    if (xt) { c->ndx++; c->dx |= 1u << o; }
    int ok = fvalid && !xt;
    if (!ok) {
      /* unfreezing: no other free agent needs g */
      int other = 0;
      for (int j = 0; j < K->nfree; j++) { int y = K->free[j]; if (y != o && (Rm[y] & gb) && vv[y][g] > val(y, c->Q[y])) other = 1; }
      if (!other) {
        mask_t r = X;
        while (r && !ok) { int h = __builtin_ctz(r); r &= r - 1; mask_t Y = X & ~((mask_t)1 << h);
          if (!has_adm(o, Y, K->U[o])) continue;
          if ((Rm[o] & gb) && vv[o][g] > val(o, Y)) continue;
          if (threat(x, Y, vg)) continue;
          int bad = 0;
          for (int j = 0; j < K->nfree && !bad; j++) { int y = K->free[j]; if (y != o && threat(y, Y, val(y, c->Q[y]))) bad = 1; }
          if (!bad) ok = 1; }
      }
    }
    if (ok) { c->comp = 1; c->compo |= 1u << o; }
  }
}
static void gen_cfg(rkey_t *K, int k, mask_t used) {
  if (k == K->nfree) {
    if (K->nc == K->cap) { K->cap = K->cap ? 2 * K->cap : 256; K->c = realloc(K->c, K->cap * sizeof(cfg_t)); }
    cfg_t *c = &K->c[K->nc++]; memset(c, 0, sizeof *c);
    for (int j = 0; j < K->nfree; j++) c->Q[K->free[j]] = curQ[K->free[j]];
    c->L = K->Mp & ~used;
    eval_cfg(K, c);
    return;
  }
  int y = K->free[k];
  for (int q = 0; q < npairs[y]; q++) if (!(pairs[y][q] & used)) { curQ[y] = pairs[y][q]; gen_cfg(K, k + 1, used | pairs[y][q]); }
}
static void build_key(rkey_t *K) {
  K->nc = 0;
  for (int k = 0; k < K->nfree; k++) {
    int y = K->free[k]; npairs[y] = 0;
    mask_t r1 = K->Mp;
    while (r1) { int a = __builtin_ctz(r1); mask_t r2 = r1 & (r1 - 1);
      while (r2) { int b = __builtin_ctz(r2); mask_t Q = ((mask_t)1 << a) | ((mask_t)1 << b);
        if (admissible(y, Q & K->U[y], K->U[y])) pairs[y][npairs[y]++] = Q;
        r2 &= r2 - 1; }
      r1 &= r1 - 1; }
  }
  gen_cfg(K, 0, 0);
}

/* ---- counters ---- */
#define NCNT 128
static const char *cname[NCNT]; static long long cval[NCNT]; static int ncnt;
static int cid(const char *s) { for (int i = 0; i < ncnt; i++) if (!strcmp(cname[i], s)) return i; cname[ncnt] = s; return ncnt++; }
#define INC(s) (cval[cid(s)]++)
#define ADD(s, v) (cval[cid(s)] += (v))

static void print_profile(const char *tag) {
  printf("EX %s n=%d m=%d vals=", tag, n, m);
  for (int i = 0; i < n; i++) { printf("%s{", i ? "," : "["); for (int k = 0; k < d[i]; k++) printf("%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); printf("}"); }
  printf("]\n");
}
static int nexs[NCNT];
static void example(const char *tag) { int i = cid(tag); if (nexs[i] < nex) { nexs[i]++; print_profile(tag); } }

/* lexicographic potentials over a configuration (maximized) */
enum { F_R, F_LAMU, F_LAMR, F_MT, F_MP, F_MTERM, F_LX, F_MVP, F_MNDX, NF };
static const char *fnames[NF] = {"r", "lamU", "lamR", "mt", "mp", "mterm", "lx", "mvp", "mndx"};
static int feat(const cfg_t *c, int f) {
  switch (f) { case F_R: return c->r; case F_LAMU: return c->lamU; case F_LAMR: return c->lamR; case F_MT: return -c->t;
    case F_MP: return -c->p; case F_MTERM: return -c->nterm; case F_LX: return c->lx; case F_MVP: return -c->vp;
    case F_MNDX: return -c->ndx; }
  return 0;
}
/* user potentials (-p "f,f;f,f"): global over all keys */
#define MAXUP 16
static int nup, upn[MAXUP], up[MAXUP][8]; static char upname[MAXUP][80], upE[MAXUP][100], upF[MAXUP][100], upS[MAXUP][100];
static void parse_pots(const char *spec) {
  char buf[1024]; strncpy(buf, spec, sizeof buf - 1); buf[sizeof buf - 1] = 0;
  for (char *save1, *tok = strtok_r(buf, ";", &save1); tok && nup < MAXUP; tok = strtok_r(NULL, ";", &save1)) {
    snprintf(upname[nup], sizeof upname[nup], "%s", tok); upn[nup] = 0;
    char b2[200]; strncpy(b2, tok, sizeof b2 - 1); b2[sizeof b2 - 1] = 0;
    for (char *save2, *f = strtok_r(b2, ",", &save2); f; f = strtok_r(NULL, ",", &save2)) {
      int k = -1; for (int q = 0; q < NF; q++) if (!strcmp(f, fnames[q])) k = q;
      if (k < 0) { fprintf(stderr, "unknown feature %s\n", f); exit(1); }
      up[nup][upn[nup]++] = k; }
    snprintf(upE[nup], 100, "pot[%s]_every", upname[nup]); snprintf(upS[nup], 100, "pot[%s]_some", upname[nup]);
    snprintf(upF[nup], 100, "FAIL_pot[%s]", upname[nup]); nup++; }
}
static int cmp_pot(const cfg_t *a, const cfg_t *b, const int *pot, int np) {
  for (int i = 0; i < np; i++) { int u = feat(a, pot[i]), v = feat(b, pot[i]); if (u != v) return u < v ? -1 : 1; }
  return 0;
}
/* per key: is every / some maximum of pot completable */
static void key_max(const rkey_t *K, const int *pot, int np, int *every, int *some) {
  int best = -1;
  for (int q = 0; q < K->nc; q++) if (best < 0 || cmp_pot(&K->c[q], &K->c[best], pot, np) > 0) best = q;
  *every = 1; *some = 0;
  for (int q = 0; q < K->nc; q++) if (!cmp_pot(&K->c[q], &K->c[best], pot, np)) { if (K->c[q].comp) *some = 1; else *every = 0; }
}

static const int P_RL[] = {F_R, F_LAMU};
static const int P_G1[] = {F_MT, F_R, F_LAMR};
static const int P_G2[] = {F_MT, F_R, F_LAMR, F_MP};
static const int P_G3[] = {F_R, F_LAMU, F_MP};

static void do_profile(void) {
  for (int i = 0; i < n; i++) { memset(vv[i], 0, sizeof vv[i]); int bt = -1;
    for (int k = 0; k < d[i]; k++) { vv[i][gl[i][k]] = tv[i][cur[i]][k]; if (bt < 0 || tv[i][cur[i]][k] > vv[i][bt]) bt = gl[i][k]; }
    top[i] = bt; }
  INC("profiles");
  int ag[MAXN]; for (int i = 0; i < n; i++) ag[i] = i;
  if (disjoint_system(n, ag, Rm, 0)) { INC("f0"); return; }
  nkeys = 0;
  for (int x = 0; x < n; x++) {
    int g = top[x], na = 0; int fr[MAXN]; mask_t U[MAXN];
    for (int y = 0; y < n; y++) { U[y] = Rm[y] & ~((mask_t)1 << g); if (y != x) fr[na++] = y; }
    if (!disjoint_system(na, fr, U, (mask_t)1 << g)) continue;
    rkey_t *K = &keys[nkeys++];
    K->g = g; K->x = x; K->nfree = na; memcpy(K->free, fr, sizeof fr); memcpy(K->U, U, sizeof U);
    K->Mp = (((mask_t)1 << m) - 1) & ~((mask_t)1 << g); K->omega = m - 2 * n + 1;
    K->lx = level(x, (mask_t)1 << g, Rm[x]);
  }
  if (!nkeys) { INC("f2plus"); return; }
  if (m - 2 * n + 1 <= 0) { INC("f1_omega_le0"); return; }
  INC("f1");
  { int gg = keys[0].g, same = 1; for (int k = 1; k < nkeys; k++) if (keys[k].g != gg) same = 0; if (same) INC("f1_keys_share_g"); else { INC("f1_keys_distinct_g"); example("keys_distinct_g"); } }
  for (int k = 0; k < nkeys; k++) build_key(&keys[k]);
  /* per key */
  int anyc[MAXN];
  int prof_every = 0, prof_any = 0;
  for (int k = 0; k < nkeys; k++) {
    rkey_t *K = &keys[k]; INC("keys");
    int e, s; key_max(K, P_RL, 2, &e, &s);
    anyc[k] = 0; for (int q = 0; q < K->nc; q++) if (K->c[q].comp) anyc[k] = 1;
    if (e) INC("key_rl_every");
    if (s) INC("key_rl_some");
    if (anyc[k]) INC("key_any"); else { INC("key_noncompletable"); example("key_noncompletable"); }
    int e3, s3; key_max(K, P_G3, 3, &e3, &s3); if (e3) INC("key_rlp_every");
    prof_every |= e; prof_any |= anyc[k];
    { /* Theorem Z's argument under the constraint t = 0: maxima of (-t, r, lamU) at this key */
      static const int PT[] = {F_MT, F_R, F_LAMU};
      int bq = -1; for (int q = 0; q < K->nc; q++) if (bq < 0 || cmp_pot(&K->c[q], &K->c[bq], PT, 3) > 0) bq = q;
      for (int q = 0; q < K->nc; q++) { cfg_t *c = &K->c[q]; if (cmp_pot(c, &K->c[bq], PT, 3)) continue;
        INC("tmax"); if (c->t) INC("tmax_t1");
        if (!c->nfv) { INC("tmax_no_freevalid"); example("tmax_no_freevalid");
          if (!c->inj) INC("tmax_no_freevalid_notinj");
          if (c->npo & ~c->rob) INC("tmax_no_freevalid_nonrobust_npo"); }
        if (c->npo & ~c->rob) INC("tmax_nonrobust_npo");
        if (!c->inj) INC("tmax_not_inj");
        if (!c->comp) INC("tmax_noncomp"); } }
    /* Theorem Z' at every (r, lamU)-max; count lemma at every pool-optimal configuration; pool-optimality at maxima */
    int best = -1; for (int q = 0; q < K->nc; q++) if (best < 0 || cmp_pot(&K->c[q], &K->c[best], P_RL, 2) > 0) best = q;
    for (int q = 0; q < K->nc; q++) {
      cfg_t *c = &K->c[q];
      if (c->poolopt && c->nfv < c->r) { INC("FAIL_count_lemma"); example("count_lemma"); }
      if (c->poolopt && c->r >= 1 && c->nfv == 0) { INC("FAIL_poolopt_r1_fv"); example("poolopt_r1_fv"); }
      if (!cmp_pot(c, &K->c[best], P_RL, 2)) {
        INC("rl_maxima");
        if (!c->poolopt) { INC("FAIL_max_poolopt"); example("max_poolopt"); }
        if (!c->nfv) { INC("FAIL_thmZprime"); example("thmZprime"); }
        if (!c->nterm) { INC("FAIL_no_terminal"); example("no_terminal"); }
        if (!c->comp) {
          INC("rl_max_noncomp");
          if (c->t) INC("noncomp_t1"); else if (c->nfv >= 2) INC("noncomp_t0_fv2"); else INC("noncomp_t0_fv1");
          /* role swap: some / every terminal whose key has every (r, lamU)-max completable */
          int someg = 0, allg = 1;
          for (int z = 0; z < n; z++) if (c->terms >> z & 1) {
            int kz = -1; for (int j = 0; j < nkeys; j++) if (keys[j].x == z) kz = j;
            if (kz < 0) { INC("FAIL_terminal_not_key"); example("terminal_not_key"); allg = 0; continue; }
            int ez, sz; key_max(&keys[kz], P_RL, 2, &ez, &sz);
            if (ez) someg = 1; else allg = 0;
          }
          if (someg) INC("swap_some_terminal_good"); else { INC("FAIL_swap_some_terminal"); example("swap_some_terminal"); }
          if (allg) INC("swap_all_terminals_good");
        }
      }
    }
  }
  /* certificates: a pool-optimal configuration with r > |D_x| has an x-safe free-valid owner (counting) */
  { int cert = 0, cert2 = 0, t0key = 1;
    for (int k = 0; k < nkeys; k++) { int t0 = 0, t0p = 0;
      for (int q = 0; q < keys[k].nc; q++) { cfg_t *c = &keys[k].c[q];
        if (!c->t) { t0 = 1; if (c->poolopt) t0p = 1; }
        if (c->poolopt && c->r > c->ndx) { cert = 1; if (!c->comp) { INC("FAIL_cert_noncomp"); example("cert_noncomp"); } }
        if (c->inj && c->r > c->ndx) { cert2 = 1; if (!c->comp) { INC("FAIL_cert2_noncomp"); example("cert2_noncomp"); } }
        if (c->poolopt && !c->inj) { INC("FAIL_poolopt_not_inj"); example("poolopt_not_inj"); } }
      if (t0) INC("key_t0_exists"); else { t0key = 0; INC("key_no_t0"); example("key_no_t0"); }
      if (t0p) INC("key_t0_poolopt_exists"); }
    if (cert) INC("prof_cert_exists"); else { INC("FAIL_prof_cert"); example("prof_cert"); }
    if (cert2) INC("prof_cert2_exists"); else { INC("FAIL_prof_cert2"); example("prof_cert2"); }
    if (t0key) INC("prof_every_key_t0");
    { int any0 = 0; for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) if (!keys[k].c[q].t) any0 = 1;
      if (!any0) { INC("prof_no_t0_anywhere"); example("prof_no_t0_anywhere"); } } }
  if (prof_every) INC("prof_some_key_every"); else { INC("FAIL_prof_some_key_every"); example("prof_some_key_every"); }
  if (prof_any) INC("prof_completable"); else { INC("FAIL_prof_completable"); example("prof_completable"); }
  for (int u = 0; u < nup; u++) {
    const cfg_t *best = NULL;
    for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) if (!best || cmp_pot(&keys[k].c[q], best, up[u], upn[u]) > 0) best = &keys[k].c[q];
    int ev = 1, so = 0;
    for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) if (!cmp_pot(&keys[k].c[q], best, up[u], upn[u])) { if (keys[k].c[q].comp) so = 1; else ev = 0; }
    if (ev) INC(upE[u]); else { INC(upF[u]); example(upF[u]); }
    if (so) INC(upS[u]);
  }
  /* structure at the maxima of the analysis potential (the first user potential, else (-t, r, lamR)) */
  { const int *AP = nup ? up[0] : P_G1; int AN = nup ? upn[0] : 3;
    const cfg_t *best = NULL;
    for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) if (!best || cmp_pot(&keys[k].c[q], best, AP, AN) > 0) best = &keys[k].c[q];
    for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) { const cfg_t *c = &keys[k].c[q];
      if (cmp_pot(c, best, AP, AN)) continue;
      INC("amax"); if (c->t) { INC("amax_t1"); example("amax_t1"); }
      if (!c->poolopt) INC("amax_not_poolopt");
      if (c->npo & ~c->rob) { INC("amax_nonrobust_not_poolopt"); example("amax_nonrobust_not_poolopt"); }
      if (!c->inj) { INC("amax_not_inj"); example("amax_not_inj"); }
      if (c->ndx >= 2) { INC("amax_ndx2"); example("amax_ndx2"); }
      if (c->r == 0) { INC("amax_r0"); example("amax_r0"); } else if (c->r == 1) INC("amax_r1");
      if (c->inj && c->r > c->ndx) INC("amax_cert2"); else { INC("amax_not_cert2"); example("amax_not_cert2"); }
      if (!c->comp) { INC("FAIL_amax_noncomp"); example("amax_noncomp"); } } }
  /* global potentials over all keys */
  const int *GP[] = {P_G1, P_G2, P_RL}; const int GN[] = {3, 4, 2}; const char *GE[] = {"glob_-t,r,lamR_every", "glob_-t,r,lamR,-p_every", "glob_r,lamU_every"};
  const char *GF[] = {"FAIL_glob_-t,r,lamR", "FAIL_glob_-t,r,lamR,-p", "FAIL_glob_r,lamU"};
  for (int gp = 0; gp < 3; gp++) {
    const cfg_t *best = NULL;
    for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) if (!best || cmp_pot(&keys[k].c[q], best, GP[gp], GN[gp]) > 0) best = &keys[k].c[q];
    int ev = 1;
    for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) if (!cmp_pot(&keys[k].c[q], best, GP[gp], GN[gp]) && !keys[k].c[q].comp) ev = 0;
    if (ev) INC(GE[gp]); else { INC(GF[gp]); example(GF[gp]); }
    if (0)
      for (int k = 0; k < nkeys; k++) for (int q = 0; q < keys[k].nc; q++) { const cfg_t *c = &keys[k].c[q];
        if (cmp_pot(c, best, GP[gp], GN[gp])) continue;
        INC("g1max"); if (c->t) INC("g1max_t1"); if (!c->poolopt) { INC("g1max_not_poolopt"); example("g1max_not_poolopt"); }
        if (c->poolopt && c->r > c->ndx) INC("g1max_cert"); else { INC("g1max_not_cert"); example("g1max_not_cert"); }
        if (c->inj && c->r > c->ndx) INC("g1max_cert2"); else { INC("g1max_not_cert2"); example("g1max_not_cert2"); }
        if (!c->inj) { INC("g1max_not_inj"); example("g1max_not_inj"); }
        if (c->npo & ~c->rob) { INC("g1max_nonrobust_not_poolopt"); example("g1max_nonrobust_not_poolopt"); }
        if (c->npo) INC("g1max_robust_not_poolopt");
        if (c->ndx >= 2) INC("g1max_ndx2");
        if (c->r == 0) INC("g1max_r0"); else if (c->r == 1) INC("g1max_r1");
        if (!c->nfv) INC("g1max_no_fv"); }
  }
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
  for (int a = 1; a < argc; a++) {
    if (!strcmp(argv[a], "-x") && a + 1 < argc) nex = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-p") && a + 1 < argc) parse_pots(argv[++a]);
  }
  if (scanf("%d %d", &n, &m) != 2) return 1;
  if (n > MAXN || m > MAXM) { fprintf(stderr, "too large\n"); return 1; }
  for (int i = 0; i < n; i++) {
    if (scanf("%d", &d[i]) != 1) return 1;
    Rm[i] = 0; for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 1; Rm[i] |= (mask_t)1 << gl[i][k]; }
    if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) return 1;
    for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 1;
  }
  long long R = 0, seed = 1;
  if (scanf("%lld %lld", &R, &seed) != 2) { R = 0; }
  if (R > 0) {
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
  for (int i = 0; i < ncnt; i++) printf("%s %lld\n", cname[i], cval[i]);
  return 0;
}
