/* c4min_f1.c: exhaustive checks of k4/c4min_f1.md (C4min with one frozen agent), written from the definitions of
   k4/c4min.md §1 (configurations) and k4/c4min_f1.md §1-§3. Enumeration of the valid pre-allocations and of the
   configurations as in k4/c4min.c; everything after that is new.

   For every strict profile of one k = 4 core with fewest frozen agents f = 1 and omega >= 1, over all configurations
   (frozen agent x on g = its top, free agents on admissible pairs outside g, pool L):
     r = number of robust agents (free y: v_y(Q_y) >= v_y(U_y \ Q_y), U_y = R_y \ {g}; x: v_x(U_x) <= v_x(g), never at
         f = 1), Lambda = sum of the levels l_i(H_i) = #{T ⊆ R_i : v_i(T) < v_i(H_i)}, Psi = (r, Lambda), t = [x is
         threatened by the pool alone].
   Theorem checks (counters in the RESULT line):
     f1fail    (r, Lambda)-maxima whose frozen agent is not big-top and that have no owner valid with C = {}   (Thm F1)
     starfail  profiles none of whose (r, Lambda)-maxima is completable                                    (Thm F1*)
     rltfail   profiles with an (r, Lambda, -t)-maximum that is not completable                             (evidence)
     cov3 / cov4  profiles with a Psi-maximum whose frozen agent has three goods / four goods, not big-top (and no
               such maximum with three goods): Theorem F1 applies; btonly: every Psi-maximum has a big-top frozen
               agent; btonly_comp: of those, some Psi-maximum is completable
   Lemma checks, with -L, on every configuration without an owner valid with C = {} (a superset of the
   non-completable ones): Lemma 1 (terminals have top g, some agent needs g); Lemma 2 (every value-raising pool move
   raises Psi); at pool-optimal ones Lemma 3 (robust free agents unthreatened, the others threatened by at most one
   owner, the kinds), Lemma 5 (every rotation of every cycle of the threat digraph through free agents raises Psi),
   Lemma 7 (x not big-top: every shortest path move from a terminal raises Psi; L7rconf counts the moves with a
   robust terminal and an (R) receiver whose fourth good lies in the pool and in x's pair), and for big-top x the
   outcomes of the path moves (Lemma 8).
   A failed assertion prints ASSERT and the profile and exits with code 4.

   stdin as k4/c4min.c: n m, per agent: d g_0 .. g_{d-1} T, then T lines of d values; then lo hi (agent 0's types).
   options: -r N random profiles (seed -S); -x N examples; -L lemma checks. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
#define MAXM 48
#define MAXT 300
typedef uint64_t mask_t;
static inline int pc(mask_t x) { return __builtin_popcountll(x); }
#define BIT(g) ((mask_t)1 << (g))

static int n, m, d[MAXN], gl[MAXN][4], nt[MAXN], tv[MAXN][MAXT][4], cur[MAXN];
static mask_t Rm[MAXN];
static int vv[MAXN][MAXM];
static int nex = 0, lemmas = 0;

static int val(int i, mask_t S) { int s = 0; mask_t r = S & Rm[i]; while (r) { int g = __builtin_ctzll(r); s += vv[i][g]; r &= r - 1; } return s; }
static int minval(int i, mask_t S) {
  if (S & ~Rm[i]) return 0;
  int mn = 1 << 30; mask_t r = S; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] < mn) mn = vv[i][g]; r &= r - 1; } return mn;
}
static int threat(int i, mask_t X, mask_t H) { if (!X) return 0; return val(i, X) - minval(i, X) > val(i, H); }
#define FOREIGN ((mask_t)1 << (MAXM - 1))
static mask_t needs(int i, mask_t B) { int b = val(i, B); mask_t N = 0, r = Rm[i] & ~B; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] > b) N |= BIT(g); r &= r - 1; } return N; }
static int top(int i) { int bg = -1, bv = -1; mask_t r = Rm[i]; while (r) { int g = __builtin_ctzll(r); if (vv[i][g] > bv) { bv = vv[i][g]; bg = g; } r &= r - 1; } return bg; }
static int level(int i, mask_t S) {
  int x = val(i, S), l = 0, k = d[i];
  for (int t = 0; t < (1 << k); t++) { int s2 = 0; for (int q = 0; q < k; q++) if (t >> q & 1) s2 += vv[i][gl[i][q]]; l += s2 < x; }
  return l;
}
static void print_prof(void) { for (int i = 0; i < n; i++) { printf(" ["); for (int k = 0; k < d[i]; k++) printf("%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); printf("]"); } }
static void print_mask(mask_t S) { printf("{"); int f = 1; for (int g = 0; g < m; g++) if (S >> g & 1) { printf("%s%d", f ? "" : ",", g); f = 0; } printf("}"); }

/* ---- valid pre-allocations (as k4/c4min.c) ---- */
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

/* ---- configurations at f = 1: H[i] = pair (free) or {g} (frozen xf) ---- */
typedef struct { mask_t H[MAXN]; mask_t L; int xf; } cfg_t;
static mask_t gbit, U[MAXN], Mp;
static cfg_t *cf; static int ncf, capcf;
static int *cfr, *cfl, *cft, *cfc0, *cfc, *cfbt; static int capfeat;
static int nfopt[MAXN]; static mask_t fopt[MAXN][1200];
static int isbt[MAXN];            /* big-top: 4 goods, top > second + third */

static int robust(const cfg_t *c, int i) {
  if (i == c->xf) return !threat(i, U[i] | FOREIGN, c->H[i]);
  return val(i, c->H[i]) >= val(i, U[i] & ~c->H[i]);
}
static void psi(const cfg_t *c, int *r, int *l) { *r = 0; *l = 0; for (int i = 0; i < n; i++) { *r += robust(c, i); *l += level(i, c->H[i]); } }
static int cmp2(int r1, int l1, int r2, int l2) { if (r1 != r2) return r1 > r2 ? 1 : -1; if (l1 != l2) return l1 > l2 ? 1 : -1; return 0; }
static int tthr(const cfg_t *c) { return threat(c->xf, c->L | FOREIGN, c->H[c->xf]); }

/* owner o of c: keeps X' = (Q_o ∪ L) \ C with an admissible base of o; |C| <= the frozen agents unfrozen once the
   owner's needs come from X' (their good needed by nobody else); nobody else threatened by X' (k4/c4min.md §1). */
static int owner_u(const cfg_t *c, int o, int allow_unf) {
  if (o == c->xf) return 0;
  mask_t Xo = c->H[o] | c->L, NAo = 0; int ncand = 0;
  for (int j = 0; j < n; j++) if (j != o) NAo |= needs(j, c->H[j]);
  if (allow_unf && !(c->H[c->xf] & NAo)) ncand = 1;
  for (mask_t C = 0;; C = (C - Xo) & Xo) {
    if (pc(C) <= ncand) {
      mask_t X = Xo & ~C; int ok;
      { int adm = 0; mask_t S = X & U[o];
        if (!S) adm = !U[o];
        for (mask_t B = S; B && !adm; B = (B - 1) & S) if (pc(B) <= 2 && !(needs(o, B) & U[o])) adm = 1;
        ok = adm; }
      if (ok && C) { mask_t No = needs(o, X & Rm[o]); if (c->H[c->xf] & No) ok = 0; }
      for (int x = 0; x < n && ok; x++) if (x != o && threat(x, X, c->H[x])) ok = 0;
      if (ok) return 1;
    }
    if (C == Xo) break;
  }
  return 0;
}
static int has_owner(const cfg_t *c, int allow_unf) { for (int o = 0; o < n; o++) if (o != c->xf && owner_u(c, o, allow_unf)) return 1; return 0; }

static mask_t curH[MAXN]; static int freel[MAXN], nfree, curxf;
static void genC(int k, mask_t used) {
  if (k == nfree) {
    if (ncf == capcf) { capcf = capcf ? 2 * capcf : 1024; cf = realloc(cf, (size_t)capcf * sizeof(cfg_t)); }
    cfg_t *c = &cf[ncf++]; memcpy(c->H, curH, sizeof curH); c->L = Mp & ~used; c->xf = curxf;
    return;
  }
  int i = freel[k];
  for (int q = 0; q < nfopt[i]; q++) { mask_t S = fopt[i][q]; if (S & used) continue; curH[i] = S; genC(k + 1, used | S); }
}
static void configs_for_key(const nkey_t *K) {
  mask_t all = ((mask_t)1 << m) - 1;
  Mp = all & ~K->NA; nfree = 0;
  for (int i = 0; i < n; i++) {
    U[i] = Rm[i] & Mp; curH[i] = K->phi[i];
    if (K->phi[i]) { curxf = i; continue; }
    freel[nfree++] = i; nfopt[i] = 0;
    for (int g = 0; g < m; g++) if (Mp >> g & 1) for (int h = g + 1; h < m; h++) if (Mp >> h & 1) {
      mask_t S = BIT(g) | BIT(h);
      if (needs(i, S & U[i]) & U[i]) continue;
      if (nfopt[i] >= 1200) { fprintf(stderr, "too many pairs\n"); exit(3); }
      fopt[i][nfopt[i]++] = S;
    }
  }
  genC(0, 0);
}

/* ---- counters ---- */
static long long cov3, cov4, covbt, covbtc;
static long long nprof, nf1, ncfgs, nmaxrl, nmaxrl_bt, f1fail, starfail, rltfail, nnoown;
static long long L2pool, L2fail, Lpo, L5cyc, L5fail, L7paths, L7fail, L7rconf, L8[4][3], nL8cfg;
static int exf1, exstar, exrlt, exl2, exl5, exl7, exrc;

static void die(const char *what, const cfg_t *c) {
  printf("ASSERT %s:", what); print_prof(); printf(" | x %d H", c->xf);
  for (int i = 0; i < n; i++) { printf(" "); print_mask(c->H[i]); } printf(" L "); print_mask(c->L); printf("\n");
  fflush(stdout); exit(4);
}
static void show(const char *tag, const cfg_t *c) {
  printf("EX %s:", tag); print_prof(); printf(" | x %d H", c->xf);
  for (int i = 0; i < n; i++) { printf(" "); print_mask(c->H[i]); } printf(" L "); print_mask(c->L); printf("\n");
}
static void check_valid(const cfg_t *c, const char *what) {
  mask_t used = 0; int cnt = 0;
  for (int i = 0; i < n; i++) { if (i == c->xf) { if (c->H[i] != gbit) die(what, c); } else { if (pc(c->H[i]) != 2 || (c->H[i] & gbit)) die(what, c); } used |= c->H[i]; cnt += pc(c->H[i]); }
  if (pc(used) != cnt || (used & c->L) || cnt + pc(c->L) != m) die(what, c);
  for (int i = 0; i < n; i++) if (needs(i, c->H[i]) & ~gbit) die(what, c);
  if (top(c->xf) != __builtin_ctzll(gbit)) die(what, c);
}

/* kinds of free agents (Lemma 3): 0 robust, 1 T3, 2 Tg, 3 T4, 4 D, 5 R (with s) */
enum { K_ROB, K_T3, K_TG, K_T4, K_D, K_R };
static int kind[MAXN], sgood[MAXN];
static void kinds(const cfg_t *c) {
  for (int y = 0; y < n; y++) {
    if (y == c->xf) continue;
    sgood[y] = -1;
    if (robust(c, y)) { kind[y] = K_ROB; continue; }
    int o[4] = {0, 0, 0, 0}, k = 0; mask_t r = Rm[y]; while (r) { o[k++] = __builtin_ctzll(r); r &= r - 1; }
    for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) if (vv[y][o[b]] > vv[y][o[a]]) { int t = o[a]; o[a] = o[b]; o[b] = t; }
    mask_t H = c->H[y] & Rm[y];
    if (Rm[y] & gbit) {
      int u[3], q = 0; for (int a = 0; a < k; a++) if (BIT(o[a]) != gbit) u[q++] = o[a];
      if (k != 4 || H != BIT(u[0]) || vv[y][u[0]] >= vv[y][u[1]] + vv[y][u[2]]) die("Lemma 3 (valuer of g)", c);
      kind[y] = K_TG; continue;
    }
    if (k == 3) { if (H != BIT(o[0])) die("Lemma 3 (3-good)", c); kind[y] = K_T3; continue; }
    if (H == BIT(o[0])) { kind[y] = K_T4; continue; }
    if (H == (BIT(o[0]) | BIT(o[3]))) { kind[y] = K_D; continue; }
    if ((H & BIT(o[0])) || pc(H) != 2) die("Lemma 3 (4-good)", c);
    kind[y] = K_R; for (int a = 1; a < 4; a++) if (!(H & BIT(o[a]))) sgood[y] = o[a];
  }
}
static int plain_robust_recv(int y, mask_t S) { return kind[y] == K_T3 || kind[y] == K_TG || kind[y] == K_D || (kind[y] == K_R && (S & BIT(sgood[y]))); }

/* Lemma 5: rotation of a cycle cyc[0] -> cyc[1] -> ... (cyc[j+1] threatened by cyc[j]) */
static void rotation(const cfg_t *c, const int *cyc, int k, cfg_t *out) {
  *out = *c; int pr = 0, mod = -1;
  for (int j = 0; j < k; j++) { int y = cyc[(j + 1) % k]; if (plain_robust_recv(y, c->H[cyc[j]])) pr = 1; }
  if (!pr) for (int j = 0; j < k; j++) { int y = cyc[(j + 1) % k]; if (kind[y] == K_R && (c->L & BIT(sgood[y]))) { mod = y; break; } }
  for (int j = 0; j < k; j++) {
    int y = cyc[(j + 1) % k]; mask_t S = c->H[cyc[j]];
    if (y == mod) { mask_t a = BIT(top(y)); if (!(S & a)) die("Lemma 5: top not in the predecessor's pair", c); out->L |= S & ~a; out->L &= ~BIT(sgood[y]); S = a | BIT(sgood[y]); }
    out->H[y] = S;
  }
  check_valid(out, "Lemma 5: rotation is not a configuration");
}
/* best pair of agent i inside S ∩ U_i */
static mask_t best_pair(int i, mask_t S) {
  mask_t T = S & U[i], best = 0; int bv = -1;
  for (mask_t a = T; a; a &= a - 1) for (mask_t b = a & (a - 1); b; b &= b - 1) { mask_t P = (a & -a) | (b & -b); int w = val(i, P); if (w > bv) { bv = w; best = P; } }
  return best;
}
/* Lemma 7: path q[0] = tau -> q[1] -> ... -> q[k] -> x */
static int path_move(const cfg_t *c, const int *q, int k, cfg_t *out) {
  int x = c->xf, tau = q[0], pr = 0, mod = -1, rconf = 0;
  mask_t Px = best_pair(x, c->H[q[k]] | c->L);
  if (pc(Px) != 2) die("Lemma 7: x has no pair", c);
  *out = *c;
  for (int j = 1; j <= k; j++) if (plain_robust_recv(q[j], c->H[q[j - 1]])) pr = 1;
  if (!pr) {
    for (int j = 1; j <= k; j++) if (kind[q[j]] == K_R && (c->L & ~Px & BIT(sgood[q[j]]))) { mod = q[j]; break; }
    if (mod < 0) for (int j = 1; j <= k; j++) if (kind[q[j]] == K_R && (c->L & BIT(sgood[q[j]]))) rconf = 1;
  }
  for (int j = 1; j <= k; j++) {
    int y = q[j]; mask_t S = c->H[q[j - 1]];
    if (y == mod) { mask_t a = BIT(top(y)); out->L |= S & ~a; out->L &= ~BIT(sgood[y]); S = a | BIT(sgood[y]); }
    out->H[y] = S;
  }
  out->L |= c->H[q[k]] & ~Px; out->L &= ~Px;
  out->H[x] = Px; out->H[tau] = gbit; out->xf = tau;
  check_valid(out, "Lemma 7: path move is not a configuration");
  return rconf;
}

static int T[MAXN];   /* threat digraph: bitmask of victims of free owner o (with C = {}) */
static int cyc[MAXN], incyc[MAXN], cycfound;
static void cycles_from(const cfg_t *c, int s, int u, int len, int *r0, int *l0) {
  for (int w = 0; w < n; w++) {
    if (!(T[u] >> w & 1) || w == c->xf) continue;
    if (w == s) { cfg_t o; rotation(c, cyc, len, &o); int r, l; psi(&o, &r, &l); L5cyc++; cycfound = 1;
      if (cmp2(r, l, *r0, *l0) <= 0) { L5fail++; if (exl5 < nex) { exl5++; show("Lemma 5 rotation does not raise Psi", c); } } }
    else if (w > s && !incyc[w]) { incyc[w] = 1; cyc[len] = w; cycles_from(c, s, w, len + 1, r0, l0); incyc[w] = 0; }
  }
}
static int pth[MAXN], inpth[MAXN];
static void paths_from(const cfg_t *c, int u, int len, int want, int *r0, int *l0, int bt) {
  /* pth[0..len-1] is the path so far, ending at u */
  if (len - 1 == want) {
    if (!(T[u] >> c->xf & 1)) return;
    cfg_t o; int rc = path_move(c, pth, len - 1, &o) && kind[pth[0]] == K_ROB; int r, l; psi(&o, &r, &l);
    int s = cmp2(r, l, *r0, *l0);
    if (!bt) { L7paths++; L7rconf += rc; if (s <= 0) { L7fail++; if (exl7 < nex) { exl7++; show("Lemma 7 shortest path move does not raise Psi", c); } }
      if (rc && exrc < nex) { exrc++; printf("EX Lemma 7 R-conflict, Psi %s, path", s > 0 ? "up" : s == 0 ? "tie" : "down"); for (int j = 0; j <= want; j++) printf(" %d", pth[j]); show("", c); } }
    else { int idx = rc ? 3 : want == 0 ? 0 : want == 1 ? 1 : 2; L8[idx][s + 1]++; }
    return;
  }
  for (int w = 0; w < n; w++) {
    if (!(T[u] >> w & 1) || w == c->xf || inpth[w]) continue;
    inpth[w] = 1; pth[len] = w; paths_from(c, w, len + 1, want, r0, l0, bt); inpth[w] = 0;
  }
}

static void lemma_checks(const cfg_t *c) {
  int x = c->xf, r0, l0, bt = isbt[x]; psi(c, &r0, &l0);
  /* Lemma 2 */
  int po = 1;
  for (int y = 0; y < n; y++) {
    if (y == x) continue;
    mask_t S = c->H[y] | c->L; int vy = val(y, c->H[y]);
    for (mask_t a = S; a; a &= a - 1) for (mask_t b = a & (a - 1); b; b &= b - 1) {
      mask_t P = (a & -a) | (b & -b);
      if (val(y, P) <= vy) continue;
      po = 0; L2pool++;
      cfg_t o = *c; o.H[y] = P; o.L = (c->L | c->H[y]) & ~P; check_valid(&o, "Lemma 2: pool move is not a configuration");
      int r, l; psi(&o, &r, &l);
      if (cmp2(r, l, r0, l0) <= 0) { L2fail++; if (exl2 < nex) { exl2++; show("Lemma 2 pool move does not raise Psi", c); } }
    }
  }
  if (!po) return;
  Lpo++;
  /* Lemma 3 */
  kinds(c);
  int indeg[MAXN] = {0};
  for (int o = 0; o < n; o++) {
    T[o] = 0; if (o == x) continue;
    for (int z = 0; z < n; z++) if (z != o && threat(z, c->H[o] | c->L, c->H[z])) { T[o] |= 1 << z; indeg[z]++; }
    if (!T[o]) die("an owner threatens nobody", c);
  }
  for (int y = 0; y < n; y++) if (y != x) { if (kind[y] == K_ROB ? indeg[y] != 0 : indeg[y] > 1) die("Lemma 3: threats on a free agent", c); }
  /* Lemma 5 */
  cycfound = 0;
  for (int s = 0; s < n; s++) { if (s == x) continue; memset(incyc, 0, sizeof incyc); incyc[s] = 1; cyc[0] = s; cycles_from(c, s, s, 1, &r0, &l0); }
  if (cycfound) return;
  /* Lemma 6/7/8: shortest paths from the terminals */
  int dist[MAXN]; for (int i = 0; i < n; i++) dist[i] = 99;
  /* distance to x along threat edges through free agents: dist[y] = 0 if y threatens x */
  for (int it = 0; it < n; it++) for (int y = 0; y < n; y++) {
    if (y == x) continue;
    if (T[y] >> x & 1) dist[y] = 0;
    for (int w = 0; w < n; w++) if (w != x && (T[y] >> w & 1) && dist[w] + 1 < dist[y]) dist[y] = dist[w] + 1;
  }
  int kmin = 99;
  for (int z = 0; z < n; z++) if (z != x && (needs(z, c->H[z]) & gbit) && dist[z] < kmin) kmin = dist[z];
  if (kmin == 99) die("Lemma 6: no terminal reaches x", c);
  for (int z = 0; z < n; z++) if (z != x && (needs(z, c->H[z]) & gbit) && dist[z] == kmin) {
    memset(inpth, 0, sizeof inpth); inpth[z] = 1; pth[0] = z; paths_from(c, z, 1, kmin, &r0, &l0, bt);
  }
  if (bt) nL8cfg++;
}

static void do_profile(void) {
  for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) vv[i][gl[i][k]] = tv[i][cur[i]][k];
  nprof++;
  fmin = 1 << 20; nkeys = 0;
  genP(0, 0, 0, 0, 0);
  if (fmin != 1 || fmin - (2 * n - m) <= 0) return;
  nf1++;
  for (int i = 0; i < n; i++) {
    isbt[i] = 0;
    if (d[i] == 4) { int w[4]; for (int k = 0; k < 4; k++) w[k] = vv[i][gl[i][k]];
      for (int a = 0; a < 4; a++) for (int b = a + 1; b < 4; b++) if (w[b] > w[a]) { int t = w[a]; w[a] = w[b]; w[b] = t; }
      isbt[i] = w[0] > w[1] + w[2]; }
  }
  ncf = 0;
  for (int q = 0; q < nkeys; q++) {
    gbit = keys[q].NA; if (pc(gbit) != 1) { printf("ASSERT f = 1 with |NA| != 1\n"); exit(4); }
    int before = ncf; configs_for_key(&keys[q]);
    if (ncf > capfeat) { capfeat = ncf + 4096; cfr = realloc(cfr, capfeat * sizeof(int)); cfl = realloc(cfl, capfeat * sizeof(int)); cft = realloc(cft, capfeat * sizeof(int)); cfc0 = realloc(cfc0, capfeat * sizeof(int)); cfc = realloc(cfc, capfeat * sizeof(int)); cfbt = realloc(cfbt, capfeat * sizeof(int)); }
    for (int a = before; a < ncf; a++) {
      cfg_t *c = &cf[a];
      /* Lemma 1 */
      if (top(c->xf) != __builtin_ctzll(gbit)) die("Lemma 1: x not on its top", c);
      int anyneed = 0;
      for (int z = 0; z < n; z++) if (z != c->xf && (needs(z, c->H[z]) & gbit)) { anyneed = 1; if (top(z) != __builtin_ctzll(gbit)) die("Lemma 1: a terminal's top is not g", c); }
      if (!anyneed) die("Lemma 1: nobody needs g", c);
      if (robust(c, c->xf)) die("x robust at f = 1", c);
      psi(c, &cfr[a], &cfl[a]); cft[a] = tthr(c); cfbt[a] = isbt[c->xf];
      cfc0[a] = has_owner(c, 0); cfc[a] = cfc0[a] || has_owner(c, 1);
      if (!cfc0[a]) { nnoown++; if (lemmas) lemma_checks(c); }
    }
  }
  ncfgs += ncf;
  /* theorem checks */
  int br = -1, bl = -1, bt3 = -1;
  for (int a = 0; a < ncf; a++) if (cmp2(cfr[a], cfl[a], br, bl) > 0) { br = cfr[a]; bl = cfl[a]; }
  int anycomp = 0, has3 = 0, has4 = 0;
  for (int a = 0; a < ncf; a++) {
    if (cfr[a] != br || cfl[a] != bl) continue;
    nmaxrl++; if (cfbt[a]) nmaxrl_bt++;
    if (cfc[a]) anycomp = 1;
    if (!cfbt[a]) { if (d[cf[a].xf] == 3) has3 = 1; else has4 = 1; }
    if (!cfbt[a] && !cfc0[a]) { f1fail++; if (exf1 < nex) { exf1++; show("Theorem F1 fails", &cf[a]); } }
  }
  if (has3) cov3++; else if (has4) cov4++; else { covbt++; if (anycomp) covbtc++; }
  if (!anycomp) { starfail++; if (exstar < nex) { exstar++; printf("EX Theorem F1* fails:"); print_prof(); printf("\n"); } }
  for (int a = 0; a < ncf; a++) if (cfr[a] == br && cfl[a] == bl && -cft[a] > bt3) bt3 = -cft[a];
  for (int a = 0; a < ncf; a++) if (cfr[a] == br && cfl[a] == bl && -cft[a] == bt3 && !cfc[a]) { rltfail++; if (exrlt < nex) { exrlt++; show("(r, Lambda, -t)-maximum not completable", &cf[a]); } break; }
}

int main(int argc, char **argv) {
  long long nr = 0; unsigned long long seed = 1;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-r")) nr = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-S")) seed = strtoull(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "-x")) nex = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-L")) lemmas = 1;
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
  }
  if (scanf("%d %d", &n, &m) != 2 || n > MAXN || m > MAXM - 2) return 2;
  for (int i = 0; i < n; i++) {
    if (scanf("%d", &d[i]) != 1) return 2;
    Rm[i] = 0; for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 2; Rm[i] |= BIT(gl[i][k]); }
    if (scanf("%d", &nt[i]) != 1) return 2;
    for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 2;
    nopt[i] = 0; opt[i][nopt[i]++] = 0;
    for (int a = 0; a < d[i]; a++) opt[i][nopt[i]++] = BIT(gl[i][a]);
    for (int a = 0; a < d[i]; a++) for (int b = a + 1; b < d[i]; b++) opt[i][nopt[i]++] = BIT(gl[i][a]) | BIT(gl[i][b]);
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
  printf("RESULT profiles %lld f1 %lld configs %lld noowner0 %lld maxrl %lld maxrl_bt %lld f1fail %lld starfail %lld rltfail %lld"
         " cov3 %lld cov4 %lld btonly %lld btonly_comp %lld"
         " L2pool %lld L2fail %lld poolopt %lld L5cyc %lld L5fail %lld L7paths %lld L7rconf %lld L7fail %lld L8cfg %lld"
         " L8k0down %lld L8k0tie %lld L8k0up %lld L8k1down %lld L8k1tie %lld L8k1up %lld L8k2down %lld L8k2tie %lld L8k2up %lld L8rcdown %lld L8rctie %lld L8rcup %lld\n",
         nprof, nf1, ncfgs, nnoown, nmaxrl, nmaxrl_bt, f1fail, starfail, rltfail, cov3, cov4, covbt, covbtc, L2pool, L2fail, Lpo, L5cyc, L5fail, L7paths, L7rconf, L7fail, nL8cfg,
         L8[0][0], L8[0][1], L8[0][2], L8[1][0], L8[1][1], L8[1][2], L8[2][0], L8[2][1], L8[2][2], L8[3][0], L8[3][1], L8[3][2]);
  return 0;
}
