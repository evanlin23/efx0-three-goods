/* c4min_hunt.c: exact tests of conjecture C4min (k4/c4x.md §5, PR #36) for the refuter workstream
   compute/k4-c4min-hunt (k4/c4min_hunt.md). Written from the definitions of k4/c4x.md §1, sharing no code with
   k4/c4x.c.

   Definitions (one strict profile of a k = 4 core; agents i with R_i of 3 or 4 goods, values v_i):
   - P: bases B_i ⊆ R_i, |B_i| <= 2, pairwise disjoint; needs N_i = {g in R_i \ B_i : v_i(g) > v_i(B_i)};
     NA = ∪ N_i; J = goods in no base. Valid: every good of NA is the whole base of one agent (a one-good base).
     Frozen: agents whose one-good base lies in NA (|F| = |NA|). cap(i) = 0 if frozen, else 2 - |B_i|; S = Σ cap.
   - def(P): |J| - S if that is <= 0 (no owner); otherwise the least |C| - S_o(C) over free owners o and C ⊆ J such
     that X_o = B_o ∪ (J \ C) threatens no agent j != o holding B_j alone (max_{h in X_o} v_j(X_o \ h) > v_j(B_j)),
     where S_o(C) = Σ_{j != o} cap'(j), frozen status recomputed with the owner's needs from its bundle,
     N_o^X = {g in R_o \ X_o : v_o(g) > v_o(X_o)} (-w0: from its base, S_o = S - cap(o)). +inf if no such (o, C).
   - f*(profile) = least |F| over valid P; d*(profile) = least def over valid P with |F| = f*.
     C4min holds at the profile iff d* <= 0. If f* <= σ = 2n - m, every min-frozen P has |J| <= S, so d* <= 0.
   - completable (the weaker form "some min-frozen P is completable, any deficit"): some owner o (free) or none, and
     a completion X_i = B_i ∪ C_i (C_i ⊆ J, frozen non-owners get nothing, free non-owners |X_i| <= 2, X_o = B_o ∪
     rest) with (OC4): max_h v_j(X_o \ h) <= v_j(X_j) for all j != o; owner's needs as above.

   stdin: n m, then per agent: d g_0 .. g_{d-1} T, then T lines of d values (strict types); then lo hi (range of
   agent 0's type index; exhaustive mode), or for -1: one line with n type indices.
   modes:
     -E        exhaustive over every profile with agent 0's type in [lo, hi): profiles are processed in slices (all
               types of agent n-1 at once, as a bitmask); certificates (P, owner, C) found by the exact search are
               kept in a cache and re-applied to whole slices through per-type masks. Prints FAIL lines and a RESULT
               line. -V: also re-solve every covered profile from scratch (slow; self-test of the masks). -B K: keep the
               best of up to K certificates per solve (the one covering most of the slice).
     -1        one profile (type indices from stdin): prints f*, d*, the counts, the weaker forms.
     -1q       one profile: f* and whether C4min holds, with a certificate (bases, owner, C); no counts.
     -1o       one profile: for each agent o, the least deficit over the min-frozen P when only o may own.
     -R N      N random profiles (uniform; with -P, the given profile with -K agents re-typed), each solved exactly
               (f* and whether C4min holds); prints FAIL lines and the f* histogram.
     -H ITER   hill-climbing from random profiles (-S seed, -Z restarts, -T stale limit, -O objective order, -P start
               profile after the types): maximizes (owner needed, d*, -#{min-frozen P with def <= 0}) (-O1: the last
               two in reverse order; -O2: (owner needed, f*, -good, d*); -C K: stop counting good beyond K; -A P:
               accept a worse move with probability P/1000);
               prints every profile with d* > 0 (CEX), each restart's end, and the best.
   options: -w0 owner's needs from its base; -D the deficit by plain enumeration of every C ⊆ J (a check of the
   branch and bound); -x N print up to N failures; -S seed; -Z restarts. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define MAXT 300
#define NOPT 11
#define TW 5                       /* words of a type mask (<= 320 types) */
#define INF 1000000
typedef uint64_t mask_t;

static int n, m, sigma, d[MAXN], gl[MAXN][4], nt[MAXN];
static int tv[MAXN][MAXT][4];
static mask_t R[MAXN], ALL;
static int nopt[MAXN], optl[MAXN][NOPT], optsz[MAXN][NOPT];
static mask_t optg[MAXN][NOPT];
static int wbase = 1, nex = 20, verify = 0;

/* per type tables */
static int vs[MAXN][MAXT][16];            /* value of a local subset */
static mask_t needT[MAXN][MAXT][NOPT];    /* N_i for each base option (global mask) */
static int thr[MAXN][MAXT][16][2];        /* max_h v(X \ h) for X ∩ R_i = q; [1] if X ⊆ R_i */
static unsigned char oneed[MAXN][MAXT][16];  /* owner's needs (local) when X_o ∩ R_o = q */

static int cur[MAXN];
static mask_t valued_from[MAXN + 1];

static inline int pc(mask_t x) { return __builtin_popcountll(x); }
static inline int loc(int i, mask_t g) {            /* local subset of g ∩ R_i */
  int s = 0; for (int k = 0; k < d[i]; k++) if (g >> gl[i][k] & 1) s |= 1 << k; return s;
}
static inline mask_t glob(int i, int s) {
  mask_t g = 0; for (int k = 0; k < d[i]; k++) if (s >> k & 1) g |= (mask_t)1 << gl[i][k]; return g;
}
static inline int threatened(int j, int t, mask_t X, int bopt) {
  if (!X) return 0;
  int q = loc(j, X), inside = (X & ~R[j]) == 0;
  return thr[j][t][q][inside] > vs[j][t][optl[j][bopt]];
}

static void tables(void) {
  for (int i = 0; i < n; i++) for (int t = 0; t < nt[i]; t++) {
    int *v = tv[i][t], full = (1 << d[i]) - 1;
    for (int s = 0; s <= full; s++) { int x = 0; for (int k = 0; k < d[i]; k++) if (s >> k & 1) x += v[k]; vs[i][t][s] = x; }
    for (int o = 0; o < nopt[i]; o++) {
      int s = optl[i][o], bv = vs[i][t][s]; mask_t nd = 0;
      for (int k = 0; k < d[i]; k++) if (!(s >> k & 1) && v[k] > bv) nd |= (mask_t)1 << gl[i][k];
      needT[i][t][o] = nd;
    }
    for (int q = 0; q <= full; q++) {
      int mn = INF; for (int k = 0; k < d[i]; k++) if (q >> k & 1 && v[k] < mn) mn = v[k];
      thr[i][t][q][0] = vs[i][t][q];                     /* some good of X outside R_i: remove it */
      thr[i][t][q][1] = q ? vs[i][t][q] - mn : 0;        /* X ⊆ R_i: remove the least good */
      int on = 0; for (int k = 0; k < d[i]; k++) if (!(q >> k & 1) && v[k] > vs[i][t][q]) on |= 1 << k;
      oneed[i][t][q] = on;
    }
  }
}

/* ------------------------------------------------------------------------------------------------------------ */
/* enumeration of valid pre-allocations for the current profile (cur), with |NA| <= gbound */
static int bo[MAXN];
static int gbound;
static int (*leaf)(mask_t used, mask_t sing, mask_t NA);
static int dfs(int i, mask_t used, mask_t sing, mask_t two, mask_t NA) {
  if (i == n) { if (NA & ~sing) return 0; return leaf(used, sing, NA); }
  for (int k = 0; k < nopt[i]; k++) {
    mask_t B = optg[i][k];
    if (B & used) continue;
    mask_t NA2 = NA | needT[i][cur[i]][k];
    if (pc(NA2) > gbound) continue;
    mask_t used2 = used | B, sing2 = sing, two2 = two;
    if (optsz[i][k] == 1) sing2 |= B; else if (optsz[i][k] == 2) two2 |= B;
    if (NA2 & two2) continue;                          /* a needed good in a two-good base */
    mask_t pend = NA2 & ~used2;                         /* needed goods that later agents must hold alone */
    if (pend & ~valued_from[i + 1]) continue;
    if (pc(pend) > n - i - 1) continue;
    bo[i] = k;
    if (dfs(i + 1, used2, sing2, two2, NA2)) return 1;
  }
  return 0;
}

/* the same enumeration with dynamic agent order (default for n > 6; -Y0 / -Y1 force static / dynamic): at every node
   the unassigned agent with the fewest feasible options is assigned next (an option is feasible if it is disjoint from
   the goods used, keeps |NA| <= gbound, puts no needed good into a two-good base, and leaves the needed goods not yet
   used to the other unassigned agents, at most one each). Each valid P with |NA| <= gbound is a leaf exactly once. */
static int dyn = -1, asg[MAXN], hall = 0;
/* Hall pruning (-G1; off by default, it was slower on H_6): the unassigned agents whose empty base is not feasible must get pairwise distinct
   goods, each from the union of its feasible options; checked by bipartite matching (Kuhn). */
static mask_t hm_G[MAXN]; static int hm_n, hm_of[64], hm_vis_stamp[64], hm_stamp;
static int hm_try(int a) {
  for (int g = 0; g < m; g++) if ((hm_G[a] >> g & 1) && hm_vis_stamp[g] != hm_stamp) {
    hm_vis_stamp[g] = hm_stamp;
    if (hm_of[g] < 0 || hm_try(hm_of[g])) { hm_of[g] = a; return 1; }
  }
  return 0;
}
static int hall_ok(void) {
  for (int g = 0; g < m; g++) hm_of[g] = -1;
  for (int a = 0; a < hm_n; a++) { hm_stamp++; if (!hm_try(a)) return 0; }
  return 1;
}
static int dfsd(int depth, mask_t used, mask_t sing, mask_t two, mask_t NA) {
  if (depth == n) { if (NA & ~sing) return 0; return leaf(used, sing, NA); }
  int nu = n - depth, bj = -1, bc = 99, bopt[NOPT], nb = 0;
  hm_n = 0;
  for (int j = 0; j < n; j++) {
    if (asg[j]) continue;
    mask_t Ro = 0; for (int q = 0; q < n; q++) if (!asg[q] && q != j) Ro |= R[q];
    int c = 0, op[NOPT], empty_ok = 0; mask_t G = 0;
    for (int k = 0; k < nopt[j]; k++) {
      mask_t B = optg[j][k];
      if (B & used) continue;
      mask_t NA2 = NA | needT[j][cur[j]][k];
      if (pc(NA2) > gbound) continue;
      if (NA2 & (two | (optsz[j][k] == 2 ? B : 0))) continue;
      mask_t pend = NA2 & ~(used | B);
      if ((pend & ~Ro) || pc(pend) > nu - 1) continue;
      op[c++] = k;
      if (!B) empty_ok = 1; else G |= B;
    }
    if (!c) return 0;
    if (!empty_ok) hm_G[hm_n++] = G;
    if (c < bc) { bc = c; bj = j; nb = c; memcpy(bopt, op, sizeof(int) * c); }
  }
  if (hall && hm_n > 1 && !hall_ok()) return 0;
  asg[bj] = 1;
  for (int q = 0; q < nb; q++) {
    int k = bopt[q]; mask_t B = optg[bj][k];
    bo[bj] = k;
    if (dfsd(depth + 1, used | B, sing | (optsz[bj][k] == 1 ? B : 0), two | (optsz[bj][k] == 2 ? B : 0), NA | needT[bj][cur[bj]][k])) { asg[bj] = 0; return 1; }
  }
  asg[bj] = 0;
  return 0;
}
static int enumerate(void) {
  if (dyn == 1 || (dyn < 0 && n > 6)) { memset(asg, 0, sizeof asg); return dfsd(0, 0, 0, 0, 0); }
  return dfs(0, 0, 0, 0, 0);
}

/* deficit of the pre-allocation bo[] (valid), exact (stop early if stop_le0 and a value <= 0 is found);
   records the certificate (owner, C) of the least value in cert_o, cert_C.
   For each free owner o: branch and bound over C. At a node C, if some j != o is threatened by X = B_o ∪ (J \ C),
   branch on a nonempty D ⊆ (J \ C) ∩ R_j (add D to C), or, if B_o ⊆ R_j, on adding (J \ C) \ R_j (so that
   X ⊆ R_j). Every threat-free C* contains a leaf reached this way (a branch inside C* exists at every node), and the
   value |C| - S_o(C) only grows with C (S_o is non-increasing in C), so the least leaf value is the deficit. Bound:
   every descendant C' ⊇ C has value >= |C| - S_o(C). -D: the plain enumeration of every C ⊆ J instead. */
static int cert_o; static mask_t cert_C;
static int plain_def = 0;
static int bb_o, bb_best, bb_stop; static mask_t bb_J, bb_Bo, bb_NAo, bb_bestC; static int bb_S, bb_capo;
static int So_of(int o, mask_t X, mask_t NAo, int S, int capo) {
  if (!wbase) return S - capo;
  mask_t NAp = NAo | glob(o, oneed[o][cur[o]][loc(o, X)]);
  int So = 0;
  for (int j = 0; j < n; j++) if (j != o) So += (optsz[j][bo[j]] == 1 && (optg[j][bo[j]] & NAp)) ? 0 : 2 - optsz[j][bo[j]];
  return So;
}
static void bb(mask_t C) {
  if (bb_stop && bb_best <= 0) return;
  mask_t X = bb_Bo | (bb_J & ~C);
  int lb = pc(C) - So_of(bb_o, X, bb_NAo, bb_S, bb_capo);
  if (lb >= bb_best) return;
  int j0 = -1, nb0 = 1 << 30; mask_t av0 = 0, out0 = 0;
  for (int j = 0; j < n; j++) {
    if (j == bb_o || !threatened(j, cur[j], X, bo[j])) continue;
    mask_t av = X & bb_J & R[j], out = (bb_Bo & ~R[j]) ? 0 : (X & bb_J & ~R[j]);
    int nb = (1 << pc(av)) - 1 + (out != 0);
    if (nb < nb0) { nb0 = nb; j0 = j; av0 = av; out0 = out; }
  }
  if (j0 < 0) { bb_best = lb; bb_bestC = C; return; }   /* threat-free: the value is lb */
  for (mask_t D = av0; D; D = (D - 1) & av0) bb(C | D);
  if (out0) bb(C | out0);
}
static int only_own = -1;                  /* -1o: only this owner */
static int deficit(mask_t used, mask_t NA, int stop_le0) {
  mask_t J = ALL & ~used;
  int frozen[MAXN], cap[MAXN], S = 0;
  for (int i = 0; i < n; i++) {
    mask_t B = optg[i][bo[i]];
    frozen[i] = optsz[i][bo[i]] == 1 && (B & NA);
    cap[i] = frozen[i] ? 0 : 2 - optsz[i][bo[i]];
    S += cap[i];
  }
  int nj = pc(J);
  if (nj <= S) { cert_o = -1; cert_C = J; return nj - S; }
  int best = INF;
  if (!plain_def) {
    for (int o = 0; o < n; o++) {
      if (frozen[o] || (only_own >= 0 && o != only_own)) continue;
      mask_t NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= needT[j][cur[j]][bo[j]];
      bb_o = o; bb_best = best; bb_stop = stop_le0; bb_J = J; bb_Bo = optg[o][bo[o]]; bb_NAo = NAo; bb_S = S; bb_capo = cap[o];
      bb(0);
      if (bb_best < best) { best = bb_best; cert_o = o; cert_C = bb_bestC; if (stop_le0 && best <= 0) return best; }
    }
    return best;
  }
  int jg[64], k0 = 0; for (int g = 0; g < m; g++) if (J >> g & 1) jg[k0++] = g;
  for (int o = 0; o < n; o++) {
    if (frozen[o] || (only_own >= 0 && o != only_own)) continue;
    mask_t NAo = 0; int Smax = 0;
    for (int j = 0; j < n; j++) if (j != o) { NAo |= needT[j][cur[j]][bo[j]]; Smax += 2 - optsz[j][bo[j]]; }
    mask_t Bo = optg[o][bo[o]];
    for (int k = 0; k <= nj; k++) {
      if (k - Smax >= best) break;
      if (stop_le0 && k > Smax) break;
      /* all k-subsets of J (indices idx[0] < ... < idx[k-1]) */
      int idx[64]; for (int r = 0; r < k; r++) idx[r] = r;
      for (;;) {
        mask_t C = 0; for (int r = 0; r < k; r++) C |= (mask_t)1 << jg[idx[r]];
        mask_t X = Bo | (J & ~C);
        int ok = 1;
        for (int j = 0; j < n && ok; j++) if (j != o && threatened(j, cur[j], X, bo[j])) ok = 0;
        if (ok) {
          int df = k - So_of(o, X, NAo, S, cap[o]);
          if (df < best) { best = df; cert_o = o; cert_C = C; if (stop_le0 && best <= 0) return best; }
        }
        int r = k - 1; while (r >= 0 && idx[r] == nj - k + r) r--;
        if (r < 0) break;
        idx[r]++; for (int s = r + 1; s < k; s++) idx[s] = idx[s - 1] + 1;
      }
    }
  }
  return best;
}

/* exact completability (weaker form) of bo[] */
static int pt_n, pt_j[MAXN], pt_cap[MAXN], pt_need[MAXN];
static int protect(int k, mask_t rest) {
  if (k == pt_n) return 1;
  int j = pt_j[k]; mask_t av = rest & R[j];
  int bv = vs[j][cur[j]][optl[j][bo[j]]];
  for (mask_t c = av;; c = (c - 1) & av) {
    if (c && pc(c) <= pt_cap[k] && bv + vs[j][cur[j]][loc(j, c)] >= pt_need[k] && protect(k + 1, rest & ~c)) return 1;
    if (!c) break;
  }
  return 0;
}
static int completable(mask_t used, mask_t NA) {
  mask_t J = ALL & ~used;
  int frozen[MAXN], S = 0;
  for (int i = 0; i < n; i++) {
    frozen[i] = optsz[i][bo[i]] == 1 && (optg[i][bo[i]] & NA);
    if (!frozen[i]) S += 2 - optsz[i][bo[i]];
  }
  if (pc(J) <= S) return 1;
  for (int o = 0; o < n; o++) {
    if (frozen[o]) continue;
    mask_t NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= needT[j][cur[j]][bo[j]];
    mask_t Bo = optg[o][bo[o]];
    for (mask_t K = J;; K = (K - 1) & J) {
      mask_t X = Bo | K, rest = J & ~K;
      mask_t NAp = wbase ? (NAo | glob(o, oneed[o][cur[o]][loc(o, X)])) : NA;
      int capj[MAXN], cs = 0;
      for (int j = 0; j < n; j++) if (j != o) { capj[j] = (optsz[j][bo[j]] == 1 && (optg[j][bo[j]] & NAp)) ? 0 : 2 - optsz[j][bo[j]]; cs += capj[j]; }
      if (pc(rest) <= cs) {
        pt_n = 0; int bad = 0;
        for (int j = 0; j < n && !bad; j++) {
          if (j == o || !X) continue;
          int q = loc(j, X), th = thr[j][cur[j]][q][(X & ~R[j]) == 0];
          if (th > vs[j][cur[j]][optl[j][bo[j]]]) {
            if (!capj[j]) bad = 1;
            else { pt_j[pt_n] = j; pt_cap[pt_n] = capj[j]; pt_need[pt_n] = th; pt_n++; }
          }
        }
        if (!bad && protect(0, rest)) return 1;
      }
      if (!K) break;
    }
  }
  return 0;
}

/* ------------------------------------------------------------------------------------------------------------ */
/* single-profile solve */
static int s_best;
static int leaf_fstar(mask_t used, mask_t sing, mask_t NA) { (void)used; (void)sing; s_best = pc(NA); gbound = s_best - 1; return gbound < 0; }
static int fstar(void) { s_best = INF; gbound = n; leaf = leaf_fstar; enumerate(); return s_best; }

static int sol_b[MAXN], sol_o; static mask_t sol_C; static int sol_f;
static int leaf_cert(mask_t used, mask_t sing, mask_t NA) {
  (void)sing;
  if (pc(NA) != gbound) return 0;
  int df = deficit(used, NA, 1);
  if (df <= 0) { memcpy(sol_b, bo, sizeof bo); sol_o = cert_o; sol_C = cert_C; return 1; }
  return 0;
}
/* returns 1 if C4min holds (certificate in sol_*), 0 if it fails; *fs = f* */
static int solve(int *fs) {
  int f = fstar(); *fs = f; sol_f = f;
  gbound = f; leaf = leaf_cert;
  return enumerate();
}

/* full statistics of one profile */
static long long st_valid, st_minF, st_good, st_comp, st_defsum; static int st_dmin, st_dmin_any;
static int leaf_stats(mask_t used, mask_t sing, mask_t NA) {
  (void)sing;
  st_valid++;
  int df = deficit(used, NA, 0);
  st_defsum += df < 99 ? df : 99;
  if (df < st_dmin_any) st_dmin_any = df;
  if (pc(NA) == sol_f) {
    st_minF++;
    if (df < st_dmin) st_dmin = df;
    if (df <= 0) { st_good++; st_comp = 1; }            /* removal-only completable ⇒ completable */
    else if (!st_comp && completable(used, NA)) st_comp = 1;
  }
  return 0;
}
/* d* (least deficit over min-frozen P), number of valid / min-frozen / min-frozen with def <= 0 P, and whether some
   min-frozen P is completable (exact) */
static void stats(int *f, int *dstar, long long *nv, long long *nmin, long long *ngood, int *comp) {
  sol_f = fstar(); *f = sol_f;
  st_valid = st_minF = st_good = st_defsum = 0; st_dmin = st_dmin_any = INF; st_comp = 0;
  gbound = n; leaf = leaf_stats; enumerate();
  *dstar = st_dmin; *nv = st_valid; *nmin = st_minF; *ngood = st_good; *comp = (int)st_comp;
}

/* the least deficit over min-frozen P only (the objective of the climber): cheaper than stats() */
static int ob_f; static long long ob_good, ob_cap = 1LL << 60; static int ob_d;
static int leaf_obj(mask_t used, mask_t sing, mask_t NA) {
  (void)sing;
  if (pc(NA) != ob_f) return 0;
  int df = deficit(used, NA, 0);
  if (df < ob_d) ob_d = df;
  if (df <= 0) ob_good++;
  return ob_good > ob_cap;            /* -C: stop counting witnesses beyond the cap (d* is then over those seen) */
}
static void objective(int *dstar, long long *ngood, int *f) {
  ob_f = fstar(); *f = ob_f; ob_d = INF; ob_good = 0;
  gbound = ob_f; leaf = leaf_obj; enumerate();
  *dstar = ob_d; *ngood = ob_good;
}

static void print_profile(FILE *fp) {
  fprintf(fp, " types");
  for (int i = 0; i < n; i++) fprintf(fp, " %d", cur[i]);
  fprintf(fp, " values");
  for (int i = 0; i < n; i++) { fprintf(fp, " ["); for (int k = 0; k < d[i]; k++) fprintf(fp, "%s%d:%d", k ? "," : "", gl[i][k], tv[i][cur[i]][k]); fprintf(fp, "]"); }
}

/* ------------------------------------------------------------------------------------------------------------ */
/* exhaustive mode: slices over the last agent L's types */
typedef struct { mask_t w[TW]; } tm_t;
static int L, TWn;
static inline void tm_clear(tm_t *a) { memset(a, 0, sizeof *a); }
static inline int tm_any(const tm_t *a) { for (int w = 0; w < TWn; w++) if (a->w[w]) return 1; return 0; }
static inline void tm_or(tm_t *a, const tm_t *b) { for (int w = 0; w < TWn; w++) a->w[w] |= b->w[w]; }
static inline void tm_and(tm_t *a, const tm_t *b) { for (int w = 0; w < TWn; w++) a->w[w] &= b->w[w]; }
static inline void tm_andnot(tm_t *a, const tm_t *b) { for (int w = 0; w < TWn; w++) a->w[w] &= ~b->w[w]; }
static inline int tm_get(const tm_t *a, int t) { return a->w[t >> 6] >> (t & 63) & 1; }
static inline void tm_set(tm_t *a, int t) { a->w[t >> 6] |= (mask_t)1 << (t & 63); }

#define MAXCL 16
static int ncl[NOPT]; static mask_t clneed[NOPT][MAXCL]; static tm_t cltm[NOPT][MAXCL];   /* L's need classes per option */
static int nocl[16]; static unsigned char ocl[16][MAXCL]; static tm_t ocltm[16][MAXCL];  /* L as owner: classes of N^X per q */
static tm_t TH[NOPT][16][2];                                                            /* L threatened */
static tm_t FULL;

static void slice_tables(void) {
  L = n - 1; TWn = (nt[L] + 63) / 64;
  tm_clear(&FULL); for (int t = 0; t < nt[L]; t++) tm_set(&FULL, t);
  for (int k = 0; k < nopt[L]; k++) {
    ncl[k] = 0;
    for (int t = 0; t < nt[L]; t++) {
      mask_t nd = needT[L][t][k]; int c;
      for (c = 0; c < ncl[k]; c++) if (clneed[k][c] == nd) break;
      if (c == ncl[k]) { if (c == MAXCL) { fprintf(stderr, "MAXCL\n"); exit(3); } clneed[k][c] = nd; tm_clear(&cltm[k][c]); ncl[k]++; }
      tm_set(&cltm[k][c], t);
    }
    for (int q = 0; q < 16; q++) for (int in = 0; in < 2; in++) {
      tm_clear(&TH[k][q][in]);
      if (q >= (1 << d[L])) continue;
      for (int t = 0; t < nt[L]; t++) if (q && thr[L][t][q][in] > vs[L][t][optl[L][k]]) tm_set(&TH[k][q][in], t);
    }
  }
  for (int q = 0; q < (1 << d[L]); q++) {
    nocl[q] = 0;
    for (int t = 0; t < nt[L]; t++) {
      int on = oneed[L][t][q], c;
      for (c = 0; c < nocl[q]; c++) if (ocl[q][c] == on) break;
      if (c == nocl[q]) { ocl[q][c] = (unsigned char)on; tm_clear(&ocltm[q][c]); nocl[q]++; }
      tm_set(&ocltm[q][c], t);
    }
  }
}

/* E_f (types of L for which some valid P has |NA| <= f), lazily per slice */
static tm_t Emask[MAXN + 1]; static int Edone[MAXN + 1];
static tm_t *Eacc; static int Ef;
static void edfs(int i, mask_t used, mask_t sing, mask_t two, mask_t NA) {
  if (i == L) {
    for (int k = 0; k < nopt[L]; k++) {
      mask_t B = optg[L][k];
      if (B & used) continue;
      mask_t sing2 = sing | (optsz[L][k] == 1 ? B : 0), two2 = two | (optsz[L][k] == 2 ? B : 0);
      for (int c = 0; c < ncl[k]; c++) {
        mask_t NA2 = NA | clneed[k][c];
        if (pc(NA2) > Ef || (NA2 & ~sing2) || (NA2 & two2)) continue;
        tm_or(Eacc, &cltm[k][c]);
      }
    }
    return;
  }
  for (int k = 0; k < nopt[i]; k++) {
    mask_t B = optg[i][k];
    if (B & used) continue;
    mask_t NA2 = NA | needT[i][cur[i]][k];
    if (pc(NA2) > Ef) continue;
    mask_t used2 = used | B, sing2 = sing, two2 = two;
    if (optsz[i][k] == 1) sing2 |= B; else if (optsz[i][k] == 2) two2 |= B;
    if (NA2 & two2) continue;
    mask_t pend = NA2 & ~used2;
    if (pend & ~valued_from[i + 1]) continue;
    if (pc(pend) > n - i - 1) continue;
    edfs(i + 1, used2, sing2, two2, NA2);
  }
}
static const tm_t *E(int f) {
  if (f < 0) { static tm_t z; tm_clear(&z); return &z; }
  if (!Edone[f]) { tm_clear(&Emask[f]); Eacc = &Emask[f]; Ef = f; edfs(0, 0, 0, 0, 0); Edone[f] = 1; }
  return &Emask[f];
}

typedef struct { unsigned char b[MAXN]; mask_t need[MAXN]; int o, f, noowner; mask_t C; } tmpl_t;
#define NCACHE 48
static tmpl_t cache[NCACHE]; static int ncache;
static long long c_prof, c_solved, c_fail, c_tmpl, c_hits, c_fstar[MAXN + 2], c_verified;

/* mask of L's types covered by template T in the current slice (types of agents < L in cur) */
static void tmpl_mask(const tmpl_t *T, tm_t *M) {
  tm_clear(M);
  for (int i = 0; i < L; i++) if (needT[i][cur[i]][T->b[i]] != T->need[i]) return;
  int kL = T->b[L], c;
  for (c = 0; c < ncl[kL]; c++) if (clneed[kL][c] == T->need[L]) break;
  if (c == ncl[kL]) return;
  *M = cltm[kL][c];
  if (T->noowner) return;
  mask_t used = 0; for (int i = 0; i < n; i++) used |= optg[i][T->b[i]];
  mask_t J = ALL & ~used, X = optg[T->o][T->b[T->o]] | (J & ~T->C);
  int o = T->o, kC = pc(T->C);
  for (int j = 0; j < L; j++) if (j != o && threatened(j, cur[j], X, T->b[j])) { tm_clear(M); return; }
  mask_t NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= T->need[j];
  if (o < L) {
    int So;
    if (wbase) {
      mask_t NAp = NAo | glob(o, oneed[o][cur[o]][loc(o, X)]); So = 0;
      for (int j = 0; j < n; j++) if (j != o) So += (optsz[j][T->b[j]] == 1 && (optg[j][T->b[j]] & NAp)) ? 0 : 2 - optsz[j][T->b[j]];
    } else {
      mask_t NA = NAo | T->need[o]; So = 0;
      for (int j = 0; j < n; j++) if (j != o) So += (optsz[j][T->b[j]] == 1 && (optg[j][T->b[j]] & NA)) ? 0 : 2 - optsz[j][T->b[j]];
    }
    if (kC > So) { tm_clear(M); return; }
    tm_andnot(M, &TH[kL][loc(L, X)][(X & ~R[L]) == 0]);
  } else {
    tm_t ok; tm_clear(&ok);
    if (wbase) {
      int q = loc(L, X);
      for (int cc = 0; cc < nocl[q]; cc++) {
        mask_t NAp = NAo | glob(L, ocl[q][cc]); int So = 0;
        for (int j = 0; j < n; j++) if (j != o) So += (optsz[j][T->b[j]] == 1 && (optg[j][T->b[j]] & NAp)) ? 0 : 2 - optsz[j][T->b[j]];
        if (kC <= So) tm_or(&ok, &ocltm[q][cc]);
      }
    } else {
      mask_t NA = NAo | T->need[o]; int So = 0;
      for (int j = 0; j < n; j++) if (j != o) So += (optsz[j][T->b[j]] == 1 && (optg[j][T->b[j]] & NA)) ? 0 : 2 - optsz[j][T->b[j]];
      if (kC <= So) ok = FULL;
    }
    tm_and(M, &ok);
  }
  if (T->f > sigma) tm_andnot(M, E(T->f - 1));
}

/* -B K: after a solve, look at up to K certificates (min-frozen P with deficit <= 0, each with its owner and C) and
   keep the one whose template covers most of the uncovered types of the slice */
static int bestK = 1, bk_found, bk_bestcov, bk_f; static tm_t *bk_U; static tmpl_t bk_best;
static int leaf_bestk(mask_t used, mask_t sing, mask_t NA) {
  (void)sing;
  if (pc(NA) != gbound || deficit(used, NA, 1) > 0) return 0;
  tmpl_t T; memset(&T, 0, sizeof T);
  for (int i = 0; i < n; i++) { T.b[i] = (unsigned char)bo[i]; T.need[i] = needT[i][cur[i]][bo[i]]; }
  T.o = cert_o; T.C = cert_C; T.f = bk_f; T.noowner = cert_o < 0;
  tm_t M; tmpl_mask(&T, &M); tm_and(&M, bk_U);
  int cov = 0; for (int w = 0; w < TWn; w++) cov += pc(M.w[w]);
  if (cov > bk_bestcov) { bk_bestcov = cov; bk_best = T; }
  return ++bk_found >= bestK;
}

static void exhaustive(int lo, int hi) {
  slice_tables();
  valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
  for (int i = 0; i < n; i++) cur[i] = 0;
  cur[0] = lo;
  if (lo >= hi) return;
  for (;;) {
    /* one slice: agents 0..L-1 fixed */
    for (int f = 0; f <= n; f++) Edone[f] = 0;
    tm_t U = FULL, FM; tm_clear(&FM);
    c_prof += nt[L];
    for (int ci = 0; ci < ncache && tm_any(&U); ci++) {
      tm_t M; tmpl_mask(&cache[ci], &M);
      tm_t hit = M; tm_and(&hit, &U);
      if (tm_any(&hit)) {
        c_hits++;
        tm_andnot(&U, &M);
        if (ci > 0) { tmpl_t tmp = cache[ci]; memmove(&cache[1], &cache[0], ci * sizeof(tmpl_t)); cache[0] = tmp; }
      }
    }
    while (tm_any(&U)) {
      int t = 0; while (!tm_get(&U, t)) t++;
      cur[L] = t;
      int f, ok = solve(&f);
      c_solved++; if (f <= n) c_fstar[f]++;
      if (!ok) {
        c_fail++;
        if (c_fail <= nex) { printf("FAIL fstar %d", f); print_profile(stdout); printf("\n"); fflush(stdout); }
        U.w[t >> 6] &= ~((mask_t)1 << (t & 63));
        tm_set(&FM, t);
        continue;
      }
      tmpl_t T; memset(&T, 0, sizeof T);
      for (int i = 0; i < n; i++) { T.b[i] = (unsigned char)sol_b[i]; T.need[i] = needT[i][cur[i]][sol_b[i]]; }
      T.o = sol_o; T.C = sol_C; T.f = f; T.noowner = sol_o < 0;
      if (bestK > 1) {
        gbound = f; leaf = leaf_bestk; bk_U = &U; bk_found = 0; bk_bestcov = -1; bk_f = f;
        enumerate();
        if (bk_bestcov > 0) T = bk_best;
      }
      tm_t M; tmpl_mask(&T, &M);
      if (!tm_get(&M, t)) { fprintf(stderr, "internal error: template does not cover its own profile\n"); print_profile(stderr); fprintf(stderr, "\n"); exit(4); }
      tm_andnot(&U, &M);
      c_tmpl++;
      int sz = ncache < NCACHE ? ncache + 1 : NCACHE;
      memmove(&cache[1], &cache[0], (sz - 1) * sizeof(tmpl_t)); cache[0] = T; ncache = sz;
    }
    if (verify) {   /* re-solve every profile of the slice from scratch */
      for (int t = 0; t < nt[L]; t++) {
        cur[L] = t; int f; int ok = solve(&f); c_verified++;
        if (ok == tm_get(&FM, t)) { printf("MISMATCH (masks and a fresh solve disagree)"); print_profile(stdout); printf("\n"); exit(5); }
      }
    }
    /* next slice */
    int i = L - 1;
    while (i >= 1 && ++cur[i] == nt[i]) { cur[i] = 0; i--; }
    if (i < 1) { if (++cur[0] >= hi) break; for (int k = 1; k < L; k++) cur[k] = 0; }
    if (L == 1 && cur[0] >= hi) break;
  }
}

/* ------------------------------------------------------------------------------------------------------------ */
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* -H: hill-climbing. Objective (maximized, lexicographic): first whether an owner is needed (f* > σ; otherwise every
   min-frozen P has deficit f* - σ <= 0 and C4min holds trivially), then -O0 (d*, -good) or -O1 (-good, d*), where
   good = the number of min-frozen P with deficit <= 0 (C4min fails iff good = 0 iff d* > 0). Moves: one agent (or,
   with probability 1/4, two agents) take random other types; a move is kept if the objective does not decrease. A
   restart ends after `stale` moves without strict improvement. -P: the first restart starts from the profile given
   after the types. */
static int obj_order = 0, stale_lim = 400, start_given = 0, start_p[MAXN], perturb = 1, anneal = 0;
static int better(int f1, int d1, long long g1, int f2, int d2, long long g2) {   /* 2 strictly better, 1 equal, 0 worse */
  int o1 = f1 > sigma, o2 = f2 > sigma;
  if (o1 != o2) return o1 > o2 ? 2 : 0;
  if (obj_order == 2) {                /* -O2: (owner needed, f*, -good, d*) */
    if (f1 != f2) return f1 > f2 ? 2 : 0;
    if (g1 != g2) return g1 < g2 ? 2 : 0;
    if (d1 != d2) return d1 > d2 ? 2 : 0;
    return 1;
  }
  long long a1 = obj_order ? -g1 : d1, b1 = obj_order ? d1 : -g1, a2 = obj_order ? -g2 : d2, b2 = obj_order ? d2 : -g2;
  if (a1 != a2) return a1 > a2 ? 2 : 0;
  if (b1 != b2) return b1 > b2 ? 2 : 0;
  return 1;
}
static void climb(long long iters, int restarts) {
  valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
  int bestd = -INF, bestf = 0; long long bestg = 1LL << 60; int bestp[MAXN]; long long evals = 0, ncex = 0;
  for (int r = 0; r < restarts; r++) {
    for (int i = 0; i < n; i++) cur[i] = (r == 0 && start_given) ? start_p[i] : (int)(rnd() % (uint64_t)nt[i]);
    int dcur, fcur; long long gcur; objective(&dcur, &gcur, &fcur); evals++;
    long long stale = 0;
    for (long long it = 0; it < iters && stale <= stale_lim; it++) {
      int old[MAXN]; memcpy(old, cur, sizeof old);
      int k = (rnd() % 4 == 0 && n > 1) ? 2 : 1;
      for (int q = 0; q < k; q++) {
        int i = (int)(rnd() % (uint64_t)n);
        if (nt[i] < 2) continue;
        int t = (int)(rnd() % (uint64_t)(nt[i] - 1)); if (t >= cur[i]) t++;
        cur[i] = t;
      }
      int dn, fn; long long gn; objective(&dn, &gn, &fn); evals++;
      int c = better(fn, dn, gn, fcur, dcur, gcur);
      if (!c && anneal && (int)(rnd() % 1000) < anneal) c = 1;     /* -A: accept a worse move with probability A/1000 */
      if (c) {
        stale = c == 2 ? 0 : stale + 1;
        dcur = dn; gcur = gn; fcur = fn;
        if (dcur > 0 && c == 2) { ncex++; printf("CEX dstar %d fstar %d", dcur, fcur); print_profile(stdout); printf("\n"); fflush(stdout); }
      } else { memcpy(cur, old, sizeof old); stale++; }
    }
    if (r == 0 || better(fcur, dcur, gcur, bestf, bestd, bestg) == 2) { bestd = dcur; bestg = gcur; bestf = fcur; memcpy(bestp, cur, sizeof bestp); }
    /* with -A the end point need not be the best of the restart; the CEX lines above report every d* > 0 seen */
    printf("RESTART %d dstar %d good %lld fstar %d owner %d\n", r, dcur, gcur, fcur, fcur > sigma); fflush(stdout);
  }
  memcpy(cur, bestp, sizeof bestp);
  printf("BEST dstar %d good %lld fstar %d evals %lld cex %lld owner %d sigma %d", bestd, bestg, bestf, evals, ncex, bestf > sigma, sigma); print_profile(stdout); printf("\n");
}

int main(int argc, char **argv) {
  int mode = 0, restarts = 1; long long iters = 0; unsigned long long seed = 1;
  for (int a = 1; a < argc; a++) {
    if (!strcmp(argv[a], "-w0")) wbase = 0;
    else if (!strcmp(argv[a], "-E")) mode = 'E';
    else if (!strcmp(argv[a], "-V")) verify = 1;
    else if (!strcmp(argv[a], "-1")) mode = '1';
    else if (!strcmp(argv[a], "-1q")) mode = 'q';
    else if (!strcmp(argv[a], "-1o")) mode = 'o';
    else if (!strcmp(argv[a], "-1f")) mode = 'F';
    else if (!strcmp(argv[a], "-H")) { mode = 'H'; iters = atoll(argv[++a]); }
    else if (!strcmp(argv[a], "-R")) { mode = 'R'; iters = atoll(argv[++a]); }
    else if (!strcmp(argv[a], "-K")) perturb = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-C")) ob_cap = atoll(argv[++a]);
    else if (!strcmp(argv[a], "-B")) bestK = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-A")) anneal = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-Z")) restarts = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-O")) obj_order = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-T")) stale_lim = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-P")) start_given = 1;
    else if (!strcmp(argv[a], "-S")) seed = strtoull(argv[++a], 0, 10);
    else if (!strcmp(argv[a], "-x")) nex = atoi(argv[++a]);
    else if (!strcmp(argv[a], "-D")) plain_def = 1;
    else if (!strcmp(argv[a], "-Y0")) dyn = 0;
    else if (!strcmp(argv[a], "-Y1")) dyn = 1;
    else if (!strcmp(argv[a], "-G1")) hall = 1;
    else { fprintf(stderr, "unknown option %s\n", argv[a]); return 2; }
  }
  if (scanf("%d %d", &n, &m) != 2) return 2;
  if (n > MAXN || m > 64) { fprintf(stderr, "too large\n"); return 2; }
  sigma = 2 * n - m; ALL = m == 64 ? ~(mask_t)0 : (((mask_t)1 << m) - 1);
  for (int i = 0; i < n; i++) {
    if (scanf("%d", &d[i]) != 1) return 2;
    for (int k = 0; k < d[i]; k++) if (scanf("%d", &gl[i][k]) != 1) return 2;
    if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) return 2;
    for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 2;
    R[i] = 0; for (int k = 0; k < d[i]; k++) R[i] |= (mask_t)1 << gl[i][k];
    nopt[i] = 0;
    for (int s = 0; s < (1 << d[i]); s++) if (pc(s) <= 2) {
      optl[i][nopt[i]] = s; optsz[i][nopt[i]] = pc(s); optg[i][nopt[i]] = 0;
      for (int k = 0; k < d[i]; k++) if (s >> k & 1) optg[i][nopt[i]] |= (mask_t)1 << gl[i][k];
      nopt[i]++;
    }
  }
  tables();
  rs = seed * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
  if (mode == 'E') {
    int lo, hi; if (scanf("%d %d", &lo, &hi) != 2) { lo = 0; hi = nt[0]; }
    if (lo < 0) lo = 0;
    if (hi > nt[0]) hi = nt[0];
    if (n < 2) return 2;
    exhaustive(lo, hi);
    printf("RESULT profiles %lld solved %lld templates %lld cachehits %lld fails %lld verified %lld fstar_solved", c_prof, c_solved, c_tmpl, c_hits, c_fail, c_verified);
    for (int f = 0; f <= n; f++) printf(" %lld", c_fstar[f]);
    printf("\n");
  } else if (mode == '1') {
    for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2;
    valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
    int f, ds, comp; long long nv, nmin, ng; stats(&f, &ds, &nv, &nmin, &ng, &comp);
    printf("PROFILE fstar %d dstar %d valid %lld minfrozen %lld good %lld completable %d sigma %d defsum %lld", f, ds, nv, nmin, ng, comp, sigma, st_defsum);
    print_profile(stdout); printf("\n");
  } else if (mode == 'q') {
    for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2;
    valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
    int f, ok = solve(&f);
    printf("QUICK fstar %d holds %d sigma %d", f, ok, sigma);
    if (ok) {
      printf(" owner %d C", sol_o); for (int g = 0; g < m; g++) if (sol_o >= 0 && (sol_C >> g & 1)) printf(" %d", g);
      printf(" bases"); for (int i = 0; i < n; i++) { printf(" {"); int first = 1; for (int g = 0; g < m; g++) if (optg[i][sol_b[i]] >> g & 1) { printf(first ? "%d" : ",%d", g); first = 0; } printf("}"); }
    }
    printf("\n");
  } else if (mode == 'F') {           /* f* only */
    for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2;
    valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
    printf("FSTAR %d\n", fstar());
  } else if (mode == 'o') {
    /* per owner o: the least deficit over the min-frozen P when only o may be the owner (INF: never free) */
    for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2;
    valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
    int f = fstar();
    printf("OWNERS fstar %d sigma %d", f, sigma);
    for (int o = 0; o < n; o++) {
      only_own = o; ob_f = f; ob_d = INF; ob_good = 0; gbound = f; leaf = leaf_obj; enumerate();
      printf(" %d", ob_d);
    }
    only_own = -1;
    printf("\n");
  } else if (mode == 'R') {
    /* random profiles: uniform, or (-P) the given profile with -K agents re-typed at random */
    if (start_given) for (int i = 0; i < n; i++) if (scanf("%d", &start_p[i]) != 1) return 2;
    valued_from[n] = 0; for (int i = n - 1; i >= 0; i--) valued_from[i] = valued_from[i + 1] | R[i];
    long long fails = 0, hist[MAXN + 2] = {0}, owner = 0;
    for (long long r = 0; r < iters; r++) {
      if (start_given) {
        memcpy(cur, start_p, sizeof cur);
        for (int q = 0; q < perturb; q++) { int i = (int)(rnd() % (uint64_t)n); cur[i] = (int)(rnd() % (uint64_t)nt[i]); }
      } else for (int i = 0; i < n; i++) cur[i] = (int)(rnd() % (uint64_t)nt[i]);
      int f, ok = solve(&f);
      if (f <= n) hist[f]++;
      owner += f > sigma;
      if (!ok) { fails++; if (fails <= nex) { printf("FAIL fstar %d", f); print_profile(stdout); printf("\n"); fflush(stdout); } }
    }
    printf("RANDOM profiles %lld fails %lld owner_needed %lld fstar", iters, fails, owner);
    for (int f = 0; f <= n; f++) printf(" %lld", hist[f]);
    printf("\n");
  } else if (mode == 'H') {
    if (start_given) for (int i = 0; i < n; i++) if (scanf("%d", &start_p[i]) != 1) return 2;
    climb(iters, restarts);
  }
  return 0;
}
