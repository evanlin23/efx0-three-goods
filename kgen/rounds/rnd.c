/* rnd.c -- ROUND+ checker (workstream proof/kgen-rounds, kgen/rounds.md).

Setting: n agents, m goods, strictly positive additive values (so EFX0 = EFX).  For every order pi the serial-
dictatorship picks y (favourite remaining good, ties to the smaller index) give every agent one pick; J = M - picks.

This file enumerates EVERY complete EFX allocation X (raw definition, DFS with a sound pruning bound: once
v_i(X_j) - min_i(X_j) exceeds v_i(X_i) + v_i(unassigned goods) no completion can repair it) and, for every distinct
start, counts the allocations X that witness each of these classes (definitions in kgen/rounds.md §1; k4/sdc.md §29,
k4/ksens.md §6):

  K_EXTF  picks extend, free completion:            y_a in X_a for every a
  K_EXT1  picks extend, one absorber:               ... and at most one agent holds >= 2 goods besides its pick
  K_OC1   one chain (t >= 0) + one-absorber completion (OC1(t >= 0) of k4/sdc.md §29, kgen/n3.md §1), zero chains included
  K_RNDF  one round of vertex-disjoint chains + free completion (zero chains included)
  K_RND1  one round + one-absorber completion
  K_MD    X value-dominates the picks: v_i(X_i) >= v_i(y_i) for all i

Reachability of X by one round (the round analogue of kgen/n3.md Lemma R; proof in kgen/rounds.md §1): let loc(a)
be the holder of y_a in X.  A round is a set of vertex-disjoint chains; with all values positive we may take every
H maximal (H_i = X_{x_i} cap J, H_0 = X_{x_0} cap (J + B_{x_t})).  Every agent a with loc(a) != a is on a chain, and
either passes its pick to s(a) = loc(a), or is a chain end (its pick is taken by its own chain start x_0 -- a ring --
or released to the junk and placed by the completion).  So we enumerate the set E of ends among the moved agents
(at most 2^n choices); passers s(a) = loc(a) must be injective and acyclic; every end needs a predecessor; then the
strict gains are checked:
   receiver b (predecessor p):  v_b(y_p) + v_b(X_b cap J) > v_b(y_b)
   start x_0 (end e):           v_{x0}(X_{x0} cap J) + [loc(e) = x0] v_{x0}(y_e) > v_{x0}(y_{x0})
Agents that keep their pick and hold junk make t = 0 moves (positive values: the gain is automatic), so in a round
the only goods outside bases are released picks.  For OC1 (one chain) off-chain agents' junk counts toward the
absorber; with no t >= 1 chain one agent may take a t = 0 move.

Build:  gcc -O2 -shared -fPIC -o librnd.so rnd.c      (used through kgen/rounds/rndlib.py)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 7
#define MAXM 16
#define MAXS 5040
enum { K_EXTF, K_EXT1, K_OC1, K_RNDF, K_RND1, K_MD, K_RNDX, K_RNDX1, K_RNDP, K_RNDP1, NK };
/* K_RNDP: ROUND-P, a round in which EVERY chain agent may take goods of the pool (junk + every chain end's pick);
   K_RNDP1 with the one-absorber completion (pool picks held by off-chain agents count) */
/* K_RNDX: ROUND-X, a round in which every chain start may take, besides junk, the released pick of ANY chain end
   (a common pool); K_RNDX1 the same with the one-absorber completion (released picks not taken count) */

typedef long long ll;

static int n, m;
static ll v[MAXN][MAXM];
static int nst;                      /* distinct starts */
static int pick[MAXS][MAXN];         /* pick[s][a] = good */
static int sorder[MAXS][MAXN];
static ll cnt[MAXS][NK];
static double msum[MAXS], mmax[MAXS];   /* over RND1 witnesses: sum / max of the witness margin */
static double tot_i[MAXN], efx_margin, best_gm;
static int margin_kind = K_RND1;          /* class whose witnesses' margins are accumulated */
static ll cap;
static int want_mask;                /* classes whose counters gate early stopping */
static int owner[MAXM];
static int gord[MAXM];
static ll val[MAXN][MAXN], mn[MAXN][MAXN], rem[MAXN];
static int bsz[MAXN];
static ll nefx;
static int done_flag;
/* witness capture */
static int wit_start = -1, wit_kind = -1, wit_found = 0, wit_owner[MAXM];
static int wit_info[4 * MAXN];      /* for rounds: s(a) (or -1), end flag, start-of-chain */

static void sd(const int *order, int *y) {
    int used[MAXM] = {0};
    for (int k = 0; k < n; k++) {
        int a = order[k], best = -1;
        for (int g = 0; g < m; g++) if (!used[g] && (best < 0 || v[a][g] > v[a][best])) best = g;
        y[a] = best; if (best >= 0) used[best] = 1;
    }
}

/* round / chain analysis of the complete allocation in owner[] for start s; returns bitmask of classes */
static int analyze_start(int s, int record) {
    int *y = pick[s];
    int loc[MAXN], isj[MAXM];
    ll vJ[MAXN]; int nJ[MAXN];
    for (int g = 0; g < m; g++) isj[g] = 1;
    for (int a = 0; a < n; a++) isj[y[a]] = 0;
    for (int a = 0; a < n; a++) { loc[a] = owner[y[a]]; vJ[a] = 0; nJ[a] = 0; }
    for (int g = 0; g < m; g++) if (isj[g]) { int b = owner[g]; vJ[b] += v[b][g]; nJ[b]++; }
    int res = 0;
    best_gm = -1;
    /* MD */
    int md = 1;
    for (int a = 0; a < n; a++) if (val[a][a] < v[a][y[a]]) { md = 0; break; }
    if (md) res |= 1 << K_MD; else return 0;      /* every other class implies MD */
    int Mv = 0;
    for (int a = 0; a < n; a++) if (loc[a] != a) Mv |= 1 << a;
    if (Mv == 0) {
        res |= 1 << K_EXTF;
        int big = 0; for (int a = 0; a < n; a++) if (nJ[a] >= 2) big++;
        if (big <= 1) res |= 1 << K_EXT1;
        if (big <= 2) res |= 1 << K_OC1;          /* one t = 0 move plus one absorber */
        res |= (1 << K_RNDF) | (1 << K_RND1) | (1 << K_RNDX) | (1 << K_RNDX1) | (1 << K_RNDP) | (1 << K_RNDP1);
        if (record) { for (int a = 0; a < n; a++) { wit_info[a] = -1; wit_info[n + a] = 0; wit_info[2 * n + a] = -1; } }
        best_gm = 1e9;                             /* no gain inequality: the witness margin is the EFX margin */
        return res;
    }
    /* enumerate subsets E of Mv = ends */
    for (int E = Mv;; E = (E - 1) & Mv) {
        int P = Mv & ~E;
        int pred[MAXN], succ[MAXN], ok = 1, tg = 0;
        for (int a = 0; a < n; a++) { pred[a] = -1; succ[a] = -1; }
        for (int a = 0; a < n && ok; a++) if (P >> a & 1) {
            int b = loc[a];
            if (tg >> b & 1) ok = 0; else { tg |= 1 << b; pred[b] = a; succ[a] = b; }
        }
        if (ok) {   /* acyclic */
            for (int a = 0; a < n && ok; a++) if (P >> a & 1) {
                int c = a, steps = 0;
                while (succ[c] >= 0 && steps <= n) { c = succ[c]; steps++; if (c == a) { ok = 0; break; } }
            }
        }
        if (ok) for (int a = 0; a < n && ok; a++) if ((E >> a & 1) && pred[a] < 0) ok = 0;
        if (ok) {   /* ROUND-P: every chain agent's base = (pred's pick) + its junk + every end's pick it holds */
            int okp = 1, relp[MAXN], onch[MAXN];
            double gmp = 1e9;
            for (int a = 0; a < n; a++) { relp[a] = 0; onch[a] = (succ[a] >= 0 || pred[a] >= 0); }
            for (int a = 0; a < n && okp; a++) if (onch[a]) {
                ll b0 = vJ[a] + (pred[a] >= 0 ? v[a][y[pred[a]]] : 0);
                for (int e = 0; e < n; e++) if (pred[e] >= 0 && succ[e] < 0 && loc[e] == a) b0 += v[a][y[e]];
                if (!(b0 > v[a][y[a]])) okp = 0;
                else { double d = (double)(b0 - v[a][y[a]]) / tot_i[a]; if (d < gmp) gmp = d; }
            }
            if (okp) {
                res |= 1 << K_RNDP;
                for (int e = 0; e < n; e++) if (pred[e] >= 0 && succ[e] < 0 && !onch[loc[e]]) relp[loc[e]]++;
                int big = 0; for (int a = 0; a < n; a++) if (relp[a] >= 2) big++;
                if (big <= 1) { res |= 1 << K_RNDP1; if (margin_kind == K_RNDP1 && gmp > best_gm) best_gm = gmp; }
                if (record && wit_kind >= 0 && (res >> wit_kind & 1)) {
                    for (int a = 0; a < n; a++) { wit_info[a] = succ[a]; wit_info[n + a] = (pred[a] >= 0 && succ[a] < 0); wit_info[2 * n + a] = onch[a]; }
                    return res;
                }
            }
        }
        double gm = 1e9;
        if (ok) {
            /* receivers' gains */
            for (int b = 0; b < n && ok; b++) if (pred[b] >= 0) {
                if (!(v[b][y[pred[b]]] + vJ[b] > v[b][y[b]])) ok = 0;
                else { double d = (double)(v[b][y[pred[b]]] + vJ[b] - v[b][y[b]]) / tot_i[b]; if (d < gm) gm = d; }
            }
        }
        int startof[MAXN], nstarts = 0, rel[MAXN];
        for (int a = 0; a < n; a++) { startof[a] = -1; rel[a] = 0; }
        if (ok) {   /* ROUND-X: starts draw from the pool J + every end's pick */
            int okx = 1, relx[MAXN], isstart[MAXN];
            for (int a = 0; a < n; a++) { relx[a] = 0; isstart[a] = (succ[a] >= 0 && pred[a] < 0); }
            double gmx = gm;
            for (int a = 0; a < n && okx; a++) if (isstart[a]) {
                ll g0 = vJ[a];
                for (int e = 0; e < n; e++) if (pred[e] >= 0 && succ[e] < 0 && loc[e] == a) g0 += v[a][y[e]];
                if (!(g0 > v[a][y[a]])) okx = 0;
                else { double d = (double)(g0 - v[a][y[a]]) / tot_i[a]; if (d < gmx) gmx = d; }
            }
            if (okx) {
                res |= 1 << K_RNDX;
                for (int e = 0; e < n; e++) if (pred[e] >= 0 && succ[e] < 0 && !isstart[loc[e]]) relx[loc[e]]++;
                int big = 0; for (int a = 0; a < n; a++) if (relx[a] >= 2) big++;
                if (big <= 1) { res |= 1 << K_RNDX1; if (margin_kind == K_RNDX1 && gmx > best_gm) best_gm = gmx; }
                if (record && wit_kind >= 0 && (res >> wit_kind & 1)) {
                    for (int a = 0; a < n; a++) { wit_info[a] = succ[a]; wit_info[n + a] = (pred[a] >= 0 && succ[a] < 0); wit_info[2 * n + a] = isstart[a] ? a : -1; }
                    return res;
                }
            }
        }
        if (ok) {
            for (int a = 0; a < n && ok; a++) if (succ[a] >= 0 && pred[a] < 0) {
                nstarts++;
                int c = a; startof[c] = a;
                while (succ[c] >= 0) { c = succ[c]; startof[c] = a; }
                int e = c;                     /* end */
                ll g0 = vJ[a] + (loc[e] == a ? v[a][y[e]] : 0);
                if (!(g0 > v[a][y[a]])) ok = 0;
                else { double d = (double)(g0 - v[a][y[a]]) / tot_i[a]; if (d < gm) gm = d; }
                if (loc[e] != a) rel[loc[e]]++;
            }
        }
        if (ok) {
            res |= 1 << K_RNDF;
            int big = 0; for (int a = 0; a < n; a++) if (rel[a] >= 2) big++;
            if (big <= 1) { res |= 1 << K_RND1; if (margin_kind == K_RND1 && gm > best_gm) best_gm = gm; }
            if (nstarts <= 1) {
                int big1 = 0;
                for (int a = 0; a < n; a++) {
                    int out = rel[a] + (startof[a] < 0 ? nJ[a] : 0);
                    if (out >= 2) big1++;
                }
                if (big1 <= 1) res |= 1 << K_OC1;
            }
            if (record && wit_kind >= 0 && (res >> wit_kind & 1)) {
                for (int a = 0; a < n; a++) { wit_info[a] = succ[a]; wit_info[n + a] = (pred[a] >= 0 && succ[a] < 0); wit_info[2 * n + a] = startof[a]; }
                return res;
            }
        }
        if (E == 0) break;
    }
    return res;
}

static void leaf(void) {
    nefx++;
    efx_margin = 1e9;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j && bsz[j] > 0) {
        double d = (double)(val[i][i] - (val[i][j] - mn[i][j])) / tot_i[i]; if (d < efx_margin) efx_margin = d;
    }
    int alldone = 1;
    for (int s = 0; s < nst; s++) {
        if (wit_kind >= 0 && s != wit_start) continue;
        int need = (want_mask == 0);
        for (int k = 0; k < NK; k++) if ((want_mask >> k & 1) && cnt[s][k] < cap) need = 1;
        if (!need && wit_kind < 0) continue;
        int r = analyze_start(s, wit_kind >= 0);
        for (int k = 0; k < NK; k++) if ((r >> k & 1) && cnt[s][k] < cap) cnt[s][k]++;
        if (r >> margin_kind & 1) { double w = efx_margin < best_gm ? efx_margin : best_gm; msum[s] += w; if (w > mmax[s]) mmax[s] = w; }
        if (wit_kind >= 0 && (r >> wit_kind & 1)) {
            for (int g = 0; g < m; g++) wit_owner[g] = owner[g];
            wit_found = 1; done_flag = 1; return;
        }
        for (int k = 0; k < NK; k++) if ((want_mask >> k & 1) && cnt[s][k] < cap) alldone = 0;
    }
    if (wit_kind < 0 && alldone && want_mask != 0) done_flag = 1;
}

static void dfs(int idx) {
    if (done_flag) return;
    if (idx == m) { leaf(); return; }
    int g = gord[idx];
    for (int a = 0; a < n; a++) {
        ll oldmn[MAXN];
        owner[g] = a; bsz[a]++;
        for (int i = 0; i < n; i++) {
            val[i][a] += v[i][g]; rem[i] -= v[i][g];
            oldmn[i] = mn[i][a];
            if (v[i][g] < mn[i][a]) mn[i][a] = v[i][g];
        }
        int bad = 0;
        for (int i = 0; i < n && !bad; i++) {
            ll pot = val[i][i] + rem[i];
            for (int j = 0; j < n; j++) if (j != i && bsz[j] > 0 && val[i][j] - mn[i][j] > pot) { bad = 1; break; }
        }
        if (!bad) dfs(idx + 1);
        for (int i = 0; i < n; i++) { val[i][a] -= v[i][g]; rem[i] += v[i][g]; mn[i][a] = oldmn[i]; }
        bsz[a]--; owner[g] = -1;
        if (done_flag) return;
    }
}

static void setup(int n_, int m_, const ll *vals) {
    n = n_; m = m_;
    for (int i = 0; i < n; i++) for (int g = 0; g < m; g++) v[i][g] = vals[i * m + g];
    /* distinct starts over all orders */
    int perm[MAXN]; for (int i = 0; i < n; i++) perm[i] = i;
    nst = 0;
    /* iterate permutations in lexicographic order */
    while (1) {
        int y[MAXN]; sd(perm, y);
        int found = 0;
        for (int s = 0; s < nst && !found; s++) if (!memcmp(pick[s], y, sizeof(int) * n)) found = 1;
        if (!found) { memcpy(pick[nst], y, sizeof(int) * n); memcpy(sorder[nst], perm, sizeof(int) * n); nst++; }
        int i = n - 2; while (i >= 0 && perm[i] > perm[i + 1]) i--;
        if (i < 0) break;
        int j = n - 1; while (perm[j] < perm[i]) j--;
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        for (int a = i + 1, b = n - 1; a < b; a++, b--) { t = perm[a]; perm[a] = perm[b]; perm[b] = t; }
    }
    /* good order: decreasing total value */
    ll tot[MAXM];
    for (int g = 0; g < m; g++) { tot[g] = 0; for (int i = 0; i < n; i++) tot[g] += v[i][g]; gord[g] = g; }
    for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) if (tot[gord[b]] > tot[gord[a]]) { int t = gord[a]; gord[a] = gord[b]; gord[b] = t; }
    memset(cnt, 0, sizeof(cnt));
    for (int s = 0; s < MAXS; s++) { msum[s] = 0; mmax[s] = 0; }
    for (int i = 0; i < n; i++) { tot_i[i] = 0; for (int g = 0; g < m; g++) tot_i[i] += v[i][g]; }
    for (int i = 0; i < n; i++) {
        rem[i] = 0; for (int g = 0; g < m; g++) rem[i] += v[i][g];
        for (int j = 0; j < n; j++) { val[i][j] = 0; mn[i][j] = (ll)1 << 62; }
        bsz[i] = 0;
    }
    for (int g = 0; g < m; g++) owner[g] = -1;
    nefx = 0; done_flag = 0;
}

/* analyze: counts per distinct start.  out_picks[s*n + a], out_order[s*n + k], out_cnt[s*NK + k].
   cap_ = per-class cap (0 = no early stop, count everything).  wmask = classes gating the early stop.
   returns number of distinct starts; *out_nefx = EFX allocations visited */
int rnd_analyze(int n_, int m_, const ll *vals, ll cap_, int wmask, int *out_picks, int *out_order, ll *out_cnt, ll *out_nefx) {
    if (n_ > MAXN || m_ > MAXM) return -1;
    setup(n_, m_, vals);
    cap = cap_ > 0 ? cap_ : ((ll)1 << 62); want_mask = wmask;
    if (cap_ <= 0) want_mask = 0;
    wit_kind = -1; wit_start = -1;
    dfs(0);
    for (int s = 0; s < nst; s++) {
        for (int a = 0; a < n; a++) { out_picks[s * n + a] = pick[s][a]; out_order[s * n + a] = sorder[s][a]; }
        for (int k = 0; k < NK; k++) out_cnt[s * NK + k] = cnt[s][k];
    }
    *out_nefx = nefx;
    return nst;
}

void rnd_set_margin_kind(int k) { margin_kind = k; }
void rnd_margins(double *out_sum, double *out_max) {
    for (int s = 0; s < nst; s++) { out_sum[s] = msum[s]; out_max[s] = mmax[s]; }
}

/* witness: first allocation (DFS order) of class `kind` for the start with the given picks.  returns 1 if found;
   out_owner[g]; out_info[3n]: succ, end flag, chain start per agent */
int rnd_witness(int n_, int m_, const ll *vals, const int *picks, int kind, int *out_owner, int *out_info) {
    setup(n_, m_, vals);
    int s0 = -1;
    for (int s = 0; s < nst; s++) if (!memcmp(pick[s], picks, sizeof(int) * n)) s0 = s;
    if (s0 < 0) { memcpy(pick[nst], picks, sizeof(int) * n); s0 = nst++; }
    cap = (ll)1 << 62; want_mask = 0;
    wit_kind = kind; wit_start = s0; wit_found = 0;
    dfs(0);
    if (wit_found) { for (int g = 0; g < m; g++) out_owner[g] = wit_owner[g]; for (int k = 0; k < 3 * n; k++) out_info[k] = wit_info[k]; }
    wit_kind = -1; wit_start = -1;
    return wit_found;
}

/* list all EFX allocations (owners), up to maxout; returns count found (may exceed maxout) */
static int *lst_buf; static ll lst_max, lst_cnt;
static void dfs_list(int idx) {
    if (idx == m) {
        if (lst_cnt < lst_max) for (int g = 0; g < m; g++) lst_buf[lst_cnt * m + g] = owner[g];
        lst_cnt++; return;
    }
    int g = gord[idx];
    for (int a = 0; a < n; a++) {
        ll oldmn[MAXN];
        owner[g] = a; bsz[a]++;
        for (int i = 0; i < n; i++) { val[i][a] += v[i][g]; rem[i] -= v[i][g]; oldmn[i] = mn[i][a]; if (v[i][g] < mn[i][a]) mn[i][a] = v[i][g]; }
        int bad = 0;
        for (int i = 0; i < n && !bad; i++) {
            ll pot = val[i][i] + rem[i];
            for (int j = 0; j < n; j++) if (j != i && bsz[j] > 0 && val[i][j] - mn[i][j] > pot) { bad = 1; break; }
        }
        if (!bad) dfs_list(idx + 1);
        for (int i = 0; i < n; i++) { val[i][a] -= v[i][g]; rem[i] += v[i][g]; mn[i][a] = oldmn[i]; }
        bsz[a]--; owner[g] = -1;
    }
}
ll rnd_list_efx(int n_, int m_, const ll *vals, int *buf, ll maxout) {
    setup(n_, m_, vals);
    lst_buf = buf; lst_max = maxout; lst_cnt = 0;
    dfs_list(0);
    return lst_cnt;
}

/* ===================================================================================================================
   TWO ROUNDS (kgen/rounds.md §4.1), free completion, strictly positive values.
   X (complete EFX, value-dominating the picks) is reachable by <= 2 rounds iff some round-1 structure S1 (roles OFF,
   T0, or a position on a path, a ring flag per path), some junk assignment H1 and some round-2 roles make the
   round-2 conditions of Lemma RC hold with sets (kgen/rounds.md §4.1, Lemma RC2):
     round-2 role of a: STAY (B1_a inside X_a), PASS (B1_a inside X_d, d != a, succ2 = d) or SPLIT (an end whose B1 is
     split: the round-2 start takes X_x0 cap B1_a, the rest is released); SPLIT agents need a predecessor;
     receivers b (pred p):  v_b(B1_p) + v_b(X_b cap J1) > v_b(B1_b);
     starts x (end e):       v_x(X_x cap J1) + v_x(X_x cap B1_e) > v_x(B1_x);
   with J1 = (J0 - H1) + (round-1 released picks).  Enumeration: S1 x SPLIT set x (target of each pick-less round-1
   start that does not split) x (for every junk good: stay in J1, or go to a round-1 chain agent a whose B1 ends in
   the good's X-bundle, or that splits). */
#define MAXS1 20000
static int s1_cnt, s1_role[MAXS1][MAXN], s1_pred[MAXS1][MAXN], s1_succ[MAXS1][MAXN], s1_ring[MAXS1][MAXN];
static int s1_n = -1;
enum { R_OFF, R_T0, R_PATH };

static void gen_s1(void) {
    if (s1_n == n) return;
    s1_n = n; s1_cnt = 0;
    int pw3 = 1; for (int i = 0; i < n; i++) pw3 *= 3;
    for (int code = 0; code < pw3; code++) {
        int role[MAXN], c = code, P[MAXN], np = 0;
        for (int a = 0; a < n; a++) { role[a] = c % 3; c /= 3; if (role[a] == R_PATH) P[np++] = a; }
        if (np == 1) continue;
        /* succ maps on P: each path agent's succ in P or none */
        int lim = 1; for (int i = 0; i < np; i++) lim *= (np + 1);
        for (int sc = 0; sc < lim; sc++) {
            int succ[MAXN], pred[MAXN], ok = 1, x = sc;
            for (int a = 0; a < n; a++) { succ[a] = -1; pred[a] = -1; }
            for (int i = 0; i < np && ok; i++) {
                int ch = x % (np + 1); x /= (np + 1);
                if (ch < np) {
                    int b = P[ch];
                    if (b == P[i] || pred[b] >= 0) ok = 0; else { succ[P[i]] = b; pred[b] = P[i]; }
                }
            }
            if (!ok) continue;
            for (int i = 0; i < np && ok; i++) {   /* acyclic, every path agent in a path of >= 2 */
                int a = P[i];
                if (succ[a] < 0 && pred[a] < 0) ok = 0;
                int cc = a, st = 0;
                while (succ[cc] >= 0 && st <= n) { cc = succ[cc]; st++; if (cc == a) { ok = 0; break; } }
            }
            if (!ok) continue;
            /* ring flags per path start */
            int starts[MAXN], ns = 0;
            for (int i = 0; i < np; i++) if (pred[P[i]] < 0) starts[ns++] = P[i];
            for (int rf = 0; rf < (1 << ns); rf++) {
                if (s1_cnt >= MAXS1) { fprintf(stderr, "MAXS1\n"); exit(1); }
                for (int a = 0; a < n; a++) { s1_role[s1_cnt][a] = role[a]; s1_pred[s1_cnt][a] = pred[a]; s1_succ[s1_cnt][a] = succ[a]; s1_ring[s1_cnt][a] = 0; }
                for (int k = 0; k < ns; k++) if (rf >> k & 1) s1_ring[s1_cnt][starts[k]] = 1;
                s1_cnt++;
            }
        }
    }
}

/* state of one two-round test */
static int T_y[MAXN], T_isj0[MAXM], T_own[MAXM];
static int T_pp[MAXN], T_chain1[MAXN], T_end1[MAXN], T_rel1[MAXM];
static int T_split[MAXN], T_d[MAXN];
static int T_jg[MAXM], T_nj;                 /* junk goods */
static int T_opt[MAXM][MAXN + 1], T_nopt[MAXM];
static int T_asg[MAXM];                      /* -1 = stays junk, else agent */

static int T_slackmode = 0; static double T_best;
static double tot_inv(int a) { return 1.0 / tot_i[a]; }
static int two_final(void) {
    double slack = 1e9;
    /* build B1 masks, J1 */
    unsigned B1[MAXN]; unsigned J1 = 0;
    for (int a = 0; a < n; a++) B1[a] = T_pp[a] >= 0 ? (1u << T_pp[a]) : 0;
    for (int k = 0; k < T_nj; k++) { int g = T_jg[k]; if (T_asg[k] < 0) J1 |= 1u << g; else B1[T_asg[k]] |= 1u << g; }
    for (int g = 0; g < m; g++) if (T_rel1[g]) J1 |= 1u << g;
    /* round-1 gains */
    for (int a = 0; a < n; a++) if (T_chain1[a]) {
        ll bv = 0; for (int g = 0; g < m; g++) if (B1[a] >> g & 1) bv += v[a][g];
        if (!(bv > v[a][T_y[a]])) return 0;
        double d = (double)(bv - v[a][T_y[a]]) * tot_inv(a); if (d < slack) slack = d;
    }
    /* round-2 roles */
    int succ2[MAXN], pred2[MAXN];
    for (int a = 0; a < n; a++) { succ2[a] = -1; pred2[a] = -1; }
    for (int a = 0; a < n; a++) {
        if (T_split[a]) continue;
        int d = T_d[a];
        if (d < 0) return 0;
        /* B1_a must lie inside X_d */
        for (int g = 0; g < m; g++) if ((B1[a] >> g & 1) && T_own[g] != d) return 0;
        if (d != a) {
            if (B1[a] == 0) return 0;               /* passed bases are nonempty */
            if (pred2[d] >= 0) return 0;
            succ2[a] = d; pred2[d] = a;
        }
    }
    for (int a = 0; a < n; a++) {               /* acyclic */
        int c = a, st = 0;
        while (succ2[c] >= 0 && st <= n) { c = succ2[c]; st++; if (c == a) return 0; }
    }
    for (int a = 0; a < n; a++) if (T_split[a] && pred2[a] < 0) return 0;
    /* gains */
    for (int b = 0; b < n; b++) if (pred2[b] >= 0) {
        int p = pred2[b]; ll l = 0, r = 0;
        for (int g = 0; g < m; g++) {
            if (B1[p] >> g & 1) l += v[b][g];
            if ((J1 >> g & 1) && T_own[g] == b) l += v[b][g];
            if (B1[b] >> g & 1) r += v[b][g];
        }
        if (!(l > r)) return 0;
        double d = (double)(l - r) * tot_inv(b); if (d < slack) slack = d;
    }
    for (int x = 0; x < n; x++) if (succ2[x] >= 0 && pred2[x] < 0) {
        int e = x; while (succ2[e] >= 0) e = succ2[e];
        ll l = 0, r = 0;
        for (int g = 0; g < m; g++) {
            if (T_own[g] == x && ((J1 >> g & 1) || (B1[e] >> g & 1))) l += v[x][g];
            if (B1[x] >> g & 1) r += v[x][g];
        }
        if (!(l > r)) return 0;
        double d = (double)(l - r) * tot_inv(x); if (d < slack) slack = d;
    }
    if (T_slackmode) { if (slack > T_best) T_best = slack; return 0; }   /* keep searching for a better structure */
    return 1;
}

static int two_dfs(int k) {
    if (k == T_nj) return two_final();
    for (int o = 0; o < T_nopt[k]; o++) { T_asg[k] = T_opt[k][o]; if (two_dfs(k + 1)) return 1; }
    return 0;
}

/* is the complete allocation in T_own reachable by <= 2 rounds from the start T_y? */
static int two_reach(void) {
    gen_s1();
    T_nj = 0;
    for (int g = 0; g < m; g++) { T_isj0[g] = 1; }
    for (int a = 0; a < n; a++) T_isj0[T_y[a]] = 0;
    for (int g = 0; g < m; g++) if (T_isj0[g]) T_jg[T_nj++] = g;
    for (int s = 0; s < s1_cnt; s++) {
        int *role = s1_role[s], *pred = s1_pred[s], *succ = s1_succ[s], *ring = s1_ring[s];
        for (int g = 0; g < m; g++) T_rel1[g] = 0;
        int pickless[MAXN], npl = 0;
        for (int a = 0; a < n; a++) {
            T_chain1[a] = role[a] != R_OFF;
            T_end1[a] = -1;
            if (role[a] == R_PATH && pred[a] < 0) {
                int e = a; while (succ[e] >= 0) e = succ[e];
                T_end1[a] = e;
                if (ring[a]) T_pp[a] = T_y[e]; else { T_pp[a] = -1; T_rel1[T_y[e]] = 1; pickless[npl++] = a; }
            } else if (role[a] == R_PATH) T_pp[a] = T_y[pred[a]];
            else T_pp[a] = T_y[a];
        }
        /* quick round-1 feasibility: each chain agent with all junk */
        int feas = 1;
        for (int a = 0; a < n && feas; a++) if (T_chain1[a]) {
            ll bv = (T_pp[a] >= 0 ? v[a][T_pp[a]] : 0);
            for (int k = 0; k < T_nj; k++) bv += v[a][T_jg[k]];
            if (!(bv > v[a][T_y[a]])) feas = 0;
        }
        if (!feas) continue;
        for (int SP = 0; SP < (1 << n); SP++) {
            for (int a = 0; a < n; a++) T_split[a] = SP >> a & 1;
            /* targets: pick part's owner; pickless non-split starts enumerate a target */
            int free_idx[MAXN], nf = 0, bad = 0;
            for (int a = 0; a < n; a++) {
                T_d[a] = -1;
                if (T_split[a]) continue;
                if (T_pp[a] >= 0) T_d[a] = T_own[T_pp[a]];
                else free_idx[nf++] = a;
            }
            if (bad) continue;
            int lim = 1; for (int i = 0; i < nf; i++) lim *= n;
            for (int fc = 0; fc < lim; fc++) {
                int x = fc;
                for (int i = 0; i < nf; i++) { T_d[free_idx[i]] = x % n; x /= n; }
                /* junk options */
                int dead = 0;
                for (int k = 0; k < T_nj && !dead; k++) {
                    int g = T_jg[k]; T_nopt[k] = 0;
                    T_opt[k][T_nopt[k]++] = -1;
                    for (int a = 0; a < n; a++) if (T_chain1[a] && (T_split[a] || T_d[a] == T_own[g])) T_opt[k][T_nopt[k]++] = a;
                }
                if (dead) continue;
                if (two_dfs(0)) return 1;
            }
        }
    }
    return 0;
}

/* rnd2_count: for the start `picks`, the number of complete EFX allocations reachable by <= 2 rounds (free
   completion), capped at cap; *out_md = number of MD EFX allocations visited */
static ll r2_cap, r2_cnt, r2_md; static int r2_picks[MAXN]; static double r2_msum;
static void dfs2(int idx) {
    if (r2_cnt >= r2_cap) return;
    if (idx == m) {
        for (int a = 0; a < n; a++) if (val[a][a] < v[a][r2_picks[a]]) return;   /* MD */
        r2_md++;
        for (int g = 0; g < m; g++) T_own[g] = owner[g];
        for (int a = 0; a < n; a++) T_y[a] = r2_picks[a];
        if (T_slackmode) {
            T_best = -1; two_reach();
            if (T_best > 0) {
                r2_cnt++;
                double em = 1e9;
                for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j && bsz[j] > 0) {
                    double d = (double)(val[i][i] - (val[i][j] - mn[i][j])) / tot_i[i]; if (d < em) em = d;
                }
                r2_msum += (em < T_best ? em : T_best);
            }
        } else if (two_reach()) r2_cnt++;
        return;
    }
    int g = gord[idx];
    for (int a = 0; a < n; a++) {
        ll oldmn[MAXN];
        owner[g] = a; bsz[a]++;
        for (int i = 0; i < n; i++) { val[i][a] += v[i][g]; rem[i] -= v[i][g]; oldmn[i] = mn[i][a]; if (v[i][g] < mn[i][a]) mn[i][a] = v[i][g]; }
        int bad = 0;
        for (int i = 0; i < n && !bad; i++) {
            ll pot = val[i][i] + rem[i];
            for (int j = 0; j < n; j++) if (j != i && bsz[j] > 0 && val[i][j] - mn[i][j] > pot) { bad = 1; break; }
        }
        if (!bad) dfs2(idx + 1);
        for (int i = 0; i < n; i++) { val[i][a] -= v[i][g]; rem[i] += v[i][g]; mn[i][a] = oldmn[i]; }
        bsz[a]--; owner[g] = -1;
        if (r2_cnt >= r2_cap) return;
    }
}
ll rnd2_count(int n_, int m_, const ll *vals, const int *picks, ll cap_, ll *out_md) {
    setup(n_, m_, vals);
    if (m > 31) return -1;
    for (int a = 0; a < n; a++) r2_picks[a] = picks[a];
    r2_cap = cap_ > 0 ? cap_ : ((ll)1 << 62); r2_cnt = 0; r2_md = 0; r2_msum = 0;
    dfs2(0);
    *out_md = r2_md;
    return r2_cnt;
}
/* the same with margins: count and the sum over two-round witnesses of min(EFX slack, best structure's gain slack) */
ll rnd2_count_margin(int n_, int m_, const ll *vals, const int *picks, ll cap_, ll *out_md, double *out_msum) {
    T_slackmode = 1;
    ll c = rnd2_count(n_, m_, vals, picks, cap_, out_md);
    T_slackmode = 0; *out_msum = r2_msum;
    return c;
}

/* ===================================================================================================================
   ZEROS (kgen/rounds.md §4.5): OC1 with zero values allowed, at PERFECT starts (every agent picks), the official move
   of k4/sdc.md §29/§31: an addition (t = 0), a chain or a ring; sets H inside the receiver's relevant goods; x0 takes
   only end goods it values; one-absorber completion (at most one agent holds >= 2 goods outside its base).
   For X (complete EFX0) the witness test: keep (one optional addition + one absorber), or exactly one path of passers
   s(a) = loc(a), with H's maximal (relevant junk in the bundle).
   rnd_oc1z: per distinct perfect start, counts of EXT1 (picks extend, one absorber), OC1 and MD, and OC1 margins. */
static ll z_cnt[MAXS][6]; static double z_msum[MAXS], z_rms[MAXS][2];   /* z_rms: RND1Z / RNDPZ margin sums */
static double z_rb[2];   /* per EFX0 allocation: best gain slack of a plain round / ROUND-P witness structure */
static int z_perfect[MAXS];

static int oc1z_start(int s, double *mg) {
    int *y = pick[s];
    int loc[MAXN], isj[MAXM];
    for (int g = 0; g < m; g++) isj[g] = 1;
    for (int a = 0; a < n; a++) isj[y[a]] = 0;
    for (int a = 0; a < n; a++) loc[a] = owner[y[a]];
    for (int a = 0; a < n; a++) if (val[a][a] < v[a][y[a]]) return 0;    /* MD is necessary */
    int res = 4;                                                          /* bit 2: MD */
    ll vJr[MAXN]; int nJr[MAXN], nJ0[MAXN];   /* relevant junk value/count, worthless junk count, per holder */
    for (int a = 0; a < n; a++) { vJr[a] = 0; nJr[a] = 0; nJ0[a] = 0; }
    for (int g = 0; g < m; g++) if (isj[g]) { int b = owner[g]; if (v[b][g] > 0) { vJr[b] += v[b][g]; nJr[b]++; } else nJ0[b]++; }
    double best = -1;
    z_rb[0] = z_rb[1] = -1;
    int Mv = 0;
    for (int a = 0; a < n; a++) if (loc[a] != a) Mv |= 1 << a;
    if (Mv == 0) {
        /* outside goods = all junk of each agent; one addition at agent t moves its relevant junk into its base */
        int big = 0; for (int a = 0; a < n; a++) if (nJr[a] + nJ0[a] >= 2) big++;
        if (big <= 1) { res |= 1; best = 1e9; }
        for (int t = 0; t < n; t++) if (nJr[t] > 0) {
            int bg = 0; for (int a = 0; a < n; a++) { int out = (a == t) ? nJ0[a] : nJr[a] + nJ0[a]; if (out >= 2) bg++; }
            if (bg <= 1) { double d = (double)vJr[t] / tot_i[t]; if (d > best) best = d; res |= 2; }
        }
        if (res & 1) res |= 2;
        if (res & 2) res |= 8;
        { int big = 0; for (int a = 0; a < n; a++) if (nJ0[a] >= 2) big++; if (big <= 1) { res |= 16 | 32; z_rb[0] = z_rb[1] = 1e9; } }
        *mg = best; return res;
    }
    for (int E = Mv;; E = (E - 1) & Mv) {
        int P = Mv & ~E, pred[MAXN], succ[MAXN], ok = 1, tg = 0;
        for (int a = 0; a < n; a++) { pred[a] = -1; succ[a] = -1; }
        for (int a = 0; a < n && ok; a++) if (P >> a & 1) {
            int b = loc[a];
            if (tg >> b & 1) ok = 0; else { tg |= 1 << b; pred[b] = a; succ[a] = b; }
        }
        if (ok) for (int a = 0; a < n && ok; a++) if (P >> a & 1) {
            int c = a, st = 0;
            while (succ[c] >= 0 && st <= n) { c = succ[c]; st++; if (c == a) { ok = 0; break; } }
        }
        if (ok) for (int a = 0; a < n && ok; a++) if ((E >> a & 1) && pred[a] < 0) ok = 0;
        if (ok) {   /* ROUNDS with zeros (kgen/rounds.md §4.9): any number of vertex-disjoint paths; off-path agents
                       make additions with their relevant junk; bit 16: plain round (a start takes only its own end's
                       pick); bit 32: ROUND-P (every non-end path agent may take any end's pick it holds and values) */
            int stof[MAXN]; for (int a = 0; a < n; a++) stof[a] = -1;
            for (int a = 0; a < n; a++) if (succ[a] >= 0 && pred[a] < 0) { int c = a; stof[c] = a; while (succ[c] >= 0) { c = succ[c]; stof[c] = a; } }
            for (int mode = 0; mode < 2; mode++) {
                int okr = 1, out[MAXN]; ll extra[MAXN];
                for (int a = 0; a < n; a++) { out[a] = nJ0[a]; extra[a] = 0; }
                for (int e = 0; e < n; e++) if (pred[e] >= 0 && succ[e] < 0) {          /* path ends */
                    int tk = loc[e], taken = 0;
                    if (v[tk][y[e]] > 0) {
                        if (mode == 0) taken = (tk == stof[e]);                         /* ring: own start only */
                        else taken = (succ[tk] >= 0);                                   /* any non-end path agent */
                    }
                    if (taken) extra[tk] += v[tk][y[e]]; else out[tk]++;
                }
                double gr = 1e9;
                for (int b = 0; b < n && okr; b++) if (stof[b] >= 0) {
                    ll l = (pred[b] >= 0 ? v[b][y[pred[b]]] : 0) + vJr[b] + extra[b];
                    if (pred[b] < 0 && vJr[b] + extra[b] == 0) okr = 0;               /* a start needs H0 nonempty */
                    if (!(l > v[b][y[b]])) okr = 0; else { double d = (double)(l - v[b][y[b]]) / tot_i[b]; if (d < gr) gr = d; }
                }
                if (okr) { int big = 0; for (int a = 0; a < n; a++) if (out[a] >= 2) big++;
                           if (big <= 1) { res |= (mode == 0 ? 16 : 32); if (gr > z_rb[mode]) z_rb[mode] = gr; } }
            }
        }
        int nst = 0, x0 = -1;
        if (ok) { for (int a = 0; a < n; a++) if (succ[a] >= 0 && pred[a] < 0) { nst++; x0 = a; } if (nst != 1) ok = 0; }
        if (ok) {
            double gm = 1e9;
            int onp[MAXN]; for (int a = 0; a < n; a++) onp[a] = (succ[a] >= 0 || pred[a] >= 0);
            for (int b = 0; b < n && ok; b++) if (pred[b] >= 0) {
                ll l = v[b][y[pred[b]]] + vJr[b];
                if (!(l > v[b][y[b]])) ok = 0; else { double d = (double)(l - v[b][y[b]]) / tot_i[b]; if (d < gm) gm = d; }
            }
            int e = x0; while (succ[e] >= 0) e = succ[e];
            int ring = (loc[e] == x0 && v[x0][y[e]] > 0);
            /* OC1' (kgen/rounds.md §4.6): a non-end path agent b holding the end's pick and valuing it may take it */
            {
                int okp = 1; int tk = loc[e]; int takes = (onp[tk] && tk != e && v[tk][y[e]] > 0);
                double gmp = 1e9;
                for (int b = 0; b < n && okp; b++) if (pred[b] >= 0) {
                    ll l = v[b][y[pred[b]]] + vJr[b] + ((takes && tk == b) ? v[b][y[e]] : 0);
                    if (!(l > v[b][y[b]])) okp = 0; else { double d = (double)(l - v[b][y[b]]) / tot_i[b]; if (d < gmp) gmp = d; }
                }
                if (okp) {
                    ll l = vJr[x0] + ((takes && tk == x0) ? v[x0][y[e]] : 0);
                    if (!(l > v[x0][y[x0]])) okp = 0;
                }
                if (okp) {
                    int out[MAXN];
                    for (int a = 0; a < n; a++) out[a] = onp[a] ? nJ0[a] : nJr[a] + nJ0[a];
                    if (!takes) out[loc[e]]++;
                    int big = 0; for (int a = 0; a < n; a++) if (out[a] >= 2) big++;
                    if (big <= 1) res |= 8;
                }
            }
            if (ok) {
                ll l = vJr[x0] + (ring ? v[x0][y[e]] : 0);
                if (!(l > v[x0][y[x0]])) ok = 0; else { double d = (double)(l - v[x0][y[x0]]) / tot_i[x0]; if (d < gm) gm = d; }
            }
            if (ok) {
                /* outside goods: off-path: all junk; on path: worthless junk; plus the end's pick if not taken by x0 */
                int out[MAXN];
                for (int a = 0; a < n; a++) out[a] = onp[a] ? nJ0[a] : nJr[a] + nJ0[a];
                if (!ring) out[loc[e]]++;
                int big = 0; for (int a = 0; a < n; a++) if (out[a] >= 2) big++;
                if (big <= 1) { res |= 2; if (gm > best) best = gm; }
            }
        }
        if (E == 0) break;
    }
    *mg = best;
    return res;
}

static void dfsz(int idx) {
    if (idx == m) {
        double em = 1e9;      /* EFX0 slack over the pairs with a real threat (with zeros, slack 0 is common otherwise) */
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j && bsz[j] > 0 && val[i][j] - mn[i][j] > 0) {
            double d = (double)(val[i][i] - (val[i][j] - mn[i][j])) / tot_i[i]; if (d < em) em = d;
        }
        nefx++;
        for (int s = 0; s < nst; s++) if (z_perfect[s]) {
            double mg; int r = oc1z_start(s, &mg);
            if (r & 1) z_cnt[s][0]++;
            if (r & 2) { z_cnt[s][1]++; z_msum[s] += (em < mg ? em : mg); }
            if (r & 4) z_cnt[s][2]++;
            if ((r & 8) || (r & 2)) z_cnt[s][3]++;
            if ((r & 16) || (r & 2)) { z_cnt[s][4]++; z_rms[s][0] += (em < z_rb[0] ? em : z_rb[0]); }
            if ((r & 32) || (r & 8) || (r & 2)) { z_cnt[s][5]++; z_rms[s][1] += (em < z_rb[1] ? em : z_rb[1]); }
        }
        return;
    }
    int g = gord[idx];
    for (int a = 0; a < n; a++) {
        ll oldmn[MAXN];
        owner[g] = a; bsz[a]++;
        for (int i = 0; i < n; i++) { val[i][a] += v[i][g]; rem[i] -= v[i][g]; oldmn[i] = mn[i][a]; if (v[i][g] < mn[i][a]) mn[i][a] = v[i][g]; }
        int bad = 0;
        for (int i = 0; i < n && !bad; i++) {
            ll pot = val[i][i] + rem[i];
            for (int j = 0; j < n; j++) if (j != i && bsz[j] > 0 && val[i][j] - mn[i][j] > pot) { bad = 1; break; }
        }
        if (!bad) dfsz(idx + 1);
        for (int i = 0; i < n; i++) { val[i][a] -= v[i][g]; rem[i] += v[i][g]; mn[i][a] = oldmn[i]; }
        bsz[a]--; owner[g] = -1;
    }
}

/* SD with zeros: favourite remaining relevant good (ties to the smaller index), none if nothing relevant is left */
static void sdz(const int *order, int *y) {
    int used[MAXM] = {0};
    for (int k = 0; k < n; k++) {
        int a = order[k], best = -1;
        for (int g = 0; g < m; g++) if (!used[g] && v[a][g] > 0 && (best < 0 || v[a][g] > v[a][best])) best = g;
        y[a] = best; if (best >= 0) used[best] = 1;
    }
}

int rnd_oc1z(int n_, int m_, const ll *vals, int *out_picks, int *out_order, int *out_perfect, ll *out_cnt, double *out_msum, ll *out_nefx) {
    setup(n_, m_, vals);
    /* recompute the starts with the zero-aware SD */
    int perm[MAXN]; for (int i = 0; i < n; i++) perm[i] = i;
    nst = 0;
    while (1) {
        int y[MAXN]; sdz(perm, y);
        int found = 0;
        for (int s = 0; s < nst && !found; s++) if (!memcmp(pick[s], y, sizeof(int) * n)) found = 1;
        if (!found) { memcpy(pick[nst], y, sizeof(int) * n); memcpy(sorder[nst], perm, sizeof(int) * n); nst++; }
        int i = n - 2; while (i >= 0 && perm[i] > perm[i + 1]) i--;
        if (i < 0) break;
        int j = n - 1; while (perm[j] < perm[i]) j--;
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        for (int a = i + 1, b = n - 1; a < b; a++, b--) { t = perm[a]; perm[a] = perm[b]; perm[b] = t; }
    }
    for (int s = 0; s < nst; s++) {
        z_perfect[s] = 1; for (int a = 0; a < n; a++) if (pick[s][a] < 0) z_perfect[s] = 0;
        for (int k = 0; k < 6; k++) z_cnt[s][k] = 0; z_msum[s] = 0; z_rms[s][0] = z_rms[s][1] = 0;
    }
    dfsz(0);
    for (int s = 0; s < nst; s++) {
        for (int a = 0; a < n; a++) { out_picks[s * n + a] = pick[s][a]; out_order[s * n + a] = sorder[s][a]; }
        out_perfect[s] = z_perfect[s];
        for (int k = 0; k < 6; k++) out_cnt[s * 6 + k] = z_cnt[s][k];
        out_msum[s] = z_msum[s];
    }
    *out_nefx = nefx;
    return nst;
}

/* ===================================================================================================================
   EXHAUSTIVE GRID (kgen/rounds.md §4.7): every profile with values in {1..V} (strictly positive), agents' rows as a
   multiset (every order is tested, so permuting agents changes nothing), n agents, m goods.  For each profile: every
   distinct start; one round (RND1 = RNDF at n <= 5) by Lemma RC; for starts failing one round, two rounds (free) by
   Lemma RC2.  out[0..4] = profiles, starts, starts failing one round, starts failing two rounds, max EFX allocations.
   The first `maxrec` profiles with a two-round failure are written to rec (n*m values each). */
ll rnd_grid(int n_, int m_, int V, ll *out, ll *rec, int maxrec, ll limit) {
    int R = 1; for (int g = 0; g < m_; g++) R *= V;
    int idx[MAXN]; for (int i = 0; i < n_; i++) idx[i] = 0;
    ll vals[MAXN * MAXM]; ll prof = 0, starts = 0, f1 = 0, f2 = 0, nrec = 0;
    int picks[MAXS * MAXN], order[MAXS * MAXN]; static ll cnt[MAXS * NK]; ll nefx_;
    while (1) {
        for (int i = 0; i < n_; i++) { int x = idx[i]; for (int g = 0; g < m_; g++) { vals[i * m_ + g] = 1 + x % V; x /= V; } }
        int ns = rnd_analyze(n_, m_, vals, 1, 1 << K_RND1, picks, order, cnt, &nefx_);
        prof++; starts += ns;
        for (int s = 0; s < ns; s++) if (cnt[s * NK + K_RND1] == 0) {
            f1++;
            ll md; ll c2 = rnd2_count(n_, m_, vals, picks + s * n_, 1, &md);
            if (c2 == 0) { f2++; if (nrec < maxrec) { for (int k = 0; k < n_ * m_; k++) rec[nrec * (n_ * m_ + n_) + k] = vals[k]; for (int a = 0; a < n_; a++) rec[nrec * (n_ * m_ + n_) + n_ * m_ + a] = picks[s * n_ + a]; nrec++; } }
        }
        if (limit > 0 && prof >= limit) break;
        /* next multiset: idx nondecreasing */
        int i = n_ - 1;
        while (i >= 0 && idx[i] == R - 1) i--;
        if (i < 0) break;
        idx[i]++; for (int j = i + 1; j < n_; j++) idx[j] = idx[i];
    }
    out[0] = prof; out[1] = starts; out[2] = f1; out[3] = f2; out[4] = nrec;
    return prof;
}

/* after rnd_oc1z: per start, margin sums of the RND1Z and RNDPZ witnesses (min of EFX0 slack and best gain slack) */
void rnd_oc1z_rmargins(double *out) { for (int s = 0; s < nst; s++) { out[2 * s] = z_rms[s][0]; out[2 * s + 1] = z_rms[s][1]; } }
