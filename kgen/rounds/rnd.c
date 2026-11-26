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
enum { K_EXTF, K_EXT1, K_OC1, K_RNDF, K_RND1, K_MD, K_RNDX, K_RNDX1, NK };
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
        res |= (1 << K_RNDF) | (1 << K_RND1) | (1 << K_RNDX) | (1 << K_RNDX1);
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
