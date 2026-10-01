/* lemmam_x.c (workstream proof/k4-lemmam-x, k4/lemmam_x.md): k4/rulef.c of PR #72 (branch proof/k4-rulef at
   aebd620; that file is unchanged since b0f4ee5) with one added mode, -A43, and the options -U and (with -H) a
   hill-climbing score for it. Everything else is rulef.c verbatim; its own header follows.

   -A43: for every first agent a (tau_a = (a, then index order), LB's P-step key) the class of rule RK's tests
   (k4/rulef.md §4): K0 (Lemma K deficit <= 0, or omega <= 0, after need-shrinking or envy-free upgrades; with -N1 also
   without upgrades), K1 (one rotation of such a state, every frozen k, need chain and base O, reaches Lemma K deficit
   <= 0), or bad. Use -Y1 for Lemma K's kept-out sets of rulef.md §2 Remark 4 (the full Lemma K). For every bad a:
   the class of its envy-free run (k4/c4.md's cases), the roles the other agents play in it, and the candidates a'
   of k4/lemmam_x.md §2 (cand43); statistics in LMX / LMXC / LMXR lines, and with -D43 one BAD line per bad pair.
   -U2 (default) roles from the envy-free run, -U1 from the need-shrinking run. -A43 -SN -HM climbs toward profiles
   with bad first agents (score: 1000 per bad first agent plus 1 per first agent not in K0). */
/* adaptive.c: LB4r (k4/lb4.md §5, lean/EFX/LB4R.lean) with an adaptive insertion rule (k4/adaptive.md).

Derived from k4/lb4r_tau.c of branch proof/k4-lb4 (itself k4/c4_lb4w.c of proof/k4-c4, which is k4/lb4.c with
64-bit masks). Changes:
  - good masks are 128-bit (m <= 128), up to 40 agents, so the cores H_t of k4/c4.md §7 fit up to t = 9;
  - the insertion step is a function (rule_choose, rollout rules in choose_seq): -AN selects the rule, see below;
    Phase 1 first computes the insertion sequence tau with the rule, then LB4r(tau) is run on that tau;
  - LB4r(tau) is always run with iterative deepening, the rotation bound outermost (bound 0 under every policy, then
    bound 1, ...; lb4.c's -d2), so a success reports the fewest rotations over the policies. This succeeds exactly when
    LB4r with at most -rN rotations does (each bound's search contains the previous one's);
  - modes: exhaustive (lazy type splitting, as lb4.c), -SN random profiles per core, -HN hill-climbing against the
    rule (score: rotations needed, then policy), -TN single profiles (one type per agent) under the rule or N random
    insertion sequences (-i10), -M mining (every insertion sequence of each profile; see mine()).
Everything else (Phase 1 with LB's P-step key, the three upgrade policies, the owner step with an exact search over the
slot sets C, rotations along need chains with every O, nested up to -rN) is lb4.c's code, unchanged in substance.

Input (stdin), any number of cores: n m, then per agent: d g_0 .. g_{d-1} T, then T lines of d values.

Options:
  -AN  insertion rule (with -i0, the default): 0 index; 1 block lookahead, least |NA| of the new block's agents;
       2 rollout, least omega after envy-free upgrades (rest of Phase 1 in index order); 3 rollout, fewest rotations
       of LB4r on (prefix, c, index order), ties by rule 2's omega; 4 rollout, least omega after need-shrinking
       upgrades; 5 least omega after Phase 1 with no upgrades (least |NA|); 6 4-good agents first; 7 3-good agents
       first; 8 least contested top (fewest other unprocessed agents value the candidate's top), ties index;
       9 most contested top; 10 rollout with rule 2 but ties broken by fewest frozen 4-good agents;
       11 rollout with key (omega, number of frozen agents with 4 goods, -pos of the last 4-good agent) (c4one's key);
       12 rule 3 at the first insertion step only, then index order; 13 rule 2 at the first insertion step only;
       14 the index run or the index run with one insertion step changed, least (rotations, omega);
       15 the same family as 14, the first sequence (index run first) with the fewest rotations (bound outermost);
       16 the same family as 12 (every first agent, then index order), the first with the fewest rotations;
       17, 18, 25: Sgouritsa-Sotiriou's first round (a maximum matching of the agents to their first or second choice,
       most first choices): insert the agents matched to their first choice first, then those matched to their second,
       then the unmatched (17); the second-choice ones first (18); the matching recomputed at every insertion step on
       the unprocessed agents and remaining goods (25);
       20, 21, 22: the first run covered by the theorems of k4/c4.md and k4/c4one.md (see covered()) in the family of
       rule 15 (index, or one step changed), of rule 16 (first agent), or among all sequences; -C1 without A4+(o),
       -C3 also the candidate A4+N after need-shrinking upgrades (see aplusN_owner),
       -Z1 check each covered run by LB4r (envy-free upgrades, needs from the base, one rotation), or for A4+N by the
       exact owner test with the owner found (needs from the base, no rotation); -Z2 check A4+N on every insertion
       sequence and with every owner its count admits (cov_all; 'covchk' counts the instances checked, per leaf);
       'uncov' counts the profiles (weighted) where no sequence of the family is covered; 'covviol' the leaves
       where a check failed. 23: rule 16 and 26: -i2, each with rule 22's coverage recorded (lines 'U uncovered
       policy rotations status count', status 0 no owner, 1 owner r, 2 another owner, 3 rotation).
       28: the first agent a whose run tau_a = (a, then index order) leaves the fewest frozen agents after
       need-shrinking upgrades (ties by index), then index order; 29: rule 16 restricted to those first agents.
  -i0 use -A (default);  -i1 every insertion sequence separately;  -i2 the fewest rotations over every insertion
       sequence (exists tau; bound outermost, sequences in lexicographic order);  -i10 -TN N random sequences (single profile)
  -uN upgrades: 0 none, 1 need-shrinking, 2 envy-free only, 3 policies 1, 2, 0 in turn (default 3)
  -rN at most N nested rotations (default 2);  -w1 owner needs from its bundle (default 1);  -c1 chains may end at
       upgraded agents (default 1);  -oN owner step: 0 every owner (default), 1 r only, 2 r then rotation
  -SN N random profiles per core;  -HN N hill-climbing steps per core (restart every 500);  -TN single-profile mode
  -LN local search on tau after the rule: up to N rounds of "change one insertion step, index order after it",
       taking a change that lowers (rotations needed, omega); -fN print at most N failures per core; -XS seed;
  -b brute force (every profile its own leaf); -v print each profile's run (single-profile modes);
  -KN print (as DEEP lines) the profiles needing at least N rotations, at most -f of them per core */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <stdint.h>

typedef unsigned __int128 u128;
typedef u128 gm;                      /* a set of goods */
#define BIT(g) ((gm)1 << (g))
#define MAXN 48                     /* lemmam_x.c: 48 (rulef.c: 40), for HH_5 (n = 42) */
#define MAXM 128
#define MAXT 1300
#define MAXG 80
#define MAXROT 6

static int n, m, d[MAXN], gl[MAXN][4];
static gm R[MAXN], ALLG;
static int nt[MAXN], tv[MAXN][MAXT][4];
static int np[MAXN], pr[MAXN][24][4], pcnt[MAXN][24], pidx[MAXN][24][MAXG];
static int OWN = 0, INS = 0, MAXF = 3, UPG = 3, BRUTE = 0, ARULE = 0, VERB = 0, LSR = 0, MINE = 0;
static long TAU = 0, SAMPLE = 0, HILL = 0;
static int DEEP = 0;                 /* -KN: report every leaf (profile) needing at least N rotations, up to -f per core */
static uint64_t rng_x = 88172645463325252ull;
static uint64_t rnd(void) { rng_x ^= rng_x << 13; rng_x ^= rng_x >> 7; rng_x ^= rng_x << 17; return rng_x; }

static int popc(gm x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }

/* run state */
static int cp[MAXN];                 /* ranking index per agent */
static u128 ts[MAXN];                /* current type set (bits over pidx[i][cp[i]]) */
static int ord[MAXN][4];
static jmp_buf env;
static int sp_i; static gm sp_S, sp_T;

static int tsum(int i, int t, gm S) { int s = 0; for (int k = 0; k < d[i]; k++) if (S >> gl[i][k] & 1) s += tv[i][t][k]; return s; }
/* sign of v_i(S) - v_i(T) (goods outside R_i count 0), for every type in the current set; splits if not constant */
static int cmpv(int i, gm S, gm T) {
    int res = 2;
    for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
        int t = pidx[i][cp[i]][k], x = tsum(i, t, S) - tsum(i, t, T), s = (x > 0) - (x < 0);
        if (res == 2) res = s; else if (res != s) { sp_i = i; sp_S = S; sp_T = T; longjmp(env, 1); }
    }
    return res;
}

/* ---- the construction ---- */
static int Y[MAXN], pos[MAXN], blk[MAXN], upg[MAXN], frz[MAXN], cap[MAXN], own[MAXM];
static gm base[MAXN], N_[MAXN], J;
static int last_status;              /* 0 no owner needed, 1 owner r, 2 other owner, 3 rotation, -1 fail */
static int lastbig;

static gm above(int i, int g) { gm s = 0; for (int r = 0; r < d[i] && ord[i][r] != g; r++) s |= BIT(ord[i][r]); return s; }
static gm NAset(void) { gm s = 0; for (int i = 0; i < n; i++) s |= N_[i]; return s; }

/* P-step choice: an unprocessed agent that lost a good, smallest (rank of favourite remaining, goods left, index) */
static int pstep(gm G, const int *done) {
    int best = -1, bk0 = 0, bk1 = 0;
    for (int i = 0; i < n; i++) if (!done[i]) {
        int left = popc(R[i] & G);
        if (left < d[i]) {
            int fr = d[i];
            for (int r = 0; r < d[i]; r++) if (G >> ord[i][r] & 1) { fr = r; break; }
            if (best < 0 || fr < bk0 || (fr == bk0 && left < bk1)) { best = i; bk0 = fr; bk1 = left; }
        }
    }
    return best;
}
static int favr(int i, gm G) { for (int r = 0; r < d[i]; r++) if (G >> ord[i][r] & 1) return ord[i][r]; return -1; }

/* ---- insertion sequences ---- */
static int pre[MAXN], npre;          /* forced insertion sequence (agent ids); later insertion steps use the rule */
static int ins_seq[MAXN], nins;      /* agents inserted by the last Phase 1 */
static int ncand_at[MAXN];           /* candidates at each insertion step of the last Phase 1 */
static int stop_at = -1;             /* Phase 1 stops at this insertion step, leaving its candidates below */
static int scand[MAXN], nscand;
static int choice[MAXN], nchoice, maxchoice[MAXN];   /* -i1 tree over candidate indices, -i10 random */
static int TAILRULE = 0;             /* rule used after the forced prefix (0 index; rules computed inside Phase 1) */

static int rule_choose(int rule, const int *cand, int nc, gm G, const int *done);
static void report(const char *what);
/* Phase 1(tau): returns 0 if stopped at insertion step stop_at (its candidates in scand), 1 when complete */
static int phase1(void) {
    gm G = ALLG;
    int done[MAXN] = {0}, b = -1;
    nins = 0;
    for (int i = 0; i < n; i++) Y[i] = -1;
    for (int step = 0; step < n; step++) {
        int best = pstep(G, done);
        if (best < 0) {              /* insertion step: every unprocessed agent has all its goods */
            int cand[MAXN], nc = 0;
            for (int i = 0; i < n; i++) if (!done[i]) cand[nc++] = i;
            if (nins == stop_at) { memcpy(scand, cand, sizeof cand); nscand = nc; J = G; return 0; }
            int c;
            if (nins < npre) c = pre[nins];
            else if (INS == 1 || INS == 10) {
                if (nins >= nchoice) choice[nchoice++] = INS == 10 ? (int)(rnd() % (uint64_t)nc) : 0;
                int q = choice[nins]; if (q >= nc) q = nc - 1; maxchoice[nins] = nc; c = cand[q];
            } else c = rule_choose(TAILRULE, cand, nc, G, done);
            ins_seq[nins] = c; ncand_at[nins] = nc; nins++;
            best = c; b++;
        }
        int i = best; Y[i] = favr(i, G);
        if (Y[i] >= 0) G &= ~BIT(Y[i]);
        done[i] = 1; pos[i] = step; blk[i] = b;
    }
    J = G;
    return 1;
}

/* is agent x threatened by bundle L when it holds H?  exists h in L: v_x(L - h) > v_x(H) */
static int threatened(int x, gm L, gm H) {
    gm Q = L & R[x];
    if (!Q) return 0;
    if ((L & ~R[x]) == 0) {          /* L inside R_x: remove its least valued good (lowest in the ranking) */
        for (int r = d[x] - 1; r >= 0; r--) if (Q >> ord[x][r] & 1) { Q &= ~BIT(ord[x][r]); break; }
        if (!Q) return 0;
    }
    return cmpv(x, Q, H & R[x]) > 0;
}

/* completion with owner o (or o = -1: none); C = goods of J going to slots; returns 1 and fills own[] if OK */
static int try_C0(int o, gm C, gm L);
static int tcnt; static int tl[MAXN]; static gm allow[MAXN]; static int mt[MAXM];
static int aug(int t, gm *seen) {
    for (int g = 0; g < m; g++) if ((allow[t] >> g & 1) && !(*seen >> g & 1)) {
        *seen |= BIT(g);
        if (mt[g] < 0 || aug(mt[g], seen)) { mt[g] = t; return 1; }
    }
    return 0;
}
static void fill_bases(void) {
    for (int g = 0; g < m; g++) own[g] = -1;
    for (int x = 0; x < n; x++) for (int g = 0; g < m; g++) if (base[x] >> g & 1) own[g] = x;
}
static int OWNW = 1;
static int try_C(int o, gm C) {
    gm L = (o >= 0 ? base[o] : 0) | (J & ~C);
    int scap[MAXN], sfrz[MAXN];
    if (OWNW && o >= 0) {            /* -w1: the owner's needs are the goods it values above its whole bundle */
        memcpy(scap, cap, sizeof cap); memcpy(sfrz, frz, sizeof frz);
        gm NA = 0, no = 0;
        for (int g = 0; g < m; g++) if ((R[o] & ~L) >> g & 1 && cmpv(o, BIT(g), L) > 0) no |= BIT(g);
        for (int i = 0; i < n; i++) NA |= (i == o) ? no : N_[i];
        for (int i = 0; i < n; i++) if (i != o) {
            frz[i] = popc(base[i]) == 1 && (NA & base[i]);
            cap[i] = frz[i] ? 0 : (popc(base[i]) >= 2 ? 0 : 2 - popc(base[i]));
        }
        int ok = try_C0(o, C, L);
        memcpy(cap, scap, sizeof cap); memcpy(frz, sfrz, sizeof frz);
        return ok;
    }
    return try_C0(o, C, L);
}
static int try_C0(int o, gm C, gm L) {
    for (int x = 0; x < n; x++) if (x != o && cap[x] == 0 && threatened(x, L, base[x])) return 0;
    /* cap-1 terminals threatened with their base alone need a protecting good (SDR); the rest needs capacity */
    int room = 0; tcnt = 0;
    for (int x = 0; x < n; x++) if (x != o) {
        room += cap[x];
        if (cap[x] == 1 && threatened(x, L, base[x])) {
            gm a = 0;
            for (int g = 0; g < m; g++) if ((C >> g & 1) && !threatened(x, L, base[x] | BIT(g))) a |= BIT(g);
            allow[tcnt] = a; tl[tcnt++] = x;
        }
    }
    if (popc(C) > room) return 0;
    for (int g = 0; g < m; g++) mt[g] = -1;
    for (int t = 0; t < tcnt; t++) { gm seen = 0; if (!aug(t, &seen)) return 0; }
    fill_bases();
    int left[MAXN];
    for (int x = 0; x < n; x++) left[x] = (x == o) ? 0 : cap[x];
    for (int g = 0; g < m; g++) if (mt[g] >= 0) { own[g] = tl[mt[g]]; left[tl[mt[g]]]--; }
    for (int g = 0; g < m; g++) if ((C >> g & 1) && own[g] < 0) {
        for (int x = 0; x < n; x++) if (left[x] > 0) { own[g] = x; left[x]--; break; }
        if (own[g] < 0) return 0;
    }
    for (int g = 0; g < m; g++) if (L >> g & 1) own[g] = o;
    return 1;
}
static long owner_tests;             /* sets C tried (effort) */
/* the owner search: every C of the size need (then, with -w1, every larger size), in lexicographic order of the index
   tuples, as lb4.c; by depth-first search with a prune that keeps it exact: a branch is cut when the goods already
   left out of C (they stay in the owner's bundle L whatever else is chosen) together with B_o threaten an agent that
   has no slot under any owner needs (a base of two or more goods, or a one-good base needed by an agent other than o),
   since threats only grow with L (monotonicity, k4/c4.md §1). -P0 turns the prune off. */
static int PRUNE = 1;
static int ow_o, ow_nj, ow_sz, ow_jl[MAXM], ow_hard[MAXN], ow_nh;
static gm ow_C;
static int ow_dfs(int p, int k, gm excl) {
    if (k == ow_sz) { owner_tests++; return try_C(ow_o, ow_C); }
    if (ow_nj - p < ow_sz - k) return 0;
    /* include jl[p] first (lexicographic order), then exclude it */
    ow_C |= BIT(ow_jl[p]);
    if (ow_dfs(p + 1, k + 1, excl)) return 1;
    ow_C &= ~BIT(ow_jl[p]);
    if (ow_nj - p - 1 < ow_sz - k) return 0;
    gm e2 = excl | BIT(ow_jl[p]);
    if (PRUNE) { gm L = base[ow_o] | e2; for (int h = 0; h < ow_nh; h++) if (threatened(ow_hard[h], L, base[ow_hard[h]])) return 0; }
    return ow_dfs(p + 1, k, e2);
}
static int try_owner(int o, int S) {
    if (o < 0) {                      /* |J| <= S: fill the slots in any order */
        int left[MAXN]; fill_bases();
        for (int x = 0; x < n; x++) left[x] = cap[x];
        for (int g = 0; g < m; g++) if (J >> g & 1)
            for (int x = 0; x < n; x++) if (left[x]) { own[g] = x; left[x]--; break; }
        for (int g = 0; g < m; g++) if (own[g] < 0) return 0;
        return 1;
    }
    int need = S - cap[o]; if (need > popc(J)) need = popc(J);
    ow_o = o; ow_nj = 0; for (int g = 0; g < m; g++) if (J >> g & 1) ow_jl[ow_nj++] = g;
    gm NAo = 0; for (int i = 0; i < n; i++) if (i != o) NAo |= N_[i];
    ow_nh = 0;
    for (int x = 0; x < n; x++) if (x != o && (popc(base[x]) >= 2 || (popc(base[x]) == 1 && (base[x] & NAo)))) ow_hard[ow_nh++] = x;
    for (int sz = need; sz <= (OWNW ? ow_nj : need); sz++) {   /* subsets of size need, then larger (-w1) */
        ow_sz = sz; ow_C = 0;
        if (ow_dfs(0, 0, 0)) return 1;
    }
    return 0;
}

static void setup_state(void) {
    for (int i = 0; i < n; i++) {
        upg[i] = 0; base[i] = Y[i] >= 0 ? BIT(Y[i]) : 0;
        N_[i] = Y[i] >= 0 ? above(i, Y[i]) : R[i];
    }
}
static int upg_mode;
static void upgrades(void) {
    if (!upg_mode) return;
    for (int again = 1; again;) {
        again = 0;
        gm NA = NAset();
        for (int k = 0; k < n && !again; k++) if (!upg[k] && Y[k] >= 0 && !(NA >> Y[k] & 1) && N_[k]) {
            for (int r = 0; r < d[k]; r++) {
                int g = ord[k][r];
                if (!(J >> g & 1)) continue;
                gm nn = 0, B = base[k] | BIT(g);
                for (int x = 0; x < m; x++) if ((N_[k] >> x & 1) && cmpv(k, BIT(x), B) > 0) nn |= BIT(x);
                if (upg_mode == 2 && cmpv(k, B, R[k] & ~B) < 0) continue;   /* mode 2: only envy-free upgrades */
                if (nn != N_[k]) { upg[k] = 1; base[k] = B; J &= ~BIT(g); N_[k] = nn; again = 1; break; }
            }
        }
    }
}
static int slots(void) {
    gm NA = NAset(); int S = 0;
    for (int i = 0; i < n; i++) {
        frz[i] = !upg[i] && Y[i] >= 0 && (NA >> Y[i] & 1);
        cap[i] = (upg[i] || frz[i]) ? 0 : (Y[i] >= 0 ? 1 : 2);
        S += cap[i];
    }
    return S;
}

/* ---- rotation: a frozen agent k gives up its pick along a need chain k = x0 -> .. -> xt (not frozen), every chain
   agent takes its predecessor's pick, xt's base is released, and k takes a nonempty O of its goods in J as its base */
static int ROT = 2, rot_depth = 0, CHUP = 1, rot_cap = 0, used_rot = 0;
static int KMODE = 0;                /* apply_chain tests Lemma K instead of the owner search (k4/rulef.md) */
static int hdefK_owner(int o);
static long effort;
static int try_rotations(void);
static int chain[MAXN], clen;
static int apply_chain(int rot_pick, int *rot_more) {
    int sY[MAXN], su[MAXN]; gm sb[MAXN], sN[MAXN], sJ = J;
    memcpy(sY, Y, sizeof Y); memcpy(su, upg, sizeof upg); memcpy(sb, base, sizeof base); memcpy(sN, N_, sizeof N_);
    effort++;
    int k = chain[0], t = chain[clen - 1];
    J |= base[t]; upg[t] = 0;            /* the chain end releases its base (a pick, or an upgraded pair) */
    for (int i = clen - 1; i >= 1; i--) { Y[chain[i]] = Y[chain[i - 1]]; base[chain[i]] = BIT(Y[chain[i]]); N_[chain[i]] = above(chain[i], Y[chain[i]]); }
    gm W = R[k] & J, B = 0;
    /* k's new base: the rot_pick-th nonempty subset of W, pairs first, then triples, singles, quadruples */
    { int cnt = 0, want = rot_pick; static const int szord[5] = {2, 3, 1, 4, 0};
      for (int zi = 0; zi < 4 && !B; zi++) for (gm O = W;; O = (O - 1) & W) {
          if (O && popc(O) == szord[zi] && cnt++ == want) { B = O; break; }
          if (!O) break; }
      if (!B) { memcpy(Y, sY, sizeof Y); memcpy(upg, su, sizeof upg); memcpy(base, sb, sizeof base); memcpy(N_, sN, sizeof N_); J = sJ; *rot_more = 0; return 0; } }
    J &= ~B; upg[k] = 1; base[k] = B; Y[k] = -2;
    gm nn = 0;
    for (int x = 0; x < m; x++) if ((R[k] & ~B) >> x & 1) { if (!B || cmpv(k, BIT(x), B) > 0) nn |= BIT(x); }
    N_[k] = nn;
    int ok = 0;
    gm NA = NAset();
    int valid = !(J & NA);
    for (int i = 0; i < n; i++) if (upg[i] && (base[i] & NA)) valid = 0;
    /* a base of 3 or more goods must be the owner's; two such bases cannot both be, and the state is rejected */
    int nbig = 0, big = -1;
    for (int i = 0; i < n; i++) if (popc(base[i]) >= 3) { nbig++; big = i; }
    if (nbig >= 2) valid = 0;
    if (valid && KMODE) {             /* Lemma K at the rotated state (k4/rulef.md): no owner search */
        int S = slots();
        if (nbig == 1) ok = hdefK_owner(big) <= 0;
        else if (popc(J) - S <= 0) ok = 1;
        else {
            ok = hdefK_owner(k) <= 0;
            for (int o = 0; o < n && !ok; o++) if (o != k && !frz[o] && (cap[o] > 0 || upg[o])) ok = hdefK_owner(o) <= 0;
        }
    } else if (valid) {
        int S = slots();
        if (nbig == 1) ok = try_owner(big, S);
        else if (popc(J) - S >= 1) ok = try_owner(k, S);
        else ok = try_owner(-1, S) || try_owner(k, S);
        if (!ok && nbig == 0 && popc(J) - S >= 1)
            for (int o = 0; o < n && !ok; o++) if (o != k && (cap[o] > 0 || upg[o])) ok = try_owner(o, S);
    }
    if (ok) used_rot = rot_depth + 1;
    if (!ok && valid && rot_depth + 1 < rot_cap) {    /* rotate again from the rotated state */
        int sc[MAXN], sl = clen; memcpy(sc, chain, sizeof sc);
        rot_depth++; ok = try_rotations(); rot_depth--;
        memcpy(chain, sc, sizeof sc); clen = sl;
    }
    if (!ok) { memcpy(Y, sY, sizeof Y); memcpy(upg, su, sizeof upg); memcpy(base, sb, sizeof base); memcpy(N_, sN, sizeof N_); J = sJ; slots(); }
    return ok;
}
static int ext_chain(void) {
    int x = chain[clen - 1];
    if (clen > 1 && !frz[x]) {
        int more = 1;
        for (int p = 0; more; p++) if (apply_chain(p, &more)) return 1;
        return 0;
    }
    for (int j = 0; j < n; j++) {
        int in = 0; for (int q = 0; q < clen; q++) if (chain[q] == j) in = 1;
        if (in || (upg[j] && !CHUP) || Y[x] < 0 || !(N_[j] >> Y[x] & 1)) continue;
        chain[clen++] = j;
        if (ext_chain()) return 1;
        clen--;
    }
    return 0;
}
static int try_rotations(void) {
    int fz[MAXN]; memcpy(fz, frz, sizeof fz);
    for (int p = n - 1; p >= 0; p--) for (int k = 0; k < n; k++) if (pos[k] == p && fz[k]) {
        chain[0] = k; clen = 1;
        if (ext_chain()) return 1;
    }
    return 0;
}

/* LB4r on the Phase 1 state of the current tau, one policy, rotation bound rot_cap */
static int construct2(void) {
    phase1();
    setup_state();
    upgrades();
    int S = slots(), w = popc(J) - S;
    if (w <= 0) { try_owner(-1, S); last_status = 0; return 1; }
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    if (!frz[r] && try_owner(r, S)) { last_status = 1; return 1; }
    if (OWN == 1) { last_status = -1; return 0; }
    if (OWN == 2) { if (rot_cap && try_rotations()) { last_status = 3; return 1; } last_status = -1; return 0; }
    int ordr[MAXN], k = 0;
    for (int p = n - 1; p >= 0; p--) for (int i = 0; i < n; i++) if (pos[i] == p && i != r && (cap[i] > 0 || upg[i])) ordr[k++] = i;
    for (int t = 0; t < k; t++) if (try_owner(ordr[t], S)) { last_status = 2; return 1; }
    if (rot_cap && try_rotations()) { last_status = 3; return 1; }
    last_status = -1; return 0;
}
static int used_pol;
static const int POLS[3] = {1, 2, 0};
/* LB4r(tau) for the tau fixed in pre[]: bound outermost, every policy at each bound; returns 1 on success, with
   used_rot (fewest rotations) and used_pol (index into POLS) */
static int lb4r(int maxrot) {
    for (int c = 0; c <= maxrot; c++) {
        for (int pi = 0; pi < 3; pi++) {
            if (UPG != 3 && POLS[pi] != UPG) continue;
            upg_mode = POLS[pi]; rot_cap = c; used_rot = 0; rot_depth = 0;
            if (construct2()) { used_pol = pi; return 1; }
        }
    }
    return 0;
}

/* omega of the Phase 1 state of the current tau (pre[]) after upgrades of policy pol */
static int omega_of(int pol, int *nfrz4) {
    phase1(); setup_state(); upg_mode = pol; upgrades();
    int S = slots(), w = popc(J) - S;
    if (nfrz4) { *nfrz4 = 0; for (int i = 0; i < n; i++) if (frz[i] && d[i] == 4) (*nfrz4)++; }
    return w;
}

/* ---- insertion rules ---- */
/* rules computed inside Phase 1 from the state at the insertion step (G: goods not yet picked, done: processed) */
static int nabove_block(int c, gm G, const int *done0) {   /* |NA| of the agents of c's block (rule 1) */
    int done[MAXN]; memcpy(done, done0, sizeof done);
    gm NA = 0;
    for (int i = c;;) {
        int y = favr(i, G); if (y >= 0) G &= ~BIT(y); done[i] = 1;
        NA |= y >= 0 ? above(i, y) : R[i];
        i = pstep(G, done); if (i < 0) break;
    }
    return popc(NA);
}
static int contest(int c, gm G, const int *done) {        /* other unprocessed agents that value c's top */
    int y = favr(c, G), k = 0;
    for (int i = 0; i < n; i++) if (!done[i] && i != c && (R[i] >> y & 1)) k++;
    return k;
}
/* the first round of Sgouritsa-Sotiriou (arXiv 2502.09777 §3, Lemma 3.7; proofs/pq_bounded.md §2.5) carried to k = 4:
   a matching of the agents in A to goods of G, each agent to its first or second choice among its goods in G, of
   maximum weight with weights 1 (first) and 0 (second) among the matchings of maximum size (min-cost flow, successive
   shortest paths by Bellman-Ford; ties by index). cls[i] = 0 matched to its first choice, 1 to its second, 2 unmatched. */
static void choice_matching(const int *A, int na, gm G, int *cls) {
    int nn = 2 + na + m, src = 0, snk = 1;               /* nodes: src, snk, agents 2.., goods 2+na.. */
    static int eu[4 * MAXN + MAXM + 8], ev[4 * MAXN + MAXM + 8], ecap[4 * MAXN + MAXM + 8], ecost[4 * MAXN + MAXM + 8];
    int ne = 0;
    #define ADDE(a, b, c) do { eu[ne] = a; ev[ne] = b; ecap[ne] = 1; ecost[ne] = c; ne++; eu[ne] = b; ev[ne] = a; ecap[ne] = 0; ecost[ne] = -(c); ne++; } while (0)
    int f1[MAXN], f2[MAXN];
    for (int q = 0; q < na; q++) {
        int i = A[q], k = 0; f1[q] = f2[q] = -1;
        for (int r = 0; r < d[i]; r++) if (G >> ord[i][r] & 1) { if (k == 0) f1[q] = ord[i][r]; else if (k == 1) f2[q] = ord[i][r]; k++; }
        ADDE(src, 2 + q, 0);
        if (f1[q] >= 0) ADDE(2 + q, 2 + na + f1[q], -(na + 2));
        if (f2[q] >= 0) ADDE(2 + q, 2 + na + f2[q], -(na + 1));
    }
    for (int g = 0; g < m; g++) if (G >> g & 1) ADDE(2 + na + g, snk, 0);
    for (;;) {                                          /* shortest augmenting path (costs negative: maximize weight) */
        long dist[2 + MAXN + MAXM]; int pe[2 + MAXN + MAXM];
        for (int v = 0; v < nn; v++) { dist[v] = 1L << 40; pe[v] = -1; }
        dist[src] = 0;
        for (int it = 0; it < nn; it++) { int ch = 0;
            for (int e = 0; e < ne; e++) if (ecap[e] > 0 && dist[eu[e]] < (1L << 40) && dist[eu[e]] + ecost[e] < dist[ev[e]]) { dist[ev[e]] = dist[eu[e]] + ecost[e]; pe[ev[e]] = e; ch = 1; }
            if (!ch) break; }
        if (pe[snk] < 0 || dist[snk] >= 0) break;
        for (int v = snk; v != src; v = eu[pe[v]]) { ecap[pe[v]]--; ecap[pe[v] ^ 1]++; }
    }
    for (int q = 0; q < na; q++) {
        cls[A[q]] = 2;
        for (int e = 0; e < ne; e += 2) if (eu[e] == 2 + q && ev[e] >= 2 + na && ecap[e] == 0) cls[A[q]] = (ev[e] - 2 - na == f1[q]) ? 0 : 1;
    }
    #undef ADDE
}
static int mcls[MAXN];               /* rules 17, 18: classes of the matching on all agents and goods, set before Phase 1 */
static int rule_choose(int rule, const int *cand, int nc, gm G, const int *done) {
    int best = cand[0]; long bk = 1L << 60;
    for (int q = 0; q < nc; q++) {
        int c = cand[q]; long k;
        switch (rule) {
        case 1: k = nabove_block(c, G, done); break;
        case 6: k = d[c] == 4 ? 0 : 1; break;
        case 7: k = d[c] == 3 ? 0 : 1; break;
        case 8: k = contest(c, G, done); break;
        case 9: k = -contest(c, G, done); break;
        case 17: k = mcls[c]; break;                    /* matched to the first choice, then the second, then unmatched */
        case 18: k = mcls[c] == 1 ? 0 : mcls[c] == 0 ? 1 : 2; break;   /* matched to the second choice first */
        case 25: {                                      /* the matching recomputed on the unprocessed agents and goods */
            if (q == 0) { int A[MAXN], na = 0; for (int i = 0; i < n; i++) if (!done[i]) A[na++] = i; choice_matching(A, na, G, mcls); }
            k = mcls[c]; break; }
        default: k = 0;
        }
        if (k < bk) { bk = k; best = c; }
    }
    return best;
}

/* rollout rules: build tau step by step; at each insertion step score every candidate c by a run on (prefix, c, then
   index order), and keep the best (ties: the candidate first in index order) */
static int ROLLROT = 2;              /* rotation bound of rule 3's rollouts */
static long rollout_score(int rule, int *fail) {
    *fail = 0;
    if (rule == 2 || rule == 4 || rule == 5 || rule == 10 || rule == 11) {
        int f4, w = omega_of(rule == 4 ? 1 : rule == 5 ? 0 : 2, &f4);
        if (rule == 10) return (long)w * 64 + f4;
        if (rule == 11) {
            int lastq = 0; for (int i = 0; i < n; i++) if (d[i] == 4 && pos[i] > lastq) lastq = pos[i];
            return ((long)w * 64 + f4) * 64 - lastq;
        }
        return w;
    }
    /* rule 3: fewest rotations, then omega after envy-free upgrades */
    int ok = lb4r(ROLLROT), r = ok ? used_rot : ROLLROT + 1;
    int w = omega_of(2, NULL);
    return (long)r * 4096 + (w + 2048);
}
static int is_rollout(int rule) { return rule == 2 || rule == 3 || rule == 4 || rule == 5 || rule == 10 || rule == 11 || rule == 12 || rule == 13; }
static int one_change(void);
static void choose_seq(int rule) {   /* fills pre[] (npre) with the rule's insertion sequence */
    npre = 0; TAILRULE = 0;
    if (rule == 14) { one_change(); return; }
    int srule = rule == 12 ? 3 : rule == 13 ? 2 : rule;   /* 12, 13: rules 3, 2 at the first insertion step only */
    if (rule == 17 || rule == 18) { int A[MAXN]; for (int i = 0; i < n; i++) A[i] = i; choice_matching(A, n, ALLG, mcls);
        if (VERB > 1) { printf("  matching classes:"); for (int i = 0; i < n; i++) printf(" %d", mcls[i]); printf("\n"); } }
    if (!is_rollout(rule)) {         /* local rule: run Phase 1 with it and record the sequence */
        TAILRULE = rule; stop_at = -1; phase1(); TAILRULE = 0;
        memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins; return;
    }
    for (;;) {
        stop_at = npre;
        int complete = phase1();
        stop_at = -1;
        if (complete) break;
        int cand[MAXN], nc = nscand; memcpy(cand, scand, sizeof cand);
        int bestc = cand[0]; long bs = 1L << 60;
        if ((rule == 12 || rule == 13) && npre > 0) { pre[npre++] = bestc; continue; }
        for (int q = 0; q < nc; q++) {
            pre[npre] = cand[q]; npre++;
            int f; long s = rollout_score(srule, &f);
            if (VERB > 1) printf("  step %d cand %d score %ld\n", npre - 1, cand[q], s);
            npre--;
            if (s < bs) { bs = s; bestc = cand[q]; }
        }
        pre[npre++] = bestc;
    }
}
/* -L: local search on tau: change one insertion step (then index order), keep a change that lowers
   (rotations needed, omega after envy-free upgrades); returns 1 if LB4r(tau) succeeds at the end */
static long tau_key(void) {
    int ok = lb4r(ROT), r = ok ? used_rot : ROT + 1;
    int w = omega_of(2, NULL);
    return (long)r * 4096 + (w + 2048);
}
static int local_search(void) {
    long cur = tau_key();
    for (int round = 0; round < LSR && cur >= 4096; round++) {   /* while some rotation is needed */
        int base_pre[MAXN], bn = npre, improved = 0;
        memcpy(base_pre, pre, sizeof base_pre);
        long bestk = cur; int bp[MAXN], bnp = 0;
        for (int j = 0; j < bn && !improved; j++) {
            /* candidates at step j of tau */
            npre = j; memcpy(pre, base_pre, sizeof(int) * j); stop_at = j; phase1(); stop_at = -1;
            int cand[MAXN], nc = nscand; memcpy(cand, scand, sizeof cand);
            for (int q = 0; q < nc; q++) if (cand[q] != base_pre[j]) {
                memcpy(pre, base_pre, sizeof(int) * j); pre[j] = cand[q]; npre = j + 1;
                TAILRULE = 0; phase1();             /* complete in index order and record the sequence */
                memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
                long k = tau_key();
                if (k < bestk) { bestk = k; memcpy(bp, pre, sizeof bp); bnp = npre; improved = 1; break; }
            }
        }
        if (!improved) { memcpy(pre, base_pre, sizeof base_pre); npre = bn; break; }
        memcpy(pre, bp, sizeof bp); npre = bnp; cur = bestk;
    }
    return cur < (long)(ROT + 1) * 4096;
}

/* rule 14: the index run, or the index run with one insertion step j changed to another candidate (index order
   after it); the sequence with the least (rotations needed, omega after envy-free upgrades), the index run on ties */
static int one_change(void) {
    npre = 0; TAILRULE = 0; stop_at = -1; phase1();
    int base_pre[MAXN], bn = nins; memcpy(base_pre, ins_seq, sizeof base_pre);
    memcpy(pre, base_pre, sizeof base_pre); npre = bn;
    long bestk = tau_key(); int bp[MAXN], bnp = bn; memcpy(bp, base_pre, sizeof bp);
    for (int j = 0; j < bn && bestk >= 4096; j++) {
        npre = j; memcpy(pre, base_pre, sizeof(int) * j); stop_at = j; phase1(); stop_at = -1;
        int cand[MAXN], nc = nscand; memcpy(cand, scand, sizeof cand);
        for (int q = 0; q < nc; q++) if (cand[q] != base_pre[j]) {
            memcpy(pre, base_pre, sizeof(int) * j); pre[j] = cand[q]; npre = j + 1;
            phase1(); memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
            long k = tau_key();
            if (k < bestk) { bestk = k; memcpy(bp, pre, sizeof bp); bnp = npre; }
        }
    }
    memcpy(pre, bp, sizeof bp); npre = bnp;
    return 1;
}

/* rules 15 and 16: the same families as rules 14 and 12, searched with the rotation bound outermost: for c = 0, 1, ..,
   -rN, the first sequence of the family (in the order below) on which LB4r succeeds with at most c rotations.
   Family of rule 15: the index run, then the index run with step j changed to another candidate (j = 0, 1, ..;
   candidates in index order; index order after the change). Family of rule 16: c first, then index order, for every
   candidate c of the first insertion step in index order. Returns 1 with pre[] set, or 0 (pre[] = index run). */
static int fam_seq(int rule, int k, int *fseq, int *fn) {   /* the k-th sequence of the family, 0 if none */
    npre = 0; TAILRULE = 0; stop_at = -1; phase1();
    int base_pre[MAXN], bn = nins; memcpy(base_pre, ins_seq, sizeof base_pre);
    if (k == 0 && rule == 15) { memcpy(fseq, base_pre, sizeof base_pre); *fn = bn; return 1; }
    int idx = rule == 15 ? 1 : 0;
    for (int j = 0; j < (rule == 15 ? bn : 1); j++) {
        npre = j; memcpy(pre, base_pre, sizeof(int) * j); stop_at = j; phase1(); stop_at = -1;
        int cand[MAXN], nc = nscand; memcpy(cand, scand, sizeof cand);
        for (int q = 0; q < nc; q++) if (rule == 16 || cand[q] != base_pre[j]) {
            if (idx++ == k) {
                memcpy(pre, base_pre, sizeof(int) * j); pre[j] = cand[q]; npre = j + 1;
                phase1(); memcpy(fseq, ins_seq, sizeof(int) * nins); *fn = nins; return 1;
            }
        }
    }
    return 0;
}
static int deepen_family(int rule) {
    int fseq[MAXN], fn;
    for (int c = 0; c <= ROT; c++)
        for (int k = 0; fam_seq(rule, k, fseq, &fn); k++) {
            memcpy(pre, fseq, sizeof fseq); npre = fn;
            if (lb4r(c)) return 1;
        }
    fam_seq(rule == 15 ? 15 : 16, 0, fseq, &fn); memcpy(pre, fseq, sizeof fseq); npre = fn;
    return 0;
}

/* ---- coverage: the theorems of k4/c4.md §2-§4c (A4, B4, B4w, A4T, A4+) and A4+(o) of k4/c4one.md §5 ----
   Ported from k4/c4check.c of branch proof/k4-c4one (check_AB, check_AB1, check_Bw, check_AT, check_Aplus,
   aplus_owner, chain_ends, first_chain, is_leader; the same conditions, the same first need chain), without its
   counters. A run of Phase 1 (tau in pre[]) is *covered* when, after envy-free upgrades, omega <= 0 or one of these
   theorems applies to it; then LB4r(tau) with envy-free upgrades and at most one rotation succeeds (by the theorems;
   the owner's needs from its base, whose completions are also completions with needs from the bundle, k4/c4.md
   §1.1). -C1: theorems of k4/c4.md only; -C2 (default): with A4+(o) for every owner. With -Z1 every covered run is
   also checked: LB4r(tau) with envy-free upgrades only, the owner's needs from the base and at most one rotation must
   succeed (a violation is printed as COVVIOL and counted). */
static int COVT = 2, COVZ = 0; static long covviol, covchk, leaf_viol, leaf_chk;   /* leaf_*: this leaf, added when it completes */
static int is_leader(int x) { for (int i = 0; i < n; i++) if (blk[i] == blk[x] && pos[i] < pos[x]) return 0; return 1; }
static int nends; static int ends_[64]; static int ch2[MAXN], cl2;
static void chain_ends(void) {
    int x = ch2[cl2 - 1];
    if (cl2 > 1 && !frz[x]) { if (nends < 64) ends_[nends] = x; nends++; return; }
    for (int j = 0; j < n; j++) {
        int in = 0; for (int q = 0; q < cl2; q++) if (ch2[q] == j) in = 1;
        if (in || upg[j] || Y[x] < 0 || !(N_[j] >> Y[x] & 1)) continue;
        ch2[cl2++] = j; chain_ends(); cl2--;
    }
}
static int first_chain(int *out, int target) {   /* a need chain from ch2[0] ending at target; returns its length */
    int x = ch2[cl2 - 1];
    if (cl2 > 1 && !frz[x]) { if (x == target) { memcpy(out, ch2, sizeof(int) * cl2); return cl2; } return 0; }
    for (int j = 0; j < n; j++) {
        int in = 0; for (int q = 0; q < cl2; q++) if (ch2[q] == j) in = 1;
        if (in || upg[j] || Y[x] < 0 || !(N_[j] >> Y[x] & 1)) continue;
        ch2[cl2++] = j; int L = first_chain(out, target); cl2--; if (L) return L;
    }
    return 0;
}
typedef struct { int Y[MAXN], upg[MAXN], frz[MAXN], cap[MAXN]; gm base[MAXN], N[MAXN], J; } snap_t;
static void snap_save(snap_t *s) { memcpy(s->Y, Y, sizeof Y); memcpy(s->upg, upg, sizeof upg); memcpy(s->frz, frz, sizeof frz); memcpy(s->cap, cap, sizeof cap); memcpy(s->base, base, sizeof base); memcpy(s->N, N_, sizeof N_); s->J = J; }
static void snap_load(const snap_t *s) { memcpy(Y, s->Y, sizeof Y); memcpy(upg, s->upg, sizeof upg); memcpy(frz, s->frz, sizeof frz); memcpy(cap, s->cap, sizeof cap); memcpy(base, s->base, sizeof base); memcpy(N_, s->N, sizeof N_); J = s->J; }
/* Theorem B4w's hypotheses: the only exposed 4-good agent w is frozen; rotate it along a need chain to r, O = R_w & W */
static int cov_Bw(int r, gm W, const int *E, int w) {
    int chn[MAXN]; ch2[0] = w; cl2 = 1; int L = first_chain(chn, r);
    if (!L) return 0;
    int hyp = 0, ks = -1;
    for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
    gm O = R[w] & W;
    int c1 = 1;
    for (int x = 0; x < n; x++) if (E[x] && x != w && d[x] == 3 && ((R[x] & ~BIT(ord[x][0])) & ~O) == 0) c1 = 0;
    int c2 = !E[ks] || ks == w || !frz[ks];
    if (!c2) { nends = 0; ch2[0] = ks; cl2 = 1; chain_ends(); for (int q = 0; q < nends && q < 64; q++) if (ends_[q] != r) c2 = 1; }
    snap_t sv; snap_save(&sv);
    J |= base[r];
    for (int i = L - 1; i >= 1; i--) { Y[chn[i]] = Y[chn[i - 1]]; base[chn[i]] = BIT(Y[chn[i]]); N_[chn[i]] = above(chn[i], Y[chn[i]]); }
    J &= ~O; upg[w] = 1; base[w] = O; Y[w] = -2;
    { gm nn = 0; for (int x = 0; x < m; x++) if ((R[w] & ~O) >> x & 1 && cmpv(w, BIT(x), O) > 0) nn |= BIT(x); N_[w] = nn; }
    gm NA = NAset(); int valid = !(J & NA);
    for (int i = 0; i < n; i++) if (upg[i] && (base[i] & NA)) valid = 0;
    for (int i = 0; i < n; i++) if (i != w && popc(base[i]) >= 3) valid = 0;
    if (valid && (base[w] | J) == W) {
        slots(); int e42 = 0;
        if (!c2 && !frz[r]) c2 = 1;              /* (ii): r is a terminal after the rotation */
        for (int x = 0; x < n; x++) if (x != w && !upg[x] && threatened(x, W, base[x]) && d[x] == 4) e42 = 1;
        hyp = !e42 && c1 && c2;
    }
    snap_load(&sv);
    return hyp;
}
/* Theorem A4T: the only exposed 4-good agent w is free; r is valid unless (Tc) or (Tb) */
static int best_junk(int x) { for (int q = 0; q < d[x]; q++) if (J >> ord[x][q] & 1) return ord[x][q]; return -1; }
static int ends_all_in(int k, int a, int b) {
    nends = 0; ch2[0] = k; cl2 = 1; chain_ends();
    if (!nends) return 0;
    for (int q = 0; q < nends && q < 64; q++) if (ends_[q] != a && ends_[q] != b) return 0;
    return 1;
}
static int cov_AT(int r, const int *E, int w) {
    int gw = best_junk(w), lw = -1, ks = -1;
    for (int i = 0; i < n; i++) if (blk[i] == blk[w] && (lw < 0 || pos[i] < pos[lw])) lw = i;
    for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
    int lwall = blk[w] != blk[r] && lw != w && E[lw] && frz[lw] && ends_all_in(lw, w, w);
    int tc = lwall && !(gw >= 0 && (R[lw] >> gw & 1));
    int served = lwall && !tc ? lw : -1;
    int disj = 1;
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++)
        if (E[x] && E[y] && d[x] == 3 && d[y] == 3 && x != served && y != served && (R[x] & R[y] & J)) disj = 0;
    int tb = ks != w && E[ks] && frz[ks] && disj && ends_all_in(ks, r, blk[w] == blk[r] ? w : r);
    return !tc && !tb;
}
static int rho4(int w, gm W) {               /* least number of junk goods of R_w to remove from W so that w is safe */
    gm cand = J & R[w]; int best = 99;
    for (gm D = cand;; D = (D - 1) & cand) {
        if (popc(D) < best && !threatened(w, W & ~D, base[w])) best = popc(D);
        if (!D) break;
    }
    return best;
}
static int cov_Aplus(int r, gm W, const int *E) {
    int dem = 0, tb = 0;
    for (int x = 0; x < n; x++) {
        if (x != r && !upg[x] && !frz[x]) tb += cap[x];
        if (!E[x]) continue;
        if (d[x] == 3 || !frz[x]) dem += 1; else dem += rho4(x, W);
    }
    return dem <= tb;
}
static int aplus_owner(int o) {
    gm Wo = base[o] | J; int dem = 0, tb = 0;
    for (int x = 0; x < n; x++) {
        if (x == o) continue;
        if (!upg[x] && !frz[x]) tb += cap[x];
        if (upg[x] || !threatened(x, Wo, base[x])) continue;
        if (!frz[x] && Y[x] >= 0 && cap[x] >= 1 && popc(base[o] & R[x]) <= 1) dem += 1;
        else dem += rho4(x, Wo);
    }
    return dem <= tb;
}
/* Theorems A4 and B4 (no exposed 4-good agent), B4w and A4T (one): 1 if one of them applies */
static int cov_AB1(int r, gm W, const int *E, int e4) {
    if (e4) {
        int ne4 = 0, w4 = -1; for (int x = 0; x < n; x++) if (E[x] && d[x] == 4) { ne4++; w4 = x; }
        if (ne4 == 1 && !frz[w4]) return cov_AT(r, E, w4);
        if (ne4 == 1 && frz[w4]) return cov_Bw(r, W, E, w4);
        return 0;
    }
    for (int x = 0; x < n; x++) if (E[x] && (d[x] != 3 || Y[x] != ord[x][0] || !is_leader(x))) { printf("A3VIOL\n"); leaf_viol++; return 0; }
    int ks = -1;
    for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
    int bad = E[ks] && ks != r && frz[ks];
    if (bad) { nends = 0; ch2[0] = ks; cl2 = 1; chain_ends(); for (int q = 0; q < nends && q < 64; q++) if (ends_[q] != r) bad = 0; if (!nends) bad = 0; }
    if (bad) for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (E[x] && E[y] && (R[x] & R[y] & J)) bad = 0;
    if (!bad) return 1;                           /* Theorem A4 */
    int pr = 0, chn[MAXN]; ch2[0] = ks; cl2 = 1; int L = first_chain(chn, r);
    snap_t sv; snap_save(&sv);
    J |= base[r];
    for (int i = L - 1; i >= 1; i--) { Y[chn[i]] = Y[chn[i - 1]]; base[chn[i]] = BIT(Y[chn[i]]); N_[chn[i]] = above(chn[i], Y[chn[i]]); }
    gm O = BIT(ord[ks][1]) | BIT(ord[ks][2]);
    J &= ~O; upg[ks] = 1; base[ks] = O; Y[ks] = -2;
    { gm nn = 0; for (int x = 0; x < m; x++) if ((R[ks] & ~O) >> x & 1 && cmpv(ks, BIT(x), O) > 0) nn |= BIT(x); N_[ks] = nn; }
    gm NA = NAset(); int valid = !(J & NA);
    for (int i = 0; i < n; i++) if (upg[i] && (base[i] & NA)) valid = 0;
    if (valid) {
        slots(); int e42 = 0;
        for (int x = 0; x < n; x++) if (x != ks && !upg[x] && threatened(x, W, base[x]) && x == r && d[x] == 4) e42 = 1;
        pr = !e42;                                /* Theorem B4: r is not a 4-good agent exposed after the rotation */
    } else { printf("ROTINV\n"); leaf_viol++; }
    snap_load(&sv);
    return pr;
}
/* -C3: candidate Theorem A4+N (k4/adaptive.md §6): A4+(o) after need-shrinking upgrades, where an upgraded agent can
   be threatened (its pair need not be envy-free); it holds its base and has no slot, so it is counted like a frozen
   one, by rho. Owner o: not frozen, with a base of at most one good, or upgraded. Returns the owner, or -1. */
/* A4+N's owners in the order tried (r first when it is not upgraded and not frozen) */
static int aplusN_cands(int *ordo) {
    int r = -1, k = 0;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    if (r >= 0 && !frz[r]) ordo[k++] = r;
    for (int o = 0; o < n; o++) if (o != r && !frz[o] && (cap[o] > 0 || upg[o])) ordo[k++] = o;
    return k;
}
/* A4+N's count for owner o: the threatened agents' demand is at most the non-frozen, non-upgraded agents' capacity */
static int aplusN_ok(int o) {
    gm Wo = base[o] | J; int dem = 0, tb = 0;
    for (int x = 0; x < n && dem < 99; x++) {
        if (x == o) continue;
        if (!upg[x] && !frz[x]) tb += cap[x];
        if (!threatened(x, Wo, base[x])) continue;
        if (!upg[x] && !frz[x] && Y[x] >= 0 && cap[x] >= 1 && popc(base[o] & R[x]) <= 1) dem += 1;
        else dem += rho4(x, Wo);
    }
    return dem <= tb;
}
static int aplusN_owner(void) {
    int ordo[MAXN], k = aplusN_cands(ordo);
    for (int q = 0; q < k; q++) if (aplusN_ok(ordo[q])) return ordo[q];
    return -1;
}
/* is the run of Phase 1 on pre[] covered? (envy-free upgrades; the state is left after the upgrades) */
static int cov_last, cov_owner;      /* how: 0 omega <= 0, 1 A4/B4/B4w/A4T, 2 A4+ for r, 3 A4+(o); with -C3 after
                                        need-shrinking upgrades: 4 omega <= 0, 5 A4+N (cov_owner) */
static int covered0(void);
static int covered(void) {
    if (covered0()) return 1;
    if (COVT < 3) return 0;
    phase1(); setup_state(); upg_mode = 1; upgrades();
    int S = slots();
    if (popc(J) - S <= 0) { cov_last = 4; return 1; }
    int o = aplusN_owner();
    if (o >= 0) { cov_last = 5; cov_owner = o; return 1; }
    return 0;
}
static int covered0(void) {
    phase1(); setup_state(); upg_mode = 2; upgrades();
    int S = slots(), w = popc(J) - S;
    if (w <= 0) { cov_last = 0; return 1; }
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    if (frz[r]) { printf("A1VIOL\n"); leaf_viol++; return 0; }
    gm W = base[r] | J;
    int E[MAXN], e4 = 0;
    for (int x = 0; x < n; x++) { E[x] = (x != r && !upg[x] && threatened(x, W, base[x])); if (E[x] && d[x] == 4) e4 = 1; }
    if (cov_AB1(r, W, E, e4)) { cov_last = 1; return 1; }
    if (cov_Aplus(r, W, E)) { cov_last = 2; return 1; }
    if (COVT >= 2) for (int o = 0; o < n; o++) if (o != r && !frz[o] && (cap[o] > 0 || upg[o]) && aplus_owner(o)) { cov_last = 3; return 1; }
    return 0;
}
/* -Z1: a covered run must give LB4r(tau) with envy-free upgrades, needs from the base, at most one rotation */
static void cov_verify(void) {
    int su = UPG, sw = OWNW, ok;
    if (cov_last >= 4) {             /* A4+N: need-shrinking upgrades, the owner found (needs from its base), no rotation */
        OWNW = 0; phase1(); setup_state(); upg_mode = 1; upgrades();
        int S = slots();
        ok = cov_last == 4 ? try_owner(-1, S) : try_owner(cov_owner, S);
        OWNW = sw;
    } else { UPG = 2; OWNW = 0; ok = lb4r(1); UPG = su; OWNW = sw; }
    if (!ok) { leaf_viol++; report(cov_last >= 4 ? "COVVIOL_N" : "COVVIOL"); }
}
/* -Z2: Theorem A4+N on every run: for every insertion sequence, after need-shrinking upgrades to a fixpoint, if
   omega <= 0 the exact owner test with no owner, else with every owner that A4+N's count admits (needs from the base,
   no rotation); leaf_chk counts the (sequence, owner) instances, leaf_viol the failures (the first one reported) */
static void cov_all(void) {
    int si = INS, sw = OWNW, bad = 0, badpre[MAXN], nbad = 0, bado = -2;
    nchoice = 0;
    for (;;) {
        INS = 1; npre = 0; stop_at = -1; phase1(); INS = si;
        memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
        int ordo[MAXN], k, own_[MAXN + 1], no = 0;
        OWNW = 0; phase1(); setup_state(); upg_mode = 1; upgrades();
        if (popc(J) - slots() <= 0) own_[no++] = -1;
        else { k = aplusN_cands(ordo); for (int q = 0; q < k; q++) if (aplusN_ok(ordo[q])) own_[no++] = ordo[q]; }
        for (int q = 0; q < no; q++) {
            phase1(); setup_state(); upg_mode = 1; upgrades();
            leaf_chk++;
            if (!try_owner(own_[q], slots())) { if (!bad++) { memcpy(badpre, pre, sizeof(int) * npre); nbad = npre; bado = own_[q]; } }
        }
        OWNW = sw;
        int j = nins - 1;
        while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
        if (j < 0) break;
        choice[j]++; nchoice = j + 1;
    }
    nchoice = 0;
    if (bad) {
        leaf_viol += bad; memcpy(pre, badpre, sizeof(int) * nbad); npre = nbad;
        char lab[48]; snprintf(lab, sizeof lab, "COVVIOL_Z2 owner=%d", bado); report(lab);
    }
}
/* rules 20-22: the first covered run in a family; if none, the family's first sequence (index run), counted as
   uncovered. 20: index run, then the index run with one insertion step changed (rule 15's family, #37's Lemma X');
   21: every first agent, then index order (rule 16's family); 22: every insertion sequence (lexicographic). */
static long uncov; static int last_uncov;
static int cover_family(int rule) {
    int fseq[MAXN], fn;
    if (rule == 22) {
        nchoice = 0;
        for (;;) {
            INS = 1; npre = 0; stop_at = -1; phase1(); INS = 0;
            memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
            if (covered()) return 1;
            int j = nins - 1;
            while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
            if (j < 0) break;
            choice[j]++; nchoice = j + 1;
        }
        nchoice = 0; npre = 0; phase1(); memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
        return 0;
    }
    int fam = rule == 20 ? 15 : 16;
    for (int k = 0; fam_seq(fam, k, fseq, &fn); k++) {
        memcpy(pre, fseq, sizeof fseq); npre = fn;
        if (covered()) return 1;
    }
    fam_seq(fam, 0, fseq, &fn); memcpy(pre, fseq, sizeof fseq); npre = fn;
    return 0;
}

/* rule 24 (statistics): for each first agent c, the most rotations over every continuation of the insertion sequence
   (all later insertion steps free); the first c (index order) minimizing that maximum; used_rot = that maximum
   (ROT + 1 if some continuation fails). Answers: once the first agent is chosen, does every later order work? */
static int minmax_first(void) {
    npre = 0; stop_at = 0; phase1(); stop_at = -1;
    int cand[MAXN], nc = nscand; memcpy(cand, scand, sizeof cand);
    int best = ROT + 2, bestc = cand[0];
    for (int q = 0; q < nc && best > 0; q++) {
        int worst = -1;
        /* odometer over the continuations: choice[0] fixed to q */
        nchoice = 1; choice[0] = q;
        for (;;) {
            INS = 1; npre = 0; stop_at = -1; phase1(); INS = 0;
            memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
            int r = lb4r(ROT) ? used_rot : ROT + 1;
            if (r > worst) worst = r;
            if (worst >= best) break;
            int j = nins - 1;
            while (j >= 1 && choice[j] + 1 >= maxchoice[j]) j--;
            if (j < 1) break;
            choice[j]++; nchoice = j + 1;
        }
        if (worst < best) { best = worst; bestc = cand[q]; }
    }
    return best * 64 + bestc;
}

/* ==== rule F data and explicit first-agent rules (k4/rulef.md, workstream proof/k4-rulef) ====
   -A40: for every first agent a (tau_a = (a, then index order)) record
     fa_rot[a]  fewest rotations (<= -rN) of LB4r(tau_a), every policy (bound outermost); ROT + 1 if it fails;
     fa_cov[a]  the run of tau_a is covered (covered(): the theorems of k4/c4.md, k4/c4one.md, and with -C3 A4+N);
     fa_dN[a]   least A4+N deficit over the owners A4+N admits, after need-shrinking upgrades (sum dem - (S - cap(o)));
     fa_dE[a]   the same count after envy-free upgrades (A4+(o) of k4/c4one.md §5);
     fa_hN[a], fa_hE[a]  the refined count A4+H (k4/rulef.md): the free threatened agents with dem 1 take their
                best junk goods (index order), and the other threatened agents need a common set H of goods kept out,
                each x a protecting set D_x inside H; deficit = #dem-1 agents + min |H minus their slot goods| - (S - cap(o));
     omega <= 0 gives deficit DNEG.  Then the rule -QK picks the first agent whose sequence is run (the histogram);
   statistics per rule: weight where the rule's agent needs more rotations than rule F's (rel), and where it fails
   with at most one rotation (abs), on all profiles and on those where no tau_a is covered (allunc). */
#define DNEG (-100)
#define DINF 999
#define NRULES 24
static int QRULE = 1;
static int fa_rot[MAXN], fa_cov[MAXN], fa_dN[MAXN], fa_dE[MAXN], fa_hN[MAXN], fa_hE[MAXN], fa_omN[MAXN], fa_omE[MAXN];
static int fa_fz[MAXN], fa_e4[MAXN], fa_r[MAXN], fa_rfz[MAXN], fa_uN[MAXN], fa_uE[MAXN], fa_kN[MAXN], fa_kE[MAXN];
static int fa_choice[NRULES];
static long rs_kpos[MAXROT + 2], rs_kneg[MAXROT + 2], rs_c40[MAXROT + 2], rs_open[MAXROT + 2], rs_kviol, rs_cviol; static int rs_kpos_last, rs_anyabs;   /* by rule F's fewest rotations: some first agent has Lemma K deficit <= 0 (kneg) or none (kpos) */
static long rs_tot, rs_unc, rs_min[MAXROT + 2], rs_umin[MAXROT + 2], rs_rel[NRULES], rs_urel[NRULES], rs_abs[NRULES], rs_uabs[NRULES];
static int DUMP = 0;                 /* -DN: print DATA lines: N=1 allunc leaves, N=2 leaves needing a rotation, N=3 all, N=4 no first agent with Lemma K deficit <= 0, N=5 agent 0 (index order) has Lemma K deficit > 0, N=6 some rule of rulef_rules fails with at most one rotation */
static long dumped = 0, DUMPMAX = 2000000;
static int defA_owner(int o) {       /* A4+N / A4+(o) count for owner o in the current state */
    gm Wo = base[o] | J; int dem = 0, tb = 0;
    for (int x = 0; x < n; x++) {
        if (x == o) continue;
        if (!upg[x] && !frz[x]) tb += cap[x];
        if (!threatened(x, Wo, base[x])) continue;
        if (!upg[x] && !frz[x] && Y[x] >= 0 && cap[x] >= 1 && popc(base[o] & R[x]) <= 1) dem += 1;
        else { int r = rho4(x, Wo); if (r >= 99) return DINF; dem += r; }
    }
    return dem - tb;
}
/* minimal protecting sets of x against Wo: D inside R_x and J, x not threatened by Wo minus D with its base */
static int prot_sets(int x, gm Wo, gm *out) {
    gm cand = J & R[x]; int k = 0;
    gm subs[16]; int ns = 0;
    for (gm D = cand;; D = (D - 1) & cand) { if (ns < 16) subs[ns++] = D; if (!D) break; }
    for (int sz = 0; sz <= 4; sz++) for (int q = 0; q < ns; q++) if (popc(subs[q]) == sz) {
        int sup = 0; for (int t = 0; t < k; t++) if ((out[t] & subs[q]) == out[t]) sup = 1;
        if (sup) continue;
        if (!threatened(x, Wo & ~subs[q], base[x])) out[k++] = subs[q];
    }
    return k;
}
static gm hs_sets[MAXN][32]; static int hs_ns[MAXN], hs_cnt, hs_best; static gm hs_P;
static void hs_dfs(int i, gm U) {
    int c = popc(U & ~hs_P);
    if (c >= hs_best) return;
    if (i == hs_cnt) { hs_best = c; return; }
    for (int q = 0; q < hs_ns[i]; q++) hs_dfs(i + 1, U | hs_sets[i][q]);
}
static int hdef_owner(int o) {       /* the refined count A4+H for owner o */
    gm Wo = base[o] | J; int tb = 0, ne1 = 0; gm P = 0;
    hs_cnt = 0;
    for (int x = 0; x < n; x++) if (x != o && !upg[x] && !frz[x]) tb += cap[x];
    for (int x = 0; x < n; x++) {
        if (x == o || !threatened(x, Wo, base[x])) continue;
        if (!upg[x] && !frz[x] && Y[x] >= 0 && cap[x] >= 1 && popc(base[o] & R[x]) <= 1) {
            ne1++;
            for (int q = 0; q < d[x]; q++) { int g = ord[x][q]; if ((J >> g & 1) && !(P >> g & 1)) { P |= BIT(g); break; } }
        } else {
            hs_ns[hs_cnt] = prot_sets(x, Wo, hs_sets[hs_cnt]);
            if (!hs_ns[hs_cnt]) return DINF;
            hs_cnt++;
        }
    }
    hs_P = P; hs_best = 1 << 20; hs_dfs(0, 0);
    return ne1 + hs_best - tb;
}
/* A4+HU (k4/rulef.md): A4+H with the owner's needs taken from a kept set B_o ∪ K, K inside J ∩ R_o (Lemma H1's
   unfreezing, k4/hall.md §1): the agents frozen only because o needs their pick, and no longer needed by o once o
   holds B_o ∪ K, become free with one slot each; slot goods (self-protection and the set H) avoid K */
static int XKEEP = 0;                /* -Y1: kept-out sets may also hold every allowed good outside R_x (k4/rulef.md §2, remark 4) */
static int prot_sets_in(int x, gm Wo, gm allow, gm *out) {
    gm cand = allow & R[x]; int k = 0;
    gm subs[16]; int ns = 0;
    for (gm D = cand;; D = (D - 1) & cand) { if (ns < 16) subs[ns++] = D; if (!D) break; }
    for (int sz = 0; sz <= 4; sz++) for (int q = 0; q < ns; q++) if (popc(subs[q]) == sz) {
        int sup = 0; for (int t = 0; t < k; t++) if ((out[t] & subs[q]) == out[t]) sup = 1;
        if (sup) continue;
        if (!threatened(x, Wo & ~subs[q], base[x])) out[k++] = subs[q];
    }
    gm non = allow & ~R[x];          /* removing every allowed good outside R_x can leave a bundle inside R_x, where x
                                        discounts its least good (EFX0) */
    if (XKEEP && non) for (int sz = 0; sz <= 4; sz++) for (int q = 0; q < ns; q++) if (popc(subs[q]) == sz) {
        gm D = subs[q] | non;
        int sup = 0; for (int t = 0; t < k; t++) if ((out[t] & D) == out[t]) sup = 1;
        if (sup) continue;
        if (!threatened(x, Wo & ~D, base[x])) out[k++] = D;
    }
    return k;
}
static int hdefU_owner(int o) {
    gm cand = J & R[o]; int best = DINF;
    gm Wo = base[o] | J;
    gm NAo = 0; for (int i = 0; i < n; i++) if (i != o) NAo |= N_[i];
    for (gm K = cand;; K = (K - 1) & cand) {
        gm XK = base[o] | K, no = 0;
        for (int g = 0; g < m; g++) if ((N_[o] >> g & 1) && cmpv(o, BIT(g), XK) > 0) no |= BIT(g);
        gm NA2 = NAo | no;
        int fz2[MAXN], cp2[MAXN], tb = 0, ne1 = 0; gm P = 0;
        for (int i = 0; i < n; i++) {
            fz2[i] = !upg[i] && Y[i] >= 0 && (NA2 >> Y[i] & 1);
            cp2[i] = (upg[i] || fz2[i]) ? 0 : (Y[i] >= 0 ? 1 : 2);
            if (i != o) tb += cp2[i];
        }
        hs_cnt = 0; int dead = 0;
        for (int x = 0; x < n && !dead; x++) {
            if (x == o || !threatened(x, Wo, base[x])) continue;
            int g1 = -1;
            if (!upg[x] && !fz2[x] && Y[x] >= 0 && cp2[x] >= 1 && popc(base[o] & R[x]) <= 1)
                for (int q = 0; q < d[x]; q++) { int g = ord[x][q]; if ((J >> g & 1) && !(P >> g & 1)) { g1 = g; break; } }
            if (g1 >= 0 && !(K >> g1 & 1)) { ne1++; P |= BIT(g1); continue; }
            if (g1 < 0 && !upg[x] && !fz2[x] && Y[x] >= 0 && cp2[x] >= 1 && popc(base[o] & R[x]) <= 1) { ne1++; continue; }
            hs_ns[hs_cnt] = prot_sets_in(x, Wo, J & ~K, hs_sets[hs_cnt]);
            if (!hs_ns[hs_cnt]) { dead = 1; break; }
            hs_cnt++;
        }
        if (!dead) {
            hs_P = P; hs_best = 1 << 20; hs_dfs(0, 0);
            int v = ne1 + hs_best - tb;
            if (v < best) best = v;
        }
        if (!K) break;
    }
    return best;
}
/* Lemma K (k4/rulef.md §2): owner o, kept set K inside J ∩ R_o, the owner's needs from B_o ∪ K (agents frozen only
   by o's needs and no longer needed become free, one slot each); every agent x threatened by W_o = B_o ∪ J with its
   base is served either by a good g of J minus K in its own slot (x free with a slot, and not threatened by W_o minus g
   when holding B_x ∪ {g}), or by a set D inside (J minus K) ∩ R_x kept out of X_o (x not threatened by W_o minus D
   with its base); slot goods distinct. deficit = least |slot goods ∪ removal sets| - (slots of the agents other than
   o under the needs from B_o ∪ K). <= 0: o is a valid owner. */
static gm hk_opt[MAXN][MAXM + 32]; static int hk_nopt[MAXN], hk_isslot[MAXN][MAXM + 32], hk_cnt, hk_best;
static void hk_dfs(int i, gm U, gm G) {
    if (popc(U) >= hk_best) return;
    if (i == hk_cnt) { hk_best = popc(U); return; }
    for (int q = 0; q < hk_nopt[i]; q++) {
        gm O = hk_opt[i][q];
        if (hk_isslot[i][q] && (G & O)) continue;           /* slot goods distinct */
        hk_dfs(i + 1, U | O, hk_isslot[i][q] ? (G | O) : G);
    }
}
static int hdefK_owner(int o) {
    gm cand = J & R[o]; int best = DINF;
    gm Wo = base[o] | J;
    gm NAo = 0; for (int i = 0; i < n; i++) if (i != o) NAo |= N_[i];
    int thr[MAXN]; for (int x = 0; x < n; x++) thr[x] = x != o && threatened(x, Wo, base[x]);
    for (gm K = cand;; K = (K - 1) & cand) {
        gm XK = base[o] | K, no = 0;
        for (int g = 0; g < m; g++) if ((N_[o] >> g & 1) && cmpv(o, BIT(g), XK) > 0) no |= BIT(g);
        gm NA2 = NAo | no;
        int tb = 0, dead = 0;
        hk_cnt = 0;
        for (int x = 0; x < n; x++) {
            int fz2 = !upg[x] && Y[x] >= 0 && (NA2 >> Y[x] & 1);
            int cp2 = (upg[x] || fz2) ? 0 : (Y[x] >= 0 ? 1 : 2);
            if (x != o) tb += cp2;
            if (!thr[x]) continue;
            int k = 0;
            if (cp2 >= 1) {          /* slot goods: those of R_x, and one good outside R_x (a restriction: sound) */
                int outside = 0;
                for (int g = 0; g < m; g++) if ((J & ~K) >> g & 1) {
                    if (!(R[x] >> g & 1)) { if (outside) continue; outside = 1; }
                    if (!threatened(x, Wo & ~BIT(g), base[x] | BIT(g))) { hk_opt[hk_cnt][k] = BIT(g); hk_isslot[hk_cnt][k] = 1; k++; }
                }
            }
            gm sets[32]; int ns = prot_sets_in(x, Wo, J & ~K, sets);
            for (int q = 0; q < ns; q++) { hk_opt[hk_cnt][k] = sets[q]; hk_isslot[hk_cnt][k] = 0; k++; }
            if (!k) { dead = 1; break; }
            hk_nopt[hk_cnt++] = k;
        }
        if (!dead) {
            hk_best = 1 << 20; hk_dfs(0, 0, 0);
            int v = hk_best - tb;
            if (v < best) best = v;
        }
        if (!K) break;
    }
    return best;
}
/* deficits of the current tau (pre[]) after upgrades of policy pol: A4+ count (*dA), refined (*dH) and refined with
   the owner's needs from a kept set (*dU), least over owners; omega <= 0 gives DNEG */
static int fa_dU_tmp, fa_dK_tmp;
static int KONLY = 0;                /* deficits(): compute only the Lemma K count (mode 41) */
static void deficits(int pol, int *dA, int *dH, int *om, int *nfz) {
    phase1(); setup_state(); upg_mode = pol; upgrades();
    int S = slots(), w = popc(J) - S; *om = w;
    *nfz = 0; for (int i = 0; i < n; i++) *nfz += frz[i];
    if (w <= 0) { *dA = *dH = DNEG; fa_dU_tmp = fa_dK_tmp = DNEG; return; }
    int ordo[MAXN], k = aplusN_cands(ordo), ba = DINF, bh = DINF, bu = DINF, bk = DINF;
    for (int q = 0; q < k; q++) {
        int o = ordo[q];
        if (!KONLY) {
            int a = defA_owner(o); if (a < ba) ba = a;
            int h = hdef_owner(o); if (h < bh) bh = h;
            int u = hdefU_owner(o); if (u < bu) bu = u;
        }
        int kk = hdefK_owner(o); if (kk < bk) bk = kk;
        if (KONLY && bk <= 0) break;
    }
    *dA = ba; *dH = bh; fa_dU_tmp = bu; fa_dK_tmp = bk;
}
static int argmin_agent(const int *key) { int b = 0; for (int a = 1; a < n; a++) if (key[a] < key[b]) b = a; return b; }
static int fa_firstcov(void) { for (int a = 0; a < n; a++) if (fa_cov[a]) return a; return -1; }
static void rulef_rules(void) {
    int k1[MAXN], k2[MAXN];
    for (int k = 0; k < NRULES; k++) fa_choice[k] = 0;
    fa_choice[0] = 0;                                    /* index order */
    fa_choice[1] = argmin_agent(fa_rot);                 /* rule F */
    { int c = fa_firstcov(); fa_choice[2] = c >= 0 ? c : 0; }   /* first covered, else index */
    fa_choice[3] = argmin_agent(fa_dN);                  /* least A4+N deficit */
    fa_choice[4] = argmin_agent(fa_dE);                  /* least A4+(o) deficit (envy-free) */
    for (int a = 0; a < n; a++) k1[a] = fa_dN[a] < fa_dE[a] ? fa_dN[a] : fa_dE[a];
    fa_choice[5] = argmin_agent(k1);                     /* least of the two */
    fa_choice[6] = argmin_agent(fa_hN);                  /* least refined deficit, need-shrinking */
    for (int a = 0; a < n; a++) k2[a] = fa_hN[a] < fa_hE[a] ? fa_hN[a] : fa_hE[a];
    fa_choice[7] = argmin_agent(k2);                     /* least refined deficit, either policy */
    { int c = fa_firstcov(); fa_choice[8] = c >= 0 ? c : argmin_agent(k2); }   /* first covered, else rule 7 */
    fa_choice[9] = argmin_agent(fa_omN);                 /* least omega after need-shrinking upgrades (#44's -A4) */
    for (int a = 0; a < n; a++) k1[a] = k2[a] * 64 + fa_fz[a];
    fa_choice[10] = argmin_agent(k1);                    /* rule 7, ties by fewest frozen (need-shrinking) */
    for (int a = 0; a < n; a++) k1[a] = (d[a] == 4 ? 0 : 1);
    fa_choice[11] = argmin_agent(k1);                    /* first 4-good agent (first step only) */
    for (int a = 0; a < n; a++) k1[a] = fa_hN[a] * 64 + fa_e4[a];
    fa_choice[12] = argmin_agent(k1);                    /* rule 6, ties by fewest exposed 4-good agents */
    fa_choice[13] = argmin_agent(fa_uN);                 /* least A4+HU deficit, need-shrinking */
    for (int a = 0; a < n; a++) k1[a] = fa_uN[a] < fa_uE[a] ? fa_uN[a] : fa_uE[a];
    fa_choice[14] = argmin_agent(k1);                    /* least A4+HU deficit, either policy */
    { int c = fa_firstcov(); fa_choice[15] = c >= 0 ? c : argmin_agent(k1); }   /* first covered, else rule 14 */
    fa_choice[16] = argmin_agent(fa_kN);                 /* least Lemma K deficit, need-shrinking */
    for (int a = 0; a < n; a++) k2[a] = fa_kN[a] < fa_kE[a] ? fa_kN[a] : fa_kE[a];
    fa_choice[17] = argmin_agent(k2);                    /* least Lemma K deficit, either policy */
    { int c = fa_firstcov(); fa_choice[18] = c >= 0 ? c : argmin_agent(k2); }   /* first covered, else rule 17 */
}
/* Corollary C4^0's hypothesis on the run of pre[] (k4/c4.md §4, Lean EFX.LB4R.corollaryC40'; ledger K4.C4.AB.L):
   after envy-free upgrades omega <= 0, or no 4-good agent is exposed w.r.t. r and r is valid (Theorem A4) or, in
   LB+'s bad case, r is not a 4-good agent exposed after LB+'s rotation along the first need chain k* -> r */
static int c40_run(void) {
    phase1(); setup_state(); upg_mode = 2; upgrades();
    int S = slots(), w = popc(J) - S;
    if (w <= 0) return 1;
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    if (frz[r]) return 0;
    gm W = base[r] | J;
    int E[MAXN], e4 = 0;
    for (int x = 0; x < n; x++) { E[x] = (x != r && !upg[x] && threatened(x, W, base[x])); if (E[x] && d[x] == 4) e4 = 1; }
    if (e4) return 0;
    return cov_AB1(r, W, E, 0);
}
/* mode 41 (fast): rule RK = the first agent a (index order) whose run has Lemma K deficit <= 0 under need-shrinking or
   envy-free upgrades (omega <= 0 included); else the first whose run reaches, by one rotation, a state with Lemma K
   deficit <= 0 (k1_run); else the first whose envy-free run satisfies C4^0's hypothesis; else the agent of least
   Lemma K deficit (ties by index). rk_class: 0 Lemma K, 1 Lemma K after one rotation, 2 C4^0, 3 none (open). */
static int rk_class, rk_choice, fa_c40[MAXN], fa_k1[MAXN];
static long rk_cls[4][MAXROT + 2], rk_viol;
/* K1 of the run of pre[] under policy pol: some single rotation (every frozen k, need chain, base O, as LB4r) reaches a
   state with Lemma K deficit <= 0 (or omega <= 0 without a base of three goods) */
static int k1_run(int pol) {
    phase1(); setup_state(); upg_mode = pol; upgrades(); slots();
    int sr = rot_cap, sd = rot_depth, su = used_rot;
    KMODE = 1; rot_cap = 1; rot_depth = 0;
    int ok = try_rotations();
    KMODE = 0; rot_cap = sr; rot_depth = sd; used_rot = su;
    return ok;
}
static int FULL41 = 0;               /* -E1: mode 41 computes the counts of every first agent (for -D5 dumps) */
static int NONEPOL = 0;              /* -N1: classes K0 and K1 also try the run without upgrades (LB4r's third policy, Lean's
                                        Policy.none); fa_kE then holds the least of the envy-free and no-upgrade deficits */
static void rulef_leaf41(void) {
    int dummy, om, fz;
    KONLY = 1;
    rk_class = 3; rk_choice = -1;
    for (int a = 0; a < n; a++) { fa_kN[a] = fa_kE[a] = DINF; fa_c40[a] = -1; fa_rot[a] = -1; fa_omN[a] = 99; }
    for (int a = 0; a < n && (rk_choice < 0 || FULL41); a++) {
        pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
        deficits(1, &dummy, &dummy, &om, &fz); fa_kN[a] = fa_dK_tmp; fa_omN[a] = om;
        if (fa_kN[a] > 0 || FULL41) { deficits(2, &dummy, &dummy, &om, &fz); fa_kE[a] = fa_dK_tmp; }
        if (NONEPOL && ((fa_kN[a] > 0 && fa_kE[a] > 0) || FULL41)) {
            deficits(0, &dummy, &dummy, &om, &fz); if (fa_dK_tmp < fa_kE[a]) fa_kE[a] = fa_dK_tmp;
        }
        if ((fa_kN[a] <= 0 || fa_kE[a] <= 0) && rk_choice < 0) { rk_choice = a; rk_class = 0; }
    }
    KONLY = 0;
    for (int a = 0; a < n; a++) fa_k1[a] = -1;
    if (rk_choice < 0 || FULL41)
        for (int a = 0; a < n && (rk_choice < 0 || FULL41); a++) {
            pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
            fa_k1[a] = k1_run(1) || k1_run(2) || (NONEPOL && k1_run(0));
            if (fa_k1[a] && rk_choice < 0) { rk_choice = a; rk_class = 1; }
        }
    if (rk_choice < 0 || FULL41)
        for (int a = 0; a < n && (rk_choice < 0 || FULL41); a++) {
            pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
            fa_c40[a] = c40_run();
            if (fa_c40[a] && rk_choice < 0) { rk_choice = a; rk_class = 2; }
        }
    if (rk_choice < 0) rk_class = 3;
    if (rk_class == 3) {
        int b = 0;
        for (int a = 1; a < n; a++) { int ka = fa_kN[a] < fa_kE[a] ? fa_kN[a] : fa_kE[a], kb = fa_kN[b] < fa_kE[b] ? fa_kN[b] : fa_kE[b]; if (ka < kb) b = a; }
        rk_choice = b;
        for (int a = 0; a < n; a++) { pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1; int ok = lb4r(ROT); fa_rot[a] = ok ? used_rot : ROT + 1; }
    }
    pre[0] = rk_choice; npre = 1; TAILRULE = 0; stop_at = -1;
}
static void rulef_stat41(long w, int ok, int rot) {
    int k = ok ? rot : ROT + 1;
    rk_cls[rk_class][k] += w;
    if (rk_class == 0 && k != 0) rk_viol += w;        /* Lemma K promises an owner without rotation */
    if (rk_class >= 1 && rk_class <= 2 && k > 1) rk_viol += w;   /* Lemma K after one rotation, C4^0: at most one */
    if (dumped < DUMPMAX && ((DUMP == 5 && fa_kN[0] > 0 && fa_kE[0] > 0) || (DUMP == 7 && rk_class >= 1))) {
        dumped++;
        printf("IDX w=%ld rot=%d class=%d choice=%d sets=[", w, k, rk_class, rk_choice);
        for (int i = 0; i < n; i++) { printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", gl[i][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
        printf("] vals=[");
        for (int i = 0; i < n; i++) {
            int q = 0; while (!(ts[i] >> q & 1)) q++;
            int t = pidx[i][cp[i]][q];
            printf("["); for (int z = 0; z < d[i]; z++) printf("%d%s", tv[i][t][z], z + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
        }
        printf("] fa=");
        for (int a = 0; a < n; a++) printf("%d:%d,%d,%d,%d,%d%s", a, fa_kN[a], fa_kE[a], fa_c40[a], fa_omN[a], fa_k1[a], a + 1 < n ? ";" : "");
        printf("\n");
    }
    if (DUMP == 1 && dumped < DUMPMAX && rk_class == 3) {
        dumped++;
        printf("OPEN w=%ld rot=%d choice=%d sets=[", w, k, rk_choice);
        for (int i = 0; i < n; i++) { printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", gl[i][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
        printf("] vals=[");
        for (int i = 0; i < n; i++) {
            int q = 0; while (!(ts[i] >> q & 1)) q++;
            int t = pidx[i][cp[i]][q];
            printf("["); for (int z = 0; z < d[i]; z++) printf("%d%s", tv[i][t][z], z + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
        }
        printf("] fa=");
        for (int a = 0; a < n; a++) printf("%d:%d,%d,%d,%d%s", a, fa_rot[a], fa_kN[a], fa_kE[a], fa_c40[a], a + 1 < n ? ";" : "");
        printf("\n");
    }
}
/* mode 42: a static first-agent rule (k4/rulef.md §5.2), and the class of its agent (K0, K1, C40 or none):
   -Q0 the first big-top agent (four goods, top worth more than the next two together) in index order, else agent 0;
   -Q1 the same, else the first agent whose least good is another agent's top, else agent 0;
   -Q2 the first big-top agent, else rule RK (mode 41);
   -Q3 the first big-top agent, else among the agents whose top is another agent's top one with the fewest private
       goods (ties by index), else agent 0;
   -Q4 the big-top agent with the fewest private goods (ties by index), else as -Q3. The class statistics and dumps
       are mode 41's. */
static int bigtop_agent(int a) { return d[a] == 4 && cmpv(a, BIT(ord[a][0]), BIT(ord[a][1]) | BIT(ord[a][2])) > 0; }
static void rulef_leaf42(void) {
    int dummy, om, fz, c = -1;
    if (QRULE == 4) {                /* the big-top agent with the fewest private goods; else -Q3's fallback */
        int bp = 99;
        for (int a = 0; a < n; a++) if (bigtop_agent(a)) {
            gm oth = 0; for (int b = 0; b < n; b++) if (b != a) oth |= R[b];
            int pv = popc(R[a] & ~oth);
            if (pv < bp) { bp = pv; c = a; }
        }
    } else
    for (int a = 0; a < n && c < 0; a++) if (bigtop_agent(a)) c = a;
    if (c < 0 && QRULE == 2) { rulef_leaf41(); return; }
    if (c < 0 && QRULE == 1)
        for (int a = 0; a < n && c < 0; a++) for (int b = 0; b < n; b++) if (b != a && ord[a][d[a] - 1] == ord[b][0]) { c = a; break; }
    if (c < 0 && (QRULE == 3 || QRULE == 4)) {       /* an agent whose top is another agent's top, fewest private goods, ties by index */
        int bp = 99;
        for (int a = 0; a < n; a++) {
            int sh = 0; for (int b = 0; b < n; b++) if (b != a && ord[b][0] == ord[a][0]) sh = 1;
            if (!sh) continue;
            gm oth = 0; for (int b = 0; b < n; b++) if (b != a) oth |= R[b];
            int pv = popc(R[a] & ~oth);
            if (pv < bp) { bp = pv; c = a; }
        }
    }
    if (c < 0) c = 0;
    for (int a = 0; a < n; a++) { fa_kN[a] = fa_kE[a] = DINF; fa_c40[a] = -1; fa_rot[a] = -1; fa_omN[a] = 99; fa_k1[a] = -1; }
    rk_choice = c; rk_class = 3;
    pre[0] = c; npre = 1; TAILRULE = 0; stop_at = -1;
    KONLY = 1;
    deficits(1, &dummy, &dummy, &om, &fz); fa_kN[c] = fa_dK_tmp; fa_omN[c] = om;
    if (fa_kN[c] > 0) { deficits(2, &dummy, &dummy, &om, &fz); fa_kE[c] = fa_dK_tmp; }
    KONLY = 0;
    if (fa_kN[c] <= 0 || fa_kE[c] <= 0) rk_class = 0;
    else {
        pre[0] = c; npre = 1; TAILRULE = 0; stop_at = -1;
        fa_k1[c] = k1_run(1) || k1_run(2);
        if (fa_k1[c]) rk_class = 1;
        else {
            pre[0] = c; npre = 1; TAILRULE = 0; stop_at = -1;
            fa_c40[c] = c40_run();
            if (fa_c40[c]) rk_class = 2;
        }
    }
    pre[0] = c; npre = 1; TAILRULE = 0; stop_at = -1;
}
static void rulef_print41(void) {
    printf("RK41");
    for (int c = 0; c < 4; c++) { printf(" c%d", c); for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rk_cls[c][k]); }
    printf(" viol %ld\n", rk_viol);
    memset(rk_cls, 0, sizeof rk_cls); rk_viol = 0;
}
static void rulef_leaf(void) {       /* fills fa_* for every first agent, then the rule's sequence in pre[] */
    for (int a = 0; a < n; a++) {
        pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
        int ok = lb4r(ROT); fa_rot[a] = ok ? used_rot : ROT + 1;
        fa_cov[a] = covered();
        int fz;
        deficits(1, &fa_dN[a], &fa_hN[a], &fa_omN[a], &fa_fz[a]); fa_uN[a] = fa_dU_tmp; fa_kN[a] = fa_dK_tmp;
        {   /* features of the need-shrinking state */
            int r = -1; for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
            fa_r[a] = r; fa_rfz[a] = r >= 0 ? frz[r] : 0; fa_e4[a] = 0;
            if (r >= 0) { gm W = base[r] | J; for (int x = 0; x < n; x++) if (x != r && d[x] == 4 && !upg[x] && threatened(x, W, base[x])) fa_e4[a]++; }
        }
        deficits(2, &fa_dE[a], &fa_hE[a], &fa_omE[a], &fz); fa_uE[a] = fa_dU_tmp; fa_kE[a] = fa_dK_tmp;
        fa_c40[a] = c40_run();
    }
    rulef_rules();
    pre[0] = fa_choice[QRULE]; npre = 1; TAILRULE = 0; stop_at = -1;
}
static void rulef_stat(long w) {     /* after a completed leaf in mode 40 */
    int mn = ROT + 1, unc = 1;
    for (int a = 0; a < n; a++) { if (fa_rot[a] < mn) mn = fa_rot[a]; if (fa_cov[a]) unc = 0; }
    rs_tot += w; rs_min[mn] += w;
    { int kp = 1; for (int a = 0; a < n; a++) if (fa_kN[a] <= 0 || fa_kE[a] <= 0) kp = 0;
      if (kp) rs_kpos[mn] += w; else rs_kneg[mn] += w; rs_kpos_last = kp; }
    for (int a = 0; a < n; a++) if ((fa_kN[a] <= 0 || fa_kE[a] <= 0) && fa_rot[a] != 0) { rs_kviol += w; break; }
    for (int a = 0; a < n; a++) if (fa_c40[a] && fa_rot[a] > 1) { rs_cviol += w; break; }
    { int kp = 1, cp_ = 0; for (int a = 0; a < n; a++) { if (fa_kN[a] <= 0 || fa_kE[a] <= 0) kp = 0; if (fa_c40[a]) cp_ = 1; }
      if (kp && cp_) rs_c40[mn] += w;
      if (kp && !cp_) rs_open[mn] += w; }
    if (unc) { rs_unc += w; rs_umin[mn] += w; }
    rs_anyabs = 0;
    for (int k = 0; k < NRULES; k++) {
        int c = fa_choice[k];
        if (fa_rot[c] > mn) { rs_rel[k] += w; if (unc) rs_urel[k] += w; }
        if (fa_rot[c] > 1) { rs_abs[k] += w; if (unc) rs_uabs[k] += w; if (k < 19 && k != 1) rs_anyabs = 1; }
    }
    if (DUMP && dumped < DUMPMAX && ((DUMP == 1 && unc) || (DUMP == 2 && mn >= 1) || DUMP == 3 || (DUMP == 4 && rs_kpos_last) || (DUMP == 5 && fa_kN[0] > 0 && fa_kE[0] > 0) || (DUMP == 6 && rs_anyabs))) {
        dumped++;
        printf("DATA w=%ld unc=%d min=%d sets=[", w, unc, mn);
        for (int i = 0; i < n; i++) { printf("["); for (int k = 0; k < d[i]; k++) printf("%d%s", gl[i][k], k + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
        printf("] vals=[");
        for (int i = 0; i < n; i++) {
            int k = 0; while (!(ts[i] >> k & 1)) k++;
            int t = pidx[i][cp[i]][k];
            printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", tv[i][t][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
        }
        printf("] fa=");
        for (int a = 0; a < n; a++) printf("%d:%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d%s", a, fa_rot[a], fa_cov[a], fa_dN[a], fa_dE[a], fa_hN[a], fa_hE[a], fa_omN[a], fa_omE[a], fa_fz[a], fa_e4[a], fa_r[a], fa_uN[a], fa_uE[a], fa_kN[a], fa_kE[a], fa_c40[a], a + 1 < n ? ";" : "");
        printf("\n");
    }
}
static void rulef_print(void) {
    printf("RULEF total %ld allunc %ld min", rs_tot, rs_unc);
    for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rs_min[k]);
    printf(" umin");
    for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rs_umin[k]);
    printf(" kneg"); for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rs_kneg[k]);
    printf(" kpos"); for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rs_kpos[k]);
    printf(" c40"); for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rs_c40[k]);
    printf(" open"); for (int k = 0; k <= ROT + 1; k++) printf(" %ld", rs_open[k]);
    printf(" kviol %ld cviol %ld", rs_kviol, rs_cviol);
    printf(" rel"); for (int k = 0; k < NRULES; k++) printf(" %ld", rs_rel[k]);
    printf(" urel"); for (int k = 0; k < NRULES; k++) printf(" %ld", rs_urel[k]);
    printf(" abs"); for (int k = 0; k < NRULES; k++) printf(" %ld", rs_abs[k]);
    printf(" uabs"); for (int k = 0; k < NRULES; k++) printf(" %ld", rs_uabs[k]);
    printf("\n");
    memset(rs_kpos, 0, sizeof rs_kpos); memset(rs_kneg, 0, sizeof rs_kneg);
    memset(rs_c40, 0, sizeof rs_c40); memset(rs_open, 0, sizeof rs_open); rs_kviol = rs_cviol = 0;
    rs_tot = rs_unc = 0; memset(rs_min, 0, sizeof rs_min); memset(rs_umin, 0, sizeof rs_umin);
    memset(rs_rel, 0, sizeof rs_rel); memset(rs_urel, 0, sizeof rs_urel); memset(rs_abs, 0, sizeof rs_abs); memset(rs_uabs, 0, sizeof rs_uabs);
}

/* ==== mode 43 (k4/lemmam_x.md, workstream proof/k4-lemmam-x): Lemma M by exchange between first agents ====
   For every first agent a (tau_a = (a, then index order)) its class under rule RK's tests: 0 = K0 (Lemma K deficit
   <= 0, or omega <= 0, under need-shrinking or envy-free upgrades; with -N1 also no upgrades), 1 = K1 (one rotation
   of that state reaches Lemma K deficit <= 0), 2 = bad (neither). For every bad a, the roles that the other agents
   play in a's run (policy -U: 2 envy-free, default; 1 need-shrinking), and whether the holders of each role are good
   (class 0 or 1). Statistics, weighted by profiles: has (some agent has the role), anyg (some holder is good), allg
   (every holder is good), firstg (the first holder in index order is good), lastg (the latest-processed holder is
   good). */
#define NR43 26
static const char *RN43[NR43] = {"EF4", "EF3", "ET4", "ET3", "LDR_r", "r", "END_EF", "END_ks", "TOPH_EF", "bigtop",
    "blk_r", "blk_a", "frozen", "free_nottop", "LDR_EF4", "NEEDER_EF", "END_EF4", "TOPH_EF4", "free", "leader",
    "E_any", "NEEDER_EF4", "END_E4all", "TOPH_bigtop", "free_E4holdstop", "LDR_E4"};
static int ROLEPOL = 2;
static int cls43[MAXN];
static long st_pairs, st_prof_bad, st_prof_allbad, st_prof, st_has[NR43], st_anyg[NR43], st_allg[NR43], st_firstg[NR43], st_lastg[NR43];
static long st_byk[MAXN + 1];         /* profiles by number of good first agents */
static int class43(int a) {
    int dummy, om, fz, pols[3] = {1, 2, 0}, npl = NONEPOL ? 3 : 2;
    KONLY = 1;
    for (int q = 0; q < npl; q++) {
        pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
        deficits(pols[q], &dummy, &dummy, &om, &fz);
        if (fa_dK_tmp <= 0) { KONLY = 0; return 0; }
    }
    KONLY = 0;
    for (int q = 0; q < npl; q++) {
        pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
        if (k1_run(pols[q])) return 1;
    }
    return 2;
}
#define NCAND43 8
static const char *CAND43[NCAND43] = {"r", "endEF_early", "endEF_idx", "endEF_maxload", "end_of_minidx_EF", "EF4_minidx", "end_of_earliest_EF", "freenottop_early"};
static int cand43[NCAND43];
static unsigned role43[MAXN];
static int rpos43[MAXN];
static void roles43(int a) {
    pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
    phase1(); setup_state(); upg_mode = ROLEPOL; upgrades(); slots();
    for (int i = 0; i < n; i++) { role43[i] = 0; rpos43[i] = pos[i]; }
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    gm W = base[r] | J;
    int E[MAXN], ks = -1;
    for (int x = 0; x < n; x++) E[x] = x != r && !upg[x] && threatened(x, W, base[x]);
    for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
    for (int x = 0; x < n; x++) {
        unsigned b = 0;
        if (E[x] && frz[x] && d[x] == 4) b |= 1u << 0;
        if (E[x] && frz[x] && d[x] == 3) b |= 1u << 1;
        if (E[x] && !frz[x] && d[x] == 4) b |= 1u << 2;
        if (E[x] && !frz[x] && d[x] == 3) b |= 1u << 3;
        if (x == ks) b |= 1u << 4;
        if (x == r) b |= 1u << 5;
        if (d[x] == 4 && cmpv(x, BIT(ord[x][0]), BIT(ord[x][1]) | BIT(ord[x][2])) > 0) b |= 1u << 9;
        if (blk[x] == blk[r]) b |= 1u << 10;
        if (blk[x] == blk[a]) b |= 1u << 11;
        if (frz[x]) b |= 1u << 12;
        if (!frz[x] && !upg[x] && Y[x] != ord[x][0]) b |= 1u << 13;
        if (!frz[x] && !upg[x]) b |= 1u << 18;
        if (is_leader(x) && blk[x] != blk[a]) b |= 1u << 19;
        if (E[x]) b |= 1u << 20;
        role43[x] |= b;
    }
    for (int x = 0; x < n; x++) {
        if (E[x] && frz[x]) {
            nends = 0; ch2[0] = x; cl2 = 1; chain_ends();
            for (int q = 0; q < nends && q < 64; q++) { role43[ends_[q]] |= 1u << 6; if (d[x] == 4) role43[ends_[q]] |= 1u << 16; }
            for (int y = 0; y < n; y++) if (base[y] >> ord[x][0] & 1) { role43[y] |= 1u << 8; if (d[x] == 4) role43[y] |= 1u << 17; }
            for (int j = 0; j < n; j++) if (j != x && Y[x] >= 0 && (N_[j] >> Y[x] & 1)) { role43[j] |= 1u << 15; if (d[x] == 4) role43[j] |= 1u << 21; }
            if (d[x] == 4) for (int i = 0; i < n; i++) if (blk[i] == blk[x] && is_leader(i)) role43[i] |= 1u << 14;
        }
        if (E[x] && d[x] == 4) {
            if (frz[x]) { nends = 0; ch2[0] = x; cl2 = 1; chain_ends(); for (int q = 0; q < nends && q < 64; q++) role43[ends_[q]] |= 1u << 22; }
            else role43[x] |= 1u << 22;
            for (int i = 0; i < n; i++) if (blk[i] == blk[x] && is_leader(i)) role43[i] |= 1u << 25;
            if (!frz[x] && Y[x] == ord[x][0]) role43[x] |= 1u << 24;
        }
        if (role43[x] >> 9 & 1) for (int y = 0; y < n; y++) if (y != x && (base[y] >> ord[x][0] & 1)) role43[y] |= 1u << 23;
    }
    if (frz[ks] && ks != r) { nends = 0; ch2[0] = ks; cl2 = 1; chain_ends(); for (int q = 0; q < nends && q < 64; q++) role43[ends_[q]] |= 1u << 7; }
    /* candidates for a' (see NCAND43) */
    int endcnt[MAXN] = {0}, efidx = -1, efpos = -1;
    for (int x = 0; x < n; x++) if (E[x] && frz[x]) {
        if (efidx < 0) efidx = x;
        if (efpos < 0 || pos[x] < pos[efpos]) efpos = x;
        nends = 0; ch2[0] = x; cl2 = 1; chain_ends();
        int seen[MAXN] = {0};
        for (int q = 0; q < nends && q < 64; q++) if (!seen[ends_[q]]) { seen[ends_[q]] = 1; endcnt[ends_[q]]++; }
    }
    for (int k = 0; k < NCAND43; k++) cand43[k] = -1;
    cand43[0] = r;
    for (int b = 0; b < n; b++) if (role43[b] >> 6 & 1) {
        if (cand43[1] < 0 || pos[b] < pos[cand43[1]]) cand43[1] = b;
        if (cand43[2] < 0) cand43[2] = b;
        if (cand43[3] < 0 || endcnt[b] > endcnt[cand43[3]] || (endcnt[b] == endcnt[cand43[3]] && pos[b] < pos[cand43[3]])) cand43[3] = b;
    }
    for (int k = 0; k < 2; k++) {
        int x = k == 0 ? efidx : efpos;
        if (x < 0) continue;
        nends = 0; ch2[0] = x; cl2 = 1; chain_ends();
        int best = -1;
        for (int q = 0; q < nends && q < 64; q++) if (best < 0 || pos[ends_[q]] < pos[best]) best = ends_[q];
        cand43[k == 0 ? 4 : 6] = best;
    }
    for (int b = 0; b < n; b++) if (role43[b] & 1u) { cand43[5] = b; break; }
    for (int b = 0; b < n; b++) if ((role43[b] >> 13 & 1) && (cand43[7] < 0 || pos[b] < pos[cand43[7]])) cand43[7] = b;
}
static void print_profile43(const char *tag, long w) {
    printf("%s w=%ld sets=[", tag, w);
    for (int i = 0; i < n; i++) { printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", gl[i][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
    printf("] vals=[");
    for (int i = 0; i < n; i++) {
        int q = 0; while (!(ts[i] >> q & 1)) q++;
        int t = pidx[i][cp[i]][q];
        printf("["); for (int z = 0; z < d[i]; z++) printf("%d%s", tv[i][t][z], z + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
    }
    printf("] cls=");
    for (int a = 0; a < n; a++) printf("%d", cls43[a]);
}
static unsigned roles_all43[MAXN][MAXN];   /* [bad a][agent] */
static int rposall43[MAXN][MAXN];
/* the class of the envy-free run of tau_a (k4/c4.md's cases): 0 omega <= 0; 1 no exposed 4-good agent and not LB+'s
   bad case (Theorem A4); 2 bad case and some need chain k* -> r after whose rotation r is not a 4-good agent exposed
   (Theorem B4); 3 (G2): bad case, r a 4-good agent exposed after the rotation along every chain k* -> r; 4 exactly one
   exposed 4-good agent, frozen; 5 exactly one, free; 6 two or more */
#define NC43 7
static const char *CN43[NC43] = {"om<=0", "A4", "B4", "G2", "E4frz", "E4free", "E4many"};
static int g2_pred_ok;                /* some last chain agent x_{t-1} before r leaves r unexposed */
static void g2_dfs(int r, gm W, int *ch, int len) {
    int x = ch[len - 1];
    for (int j = 0; j < n && !g2_pred_ok; j++) {
        int in = 0; for (int q = 0; q < len; q++) if (ch[q] == j) in = 1;
        if (in || upg[j] || Y[x] < 0 || !(N_[j] >> Y[x] & 1)) continue;
        if (j == r) { if (!(d[r] == 4 && threatened(r, W, BIT(Y[x])))) g2_pred_ok = 1; continue; }
        if (!frz[j]) continue;
        ch[len] = j; g2_dfs(r, W, ch, len + 1);
    }
}
static int runclass43(int a) {
    pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
    phase1(); setup_state(); upg_mode = 2; upgrades();
    int S = slots();
    if (popc(J) - S <= 0) return 0;
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    gm W = base[r] | J;
    int E[MAXN], e4 = 0, e4f = 0;
    for (int x = 0; x < n; x++) { E[x] = x != r && !upg[x] && threatened(x, W, base[x]); if (E[x] && d[x] == 4) { e4++; e4f += frz[x]; } }
    if (e4 >= 2) return 6;
    if (e4 == 1) return e4f ? 4 : 5;
    int ks = -1;
    for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
    int bad = E[ks] && ks != r && frz[ks];
    if (bad) { nends = 0; ch2[0] = ks; cl2 = 1; chain_ends(); for (int q = 0; q < nends && q < 64; q++) if (ends_[q] != r) bad = 0; if (!nends) bad = 0; }
    if (bad) for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (E[x] && E[y] && (R[x] & R[y] & J)) bad = 0;
    if (!bad) return 1;
    int ch[MAXN]; ch[0] = ks; g2_pred_ok = 0; g2_dfs(r, W, ch, 1);
    return g2_pred_ok ? 2 : 3;
}
static int rcls43[MAXN];
static int candall43[MAXN][NCAND43];
static long st_cdir[NCAND43], st_cit[NCAND43], st_cnone[NCAND43];
static long st_cls[NC43], st_chas[NC43][NR43], st_canyg[NC43][NR43], st_callg[NC43][NR43], st_cfirstg[NC43][NR43], st_clastg[NC43][NR43];
static long st_c40viol;
static int omE43[MAXN], omN43[MAXN];
static int omega_pol43(int a, int pol) {
    pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
    phase1(); setup_state(); upg_mode = pol; upgrades();
    int S = slots(); return popc(J) - S;
}
static void leaf43(void) {
    for (int a = 0; a < n; a++) cls43[a] = class43(a);
    int anybad = 0; for (int a = 0; a < n; a++) if (cls43[a] == 2) anybad = 1;
    if (anybad) for (int a = 0; a < n; a++) { omE43[a] = omega_pol43(a, 2); omN43[a] = omega_pol43(a, 1); }
    for (int a = 0; a < n; a++) if (cls43[a] == 2) {
        rcls43[a] = runclass43(a);
        roles43(a); memcpy(roles_all43[a], role43, sizeof role43); memcpy(rposall43[a], rpos43, sizeof rpos43);
        memcpy(candall43[a], cand43, sizeof cand43);
    }
}
static void stat43(long w) {
    int ng = 0, nb = 0;
    for (int a = 0; a < n; a++) { if (cls43[a] <= 1) ng++; else nb++; }
    st_prof += w; st_byk[ng] += w;
    if (nb) st_prof_bad += w;
    if (!ng) { st_prof_allbad += w; print_profile43("ALLBAD", w); printf("\n"); }
    for (int a = 0; a < n; a++) if (cls43[a] == 2) {
        int c = rcls43[a];
        st_pairs += w; st_cls[c] += w;
        if (c <= 2) { st_c40viol += w; print_profile43("C40VIOL", w); printf(" a=%d runclass=%d\n", a, c); }
        for (int k = 0; k < NR43; k++) {
            int has = 0, any = 0, all = 1, first = -1, last = -1;
            for (int b = 0; b < n; b++) if (roles_all43[a][b] >> k & 1) {
                has = 1; int g = cls43[b] <= 1;
                if (g) any = 1; else all = 0;
                if (first < 0 || rposall43[a][b] < rposall43[a][first]) first = b;   /* earliest processed */
                if (last < 0 || rposall43[a][b] > rposall43[a][last]) last = b;
            }
            if (!has) continue;
            st_has[k] += w; if (any) st_anyg[k] += w; if (all) st_allg[k] += w;
            if (cls43[first] <= 1) st_firstg[k] += w;
            if (cls43[last] <= 1) st_lastg[k] += w;
            st_chas[c][k] += w; if (any) st_canyg[c][k] += w; if (all) st_callg[c][k] += w;
            if (cls43[first] <= 1) st_cfirstg[c][k] += w;
            if (cls43[last] <= 1) st_clastg[c][k] += w;
        }
        for (int k = 0; k < NCAND43; k++) {
            int b = candall43[a][k];
            if (b < 0) { st_cnone[k] += w; continue; }
            if (cls43[b] <= 1) st_cdir[k] += w;
            int cur = a, steps = 0;      /* iterate the successor map until a good agent, a dead end or n steps */
            while (steps <= n && cls43[cur] == 2 && candall43[cur][k] >= 0) { cur = candall43[cur][k]; steps++; }
            if (cls43[cur] <= 1) st_cit[k] += w;
        }
        if (DUMP == 43 && dumped < DUMPMAX) {
            dumped++;
            print_profile43("BAD", w);
            printf(" a=%d runclass=%d omE=", a, c);
            for (int b = 0; b < n; b++) printf("%d%s", omE43[b], b + 1 < n ? "," : "");
            printf(" cand=");
            for (int k = 0; k < NCAND43; k++) printf("%d%s", candall43[a][k], k + 1 < NCAND43 ? "," : "");
            printf(" omN=");
            for (int b = 0; b < n; b++) printf("%d%s", omN43[b], b + 1 < n ? "," : "");
            printf(" roles=");
            for (int b = 0; b < n; b++) printf("%x%s", roles_all43[a][b], b + 1 < n ? "," : "");
            printf("\n");
        }
    }
}
static void print43(void) {
    printf("LMX prof %ld prof_bad %ld prof_allbad %ld pairs %ld c40viol %ld byk", st_prof, st_prof_bad, st_prof_allbad, st_pairs, st_c40viol);
    for (int k = 0; k <= 4; k++) printf(" %ld", k <= n ? st_byk[k] : 0L);
    printf(" cls"); for (int c = 0; c < NC43; c++) printf(" %ld", st_cls[c]);
    printf("\n");
    for (int k = 0; k < NR43; k++)
        printf("LMXR %s has %ld anyg %ld allg %ld firstg %ld lastg %ld\n", RN43[k], st_has[k], st_anyg[k], st_allg[k], st_firstg[k], st_lastg[k]);
    for (int k = 0; k < NCAND43; k++) printf("LMXC %s direct %ld iterated %ld none %ld\n", CAND43[k], st_cdir[k], st_cit[k], st_cnone[k]);
    memset(st_cdir, 0, sizeof st_cdir); memset(st_cit, 0, sizeof st_cit); memset(st_cnone, 0, sizeof st_cnone);
    for (int c = 0; c < NC43; c++) if (st_cls[c]) for (int k = 0; k < NR43; k++)
        printf("LMXR %s@%s has %ld anyg %ld allg %ld firstg %ld lastg %ld\n", RN43[k], CN43[c], st_chas[c][k], st_canyg[c][k], st_callg[c][k], st_cfirstg[c][k], st_clastg[c][k]);
    st_prof = st_prof_bad = st_prof_allbad = st_pairs = st_c40viol = 0;
    memset(st_byk, 0, sizeof st_byk); memset(st_has, 0, sizeof st_has); memset(st_anyg, 0, sizeof st_anyg);
    memset(st_allg, 0, sizeof st_allg); memset(st_firstg, 0, sizeof st_firstg); memset(st_lastg, 0, sizeof st_lastg);
    memset(st_cls, 0, sizeof st_cls); memset(st_chas, 0, sizeof st_chas); memset(st_canyg, 0, sizeof st_canyg);
    memset(st_callg, 0, sizeof st_callg); memset(st_cfirstg, 0, sizeof st_cfirstg); memset(st_clastg, 0, sizeof st_clastg);
    fflush(stdout);
}
/* ==== mode 44 (k4/lemmam_x.md §6, adaptive Lemma M): choose the inserted agent at every insertion step ====
   A run is built block by block. At each insertion step every unprocessed agent c is tried: the block it starts is
   simulated (c inserted, then P-steps by LB's key until no unprocessed agent has lost a good) and its *block count*
   delta(c) is computed (below); the agent with the least delta is inserted (ties: least index). The block count is
   pessimistic, computed when the block ends, from the block alone and the set G of goods still unpicked:
     frozen: an agent of the block whose pick is needed by another agent of the block (no upgrades; nobody outside
             the block can need it, (B2));
     X:      the frozen agents x of the block threatened by G with their pick (the final W is a subset of G);
     rho(x): the least |D|, D a set of goods of G valued by x, with x not threatened by G - D;
     D(x):   the ends of need chains from x inside the block that are not threatened by G with their pick, and, in the
             last block, other than its last-processed agent r (the owner);
     delta:  max over nonempty X' of X of (sum of rho(x) - |union of D(x)|), at least 0 (Hall's condition, Lemma 3).
   At the end the run's sequence tau is evaluated: the least d <= -r such that some policy (none, need-shrinking,
   envy-free) and at most d nested rotations reach Lemma K deficit <= 0 (or omega <= 0), else -r + 1. Statistics
   (ADP lines): profiles, how many had every block with delta = 0, the histogram of d, and d by whether every block had
   delta = 0 (soundness of the block count: those should have d = 0 under the no-upgrade policy). -D44 prints the
   profiles with d >= 1 (ADPBAD lines, with tau and the deltas). */
static int b_done[MAXN], b_Y[MAXN], b_pos[MAXN], b_blk[MAXN], b_step;
static gm b_G;
static void bsim_block(int c, int bid) {
    int i = c;
    for (;;) {
        b_Y[i] = favr(i, b_G); if (b_Y[i] >= 0) b_G &= ~BIT(b_Y[i]);
        b_done[i] = 1; b_pos[i] = b_step++; b_blk[i] = bid;
        i = pstep(b_G, b_done); if (i < 0) break;
    }
}
static int bc_mem[MAXN], bc_nm, bc_fz[MAXN], bc_ex[MAXN], bc_rho[MAXN], bc_ch[MAXN], bc_cl, bc_last;
static gm bc_N[MAXN], bc_ends;
static void bc_dfs(void) {
    int x = bc_ch[bc_cl - 1];
    if (bc_cl > 1 && !bc_fz[x]) { if (!bc_ex[x] && x != bc_last) bc_ends |= BIT(x); return; }
    for (int q = 0; q < bc_nm; q++) {
        int y = bc_mem[q], in = 0;
        for (int k = 0; k < bc_cl; k++) if (bc_ch[k] == y) in = 1;
        if (in || b_Y[x] < 0 || !(bc_N[y] >> b_Y[x] & 1)) continue;
        bc_ch[bc_cl++] = y; bc_dfs(); bc_cl--;
    }
}
static int block_count(int bid, int last) {
    bc_nm = 0;
    for (int i = 0; i < n; i++) if (b_done[i] && b_blk[i] == bid) bc_mem[bc_nm++] = i;
    for (int q = 0; q < bc_nm; q++) { int x = bc_mem[q]; bc_N[x] = b_Y[x] >= 0 ? above(x, b_Y[x]) : R[x]; }
    bc_last = -1;
    if (last) for (int q = 0; q < bc_nm; q++) if (bc_last < 0 || b_pos[bc_mem[q]] > b_pos[bc_last]) bc_last = bc_mem[q];
    int X[MAXN], nx = 0;
    for (int q = 0; q < bc_nm; q++) {
        int x = bc_mem[q];
        bc_fz[x] = 0;
        if (b_Y[x] >= 0) for (int p = 0; p < bc_nm; p++) if (bc_mem[p] != x && (bc_N[bc_mem[p]] >> b_Y[x] & 1)) bc_fz[x] = 1;
        bc_ex[x] = b_Y[x] >= 0 && x != bc_last && threatened(x, b_G, BIT(b_Y[x]));
    }
    gm endsX[MAXN];
    for (int q = 0; q < bc_nm; q++) {
        int x = bc_mem[q];
        if (!bc_fz[x] || !bc_ex[x]) continue;
        gm cand = b_G & R[x]; int best = 99;
        for (gm D = cand;; D = (D - 1) & cand) {
            if (popc(D) < best && !threatened(x, b_G & ~D, BIT(b_Y[x]))) best = popc(D);
            if (!D) break;
        }
        bc_rho[x] = best;
        bc_ends = 0; bc_ch[0] = x; bc_cl = 1; bc_dfs();
        endsX[nx] = bc_ends; X[nx++] = x;
    }
    int worst = 0;
    if (nx > 20) nx = 20;            /* (never reached on the instances run) */
    for (long s = 1; s < (1L << nx); s++) {
        int sum = 0; gm U = 0;
        for (int k = 0; k < nx; k++) if (s >> k & 1) { sum += bc_rho[X[k]]; U |= endsX[k]; }
        int v = sum - popc(U);
        if (v > worst) worst = v;
    }
    return worst;
}
/* the least d <= -r such that some policy (none, need-shrinking, envy-free) and at most d nested rotations (every
   frozen k, need chain, base O, as LB4r's R(d)) reach Lemma K deficit <= 0 (or omega <= 0) from Phase 1(tau); -r + 1 if
   none (k4/lemmam_x.md §6) */
static int least_rot_seq(const int *tau, int nt) {
    int pols[3] = {0, 1, 2}, dummy, om, fz, best = ROT + 1;
    KONLY = 1;
    for (int q = 0; q < 3 && best > 0; q++) {
        memcpy(pre, tau, sizeof(int) * nt); npre = nt; TAILRULE = 0; stop_at = -1;
        deficits(pols[q], &dummy, &dummy, &om, &fz);
        if (fa_dK_tmp <= 0) best = 0;
    }
    KONLY = 0;
    for (int dd = 1; dd <= ROT && best > dd; dd++)
        for (int q = 0; q < 3 && best > dd; q++) {
            memcpy(pre, tau, sizeof(int) * nt); npre = nt; TAILRULE = 0; stop_at = -1;
            phase1(); setup_state(); upg_mode = pols[q]; upgrades(); slots();
            int sr = rot_cap, sdp = rot_depth, su = used_rot;
            KMODE = 1; rot_cap = dd; rot_depth = 0;
            if (try_rotations()) best = dd;
            KMODE = 0; rot_cap = sr; rot_depth = sdp; used_rot = su;
        }
    return best;
}
static int adp_tau[MAXN], adp_ntau, adp_delta[MAXN], adp_d, adp_all0, adp_lastdelta, adp_nonlast;
static void adaptive44(void) {
    for (int i = 0; i < n; i++) { b_done[i] = 0; b_Y[i] = -1; }
    b_G = ALLG; b_step = 0; adp_ntau = 0; adp_all0 = 1; adp_nonlast = 0;
    int sd[MAXN], sY[MAXN], sp[MAXN], sb[MAXN], sstep; gm sG;
    for (int bid = 0;; bid++) {
        int any = 0; for (int i = 0; i < n; i++) if (!b_done[i]) any = 1;
        if (!any) break;
        memcpy(sd, b_done, sizeof sd); memcpy(sY, b_Y, sizeof sY); memcpy(sp, b_pos, sizeof sp); memcpy(sb, b_blk, sizeof sb);
        sG = b_G; sstep = b_step;
        int bestc = -1, bestd = 1 << 20;
        for (int c = 0; c < n; c++) if (!sd[c]) {
            memcpy(b_done, sd, sizeof sd); memcpy(b_Y, sY, sizeof sY); memcpy(b_pos, sp, sizeof sp); memcpy(b_blk, sb, sizeof sb);
            b_G = sG; b_step = sstep;
            bsim_block(c, bid);
            int last = 1; for (int i = 0; i < n; i++) if (!b_done[i]) last = 0;
            int dl = block_count(bid, last);
            if (dl < bestd) { bestd = dl; bestc = c; }
        }
        memcpy(b_done, sd, sizeof sd); memcpy(b_Y, sY, sizeof sY); memcpy(b_pos, sp, sizeof sp); memcpy(b_blk, sb, sizeof sb);
        b_G = sG; b_step = sstep;
        bsim_block(bestc, bid);
        adp_delta[adp_ntau] = bestd; adp_tau[adp_ntau++] = bestc;
        if (bestd > 0) adp_all0 = 0;
        adp_lastdelta = bestd;
        { int lc = 1; for (int i = 0; i < n; i++) if (!b_done[i]) lc = 0; if (bestd > 0 && !lc) adp_nonlast++; }
    }
    adp_d = least_rot_seq(adp_tau, adp_ntau);
}
static long adp_prof, adp_all0cnt, adp_hist[MAXROT + 2], adp_hist0[MAXROT + 2], adp_lastd1, adp_nlcnt, adp_nlhist[MAXROT + 2];
static void stat44(long w) {
    adp_prof += w; if (adp_all0) adp_all0cnt += w;
    adp_hist[adp_d] += w; if (adp_all0) adp_hist0[adp_d] += w;
    if (adp_d >= 1 && adp_lastdelta == 1) adp_lastd1 += w;
    if (adp_nonlast) { adp_nlcnt += w; adp_nlhist[adp_d] += w; }
    if (DUMP == 44 && adp_d >= 1 && dumped < DUMPMAX) {
        dumped++;
        printf("ADPBAD w=%ld d=%d sets=[", w, adp_d);
        for (int i = 0; i < n; i++) { printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", gl[i][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
        printf("] vals=[");
        for (int i = 0; i < n; i++) {
            int q = 0; while (!(ts[i] >> q & 1)) q++;
            int t = pidx[i][cp[i]][q];
            printf("["); for (int z = 0; z < d[i]; z++) printf("%d%s", tv[i][t][z], z + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
        }
        printf("] tau=");
        for (int k = 0; k < adp_ntau; k++) printf("%d%s", adp_tau[k], k + 1 < adp_ntau ? "," : "");
        printf(" deltas=");
        for (int k = 0; k < adp_ntau; k++) printf("%d%s", adp_delta[k], k + 1 < adp_ntau ? "," : "");
        printf("\n");
    }
}
static void print44(void) {
    printf("ADP prof %ld all_blocks_delta0 %ld hist", adp_prof, adp_all0cnt);
    for (int k = 0; k <= ROT + 1; k++) printf(" %ld", adp_hist[k]);
    printf(" hist_all0");
    for (int k = 0; k <= ROT + 1; k++) printf(" %ld", adp_hist0[k]);
    printf(" bad_with_last_delta1 %ld nonlast_positive %ld nonlast_hist", adp_lastd1, adp_nlcnt);
    for (int k = 0; k <= ROT + 1; k++) printf(" %ld", adp_nlhist[k]);
    printf("\n");
    adp_prof = adp_all0cnt = adp_lastd1 = adp_nlcnt = 0; memset(adp_nlhist, 0, sizeof adp_nlhist); memset(adp_hist, 0, sizeof adp_hist); memset(adp_hist0, 0, sizeof adp_hist0);
    fflush(stdout);
}

/* ==== mode 45 (k4/lemmam_x.md §6, the rotation bound): for every first agent a, the least d of least_rot_seq on
   tau_a = (a, then index order); FA lines list them, and the statistics count the profiles by the least d over the
   first agents (the rule-F bound: some first agent with at most d rotations) ==== */
static int fa45[MAXN], min45;
static long hist45[MAXROT + 2];
static void leaf45(void) {
    min45 = ROT + 1;
    for (int a = 0; a < n; a++) { int t[1] = {a}; fa45[a] = least_rot_seq(t, 1); if (fa45[a] < min45) min45 = fa45[a]; }
}
static void stat45(long w) {
    hist45[min45] += w;
    if (DUMP == 45 && dumped < DUMPMAX) {
        dumped++;
        printf("FA w=%ld min=%d d=", w, min45);
        for (int a = 0; a < n; a++) printf("%d%s", fa45[a], a + 1 < n ? "," : "");
        printf("\n");
    }
}
static void print45(void) {
    printf("FA45 hist"); for (int k = 0; k <= ROT + 1; k++) printf(" %ld", hist45[k]); printf("\n");
    memset(hist45, 0, sizeof hist45); fflush(stdout);
}

/* the whole construction for the current profile: tau by the rule (or tree / random choices), then LB4r(tau) */
static int construct(void) {
    if (INS == 1 || INS == 10) {     /* tree or random: Phase 1 draws/extends choice[]; fix tau from it */
        npre = 0; stop_at = -1; phase1();
        memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
    } else if (INS == 2) {           /* -i2: the fewest rotations over every insertion sequence (bound outermost) */
        for (int c = 0; c <= ROT; c++) {
            nchoice = 0;
            for (;;) {
                INS = 1; npre = 0; stop_at = -1; phase1(); INS = 2;
                memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
                if (lb4r(c)) return 1;
                int j = nins - 1;
                while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
                if (j < 0) break;
                choice[j]++; nchoice = j + 1;
            }
        }
        return 0;
    } else if (ARULE >= 20 && ARULE <= 22) {
        if (COVZ == 2) cov_all();    /* before the family, which leaves pre[] at its run for lb4r below */
        last_uncov = !cover_family(ARULE);
        if (!last_uncov && COVZ == 1) cov_verify();
        return lb4r(ROT);
    } else if (ARULE == 24) {
        int b = minmax_first(), mx = b / 64;
        pre[0] = b % 64; npre = 1; TAILRULE = 0; phase1(); memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
        if (mx > ROT) return 0;
        int ok = lb4r(ROT); used_rot = mx; return ok;
    } else if (ARULE == 28 || ARULE == 29) {   /* the first agents whose run leaves the fewest frozen agents */
        int fz[MAXN], best = 1 << 20, fseq[MAXN][MAXN], fnn[MAXN];
        for (int a = 0; a < n; a++) {   /* tau_a = (a, then index order); frozen after need-shrinking upgrades */
            pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1; phase1();
            memcpy(fseq[a], ins_seq, sizeof(int) * nins); fnn[a] = nins;
            setup_state(); upg_mode = 1; upgrades(); slots();
            fz[a] = 0; for (int i = 0; i < n; i++) fz[a] += frz[i];
            if (fz[a] < best) best = fz[a];
        }
        if (ARULE == 28) {               /* 28: the first of them (index order) */
            for (int a = 0; a < n; a++) if (fz[a] == best) { memcpy(pre, fseq[a], sizeof(int) * fnn[a]); npre = fnn[a]; break; }
            return lb4r(ROT);
        }
        for (int c = 0; c <= ROT; c++) for (int a = 0; a < n; a++) if (fz[a] == best) {   /* 29: rule 16 among them */
            memcpy(pre, fseq[a], sizeof(int) * fnn[a]); npre = fnn[a];
            if (lb4r(c)) return 1;
        }
        for (int a = 0; a < n; a++) if (fz[a] == best) { memcpy(pre, fseq[a], sizeof(int) * fnn[a]); npre = fnn[a]; break; }
        return 0;
    } else if (ARULE == 42) {        /* a static first-agent rule (k4/rulef.md §5.2) */
        rulef_leaf42();
        return lb4r(ROT);
    } else if (ARULE == 43) {        /* Lemma M by exchange (k4/lemmam_x.md): classes and roles of every first agent */
        leaf43();
        return 0;
    } else if (ARULE == 44) {        /* adaptive insertion by the block count (k4/lemmam_x.md §6) */
        adaptive44();
        return 0;
    } else if (ARULE == 45) {        /* every first agent: least rotations with Lemma K (k4/lemmam_x.md §6) */
        leaf45();
        return 0;
    } else if (ARULE == 41) {        /* rule RK (k4/rulef.md), fast */
        rulef_leaf41();
        return lb4r(ROT);
    } else if (ARULE == 40) {        /* rule F data (k4/rulef.md): every first agent, then the rule -Q */
        rulef_leaf();
        return lb4r(ROT);
    } else if (ARULE == 26) {        /* -i2 (every sequence), with the coverage of every sequence recorded (statistics) */
        last_uncov = !cover_family(22);
        INS = 2; int ok = construct(); INS = 0;
        return ok;
    } else if (ARULE == 23) {        /* rule 16, with the coverage of every sequence recorded (statistics, -A23) */
        last_uncov = !cover_family(22);
        if (!deepen_family(16)) return 0;
        return lb4r(ROT);
    } else if (ARULE == 15 || ARULE == 16) {
        if (!deepen_family(ARULE)) return 0;
        return lb4r(ROT);             /* re-run on the sequence found: the same fewest rotations, and own[] */
    } else choose_seq(ARULE);
    if (LSR) { if (!local_search()) return 0; return lb4r(ROT); }
    return lb4r(ROT);
}

/* raw EFX0 check of own[] for every type in every agent's set; D2 shape */
static int rawcheck(void) {
    int sz[MAXN] = {0}, big = 0;
    for (int g = 0; g < m; g++) { if (own[g] < 0 || own[g] >= n) return 0; sz[own[g]]++; }
    for (int i = 0; i < n; i++) if (sz[i] > 2) big++;
    lastbig = 0; for (int i = 0; i < n; i++) if (sz[i] > 2) lastbig = sz[i];
    if (big > 1) return 0;
    for (int i = 0; i < n; i++) for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
        int t = pidx[i][cp[i]][k], vo = 0;
        int v[MAXM]; for (int g = 0; g < m; g++) v[g] = 0;
        for (int q = 0; q < d[i]; q++) v[gl[i][q]] = tv[i][t][q];
        for (int g = 0; g < m; g++) if (own[g] == i) vo += v[g];
        for (int j = 0; j < n; j++) if (j != i) {
            int s = 0, mn = 1 << 30, cnt = 0;
            for (int g = 0; g < m; g++) if (own[g] == j) { s += v[g]; if (v[g] < mn) mn = v[g]; cnt++; }
            if (cnt && vo < s - mn) return 0;
        }
    }
    return 1;
}

static long weight(void) { long w = 1; for (int i = 0; i < n; i++) w *= popc(ts[i]); return w; }

static void report(const char *what) {
    stop_at = -1; phase1();          /* the Phase 1 state of tau (picks, order, blocks), not the state after rotations */
    printf("%s n=%d m=%d sets=[", what, n, m);
    for (int i = 0; i < n; i++) { printf("["); for (int k = 0; k < d[i]; k++) printf("%d%s", gl[i][k], k + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
    printf("] vals=[");
    for (int i = 0; i < n; i++) {
        int k = 0; while (!(ts[i] >> k & 1)) k++;
        int t = pidx[i][cp[i]][k];
        printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", tv[i][t][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
    }
    printf("] tau=");
    for (int q = 0; q < npre; q++) printf("%d%s", pre[q], q + 1 < npre ? "," : "");
    printf(" order=");
    for (int p = 0; p < n; p++) for (int i = 0; i < n; i++) if (pos[i] == p) printf("%d ", i);
    printf(" picks=");
    for (int i = 0; i < n; i++) printf("%d%s", Y[i], i + 1 < n ? "," : "");
    printf(" blocks=");
    for (int i = 0; i < n; i++) printf("%d%s", blk[i], i + 1 < n ? "," : "");
    printf("\n");
    fflush(stdout);
}

/* one run of the construction on the current type sets; returns 1 if a comparison split them. The mode globals that
   construct() overrides temporarily (INS in -i2 and rules 22-24, UPG and OWNW in cov_verify, TAILRULE, stop_at) are
   restored when a split jumps out of it. */
static int leaf_INS, leaf_UPG, leaf_OWNW;
static int run_leaf(int *ok) {
    leaf_INS = INS; leaf_UPG = UPG; leaf_OWNW = OWNW;
    if (setjmp(env)) { stop_at = -1; TAILRULE = 0; INS = leaf_INS; UPG = leaf_UPG; OWNW = leaf_OWNW; return 1; }
    rot_depth = 0; last_uncov = 0; leaf_viol = leaf_chk = 0;
    *ok = construct();
    covviol += leaf_viol; covchk += leaf_chk;
    return 0;
}

/* set the rankings for ranking indices rk[] */
static void set_ranks(const int *rk) {
    for (int i = 0; i < n; i++) { cp[i] = rk[i]; for (int r = 0; r < d[i]; r++) ord[i][r] = gl[i][pr[i][cp[i]][r]]; }
}
/* set singleton type sets for type indices ty[] */
static void set_types(const int *ty) {
    for (int i = 0; i < n; i++) {
        int t = ty[i], p, kk = 0;
        for (p = 0; p < np[i]; p++) { for (kk = 0; kk < pcnt[i][p]; kk++) if (pidx[i][p][kk] == t) break; if (kk < pcnt[i][p]) break; }
        cp[i] = p; ts[i] = (u128)1 << kk;
        for (int r = 0; r < d[i]; r++) ord[i][r] = gl[i][pr[i][cp[i]][r]];
    }
}

static long hist_rot[MAXROT + 2], hist_pol[3], ustat[2][3][MAXROT + 1][4];   /* -A23: [uncovered][policy][rotations][status] */

/* -M mining on one profile (singleton type sets): every insertion sequence, fewest rotations of each; prints the
   profile's summary line "MINE best=.. index=.. frac0=.." and, per first-step candidate, the fewest rotations over
   the sequences starting with it */
static void mine(void) {
    nchoice = 0; INS = 1;
    int bestr = 99, nseq = 0, nzero = 0, idxr = -1, firstbest[MAXN];
    for (int i = 0; i < n; i++) firstbest[i] = 99;
    for (;;) {
        int ok; if (run_leaf(&ok)) { fprintf(stderr, "split with singleton type sets\n"); exit(1); }
        int r = ok ? used_rot : ROT + 1;
        if (ok && !rawcheck()) { report("RAWFAIL"); exit(2); }
        if (nseq == 0) idxr = r;
        nseq++; if (r == 0) nzero++;
        if (r < bestr) bestr = r;
        if (r < firstbest[pre[0]]) firstbest[pre[0]] = r;
        int j = nins - 1;
        while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
        if (j < 0) break;
        choice[j]++; nchoice = j + 1;
    }
    INS = 0;
    printf("MINE best=%d index=%d seqs=%d zero=%d first:", bestr, idxr, nseq, nzero);
    for (int i = 0; i < n; i++) if (firstbest[i] < 99) printf(" %d:%d", i, firstbest[i]);
    printf("\n");
}

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strncmp(argv[a], "-o", 2)) OWN = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-i", 2)) INS = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-f", 2)) MAXF = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-u", 2)) UPG = atoi(argv[a] + 2);
        else if (!strcmp(argv[a], "-b")) BRUTE = 1;
        else if (!strcmp(argv[a], "-v")) VERB = 1;
        else if (!strcmp(argv[a], "-vv")) VERB = 2;
        else if (!strcmp(argv[a], "-M")) MINE = 1;
        else if (!strncmp(argv[a], "-r", 2)) ROT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-R", 2)) ROLLROT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-A", 2)) ARULE = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-L", 2)) LSR = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-K", 2)) DEEP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-P", 2)) PRUNE = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-C", 2)) COVT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-Z", 2)) COVZ = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-T", 2)) TAU = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-S", 2)) SAMPLE = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-H", 2)) HILL = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-X", 2)) rng_x ^= (uint64_t)atol(argv[a] + 2) * 0x9E3779B97F4A7C15ull;
        else if (!strncmp(argv[a], "-w", 2)) OWNW = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-Q", 2)) QRULE = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-Y", 2)) XKEEP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-E", 2)) FULL41 = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-N", 2)) NONEPOL = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-D", 2)) DUMP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-c", 2)) CHUP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-U", 2)) ROLEPOL = atoi(argv[a] + 2);
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 1; }
    }
    if (ROT < 0 || ROT > MAXROT) { fprintf(stderr, "-r: the rotation bound must be 0 .. %d\n", MAXROT); return 1; }
    while (scanf("%d %d", &n, &m) == 2) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "n = %d or m = %d too large\n", n, m); return 1; }
        ALLG = m == 128 ? ~(gm)0 : (BIT(m) - 1);
        for (int i = 0; i < n; i++) {
            if (scanf("%d", &d[i]) != 1) return 3;
            R[i] = 0;
            for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 3; R[i] |= BIT(gl[i][k]); }
            if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) return 3;
            for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 3;
            /* group by tie-broken ranking: decreasing value, ties by position in the list */
            np[i] = 0;
            for (int t = 0; t < nt[i]; t++) {
                int o[4]; for (int k = 0; k < d[i]; k++) o[k] = k;
                for (int a = 0; a < d[i]; a++) for (int b = a + 1; b < d[i]; b++)
                    if (tv[i][t][o[b]] > tv[i][t][o[a]] || (tv[i][t][o[b]] == tv[i][t][o[a]] && o[b] < o[a])) { int z = o[a]; o[a] = o[b]; o[b] = z; }
                int p;
                for (p = 0; p < np[i]; p++) if (!memcmp(pr[i][p], o, sizeof(int) * d[i])) break;
                if (p == np[i]) { memcpy(pr[i][p], o, sizeof(int) * d[i]); pcnt[i][p] = 0; np[i]++; }
                if (pcnt[i][p] >= MAXG) { fprintf(stderr, "group too large\n"); return 1; }
                pidx[i][p][pcnt[i][p]++] = t;
            }
        }
        long total = 0, leaves = 0, fails = 0, rawf = 0, runs = 0, shown = 0;
        memset(hist_rot, 0, sizeof hist_rot); memset(hist_pol, 0, sizeof hist_pol);
        if (TAU > 0 || MINE) {           /* single profile: one type per agent */
            int ty[MAXN];
            for (int i = 0; i < n; i++) { if (nt[i] != 1) { fprintf(stderr, "single-profile mode needs one type per agent\n"); return 1; } ty[i] = 0; }
            set_types(ty);
            if (MINE) { mine(); continue; }
            long nsm = INS == 10 ? TAU : 1;
            for (long smp = 0; smp < nsm; smp++) {
                nchoice = 0; owner_tests = 0; effort = 0;
                int ok; if (run_leaf(&ok)) { fprintf(stderr, "split with a single type per agent\n"); return 1; }
                int k = ok ? used_rot : ROT + 1;
                if (ok && !rawcheck()) { report("RAWFAIL"); return 2; }
                if (ARULE == 40) rulef_stat(1);
                if (ARULE == 41 || ARULE == 42) rulef_stat41(1, ok, used_rot);
                if (ARULE == 43) { stat43(1); leaves++; total++; continue; }
                if (ARULE == 44) { stat44(1); leaves++; total++; continue; }
                if (ARULE == 45) { stat45(1); leaves++; total++; continue; }
                hist_rot[k]++; if (ok) hist_pol[used_pol]++;
                if (VERB || !ok) { char lab[64]; snprintf(lab, sizeof lab, ok ? "RUN rot=%d pol=%d" : "RUN fail", k, used_pol); report(lab); }
                if (INS == 10) printf("sample %ld: %s %d\n", smp, ok ? "rot" : "fail", k);
                fflush(stdout);
            }
            printf("single rule=%d samples=%ld", ARULE, nsm);
            for (int k = 0; k <= ROT; k++) printf(" rot%d=%ld", k, hist_rot[k]);
            printf(" fail=%ld uncov=%d\n", hist_rot[ROT + 1], last_uncov); fflush(stdout);
            if (ARULE == 40) rulef_print();
            if (ARULE == 41 || ARULE == 42) rulef_print41();
            if (ARULE == 43) print43();
            if (ARULE == 44) print44();
            if (ARULE == 45) print45();
            continue;
        }
        if (SAMPLE > 0 || HILL > 0) {    /* random profiles (-S), or hill-climbing toward hard profiles (-H) */
            uint64_t x = 88172645463325252ull ^ (uint64_t)(n * 131 + m) ^ rng_x;
            for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) x = x * 6364136223846793005ull + (uint64_t)(gl[i][k] + 17 * k + 1);
            int ty[MAXN]; long cur = -1, top = -1;
            long nsteps = SAMPLE > 0 ? SAMPLE : HILL;
            for (long sidx = 0; sidx < nsteps; sidx++) {
                int restart = SAMPLE > 0 || sidx % 500 == 0, mi = -1, mold = 0;
                if (restart) for (int i = 0; i < n; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; ty[i] = (int)(x % (uint64_t)nt[i]); }
                else {                   /* mutate one agent's type */
                    x ^= x << 13; x ^= x >> 7; x ^= x << 17; mi = (int)(x % (uint64_t)n); mold = ty[mi];
                    x ^= x << 13; x ^= x >> 7; x ^= x << 17; ty[mi] = (int)(x % (uint64_t)nt[mi]);
                }
                set_types(ty);
                nchoice = 0; effort = 0;
                int ok; if (run_leaf(&ok)) { fprintf(stderr, "split with singleton type sets\n"); return 1; }
                runs++; leaves++; total++;
                if (ARULE == 40) rulef_stat(1);
                if (ARULE == 41 || ARULE == 42) rulef_stat41(1, ok, used_rot);
                if (ARULE == 43) {
                    stat43(1);
                    if (HILL > 0) {      /* climb toward bad first agents: score (bad agents, agents not in K0) */
                        long sc = 0; for (int q = 0; q < n; q++) sc += (cls43[q] == 2) * 1000 + (cls43[q] >= 1);
                        if (!restart && sc < cur) ty[mi] = mold; else cur = sc;
                    }
                    continue;
                }
                if (ARULE == 44) {
                    stat44(1);
                    if (HILL > 0) {      /* climb toward profiles the adaptive rule certifies only with rotations */
                        long sc = adp_d * 100 + (adp_all0 ? 0 : 1);
                        if (!restart && sc < cur) ty[mi] = mold; else cur = sc;
                    }
                    continue;
                }
                if (ARULE == 45) { stat45(1); continue; }
                if (last_uncov) { uncov++; if (DEEP && shown < MAXF) { report("UNCOV"); shown++; } }
                if (!ok) { fails++; hist_rot[ROT + 1]++; if (shown < MAXF) { report("FAIL"); shown++; } if (HILL > 0) break; continue; }
                if (!rawcheck()) { rawf++; if (shown < MAXF) { report("RAWFAIL"); shown++; } continue; }
                hist_rot[used_rot]++; hist_pol[used_pol]++;
                ustat[last_uncov][used_pol][used_rot][last_status]++;
                if (DEEP && used_rot >= DEEP && shown < MAXF) { char lab[48]; snprintf(lab, sizeof lab, "DEEP r=%d p=%d", used_rot, used_pol); report(lab); shown++; }
                long sc = used_rot * 100000000L + used_pol * 1000000L + (effort < 999999 ? effort : 999999);
                if (sc > top) { top = sc; if (used_rot >= 1 && VERB) { char lab[64]; snprintf(lab, sizeof lab, "HARD r=%d p=%d e=%ld", used_rot, used_pol, effort); report(lab); } }
                if (HILL > 0 && !restart && sc < cur) ty[mi] = mold;   /* reject a downhill move */
                else cur = sc;
            }
            goto core_done;
        }
        {   /* exhaustive: odometer over ranking profiles, DFS over type-set splits */
            int rk[MAXN] = {0};
            for (;;) {
                set_ranks(rk);
                nchoice = 0;
                for (;;) {
                    static u128 stack[1 << 11][MAXN]; int top = 0;
                    if (!BRUTE) {
                        for (int i = 0; i < n; i++) { int c = pcnt[i][cp[i]]; stack[0][i] = c == 128 ? ~(u128)0 : (((u128)1 << c) - 1); }
                        top = 1;
                    } else {
                        int kk[MAXN] = {0};
                        for (top = 0;;) {
                            if (top >= (1 << 11)) { fprintf(stderr, "brute: too many profiles\n"); return 1; }
                            for (int i = 0; i < n; i++) stack[top][i] = (u128)1 << kk[i];
                            top++;
                            int i = 0;
                            while (i < n && ++kk[i] == pcnt[i][cp[i]]) kk[i++] = 0;
                            if (i == n) break;
                        }
                    }
                    int ochoice[MAXN] = {0}, onchoice = nchoice; memcpy(ochoice, choice, sizeof(int) * nchoice);   /* Phase 1 extends it with zeros */
                    int lastnins = 0, lastmax[MAXN];
                    while (top) {
                        top--;
                        for (int i = 0; i < n; i++) ts[i] = stack[top][i];
                        runs++;
                        memcpy(choice, ochoice, sizeof choice); nchoice = onchoice;
                        int ok;
                        if (run_leaf(&ok)) {        /* a comparison split the type sets: push the parts */
                            u128 part[3] = {0, 0, 0}; int i = sp_i;
                            for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
                                int t = pidx[i][cp[i]][k], x = tsum(i, t, sp_S) - tsum(i, t, sp_T);
                                part[(x > 0) - (x < 0) + 1] |= (u128)1 << k;
                            }
                            for (int s = 0; s < 3; s++) if (part[s]) {
                                if (top >= (1 << 11)) { fprintf(stderr, "stack overflow\n"); return 1; }
                                for (int j = 0; j < n; j++) stack[top][j] = ts[j];
                                stack[top][i] = part[s]; top++;
                            }
                            continue;
                        }
                        lastnins = nins; memcpy(lastmax, maxchoice, sizeof lastmax);
                        long w = weight();
                        if (ARULE == 40) rulef_stat(w);
                        if (ARULE == 41 || ARULE == 42) rulef_stat41(w, ok, used_rot);
                        if (ARULE == 43) { stat43(w); leaves++; total += w; continue; }
                        if (ARULE == 44) { stat44(w); leaves++; total += w; continue; }
                        if (ARULE == 45) { stat45(w); leaves++; total += w; continue; }
                        if (last_uncov) { uncov += w; if (DEEP && shown < MAXF) { report("UNCOV"); shown++; } }
                        leaves++; total += w;
                        if (!ok) { fails += w; hist_rot[ROT + 1] += w; if (shown < MAXF) { report("FAIL"); shown++; } continue; }
                        if (!rawcheck()) { rawf += w; if (shown < MAXF) { report("RAWFAIL"); shown++; } continue; }
                        hist_rot[used_rot] += w; hist_pol[used_pol] += w;
                        ustat[last_uncov][used_pol][used_rot][last_status] += w;
                        if (DEEP && used_rot >= DEEP && shown < MAXF) { char lab[48]; snprintf(lab, sizeof lab, "DEEP r=%d p=%d w=%ld", used_rot, used_pol, w); report(lab); shown++; }
                    }
                    if (INS != 1) break;
                    /* next insertion sequence (the tree's shape depends only on the rankings) */
                    memcpy(choice, ochoice, sizeof choice); nchoice = onchoice;
                    nins = lastnins; memcpy(maxchoice, lastmax, sizeof maxchoice);
                    int j = nins - 1;
                    while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
                    if (j < 0) break;
                    choice[j]++; nchoice = j + 1;
                }
                int i = 0;
                while (i < n && ++rk[i] == np[i]) rk[i++] = 0;
                if (i == n) break;
            }
        }
      core_done:
        if (ARULE == 23 || ARULE == 26) {   /* U unc pol rot status count, status 0 no owner, 1 owner r, 2 other owner, 3 rotation */
            for (int a = 0; a < 2; a++) for (int b = 0; b < 3; b++) for (int c = 0; c <= MAXROT; c++) for (int e = 0; e < 4; e++)
                if (ustat[a][b][c][e]) printf("U %d %d %d %d %ld\n", a, b, c, e, ustat[a][b][c][e]);
            memset(ustat, 0, sizeof ustat);
        }
        if (ARULE == 40) rulef_print();
        if (ARULE == 41 || ARULE == 42) rulef_print41();
        if (ARULE == 43) print43();
        if (ARULE == 44) print44();
        if (ARULE == 45) print45();
        printf("total %ld leaves %ld runs %ld fails %ld rawfails %ld rot", total, leaves, runs, fails, rawf);
        for (int k = 0; k <= ROT; k++) printf(" %ld", hist_rot[k]);
        printf(" pol %ld %ld %ld uncov %ld covviol %ld covchk %ld\n", hist_pol[0], hist_pol[1], hist_pol[2], uncov, covviol, covchk);
        uncov = covviol = covchk = 0;
        fflush(stdout);
    }
    return 0;
}
