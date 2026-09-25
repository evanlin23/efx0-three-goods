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
       exact owner test with the owner found (needs from the base, no rotation); 'uncov' counts
       the profiles (weighted) where no sequence of the family is covered.
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
#define MAXN 40
#define MAXM 128
#define MAXT 1300
#define MAXG 80
#define MAXROT 6

static int n, m, d[MAXN], gl[MAXN][4];
static gm R[MAXN], ALLG;
static int nt[MAXN], tv[MAXN][MAXT][4];
static int np[MAXN], pr[MAXN][24][4], pcnt[MAXN][24], pidx[MAXN][24][MAXG];
static int EXISTS = 0;               /* -i2 given */
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
    if (valid) {
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
        case 18: k = mcls[c] == 1 ? 0 : mcls[c] == 0 ? 1 : 2;   /* matched to the second choice first */
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
static int COVT = 2, COVZ = 0; static long covviol;
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
    for (int x = 0; x < n; x++) if (E[x] && (d[x] != 3 || Y[x] != ord[x][0] || !is_leader(x))) { printf("A3VIOL\n"); covviol++; return 0; }
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
    } else { printf("ROTINV\n"); covviol++; }
    snap_load(&sv);
    return pr;
}
/* -C3: candidate Theorem A4+N (k4/adaptive.md §6): A4+(o) after need-shrinking upgrades, where an upgraded agent can
   be threatened (its pair need not be envy-free); it holds its base and has no slot, so it is counted like a frozen
   one, by rho. Owner o: not frozen, with a base of at most one good, or upgraded. Returns the owner, or -1. */
static int aplusN_owner(void) {
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    int ordo[MAXN], k = 0;
    if (r >= 0 && !frz[r]) ordo[k++] = r;
    for (int o = 0; o < n; o++) if (o != r && !frz[o] && (cap[o] > 0 || upg[o])) ordo[k++] = o;
    for (int q = 0; q < k; q++) {
        int o = ordo[q]; gm Wo = base[o] | J; int dem = 0, tb = 0;
        for (int x = 0; x < n && dem < 99; x++) {
            if (x == o) continue;
            if (!upg[x] && !frz[x]) tb += cap[x];
            if (!threatened(x, Wo, base[x])) continue;
            if (!upg[x] && !frz[x] && Y[x] >= 0 && cap[x] >= 1 && popc(base[o] & R[x]) <= 1) dem += 1;
            else dem += rho4(x, Wo);
        }
        if (dem <= tb) return o;
    }
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
    if (frz[r]) { printf("A1VIOL\n"); covviol++; return 0; }
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
    if (!ok) { covviol++; report(cov_last >= 4 ? "COVVIOL_N" : "COVVIOL"); }
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
        last_uncov = !cover_family(ARULE);
        if (!last_uncov && COVZ) cov_verify();
        return lb4r(ROT);
    } else if (ARULE == 24) {
        int b = minmax_first(), mx = b / 64;
        pre[0] = b % 64; npre = 1; TAILRULE = 0; phase1(); memcpy(pre, ins_seq, sizeof(int) * nins); npre = nins;
        if (mx > ROT) return 0;
        int ok = lb4r(ROT); used_rot = mx; return ok;
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

/* one run of the construction on the current type sets; returns 1 if a comparison split them */
static int run_leaf(int *ok) {
    if (setjmp(env)) { stop_at = -1; TAILRULE = 0; if (INS == 1 && EXISTS) INS = 2; return 1; }
    rot_depth = 0; last_uncov = 0;
    *ok = construct();
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
        else if (!strncmp(argv[a], "-i", 2)) { INS = atoi(argv[a] + 2); EXISTS = INS == 2; }
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
        else if (!strncmp(argv[a], "-c", 2)) CHUP = atoi(argv[a] + 2);
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
                hist_rot[k]++; if (ok) hist_pol[used_pol]++;
                if (VERB || !ok) { char lab[64]; snprintf(lab, sizeof lab, ok ? "RUN rot=%d pol=%d" : "RUN fail", k, used_pol); report(lab); }
                if (INS == 10) printf("sample %ld: %s %d\n", smp, ok ? "rot" : "fail", k);
                fflush(stdout);
            }
            printf("single rule=%d samples=%ld", ARULE, nsm);
            for (int k = 0; k <= ROT; k++) printf(" rot%d=%ld", k, hist_rot[k]);
            printf(" fail=%ld uncov=%d\n", hist_rot[ROT + 1], last_uncov); fflush(stdout);
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
        if (ARULE == 23) {               /* U unc pol rot status count, status 0 no owner, 1 owner r, 2 other owner, 3 rotation */
            for (int a = 0; a < 2; a++) for (int b = 0; b < 3; b++) for (int c = 0; c <= MAXROT; c++) for (int e = 0; e < 4; e++)
                if (ustat[a][b][c][e]) printf("U %d %d %d %d %ld\n", a, b, c, e, ustat[a][b][c][e]);
            memset(ustat, 0, sizeof ustat);
        }
        printf("total %ld leaves %ld runs %ld fails %ld rawfails %ld rot", total, leaves, runs, fails, rawf);
        for (int k = 0; k <= ROT; k++) printf(" %ld", hist_rot[k]);
        printf(" pol %ld %ld %ld uncov %ld covviol %ld\n", hist_pol[0], hist_pol[1], hist_pol[2], uncov, covviol);
        uncov = covviol = 0;
        fflush(stdout);
    }
    return 0;
}
