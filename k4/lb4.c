/* LB4: construction LB+ carried to four goods (k4/lb4.md), with an exhaustive tester.

Input (stdin), any number of cores:  n m, then per agent: d g_0 .. g_{d-1} T, then T lines of d values (a type
representative, values in the order g_0 .. g_{d-1}).  The tester enumerates every profile of the given types
(one type per agent), lazily: types of the same tie-broken ranking are kept as a set and split only when the
construction asks a comparison v_i(S) vs v_i(T) on which they disagree.  Every leaf's output is checked against the
raw EFX0 definition for every type in every agent's set (explicit integer values), and for the D2 shape (at most one
bundle of more than 2 goods).  One result line per core on stdout; failing configurations on stderr.

Options (k4/lb4.md §2 and §6): LB4 is -i2 -u1 -r1 -w1 -c1.
  -iN insertion: 0 index, 1 every sequence separately, 2 every sequence until one succeeds, 3 block lookahead,
      4 least omega, 5 "a > b + c" first, 6 index with one step changed, 7 index then the last block led by r,
      8 index then every leader of the last block, 9 every sequence then every leader of its last block;
  -uN upgrades: 0 none, 1 need-shrinking, 2 envy-free only, 3 policies 1, 2, 0 in turn;
  -oN owner: 0 every owner, 1 r only, 2 r then rotation;  -rN up to N rotations in a row; -d1 iterative deepening on N (0, 1, ..., N: same successes, least rotations) for each policy, -d2 with the bound outermost (least over all policies);
  -w1 owner needs from its bundle;  -c1 chains may end at upgraded agents;
  -s sensitivity (owner constraint ignored: must give raw failures);  -b brute force (every profile its own leaf);
  -a print the leaf allocations;  -fN print at most N failures per core. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <stdint.h>

typedef unsigned __int128 u128;
#define MAXN 8
#define MAXM 32
#define MAXT 1300
#define MAXG 80

static int n, m, d[MAXN], gl[MAXN][4], loc[MAXN][MAXM];
static uint32_t R[MAXN];
static int nt[MAXN], tv[MAXN][MAXT][4];
static int np[MAXN], pr[MAXN][24][4], pcnt[MAXN][24], pidx[MAXN][24][MAXG];
static int OWN = 0, INS = 0, SENS = 0, MAXF = 3, UPG = 1, BRUTE = 0, ALLOC = 0;
static long SAMPLE = 0;   /* -SN: N random profiles per core instead of all */
/* -a: distinct leaf allocations per core (owners packed 3 bits per good), printed as "A o_0 .. o_{m-1}" lines */
#define HBITS 22
static uint64_t *htab; static long hcnt;
static void hadd(const int *own_) {
    uint64_t key = 1;
    for (int g = 0; g < m; g++) key = key << 3 | (uint64_t)own_[g];
    uint64_t h = key * 0x9E3779B97F4A7C15ull >> (64 - HBITS);
    while (htab[h] && htab[h] != key) h = (h + 1) & ((1u << HBITS) - 1);
    if (!htab[h]) { if (++hcnt > (1 << HBITS) / 2) { fprintf(stderr, "hash full\n"); exit(1); } htab[h] = key; }
}

/* run state */
static int cp[MAXN];                 /* ranking index per agent */
static u128 ts[MAXN];                /* current type set (bits over pidx[i][cp[i]]) */
static int ord[MAXN][4], rp[MAXN][MAXM];
static jmp_buf env;
static int sp_i; static uint32_t sp_S, sp_T;

static int popc(uint32_t x) { return __builtin_popcount(x); }
static int tsum(int i, int t, uint32_t S) { int s = 0; for (int k = 0; k < d[i]; k++) if (S >> gl[i][k] & 1) s += tv[i][t][k]; return s; }
/* sign of v_i(S) - v_i(T) (goods outside R_i count 0), for every type in the current set; splits if not constant */
static int cmpv(int i, uint32_t S, uint32_t T) {
    int res = 2;
    for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
        int t = pidx[i][cp[i]][k], x = tsum(i, t, S) - tsum(i, t, T), s = (x > 0) - (x < 0);
        if (res == 2) res = s; else if (res != s) { sp_i = i; sp_S = S; sp_T = T; longjmp(env, 1); }
    }
    return res;
}

/* ---- the construction ---- */
static int Y[MAXN], pos[MAXN], blk[MAXN], upg[MAXN], frz[MAXN], cap[MAXN], own[MAXM];
static uint32_t base[MAXN], N_[MAXN], J;
static int choice[MAXN], nchoice, maxchoice[MAXN], nins;   /* insertion choices (tree mode) */
static int last_status;              /* 0 no owner needed, 1 owner r, 2 other owner, 3 rotation, -1 fail */
static int lastbig;

static uint32_t above(int i, int g);
/* P-step choice: an unprocessed agent that lost a good, smallest (rank of favourite remaining, goods left, index) */
static int pstep(uint32_t G, const int *done) {
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
static int favr(int i, uint32_t G) { for (int r = 0; r < d[i]; r++) if (G >> ord[i][r] & 1) return ord[i][r]; return -1; }
/* lookahead (INS = 3): insert c, run the P-steps of its block, count the goods needed alone by the agents processed */
static int lookahead(int c, uint32_t G, const int *done0, const int *Y0) {
    int done[MAXN], y[MAXN]; memcpy(done, done0, sizeof done); memcpy(y, Y0, sizeof y);
    for (int i = c;;) {
        y[i] = favr(i, G); if (y[i] >= 0) G &= ~(1u << y[i]); done[i] = 1;
        i = pstep(G, done); if (i < 0) break;
    }
    uint32_t NA = 0;
    for (int i = 0; i < n; i++) if (done[i]) NA |= y[i] >= 0 ? above(i, y[i]) : R[i];
    return popc(NA);
}
static void phase1(void) {
    uint32_t G = (m == 32) ? 0xffffffffu : ((1u << m) - 1);
    int done[MAXN] = {0}, b = -1;
    nins = 0;
    for (int i = 0; i < n; i++) Y[i] = -1;
    for (int step = 0; step < n; step++) {
        int best = -1, bk0 = 0, bk1 = 0;
        for (int i = 0; i < n; i++) if (!done[i]) {
            int left = popc(R[i] & G);
            if (left < d[i]) {
                int fr = d[i];
                for (int r = 0; r < d[i]; r++) if (G >> ord[i][r] & 1) { fr = r; break; }
                if (best < 0 || fr < bk0 || (fr == bk0 && left < bk1)) { best = i; bk0 = fr; bk1 = left; }
            }
        }
        if (best < 0) {              /* insertion step: every unprocessed agent has all its goods */
            int cand[MAXN], nc = 0;
            for (int i = 0; i < n; i++) if (!done[i]) cand[nc++] = i;
            int c = 0;
            if (INS == 5) {          /* prefer an agent whose top beats its next two goods (a > b + c), then index */
                for (int q = 0; q < nc; q++) { int i = cand[q];
                    if (d[i] == 4 && cmpv(i, 1u << ord[i][0], 1u << ord[i][1] | 1u << ord[i][2]) > 0) { c = q; break; } }
            }
            else if (INS == 3) { int bv = 1 << 30; for (int q = 0; q < nc; q++) { int v = lookahead(cand[q], G, done, Y); if (v < bv) { bv = v; c = q; } } }
            else if (INS >= 1) { if (nins >= nchoice) choice[nchoice++] = 0; c = choice[nins]; maxchoice[nins] = nc; if (c >= nc) c = nc - 1; }
            nins++;
            best = cand[c]; b++;
        }
        int i = best; Y[i] = -1;
        for (int r = 0; r < d[i]; r++) if (G >> ord[i][r] & 1) { Y[i] = ord[i][r]; break; }
        if (Y[i] >= 0) G &= ~(1u << Y[i]);
        done[i] = 1; pos[i] = step; blk[i] = b;
    }
    J = G;
}

static uint32_t above(int i, int g) { uint32_t s = 0; for (int r = 0; r < d[i] && ord[i][r] != g; r++) s |= 1u << ord[i][r]; return s; }
static uint32_t NAset(void) { uint32_t s = 0; for (int i = 0; i < n; i++) s |= N_[i]; return s; }

/* is agent x threatened by bundle L when it holds H?  exists h in L: v_x(L - h) > v_x(H) */
static int threatened(int x, uint32_t L, uint32_t H) {
    uint32_t Q = L & R[x];
    if (!Q) return 0;
    if ((L & ~R[x]) == 0) {          /* L inside R_x: remove its least valued good (lowest in the ranking) */
        for (int r = d[x] - 1; r >= 0; r--) if (Q >> ord[x][r] & 1) { Q &= ~(1u << ord[x][r]); break; }
        if (!Q) return 0;
    }
    return cmpv(x, Q, H & R[x]) > 0;
}

/* completion with owner o (or o = -1: none); C = goods of J going to slots; returns 1 and fills own[] if OK */
static int try_C0(int o, uint32_t C, uint32_t L);
static int tcnt; static int tl[MAXN]; static uint32_t allow[MAXN]; static int mt[MAXM];
static int aug(int t, uint32_t *seen) {
    for (int g = 0; g < m; g++) if ((allow[t] >> g & 1) && !(*seen >> g & 1)) {
        *seen |= 1u << g;
        if (mt[g] < 0 || aug(mt[g], seen)) { mt[g] = t; return 1; }
    }
    return 0;
}
static void fill_bases(void) {
    for (int g = 0; g < m; g++) own[g] = -1;
    for (int x = 0; x < n; x++) for (int g = 0; g < m; g++) if (base[x] >> g & 1) own[g] = x;
}
static int OWNW = 0;
static int try_C(int o, uint32_t C) {
    uint32_t L = (o >= 0 ? base[o] : 0) | (J & ~C);
    int scap[MAXN], sfrz[MAXN];
    if (OWNW && o >= 0) {            /* -w1: the owner's needs are the goods it values above its whole bundle */
        memcpy(scap, cap, sizeof cap); memcpy(sfrz, frz, sizeof frz);
        uint32_t NA = 0, no = 0;
        for (int g = 0; g < m; g++) if ((R[o] & ~L) >> g & 1 && cmpv(o, 1u << g, L) > 0) no |= 1u << g;
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
static int try_C0(int o, uint32_t C, uint32_t L) {
    for (int x = 0; x < n; x++) if (x != o && cap[x] == 0 && threatened(x, L, base[x])) return 0;
    /* cap-1 terminals threatened with their base alone need a protecting good (SDR); the rest needs capacity */
    int room = 0; tcnt = 0;
    for (int x = 0; x < n; x++) if (x != o) {
        room += cap[x];
        if (cap[x] == 1 && threatened(x, L, base[x])) {
            uint32_t a = 0;
            for (int g = 0; g < m; g++) if ((C >> g & 1) && !threatened(x, L, base[x] | 1u << g)) a |= 1u << g;
            allow[tcnt] = a; tl[tcnt++] = x;
        }
    }
    if (popc(C) > room) return 0;
    for (int g = 0; g < m; g++) mt[g] = -1;
    for (int t = 0; t < tcnt; t++) { uint32_t seen = 0; if (!aug(t, &seen)) return 0; }
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
    for (uint32_t C = J;; C = (C - 1) & J) {   /* every subset of J of size need (a maximal C is WLOG) */
        if (popc(C) == need && try_C(o, C)) return 1;
        if (!C) break;
    }
    if (OWNW) for (uint32_t C = J;; C = (C - 1) & J) {   /* -w1: slots grow with the owner's bundle; any size */
        if (popc(C) > need && try_C(o, C)) return 1;
        if (!C) break;
    }
    return 0;
}

static void setup_state(void) {
    for (int i = 0; i < n; i++) {
        upg[i] = 0; base[i] = Y[i] >= 0 ? 1u << Y[i] : 0;
        N_[i] = Y[i] >= 0 ? above(i, Y[i]) : R[i];
    }
}
static int upg_mode;
static void upgrades(void) {
    if (!upg_mode) return;
    for (int again = 1; again;) {
        again = 0;
        uint32_t NA = NAset();
        for (int k = 0; k < n && !again; k++) if (!upg[k] && Y[k] >= 0 && !(NA >> Y[k] & 1) && N_[k]) {
            for (int r = 0; r < d[k]; r++) {
                int g = ord[k][r];
                if (!(J >> g & 1)) continue;
                uint32_t nn = 0, B = base[k] | 1u << g;
                for (int x = 0; x < m; x++) if ((N_[k] >> x & 1) && cmpv(k, 1u << x, B) > 0) nn |= 1u << x;
                if (upg_mode == 2 && cmpv(k, B, R[k] & ~B) < 0) continue;   /* mode 2: only envy-free upgrades */
                if (nn != N_[k]) { upg[k] = 1; base[k] = B; J &= ~(1u << g); N_[k] = nn; again = 1; break; }
            }
        }
    }
}
static int slots(void) {
    uint32_t NA = NAset(); int S = 0;
    for (int i = 0; i < n; i++) {
        frz[i] = !upg[i] && Y[i] >= 0 && (NA >> Y[i] & 1);
        cap[i] = (upg[i] || frz[i]) ? 0 : (Y[i] >= 0 ? 1 : 2);
        S += cap[i];
    }
    return S;
}


/* ---- rotation (exploration): a frozen agent k gives up its pick along a need chain k = x0 -> .. -> xt (terminal),
   every chain agent takes its predecessor's pick, xt's pick is released, and k takes its relevant junk as its base */
static int ROT = 0, rot_depth = 0, CHUP = 0, rot_cap = 0, DEEPEN = 0;   /* rot_cap: the depth bound in force */
static int used_pol, used_rot; static long effort;   /* how a run succeeded: policy index, rotations, rotation attempts */
static int try_rotations(void);
static int chain[MAXN], clen;
static int apply_chain(int rot_pick, int *rot_more) {
    effort++;
    int sY[MAXN], su[MAXN]; uint32_t sb[MAXN], sN[MAXN], sJ = J;
    memcpy(sY, Y, sizeof Y); memcpy(su, upg, sizeof upg); memcpy(sb, base, sizeof base); memcpy(sN, N_, sizeof N_);
    int k = chain[0], t = chain[clen - 1];
    J |= base[t]; upg[t] = 0;            /* the chain end releases its base (a pick, or an upgraded pair) */
    for (int i = clen - 1; i >= 1; i--) { Y[chain[i]] = Y[chain[i - 1]]; base[chain[i]] = 1u << Y[chain[i]]; N_[chain[i]] = above(chain[i], Y[chain[i]]); }
    uint32_t W = R[k] & J, B = 0;
    /* k's new base: the rot_pick-th nonempty subset of W, pairs first, then triples, singles, quadruples */
    { int cnt = 0, want = rot_pick; static const int szord[5] = {2, 3, 1, 4, 0};
      for (int zi = 0; zi < 4 && !B; zi++) for (uint32_t O = W;; O = (O - 1) & W) {
          if (O && popc(O) == szord[zi] && cnt++ == want) { B = O; break; }
          if (!O) break; }
      if (!B) { memcpy(Y, sY, sizeof Y); memcpy(upg, su, sizeof upg); memcpy(base, sb, sizeof base); memcpy(N_, sN, sizeof N_); J = sJ; *rot_more = 0; return 0; } }
    J &= ~B; upg[k] = 1; base[k] = B; Y[k] = -2;
    uint32_t nn = 0;
    for (int x = 0; x < m; x++) if ((R[k] & ~B) >> x & 1) { if (!B || cmpv(k, 1u << x, B) > 0) nn |= 1u << x; }
    N_[k] = nn;
    int ok = 0;
    uint32_t NA = NAset();
    int valid = !(J & NA);
    for (int i = 0; i < n; i++) if (upg[i] && (base[i] & NA)) valid = 0;
    /* a base of 3 or more goods must be the owner's: after nested rotations (-rN, N >= 2) an earlier rotated agent
       may hold one; two such bases cannot both be the owner's, and the state is rejected */
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
    if (ok) used_rot = rot_depth + 1;             /* succeeded after rot_depth + 1 rotations */
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

static int construct1(void);
static int fb_seq, fb_upg, construct1_probe, ochoice[MAXN], onchoice;           /* fallbacks used: a later insertion sequence, a later upgrade policy */
static int construct(void) {
    if (INS == 4) {                  /* -i4: the insertion sequence with least omega after upgrades (mode 1), first in lex order */
        int best[MAXN], bn = 0, bw = 1 << 30;
        nchoice = 0;
        for (;;) {
            phase1(); setup_state(); upg_mode = 1; upgrades();
            int w = popc(J) - slots();
            if (w < bw) { bw = w; bn = nins; memcpy(best, choice, sizeof best); }
            int j = nins - 1;
            while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
            if (j < 0) break;
            choice[j]++; nchoice = j + 1;
        }
        memcpy(choice, best, sizeof best); nchoice = bn;
        return construct1();
    }
    if (INS == 7) {                  /* -i7: index insertion; if it fails, the last block led by r of that run */
        nchoice = 0;
        if (construct1()) return 1;
        fb_seq = 1;
        int r0 = -1, bl = 0, jl = nins - 1, q = 0;
        for (int i = 0; i < n; i++) { if (!upg[i] && (r0 < 0 || pos[i] > pos[r0])) r0 = i; if (blk[i] > bl) bl = blk[i]; }
        if (blk[r0] != bl) return 0;
        for (int i = 0; i < r0; i++) if (blk[i] == bl) q++;
        if (q == 0) return 0;          /* r already leads the last block */
        memset(choice, 0, sizeof choice); choice[jl] = q; nchoice = jl + 1;
        return construct1();
    }
    if (INS == 9) {                  /* -i9: the given insertion sequence; if it fails, every other leader at its last step */
        int sc[MAXN], smc[MAXN], sn = onchoice;
        memcpy(sc, ochoice, sizeof sc);   /* the outer sequence (a type split may have interrupted a deviation run) */
        memcpy(choice, sc, sizeof sc); nchoice = sn;
        int ok = construct1();
        int sni = nins; memcpy(smc, maxchoice, sizeof smc);
        memcpy(sc, choice, sizeof sc);   /* the effective sequence (Phase 1 extends it with zeros) */
        if (!ok) {
            fb_seq = 1;
            int jl = nins - 1;
            for (int q = 0; q < smc[jl] && !ok; q++) if (q != sc[jl]) {
                memcpy(choice, sc, sizeof sc); choice[jl] = q; nchoice = jl + 1;
                ok = construct1();
            }
        }
        memcpy(choice, sc, sizeof sc); nchoice = sn; nins = sni; memcpy(maxchoice, smc, sizeof smc);
        return ok;
    }
    if (INS == 8) {                  /* -i8: index insertion; if it fails, every other leader of the last block */
        nchoice = 0;
        if (construct1()) return 1;
        fb_seq = 1;
        int jl = nins - 1, nc = maxchoice[jl];     /* the last block's candidates in the index run */
        for (int q = 1; q < nc; q++) {           /* later insertion steps (if any) take the first agent */
            memset(choice, 0, sizeof choice); choice[jl] = q; nchoice = jl + 1;
            if (construct1()) return 1;
        }
        return 0;
    }
    if (INS == 6) {                  /* -i6: index insertion, or index with one insertion step changed */
        nchoice = 0;
        if (construct1()) return 1;
        fb_seq = 1;
        for (int j = 0; j < n; j++) {
            for (int q = 1;; q++) {
                memset(choice, 0, sizeof choice); choice[j] = q; nchoice = j + 1;
                construct1_probe = 1;
                int ok = construct1();
                construct1_probe = 0;
                if (nins <= j || q >= maxchoice[j]) break;   /* fewer insertion steps, or q out of range */
                if (ok) return 1;
            }
        }
        return 0;
    }
    if (INS != 2) return construct1();
    nchoice = 0;                     /* -i2: backtrack over insertion sequences until one succeeds */
    for (;;) {
        if (construct1()) return 1;
        fb_seq = 1;
        int j = nins - 1;
        while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
        if (j < 0) return 0;
        choice[j]++; nchoice = j + 1;
    }
}
static int construct2(void);
/* one policy with rotation depth bound ROT; with -d1 (iterative deepening) bounds 0, 1, ..., ROT in turn, which
   succeeds exactly when bound ROT does (each bound's search contains the previous one's) and finds the least depth */
static int construct_rot(void) {
    for (rot_cap = DEEPEN ? 0 : ROT; rot_cap <= ROT; rot_cap++) { used_rot = 0; if (construct2()) return 1; }
    return 0;
}
static int construct1(void) {
    if (UPG != 3) { upg_mode = UPG; used_pol = 0; return construct_rot(); }
    if (DEEPEN == 2) {                   /* -d2: bound outermost, every policy at each bound: the least rotations over all policies */
        for (int cap = 0; cap <= ROT; cap++) {
            int pi = 0;
            for (upg_mode = 1; upg_mode >= 0; upg_mode = upg_mode == 1 ? 2 : upg_mode == 2 ? 0 : -1, pi++) {
                rot_cap = cap; used_rot = 0;
                if (construct2()) { used_pol = pi; fb_upg = pi > 0; return 1; }
            }
        }
        fb_upg = 1; return 0;
    }
    int pi = 0;
    for (upg_mode = 1; upg_mode >= 0; upg_mode = upg_mode == 1 ? 2 : upg_mode == 2 ? 0 : -1, pi++) {  /* -u3: 1, 2, 0 */
        if (construct_rot()) { used_pol = pi; return 1; }
        fb_upg = 1;
    }
    return 0;
}
static int construct2(void) {
    phase1();
    setup_state();
    upgrades();
    int S = slots(), w = popc(J) - S;
    if (w <= 0) { try_owner(-1, S); last_status = 0; return 1; }
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    if (SENS) { fill_bases(); for (int g = 0; g < m; g++) if (own[g] < 0) own[g] = r; last_status = 1; return 1; }
    if (!frz[r] && try_owner(r, S)) { last_status = 1; return 1; }
    if (OWN == 1) { last_status = -1; return 0; }
    if (OWN == 2) { if (rot_cap && try_rotations()) { last_status = 3; return 1; } last_status = -1; return 0; }
    int ordr[MAXN], k = 0;
    for (int p = n - 1; p >= 0; p--) for (int i = 0; i < n; i++) if (pos[i] == p && i != r && (cap[i] > 0 || upg[i])) ordr[k++] = i;
    for (int t = 0; t < k; t++) if (try_owner(ordr[t], S)) { last_status = 2; return 1; }
    if (rot_cap && try_rotations()) { last_status = 3; return 1; }
    last_status = -1; return 0;
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

static long weight(void) { long w = 1; for (int i = 0; i < n; i++) w *= popc((uint32_t)ts[i]) + popc((uint32_t)(ts[i] >> 32)) + popc((uint32_t)(ts[i] >> 64)) + popc((uint32_t)(ts[i] >> 96)); return w; }

static void report(const char *what) {
    fprintf(stderr, "%s n=%d m=%d sets=[", what, n, m);
    for (int i = 0; i < n; i++) { fprintf(stderr, "["); for (int k = 0; k < d[i]; k++) fprintf(stderr, "%d%s", gl[i][k], k + 1 < d[i] ? "," : ""); fprintf(stderr, "]%s", i + 1 < n ? "," : ""); }
    fprintf(stderr, "] vals=[");
    for (int i = 0; i < n; i++) {
        int k = 0; while (!(ts[i] >> k & 1)) k++;
        int t = pidx[i][cp[i]][k];
        fprintf(stderr, "["); for (int q = 0; q < d[i]; q++) fprintf(stderr, "%d%s", tv[i][t][q], q + 1 < d[i] ? "," : ""); fprintf(stderr, "]%s", i + 1 < n ? "," : "");
    }
    fprintf(stderr, "] order=");
    for (int p = 0; p < n; p++) for (int i = 0; i < n; i++) if (pos[i] == p) fprintf(stderr, "%d ", i);
    fprintf(stderr, " picks=");
    for (int i = 0; i < n; i++) fprintf(stderr, "%d%s", Y[i], i + 1 < n ? "," : "");
    fprintf(stderr, " blocks=");
    for (int i = 0; i < n; i++) fprintf(stderr, "%d%s", blk[i], i + 1 < n ? "," : "");
    fprintf(stderr, " upg=");
    for (int i = 0; i < n; i++) if (upg[i]) fprintf(stderr, "%d:%x ", i, base[i]);
    fprintf(stderr, " frozen=");
    for (int i = 0; i < n; i++) if (frz[i]) fprintf(stderr, "%d ", i);
    fprintf(stderr, " J=%x w=%d\n", J, popc(J) - slots());
}

/* one run of the construction on the current type sets; returns 1 if a comparison split them (setjmp lives here, so
   no local of main is live across it) */
static int run_leaf(int *ok) {
    if (setjmp(env)) return 1;
    fb_seq = fb_upg = 0; rot_depth = 0;  /* a split may have interrupted a nested rotation */
    *ok = construct();
    return 0;
}


static long HILL = 0;                    /* -HN: N hill-climbing steps per core (restart every 500) */
static int PSCORE = 0;                   /* -P1: hardness = how few policies succeed on their own; -P2: rotations first */
static int DEEPREP = 0;                  /* -TN: report every run (-S, -H) needing at least N rotations */
static long hist_pol[3], hist_rot[4];
static long sstat[5], sbig[40], sfb_upg;   /* per-run counters of the -S and -H modes */
/* set the rankings and singleton type sets for type indices ty[]; run LB4 (every insertion sequence when -i1);
   *score = max over runs of policy * 1e8 + rotations * 1e6 + min(effort, 999999); returns 1 if every run succeeds */
static int eval_profile(const int *ty, long *score, long *nruns) {
    for (int i = 0; i < n; i++) {
        int t = ty[i], p, kk = 0;
        for (p = 0; p < np[i]; p++) { for (kk = 0; kk < pcnt[i][p]; kk++) if (pidx[i][p][kk] == t) break; if (kk < pcnt[i][p]) break; }
        cp[i] = p; ts[i] = (u128)1 << kk;
        for (int r = 0; r < d[i]; r++) ord[i][r] = gl[i][pr[i][cp[i]][r]];
        for (int g = 0; g < m; g++) rp[i][g] = -1;
        for (int r = 0; r < d[i]; r++) rp[i][ord[i][r]] = r;
    }
    long sc = 0; nchoice = 0;
    int bchoice[MAXN], bnchoice = 0;     /* the hardest run's insertion sequence (-i1), re-run at the end for reports */
    for (;;) {
        int ok; effort = 0;
        long sc0 = sc;
        if (PSCORE == 1 && UPG == 3) {   /* -P1: run each policy on its own; score by how few succeed */
            int nsucc = 0, rmin = 99; long eff = 0;
            for (UPG = 0; UPG < 3; UPG++) {
                effort = 0;
                if (run_leaf(&ok)) { fprintf(stderr, "split with singleton type sets\n"); exit(1); }
                eff += effort;
                if (ok) { nsucc++; if (used_rot < rmin) rmin = used_rot; if (!rawcheck()) { report("RAWFAIL"); exit(2); } }
            }
            UPG = 3;
            (*nruns)++;
            if (!nsucc) { *score = -1; return 0; }
            long e = eff < 999999 ? eff : 999999, v = (3 - nsucc) * 100000000L + rmin * 1000000L + e;
            if (v > sc) sc = v;
            if (run_leaf(&ok) || !ok) { fprintf(stderr, "-P1: LB4r disagrees with its policies\n"); exit(1); }
        } else {
        if (run_leaf(&ok)) { fprintf(stderr, "split with singleton type sets\n"); exit(1); }
        (*nruns)++;
        if (!ok) { *score = -1; return 0; }
        }
        if (!rawcheck()) { report("RAWFAIL"); exit(2); }
        if (DEEPREP && used_rot >= DEEPREP) { char lab[48]; snprintf(lab, sizeof lab, "DEEP p=%d r=%d", used_pol, used_rot); report(lab); }
        sstat[last_status]++; if (lastbig) sbig[lastbig]++; if (fb_upg) sfb_upg++;
        hist_pol[used_pol]++; hist_rot[used_rot]++;
        long e = effort < 999999 ? effort : 999999, v = used_pol * 100000000L + used_rot * 1000000L + e;
        if (PSCORE == 2) v = used_rot * 100000000L + used_pol * 1000000L + e;   /* -P2: rotations first */
        if (PSCORE != 1 && v > sc) sc = v;
        if (sc > sc0 || !bnchoice) { memcpy(bchoice, choice, sizeof bchoice); bnchoice = nchoice ? nchoice : -1; }
        if (INS != 1) break;
        int j = nins - 1;                /* next insertion sequence */
        while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
        if (j < 0) break;
        choice[j]++; nchoice = j + 1;
    }
    if (INS == 1) {                      /* leave the state of the hardest run, for report() */
        int ok; memcpy(choice, bchoice, sizeof bchoice); nchoice = bnchoice < 0 ? 0 : bnchoice;
        if (run_leaf(&ok) || !ok) { fprintf(stderr, "re-run of the hardest run failed\n"); exit(1); }
    }
    *score = sc; return 1;
}

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strncmp(argv[a], "-o", 2)) OWN = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-i", 2)) INS = atoi(argv[a] + 2);
        else if (!strcmp(argv[a], "-s")) SENS = 1;
        else if (!strncmp(argv[a], "-f", 2)) MAXF = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-u", 2)) UPG = atoi(argv[a] + 2);
        else if (!strcmp(argv[a], "-b")) BRUTE = 1;
        else if (!strcmp(argv[a], "-a")) ALLOC = 1;
        else if (!strncmp(argv[a], "-S", 2)) SAMPLE = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-H", 2)) HILL = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-r", 2)) ROT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-d", 2)) DEEPEN = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-P", 2)) PSCORE = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-T", 2)) DEEPREP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-w", 2)) OWNW = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-c", 2)) CHUP = atoi(argv[a] + 2);
    }
    if (ALLOC) htab = calloc((size_t)1 << HBITS, sizeof(uint64_t));
    while (scanf("%d %d", &n, &m) == 2) {
        memset(loc, -1, sizeof loc);
        for (int i = 0; i < n; i++) {
            scanf("%d", &d[i]); R[i] = 0;
            for (int k = 0; k < d[i]; k++) { scanf("%d", &gl[i][k]); loc[i][gl[i][k]] = k; R[i] |= 1u << gl[i][k]; }
            scanf("%d", &nt[i]);
            for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) scanf("%d", &tv[i][t][k]);
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
        long stat[5] = {0}, bigsz[40] = {0}, nfb_seq = 0, nfb_upg = 0;
        if (SAMPLE > 0 || HILL > 0) {    /* random profiles (-S), or hill-climbing toward hard profiles (-H) */
            uint64_t x = 88172645463325252ull ^ (uint64_t)(n * 131 + m);
            for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) x = x * 6364136223846793005ull + (uint64_t)(gl[i][k] + 17 * k + 1);
            int ty[MAXN], best[MAXN]; long cur = -1, top = -1;
            long nsteps = SAMPLE > 0 ? SAMPLE : HILL;
            for (long sidx = 0; sidx < nsteps; sidx++) {
                int restart = SAMPLE > 0 || sidx % 500 == 0, mi = -1, mold = 0;
                if (restart) for (int i = 0; i < n; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; ty[i] = (int)(x % (uint64_t)nt[i]); }
                else {                   /* mutate one agent's type */
                    x ^= x << 13; x ^= x >> 7; x ^= x << 17; mi = (int)(x % (uint64_t)n); mold = ty[mi];
                    x ^= x << 13; x ^= x >> 7; x ^= x << 17; ty[mi] = (int)(x % (uint64_t)nt[mi]);
                }
                long sc; int ok = eval_profile(ty, &sc, &runs);
                leaves++; total++;
                if (!ok) {
                    fails++; if (shown < MAXF) { report("FAIL"); shown++; }
                    if (HILL > 0) break;
                    continue;
                }
                if (sc > top) {          /* hardest so far on this core */
                    top = sc; memcpy(best, ty, sizeof best);
                    if (sc >= 2000000L) { char lab[64]; snprintf(lab, sizeof lab, PSCORE == 2 ? "HARD r=%ld p=%ld e=%ld" : "HARD p=%ld r=%ld e=%ld", sc / 100000000L, (sc / 1000000L) % 100, sc % 1000000L); report(lab); }
                }
                if (HILL > 0 && !restart && sc < cur) ty[mi] = mold;   /* reject a downhill move */
                else cur = sc;
            }
            (void)best;
            for (int k = 0; k < 5; k++) stat[k] += sstat[k];
            for (int k = 0; k < 40; k++) bigsz[k] += sbig[k];
            nfb_upg += sfb_upg;
            memset(sstat, 0, sizeof sstat); memset(sbig, 0, sizeof sbig); sfb_upg = 0;
            goto core_done;
        }
        /* odometer over ranking profiles */
        int rk[MAXN] = {0};
        for (;;) {
            for (int i = 0; i < n; i++) {
                cp[i] = rk[i];
                for (int r = 0; r < d[i]; r++) ord[i][r] = gl[i][pr[i][cp[i]][r]];
                for (int g = 0; g < m; g++) rp[i][g] = -1;
                for (int r = 0; r < d[i]; r++) rp[i][ord[i][r]] = r;
            }
            /* insertion-sequence tree (INS = 1): odometer over choices */
            nchoice = 0;
            for (;;) {
                memcpy(ochoice, choice, sizeof ochoice); onchoice = nchoice;
                /* DFS over type-set splits */
                static u128 stack[1 << 16][MAXN]; int top = 0;
                if (!BRUTE) {
                    for (int i = 0; i < n; i++) { int c = pcnt[i][cp[i]]; stack[0][i] = c == 128 ? ~(u128)0 : (((u128)1 << c) - 1); }
                    top = 1;
                } else {                 /* every profile its own leaf (singleton type sets) */
                    int kk[MAXN] = {0};
                    for (top = 0;;) {
                        if (top >= (1 << 16)) { fprintf(stderr, "brute: too many profiles\n"); return 1; }
                        for (int i = 0; i < n; i++) stack[top][i] = (u128)1 << kk[i];
                        top++;
                        int i = 0;
                        while (i < n && ++kk[i] == pcnt[i][cp[i]]) kk[i++] = 0;
                        if (i == n) break;
                    }
                }
                while (top) {
                    top--;
                    for (int i = 0; i < n; i++) ts[i] = stack[top][i];
                    runs++;
                    int ok;
                    if (run_leaf(&ok)) {        /* a comparison split the type sets: push the parts */
                        u128 part[3] = {0, 0, 0}; int i = sp_i;
                        for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
                            int t = pidx[i][cp[i]][k], x = tsum(i, t, sp_S) - tsum(i, t, sp_T);
                            part[(x > 0) - (x < 0) + 1] |= (u128)1 << k;
                        }
                        for (int s = 0; s < 3; s++) if (part[s]) {
                            if (top >= (1 << 16)) { fprintf(stderr, "stack overflow\n"); return 1; }
                            for (int j = 0; j < n; j++) stack[top][j] = ts[j];
                            stack[top][i] = part[s]; top++;
                        }
                        continue;
                    }
                    long w = weight();
                    leaves++; total += w;
                    if (!ok) { fails += w; if (shown < MAXF) { report("FAIL"); shown++; } continue; }
                    stat[last_status] += w;
                    hist_pol[used_pol] += w; hist_rot[used_rot] += w;
                    if (fb_seq) nfb_seq += w;
                    if (fb_upg) nfb_upg += w;
                    if (!rawcheck()) { rawf += w; if (shown < MAXF) { report("RAWFAIL"); shown++; } continue; }
                    if (lastbig) bigsz[lastbig] += w;
                    if (ALLOC) hadd(own);
                }
                if (INS != 1 && INS != 9) break;
                if (INS == 9) { memcpy(choice, ochoice, sizeof choice); nchoice = onchoice; phase1(); }   /* odometer state of the outer sequence */
                /* next insertion sequence */
                int j = nins - 1;
                while (j >= 0 && choice[j] + 1 >= maxchoice[j]) j--;
                if (j < 0) break;
                choice[j]++; nchoice = j + 1;
            }
            int i = 0;
            while (i < n && ++rk[i] == np[i]) rk[i++] = 0;
            if (i == n) break;
        }
      core_done:
        printf("H %ld %ld %ld %ld %ld %ld %ld\n", hist_pol[0], hist_pol[1], hist_pol[2], hist_rot[0], hist_rot[1], hist_rot[2], hist_rot[3]);
        memset(hist_pol, 0, sizeof hist_pol); memset(hist_rot, 0, sizeof hist_rot);
        if (ALLOC) {
            for (long h = 0; h < (1 << HBITS); h++) if (htab[h]) {
                int o[MAXM]; uint64_t key = htab[h];
                for (int g = m - 1; g >= 0; g--) { o[g] = key & 7; key >>= 3; }
                printf("A"); for (int g = 0; g < m; g++) printf(" %d", o[g]); printf("\n");
            }
            memset(htab, 0, sizeof(uint64_t) << HBITS); hcnt = 0;
        }
        printf("total %ld leaves %ld runs %ld fails %ld rawfails %ld nobig %ld owner_r %ld owner_other %ld rot %ld later_seq %ld later_upg %ld big", total, leaves, runs, fails, rawf, stat[0], stat[1], stat[2], stat[3], nfb_seq, nfb_upg);
        for (int s = 3; s < 40; s++) if (bigsz[s]) printf(" %d:%ld", s, bigsz[s]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
