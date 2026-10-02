/* lemmam_portfolio.c: a portfolio of candidate strengthenings of Lemma M (k4/rulef.md §4, §6), evaluated in one pass.
   Workstream compute/k4-m-portfolio. EVIDENCE only (PROMPT.md §5 rule 3).

   This file #includes k4/rulef.c UNCHANGED (its main is renamed rulef_main and not used), so the classes K0 and K1 are
   rulef.c's own code (deficits() with KONLY, k1_run(), c40_run(), the lazy type splitting of the exhaustive mode). It
   adds, for every leaf (a set of strict profiles on which every comparison made is constant) and every first agent a
   (tau_a = (a, then index order)):
     K0(a)   some policy (need-shrinking, envy-free; -N1 also none) has Lemma K deficit <= 0 or omega <= 0 (rulef.c);
     K1(a)   not K0, and some policy and single rotation reach Lemma K deficit <= 0 (rulef.c k1_run);  W(a) = K0 or K1;
     M1(a,pol)   k4/rulef.md §6 Step 3 (M1): omega <= 0, or r (the last-processed agent that is not upgraded) is not
             frozen and a least ∅-service sigma_F of the exposed agents that are not free has |sigma_F| <= kappa_0, the
             number of free agents other than r that are not exposed (Lemma S then gives Lemma K deficit <= 0: K0);
     KRb(a,pol)  Lemma KR (§3) with o = r, "in particular" form: some ∅-service sigma of E (owner r, K = ∅) of size
             kappa + delta, some frozen k with a need chain k -> .. -> r (frozen inner agents), some O inside R_k ∩ W with
             v_k(O) > v_k(Y_k), (i) no good of O used by sigma for an agent other than k, (ii) r not frozen after the
             rotation, and delta <= 1 and (eps = 0, or c_k >= 1 and eps = 1)   [the task's M_def1 / M2];
     KRa(a,pol)  the same with the lemma's full bound delta - 1 - c_k + eps <= 0 (o = r);
     KRo(a,pol)  KRa for some owner o that is not frozen and not upgraded (|B_o| <= 1), not only r;
     partners  exposed (w.r.t. r) frozen 4-good agents (x1), the leader of r's block (x2), the ends of the need chains
             from the x1 agents (x3), from r's block leader when exposed and frozen (x3b), from any exposed frozen agent
             (x3c), and r itself (x4), per policy;
     C40(a)  rulef.c c40_run (Corollary C4^0's hypothesis, envy-free run);  G2(a): envy-free run, omega >= 1, r not
             frozen, no exposed 4-good agent, LB+'s bad case (as rulef.c cov_AB1), r has four goods and is exposed after
             the rotation (O = {b, c} of r's block leader k*) along EVERY need chain k* -> r ((G2) of k4/c4.md §6).
   Big-top (four goods, top worth more than the next two together) is rulef.c's bigtop_agent (a comparison, so the leaf
   splits on it). M_gap's agent (largest a - (b + c), ties to the lowest index) depends on the representative values
   of the types, not only on the leaf: its counts are exact per profile (every type tuple of the leaf is counted).

   Rw(a,pol)   some single rotation (RotStep: frozen k, need chain to r, any nonempty base O) reaches a valid state with
             no base of three or more goods and omega' <= 0 (no owner needed; EFX.LB4.complete_none_exists); Rwo: the same
             along a chain to any end. Rwo implies K1 (rulef.c's k1_run accepts exactly such states).
   Candidates: an allowed set A (SNAME) x a predicate P (QNAME), named "set:pred"; the candidate holds on a profile when
   some agent of A satisfies P (for some policy); "app" = the set's hypothesis holds; "tight" = exactly one agent of A
   satisfies P; "only" = exactly one first agent of the whole profile is in K0 or K1, and it is the candidate's.
     sets: all; bt = big-top agents (applicable if some); bt1 = the big-top agent (if exactly one); nobt = agents sharing
       their top good with another agent (no big-top agent, some shared top); nobt0 = all (no big-top, no shared top);
       gap / gapn = the argmax of a - (b + c) / of (a - b - c)/(a + b + c + d) (representative values, ties lowest index);
       btp = big-top agents with the fewest private goods; shp = shared-top agents with the fewest private goods (no
       big-top); bt2 = big-top agents (if two or more); sh = agents sharing their top good with another agent (if some,
       whether or not some agent is big-top); btsh = big-top or top-sharing agents (if some).
     predicates: W = K0 or K1; K0; M1; KRb; M1|KRb; K0|KRa; K0|KRo; K0|KRb; K0|KRa|Rw; K0|KRo|Rwo.
   The task's names (k4/lemmam_portfolio.py ALIAS): M = all:W, M_K0 = all:K0, M_bt = bt:W, M_bt1 = bt1:W, M_nobt = nobt:W,
   M_gap = gap:W, M_gapn = gapn:W, M_kappa = all:M1, M_def1 = all:KRb, M_12 = all:M1|KRb, M_K0KR = all:K0|KRa, ...
   Exchange partners: for every agent a not in W and each variant, the partner set; "undef" if empty, "any" if some
   partner is in W, "all" if every one is.

   Modes (stdin as rulef.c: any number of cores):
     (default) exhaustive over every strict profile (lazy type splitting, rulef.c's odometer);
     -SN  N random profiles per core;   -T1  single profiles (one type per agent);
     -HN  hill-climbing / annealing against candidate -cK (K < 1000: index set * NPRED + predicate) or partner variant
          -cK (K = 1000 + variant) for N
          steps per core, restarts every -BN steps (default 3000) from random types, or from -I<t0,t1,..> (type indices)
          when given; stops at the first failure (prints HFAIL) and prints the tightest profiles found (HTIGHT).
   Options: -Y1 (Lemma K kept-out sets may hold goods outside R_x: Remark 4; use it, Lemma M needs it on a suite core),
     -N1 (also the no-upgrade policy, rule RK3), -fN failure lines per candidate per core (default 2), -XS seed,
     -O0 skip KRo (any owner), -v (print every profile's per-agent data as PROF lines).
   Output per core: "PM ..." counters (see pm_print), "PFAIL cand=.. w=.. sets=.. vals=.. fa=.." and
   "XFAIL var=.. a=.. ..." lines. */
#include <math.h>
#define main rulef_main
#include "rulef.c"
#undef main

#define NSET 12
#define NPRED 10
#define NCAND (NSET * NPRED)          /* candidate c = set (c / NPRED) x predicate (c % NPRED), named "set:pred" */
static const char *SNAME[NSET] = {"all", "bt", "bt1", "nobt", "nobt0", "gap", "gapn", "btp", "shp", "bt2", "sh", "btsh"};
static const char *QNAME[NPRED] = {"W", "K0", "M1", "KRb", "M1|KRb", "K0|KRa", "K0|KRo", "K0|KRb", "K0|KRa|Rw", "K0|KRo|Rwo"};
static char CNAMEbuf[NCAND][40]; static const char *CNAME[NCAND];
#define NVAR 18                       /* partner variants: 6 kinds x 3 policies */
static const char *VKIND[6] = {"x1", "x2", "x3", "x3b", "x3c", "x4"};
static const char *PNAME[3] = {"N", "E", "0"};   /* need-shrinking, envy-free, none (index into polv) */
static int npols = 2, polv[3] = {1, 2, 0};
static int DO_KRO = 1, PMVERB = 0, FAILMAX = 2;

typedef struct {
    int K0, K1, W;
    int om[3], r[3], rfz[3], ks[3], M1[3], KRb[3], KRa[3], KRo[3], Rw[3], Rwo[3];
    uint64_t part[3][6];             /* partner sets per policy and kind */
    int c40, g2, g2bad;
} pa_t;
static pa_t PA[MAXN];
static int BT[MAXN], SHT[MAXN], PRIV[MAXN];

/* ---- Lemma K options (unrestricted slot goods: Lemma K as written), K = ∅ ---- */
static gm po_opt[MAXN][MAXM + 40]; static int po_slot[MAXN][MAXM + 40], po_n[MAXN];
static int build_opts(int i, int x, gm Wo, int capx) {
    int k = 0;
    if (capx >= 1)
        for (int g = 0; g < m; g++) if (J >> g & 1)
            if (!threatened(x, Wo & ~BIT(g), base[x] | BIT(g))) { po_opt[i][k] = BIT(g); po_slot[i][k] = 1; k++; }
    gm sets[32]; int ns = prot_sets_in(x, Wo, J, sets);
    for (int q = 0; q < ns; q++) { po_opt[i][k] = sets[q]; po_slot[i][k] = 0; k++; }
    po_n[i] = k;
    return k;
}
static int po_cnt, po_best;
static void po_dfs(int i, gm U, gm G) {
    if (popc(U) >= po_best) return;
    if (i == po_cnt) { po_best = popc(U); return; }
    for (int q = 0; q < po_n[i]; q++) {
        gm O = po_opt[i][q];
        if (po_slot[i][q] && (G & O)) continue;
        po_dfs(i + 1, U | O, po_slot[i][q] ? (G | O) : G);
    }
}
/* M1 at the current state (after slots()), owner r: |sigma_F| <= kappa_0 */
static int m1_state(int r) {
    if (frz[r] || upg[r]) return 0;
    gm Wr = base[r] | J; int kappa0 = 0;
    po_cnt = 0;
    for (int x = 0; x < n; x++) if (x != r) {
        int thr = threatened(x, Wr, base[x]);
        int fre = !upg[x] && !frz[x] && Y[x] >= 0;
        if (!thr) { if (fre) kappa0++; continue; }
        if (fre) continue;
        if (!build_opts(po_cnt, x, Wr, cap[x])) return 0;
        po_cnt++;
    }
    po_best = 1 << 20; po_dfs(0, 0, 0);
    return po_best <= kappa0;
}

/* ---- Lemma KR at the current state, owner o ---- */
static int kr_list[MAXN], kr_ne, kr_kappa, kr_k, kr_tho, kr_resa, kr_resb;
static gm kr_O, kr_Go;
static void kr_dfs(int i, gm Uo, gm G, gm Uk) {
    if (popc(Uo) > kr_kappa + 1 || (kr_resa && kr_resb)) return;
    if (i == kr_ne) {
        int eps = !kr_tho ? 0 : ((kr_Go & ~G) ? 1 : 99);
        if (eps == 99) return;
        int ck = popc(Uk & ~Uo), delta = popc(Uo | Uk) - kr_kappa;
        if (delta - 1 - ck + eps <= 0) kr_resa = 1;
        if (delta <= 1 && (eps == 0 || (ck >= 1 && eps == 1))) kr_resb = 1;
        return;
    }
    int x = kr_list[i];
    for (int q = 0; q < po_n[i]; q++) {
        gm Ob = po_opt[i][q];
        if (x != kr_k && (Ob & kr_O)) continue;                 /* (i) */
        if (po_slot[i][q] && (G & Ob)) continue;                 /* slot goods distinct */
        gm G2 = po_slot[i][q] ? (G | Ob) : G;
        if (x == kr_k) kr_dfs(i + 1, Uo, G2, Uk | Ob); else kr_dfs(i + 1, Uo | Ob, G2, Uk);
    }
}
static int kc[MAXN], kcl, kr_o; static gm kr_W;
static void kr_try_chain(void) {
    int k = kc[0], t = kcl - 1, o = kr_o;
    int yt1 = Y[kc[t - 1]];
    gm NAr = 0;
    for (int j = 0; j < n; j++) {
        int in = 0; for (int q = 0; q < kcl; q++) if (kc[q] == j) in = 1;
        if (!in) NAr |= N_[j];
    }
    for (int i = 1; i < t; i++) NAr |= above(kc[i], Y[kc[i - 1]]);
    int tho = threatened(o, kr_W, BIT(yt1));
    gm Go = 0;
    if (tho) for (int g = 0; g < m; g++) if ((kr_W >> g & 1) && !threatened(o, kr_W & ~BIT(g), BIT(yt1) | BIT(g))) Go |= BIT(g);
    gm RkW = R[k] & kr_W;
    for (gm O = RkW; O; O = (O - 1) & RkW) {
        if (cmpv(k, O, BIT(Y[k])) <= 0) continue;
        gm nk = 0;
        for (int g = 0; g < m; g++) if (((R[k] & ~O) >> g & 1) && cmpv(k, BIT(g), O) > 0) nk |= BIT(g);
        if ((NAr | nk) >> yt1 & 1) continue;                     /* (ii) */
        kr_O = O; kr_k = k; kr_Go = Go & ~O; kr_tho = tho;
        kr_dfs(0, 0, 0, 0);
        if (kr_resa && kr_resb) return;
    }
}
static void kr_chain(void) {
    int x = kc[kcl - 1];
    if (Y[x] < 0) return;
    for (int j = 0; j < n && !(kr_resa && kr_resb); j++) {
        int in = 0; for (int q = 0; q < kcl; q++) if (kc[q] == j) in = 1;
        if (in || !(N_[j] >> Y[x] & 1)) continue;
        if (j == kr_o) { kc[kcl++] = j; kr_try_chain(); kcl--; }
        else if (frz[j]) { kc[kcl++] = j; kr_chain(); kcl--; }
    }
}
static void kr_state(int o, int *ra, int *rb) {
    kr_resa = kr_resb = 0; *ra = *rb = 0;
    if (frz[o] || upg[o]) return;
    kr_W = base[o] | J; kr_kappa = 0; kr_o = o; kr_ne = 0;
    for (int x = 0; x < n; x++) if (x != o) kr_kappa += cap[x];
    for (int x = 0; x < n; x++) if (x != o && threatened(x, kr_W, base[x])) {
        if (!build_opts(kr_ne, x, kr_W, cap[x])) return;
        kr_list[kr_ne++] = x;
    }
    for (int k = 0; k < n && !(kr_resa && kr_resb); k++) if (k != o && frz[k]) { kc[0] = k; kcl = 1; kr_chain(); }
    *ra = kr_resa; *rb = kr_resb;
}

/* Rw: a single rotation (RotStep: frozen k, need chain k -> .. -> end with frozen inner agents, any nonempty base O
   inside R_k and the junk after the end's base is released) to a valid state with no base of three or more goods and
   omega' <= 0, so that no owner is needed (EFX.LB4.complete_none_exists). rw_r: chains ending at r; rw_any: any end. */
static int rw_hit_r, rw_hit_any, rw_r;
static void rw_try_chain(void) {
    int k = kc[0], t = kc[kcl - 1];
    if (rw_hit_any && (rw_hit_r || t != rw_r)) return;
    snap_t sv; snap_save(&sv);
    J |= base[t]; upg[t] = 0;
    for (int i = kcl - 1; i >= 1; i--) { Y[kc[i]] = Y[kc[i - 1]]; base[kc[i]] = BIT(Y[kc[i]]); N_[kc[i]] = above(kc[i], Y[kc[i]]); }
    gm J0 = J, W2 = R[k] & J;
    for (gm O = W2; O; O = (O - 1) & W2) {
        if (popc(O) >= 3) continue;
        J = J0 & ~O; upg[k] = 1; base[k] = O; Y[k] = -2;
        gm nn = 0;
        for (int x = 0; x < m; x++) if (((R[k] & ~O) >> x & 1) && cmpv(k, BIT(x), O) > 0) nn |= BIT(x);
        N_[k] = nn;
        gm NA = NAset(); int valid = !(J & NA);
        for (int i = 0; i < n && valid; i++) if ((upg[i] && (base[i] & NA)) || popc(base[i]) >= 3) valid = 0;
        if (valid && popc(J) - slots() <= 0) { rw_hit_any = 1; if (t == rw_r) rw_hit_r = 1; break; }
    }
    snap_load(&sv); slots();
}
static void rw_chain(void) {
    int x = kc[kcl - 1];
    if (Y[x] < 0) return;
    for (int j = 0; j < n && !(rw_hit_r && rw_hit_any); j++) {
        int in = 0; for (int q = 0; q < kcl; q++) if (kc[q] == j) in = 1;
        if (in || !(N_[j] >> Y[x] & 1)) continue;
        kc[kcl++] = j;
        if (frz[j]) rw_chain(); else rw_try_chain();
        kcl--;
    }
}
static void rw_state(int r, int *hr, int *ha) {
    rw_hit_r = rw_hit_any = 0; rw_r = r;
    int fz[MAXN]; memcpy(fz, frz, sizeof fz);
    for (int k = 0; k < n && !(rw_hit_r && rw_hit_any); k++) if (fz[k]) { kc[0] = k; kcl = 1; rw_chain(); }
    *hr = rw_hit_r; *ha = rw_hit_any;
}
/* ends of need chains from k (frozen inner agents; the end is the first agent that is not frozen) */
static uint64_t pm_ends; static int pc[MAXN], pcl;
static void pm_chain_ends(void) {
    int x = pc[pcl - 1];
    if (pcl > 1 && !frz[x]) { pm_ends |= 1ull << x; return; }
    if (Y[x] < 0) return;
    for (int j = 0; j < n; j++) {
        int in = 0; for (int q = 0; q < pcl; q++) if (pc[q] == j) in = 1;
        if (in || !(N_[j] >> Y[x] & 1)) continue;
        pc[pcl++] = j; pm_chain_ends(); pcl--;
    }
}
static uint64_t ends_from(int k) { pm_ends = 0; pc[0] = k; pcl = 1; pm_chain_ends(); return pm_ends; }

/* (G2) on the envy-free run of pre[] */
static int g2_ok, g2_cnt;
static void g2_chains(int r, gm W) {        /* every chain from pc[0] ending at r: is r exposed after the rotation? */
    int x = pc[pcl - 1];
    if (pcl > 1 && !frz[x]) {
        if (x == r) { g2_cnt++; if (!threatened(r, W, BIT(Y[pc[pcl - 2]]))) g2_ok = 0; }
        return;
    }
    if (Y[x] < 0) return;
    for (int j = 0; j < n; j++) {
        int in = 0; for (int q = 0; q < pcl; q++) if (pc[q] == j) in = 1;
        if (in || upg[j] || !(N_[j] >> Y[x] & 1)) continue;
        pc[pcl++] = j; g2_chains(r, W); pcl--;
    }
}
static int g2_run(int *bad_out) {
    *bad_out = 0;
    phase1(); setup_state(); upg_mode = 2; upgrades();
    int S = slots(), w = popc(J) - S;
    if (w <= 0) return 0;
    int r = -1;
    for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    if (frz[r]) return 0;
    gm W = base[r] | J;
    int E[MAXN];
    for (int x = 0; x < n; x++) { E[x] = x != r && !upg[x] && threatened(x, W, base[x]); if (E[x] && d[x] == 4) return 0; }
    int ks = -1;
    for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
    int bad = E[ks] && ks != r && frz[ks];
    if (bad) { nends = 0; ch2[0] = ks; cl2 = 1; chain_ends(); for (int q = 0; q < nends && q < 64; q++) if (ends_[q] != r) bad = 0; if (!nends) bad = 0; }
    if (bad) for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (E[x] && E[y] && (R[x] & R[y] & J)) bad = 0;
    if (!bad) return 0;
    *bad_out = 1;
    if (d[r] != 4) return 0;
    g2_ok = 1; g2_cnt = 0; pc[0] = ks; pcl = 1; g2_chains(r, W);
    return g2_ok && g2_cnt > 0;
}

static void pm_agent(int a) {
    pa_t *p = &PA[a]; memset(p, 0, sizeof *p);
    int dummy, om, fz;
    KONLY = 1;
    for (int pi = 0; pi < npols; pi++) {
        int pol = polv[pi];
        pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
        deficits(pol, &dummy, &dummy, &om, &fz);   /* state left after Phase 1, upgrades of pol and slots() */
        p->om[pi] = om;
        if (fa_dK_tmp <= 0) p->K0 = 1;
        int r = -1;
        for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
        p->r[pi] = r; p->rfz[pi] = r >= 0 ? frz[r] : 1;
        int ks = -1;
        if (r >= 0) for (int i = 0; i < n; i++) if (blk[i] == blk[r] && (ks < 0 || pos[i] < pos[ks])) ks = i;
        p->ks[pi] = ks;
        if (om <= 0) { p->M1[pi] = 1; continue; }
        if (r < 0) continue;
        gm W = base[r] | J;
        int E[MAXN];
        for (int x = 0; x < n; x++) E[x] = x != r && threatened(x, W, base[x]);
        uint64_t x1 = 0, x3 = 0, x3b = 0, x3c = 0;
        for (int x = 0; x < n; x++) if (E[x] && frz[x]) {
            uint64_t e = ends_from(x);
            x3c |= e;
            if (d[x] == 4) { x1 |= 1ull << x; x3 |= e; }
        }
        if (ks >= 0 && ks != r && E[ks] && frz[ks]) x3b = ends_from(ks);
        p->part[pi][0] = x1; p->part[pi][1] = ks >= 0 ? 1ull << ks : 0; p->part[pi][2] = x3;
        p->part[pi][3] = x3b; p->part[pi][4] = x3c; p->part[pi][5] = 1ull << r;
        p->M1[pi] = m1_state(r);
        kr_state(r, &p->KRa[pi], &p->KRb[pi]);
        p->KRo[pi] = p->KRa[pi];
        if (DO_KRO) for (int o = 0; o < n && !p->KRo[pi]; o++) if (o != r) { int ra, rb; kr_state(o, &ra, &rb); if (ra) p->KRo[pi] = 1; }
        rw_state(r, &p->Rw[pi], &p->Rwo[pi]);
    }
    pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
    p->c40 = c40_run();
    pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
    p->g2 = g2_run(&p->g2bad);
    if (!p->K0)
        for (int pi = 0; pi < npols && !p->K1; pi++) {
            pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1;
            if (k1_run(polv[pi])) p->K1 = 1;
        }
    p->W = p->K0 || p->K1;
}
static void pm_leaf(void) {
    for (int a = 0; a < n; a++) BT[a] = bigtop_agent(a);
    for (int a = 0; a < n; a++) { SHT[a] = 0; for (int b = 0; b < n; b++) if (b != a && ord[b][0] == ord[a][0]) SHT[a] = 1; }
    for (int a = 0; a < n; a++) { gm oth = 0; for (int b = 0; b < n; b++) if (b != a) oth |= R[b]; PRIV[a] = popc(R[a] & ~oth); }
    for (int a = 0; a < n; a++) pm_agent(a);
}
static int pm_run_leaf(void) {
    if (setjmp(env)) { stop_at = -1; TAILRULE = 0; KMODE = 0; rot_depth = 0; return 1; }
    pm_leaf();
    return 0;
}

/* ---- statistics ---- */
static long st_app[NCAND], st_fail[NCAND], st_tight[NCAND], st_only[NCAND], st_tot, st_tightM;
static long sv_pairs[NVAR], sv_undef[NVAR], sv_any[NVAR], sv_all[NVAR];
static long st_g2, st_g2W, st_g2bad, st_c40, st_c40notW, st_profc40, st_profnoc40, st_m1notK0, st_krnotW, st_kroNotW;
static long st_K1only, st_wK0, st_wK1, st_wKR, st_wK1noKR, st_wK1noKRRw, st_wK1noKRoRwo;
static int fails_shown[NCAND], xfails_shown[NVAR];

static int predQ(int q, int a) {     /* predicate q on agent a (some policy) */
    pa_t *p = &PA[a];
    int m1 = 0, krb = 0, kra = 0, kro = 0, rw = 0, rwo = 0;
    for (int pi = 0; pi < npols; pi++) { m1 |= p->M1[pi]; krb |= p->KRb[pi]; kra |= p->KRa[pi]; kro |= p->KRo[pi]; rw |= p->Rw[pi]; rwo |= p->Rwo[pi]; }
    switch (q) {
    case 8: return p->K0 || kra || rw;
    case 9: return p->K0 || kro || rwo;
    case 0: return p->W;
    case 1: return p->K0;
    case 2: return m1;
    case 3: return krb;
    case 4: return m1 || krb;
    case 5: return p->K0 || kra;
    case 6: return p->K0 || kro;
    case 7: return p->K0 || krb;
    default: return 0;
    }
}
/* allowed set s (static sets; 5, 6 are per profile); returns 0 if not applicable */
static int allowedS(int s, uint64_t *A) {
    int nbt = 0, q = -1, nsh = 0, pb = 99, ps = 99; uint64_t bt = 0, sh = 0, btp = 0, shp = 0, all = n == 64 ? ~0ull : ((1ull << n) - 1);
    for (int a = 0; a < n; a++) {
        if (BT[a]) { nbt++; q = a; bt |= 1ull << a; if (PRIV[a] < pb) pb = PRIV[a]; }
        if (SHT[a]) { nsh++; sh |= 1ull << a; if (PRIV[a] < ps) ps = PRIV[a]; }
    }
    for (int a = 0; a < n; a++) { if (BT[a] && PRIV[a] == pb) btp |= 1ull << a; if (SHT[a] && PRIV[a] == ps) shp |= 1ull << a; }
    switch (s) {
    case 1: *A = bt; return nbt > 0;
    case 2: *A = q >= 0 ? 1ull << q : 0; return nbt == 1;
    case 3: *A = sh; return nbt == 0 && nsh > 0;
    case 4: *A = all; return nbt == 0 && nsh == 0;
    case 7: *A = btp; return nbt > 0;
    case 8: *A = shp; return nbt == 0 && nsh > 0;
    case 9: *A = bt; return nbt >= 2;
    case 10: *A = sh; return nsh > 0;
    case 11: *A = bt | sh; return nbt > 0 || nsh > 0;
    default: *A = all; return 1;
    }
}
static double gapval(int i, int t, int norm) {
    int v[4] = {0, 0, 0, 0};
    for (int q = 0; q < d[i]; q++) v[q] = tv[i][t][q];
    for (int x = 0; x < 4; x++) for (int y = x + 1; y < 4; y++) if (v[y] > v[x]) { int z = v[x]; v[x] = v[y]; v[y] = z; }
    double g = v[0] - v[1] - v[2];
    if (norm) g /= (double)(v[0] + v[1] + v[2] + v[3]);
    return g;
}
static void print_profile(const int *ty) {   /* ty: type index per agent, or NULL for the leaf representative */
    printf("n=%d m=%d sets=[", n, m);
    for (int i = 0; i < n; i++) { printf("["); for (int k = 0; k < d[i]; k++) printf("%d%s", gl[i][k], k + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : ""); }
    printf("] vals=[");
    for (int i = 0; i < n; i++) {
        int t;
        if (ty) t = ty[i]; else { int k = 0; while (!(ts[i] >> k & 1)) k++; t = pidx[i][cp[i]][k]; }
        printf("["); for (int q = 0; q < d[i]; q++) printf("%d%s", tv[i][t][q], q + 1 < d[i] ? "," : ""); printf("]%s", i + 1 < n ? "," : "");
    }
    printf("]");
}
static void print_fa(void) {
    printf(" fa=");
    for (int a = 0; a < n; a++) {
        pa_t *p = &PA[a];
        printf("%d:K0=%d,K1=%d,bt=%d,sh=%d,c40=%d,g2=%d", a, p->K0, p->K1, BT[a], SHT[a], p->c40, p->g2);
        for (int pi = 0; pi < npols; pi++)
            printf(",%s[om=%d,r=%d,rfz=%d,ks=%d,M1=%d,KRb=%d,KRa=%d,KRo=%d,Rw=%d,Rwo=%d,x1=%llx,x3=%llx]", PNAME[pi], p->om[pi], p->r[pi], p->rfz[pi],
                   p->ks[pi], p->M1[pi], p->KRb[pi], p->KRa[pi], p->KRo[pi], p->Rw[pi], p->Rwo[pi], (unsigned long long)p->part[pi][0], (unsigned long long)p->part[pi][2]);
        printf("%s", a + 1 < n ? ";" : "");
    }
}
/* counts of types in agent j's leaf set with gap < g (lt) or <= g */
static long cnt_gap(int j, double g, int norm, int le) {
    long c = 0;
    for (int k = 0; k < pcnt[j][cp[j]]; k++) if (ts[j] >> k & 1) { double x = gapval(j, pidx[j][cp[j]][k], norm); if (x < g || (le && x == g)) c++; }
    return c;
}
/* returns the number of agents in W (for the hill climb), accumulates statistics with weight w (w = 0: none) */
static int nW_last, cand_nok[NCAND], cand_app[NCAND];
static void pm_stat(long w) {
    int nW = 0, only = -1;
    for (int a = 0; a < n; a++) if (PA[a].W) { nW++; only = a; }
    if (nW != 1) only = -1;
    nW_last = nW;
    if (w) st_tot += w;
    for (int sidx = 5; sidx <= 6; sidx++) {   /* per profile: exact counts over the leaf's type tuples */
        int norm = sidx == 6, c0 = sidx * NPRED;
        long fw[NPRED] = {0}, ow[NPRED] = {0};
        int am = -1; double gm_ = -1e18;
        for (int i = 0; i < n; i++) {
            for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
                double g = gapval(i, pidx[i][cp[i]][k], norm);
                if (g > gm_) { gm_ = g; am = i; }      /* singleton sets: the argmax (ties: lowest index) */
                long prod = 1;
                for (int j = 0; j < n && prod; j++) if (j != i) prod *= cnt_gap(j, g, norm, j > i);
                if (!prod) continue;
                for (int q = 0; q < NPRED; q++) {
                    if (predQ(q, i)) { if (i == only) ow[q] += prod; continue; }
                    fw[q] += prod;
                    if (w && fails_shown[c0 + q] < FAILMAX) {   /* one failing type tuple */
                        int ty[MAXN];
                        for (int j = 0; j < n; j++) {
                            if (j == i) { ty[j] = pidx[i][cp[i]][k]; continue; }
                            for (int kk = 0; kk < pcnt[j][cp[j]]; kk++) if (ts[j] >> kk & 1) {
                                double x = gapval(j, pidx[j][cp[j]][kk], norm);
                                if (x < g || (j > i && x == g)) { ty[j] = pidx[j][cp[j]][kk]; break; }
                            }
                        }
                        fails_shown[c0 + q]++;
                        printf("PFAIL cand=%s w=1 agent=%d ", CNAME[c0 + q], i); print_profile(ty); print_fa(); printf("\n");
                    }
                }
            }
        }
        for (int q = 0; q < NPRED; q++) {
            cand_app[c0 + q] = 1; cand_nok[c0 + q] = am >= 0 && predQ(q, am);
            if (w) { st_app[c0 + q] += w; st_fail[c0 + q] += fw[q]; st_tight[c0 + q] += w - fw[q]; st_only[c0 + q] += ow[q]; }
        }
    }
    for (int c = 0; c < NCAND; c++) {
        int sidx = c / NPRED, q = c % NPRED;
        if (sidx == 5 || sidx == 6) continue;
        uint64_t A; int app = allowedS(sidx, &A);
        cand_app[c] = app;
        int nok = 0, okag = -1;
        for (int a = 0; a < n; a++) if ((A >> a & 1) && predQ(q, a)) { nok++; okag = a; }
        cand_nok[c] = nok;
        if (!w || !app) continue;
        st_app[c] += w;
        if (nok == 0) {
            st_fail[c] += w;
            if (fails_shown[c] < FAILMAX) { fails_shown[c]++; printf("PFAIL cand=%s w=%ld ", CNAME[c], w); print_profile(NULL); print_fa(); printf("\n"); }
        }
        if (nok == 1) { st_tight[c] += w; if (only >= 0 && okag == only) st_only[c] += w; }
    }
    if (!w) return;
    if (nW == 1) st_tightM += w;
    /* exchange partners */
    for (int a = 0; a < n; a++) if (!PA[a].W)
        for (int pi = 0; pi < npols; pi++) for (int k = 0; k < 6; k++) {
            int v = pi * 6 + k;
            uint64_t P = PA[a].part[pi][k] & ~(1ull << a);
            sv_pairs[v] += w;
            if (!P) { sv_undef[v] += w; continue; }
            int any = 0, all = 1;
            for (int b = 0; b < n; b++) if (P >> b & 1) { if (PA[b].W) any = 1; else all = 0; }
            if (any) sv_any[v] += w;
            if (all) sv_all[v] += w;
            if (!any && xfails_shown[v] < FAILMAX) {
                xfails_shown[v]++;
                printf("XFAIL var=%s%s a=%d partners=%llx w=%ld ", VKIND[k], PNAME[pi], a, (unsigned long long)P, w);
                print_profile(NULL); print_fa(); printf("\n");
            }
        }
    /* (G2), C40, consistency of the proved lemmas with the classes */
    int anyc40 = 0;
    for (int a = 0; a < n; a++) {
        pa_t *p = &PA[a];
        if (p->g2bad) st_g2bad += w;
        if (p->g2) { st_g2 += w; if (p->W) st_g2W += w; }
        if (p->c40) { st_c40 += w; anyc40 = 1; if (!p->W) { st_c40notW += w; printf("C40VIOL a=%d ", a); print_profile(NULL); print_fa(); printf("\n"); } }
        int m1 = 0, kra = 0, kro = 0;
        for (int pi = 0; pi < npols; pi++) { m1 |= p->M1[pi]; kra |= p->KRa[pi] | p->KRb[pi]; kro |= p->KRo[pi]; }
        if (m1 && !p->K0) { st_m1notK0 += w; printf("M1VIOL a=%d ", a); print_profile(NULL); print_fa(); printf("\n"); }
        if (kra && !p->W) { st_krnotW += w; printf("KRVIOL a=%d ", a); print_profile(NULL); print_fa(); printf("\n"); }
        if (kro && !p->W) { st_kroNotW += w; printf("KROVIOL a=%d ", a); print_profile(NULL); print_fa(); printf("\n"); }
        { int rwo = 0; for (int pi = 0; pi < npols; pi++) rwo |= p->Rwo[pi]; if (rwo && !p->K0 && !p->K1) { st_kroNotW += w; printf("RWVIOL a=%d ", a); print_profile(NULL); print_fa(); printf("\n"); } }
        if (p->K0) st_wK0 += w;
        else if (p->K1) {
            st_wK1 += w; if (kra) st_wKR += w; else st_wK1noKR += w;
            int ka = 0, rw = 0, ko = 0, rwo = 0;
            for (int pi = 0; pi < npols; pi++) { ka |= p->KRa[pi]; rw |= p->Rw[pi]; ko |= p->KRo[pi]; rwo |= p->Rwo[pi]; }
            if (!ka && !rw) st_wK1noKRRw += w;
            if (!ko && !rwo) st_wK1noKRoRwo += w;
        }
    }
    if (anyc40) st_profc40 += w; else st_profnoc40 += w;
    { int k0 = 0; for (int a = 0; a < n; a++) k0 |= PA[a].K0; if (!k0 && nW) st_K1only += w; }
    if (PMVERB) { printf("PROF w=%ld ", w); print_profile(NULL); print_fa(); printf("\n"); }
}
static void pm_print(void) {
    printf("PM tot %ld tightM %ld K1only %ld", st_tot, st_tightM, st_K1only);
    for (int c = 0; c < NCAND; c++) printf(" %s %ld %ld %ld %ld", CNAME[c], st_app[c], st_fail[c], st_tight[c], st_only[c]);
    for (int v = 0; v < NVAR && v < npols * 6; v++) printf(" %s%s %ld %ld %ld %ld", VKIND[v % 6], PNAME[v / 6], sv_pairs[v], sv_undef[v], sv_any[v], sv_all[v]);
    printf(" g2 %ld g2W %ld g2bad %ld c40 %ld c40notW %ld profc40 %ld profnoc40 %ld m1notK0 %ld krnotW %ld kronotW %ld",
           st_g2, st_g2W, st_g2bad, st_c40, st_c40notW, st_profc40, st_profnoc40, st_m1notK0, st_krnotW, st_kroNotW);
    printf(" wK0 %ld wK1 %ld wK1KR %ld wK1noKR %ld wK1noKRRw %ld wK1noKRoRwo %ld\n", st_wK0, st_wK1, st_wKR, st_wK1noKR, st_wK1noKRRw, st_wK1noKRoRwo);
    memset(st_app, 0, sizeof st_app); memset(st_fail, 0, sizeof st_fail); memset(st_tight, 0, sizeof st_tight);
    memset(st_only, 0, sizeof st_only); st_tot = st_tightM = st_K1only = 0;
    memset(sv_pairs, 0, sizeof sv_pairs); memset(sv_undef, 0, sizeof sv_undef); memset(sv_any, 0, sizeof sv_any); memset(sv_all, 0, sizeof sv_all);
    st_g2 = st_g2W = st_g2bad = st_c40 = st_c40notW = st_profc40 = st_profnoc40 = st_m1notK0 = st_krnotW = st_kroNotW = 0;
    st_wK0 = st_wK1 = st_wKR = st_wK1noKR = st_wK1noKRRw = st_wK1noKRoRwo = 0;
    memset(fails_shown, 0, sizeof fails_shown); memset(xfails_shown, 0, sizeof xfails_shown);
    fflush(stdout);
}

/* ---- hill climbing against one candidate (singleton type sets) ---- */
static int HCAND = 0, HRESTART = 3000; static char *HINIT = NULL;
/* score: lower is tighter; < 0 is a failure */
static long h_score(void) {
    pm_stat(0);
    if (HCAND < 1000) {
        int c = HCAND;
        if (!cand_app[c]) return 100000;
        if (cand_nok[c] == 0) return -1;
        return (long)cand_nok[c] * 64 + nW_last;
    }
    int v = HCAND - 1000, pi = v / 6, k = v % 6;      /* partner variant: some a not in W whose partners all fail */
    long best = 100000;
    for (int a = 0; a < n; a++) if (!PA[a].W) {
        uint64_t P = PA[a].part[pi][k] & ~(1ull << a);
        if (!P) continue;
        int nw = 0; for (int b = 0; b < n; b++) if ((P >> b & 1) && PA[b].W) nw++;
        if (nw == 0) return -1;
        if (nw * 64L < best) best = nw * 64L;
    }
    return best == 100000 ? 1000 + (long)nW_last * 64 : best + nW_last;
}
static void h_print(const char *tag, const int *ty, long sc, long step) {
    printf("%s cand=%s score=%ld step=%ld ", tag, HCAND < 1000 ? CNAME[HCAND] : "partner", sc, step);
    if (HCAND >= 1000) printf("var=%s%s ", VKIND[(HCAND - 1000) % 6], PNAME[(HCAND - 1000) / 6]);
    print_profile(ty); print_fa(); printf("\n"); fflush(stdout);
}
static void hill_core(long steps) {
    uint64_t x = 88172645463325252ull ^ (uint64_t)(n * 131 + m) ^ rng_x;
    for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) x = x * 6364136223846793005ull + (uint64_t)(gl[i][k] + 17 * k + 1);
    #define XR() (x ^= x << 13, x ^= x >> 7, x ^= x << 17, x)
    int ty[MAXN], init[MAXN], hasinit = 0;
    if (HINIT) { char *s = HINIT; for (int i = 0; i < n; i++) { init[i] = (int)strtol(s, &s, 10); if (*s == ',') s++; if (init[i] < 0 || init[i] >= nt[i]) init[i] = 0; } hasinit = 1; }
    long cur = 0, best = 1L << 40, ntight = 0; int shown = 0;
    double T = 0;
    for (long st = 0; st < steps; st++) {
        int restart = st % HRESTART == 0, prev[MAXN];
        memcpy(prev, ty, sizeof prev);
        if (restart) {
            for (int i = 0; i < n; i++) ty[i] = (hasinit && (st == 0 || XR() % 2)) ? init[i] : (int)(XR() % (uint64_t)nt[i]);
            if (hasinit && st > 0) { int i = (int)(XR() % (uint64_t)n); ty[i] = (int)(XR() % (uint64_t)nt[i]); }
            T = 48.0;
        } else {
            int mi = (int)(XR() % (uint64_t)n); ty[mi] = (int)(XR() % (uint64_t)nt[mi]);
            if (XR() % 4 == 0) { int mj = (int)(XR() % (uint64_t)n); if (mj != mi) ty[mj] = (int)(XR() % (uint64_t)nt[mj]); }
        }
        set_types(ty);
        if (pm_run_leaf()) { fprintf(stderr, "split with singleton type sets\n"); exit(1); }
        long sc = h_score();
        if (sc < 0) { h_print("HFAIL", ty, sc, st); return; }
        if (sc < best) best = sc;
        if (sc < 64 + 2 && HCAND < 1000) { ntight++; if (shown < FAILMAX) { h_print("HTIGHT", ty, sc, st); shown++; } }
        if (!restart) {
            double u = (double)(XR() % 1000000) / 1e6;
            if (sc > cur && !(T > 0.01 && u < exp(-(double)(sc - cur) / T))) { memcpy(ty, prev, sizeof prev); T *= 0.9985; continue; }
        }
        cur = sc;
        T *= 0.9985;
    }
    printf("HDONE cand=%s steps=%ld best=%ld tight_hits=%ld\n", HCAND < 1000 ? CNAME[HCAND] : "partner", steps, best, ntight);
    fflush(stdout);
}

int main(int argc, char **argv) {
    long HSTEPS = 0;
    for (int a = 1; a < argc; a++) {
        if (!strncmp(argv[a], "-Y", 2)) XKEEP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-N", 2)) npols = atoi(argv[a] + 2) ? 3 : 2;
        else if (!strncmp(argv[a], "-S", 2)) SAMPLE = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-T", 2)) TAU = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-H", 2)) HSTEPS = atol(argv[a] + 2);
        else if (!strncmp(argv[a], "-c", 2)) HCAND = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-B", 2)) HRESTART = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-I", 2)) HINIT = argv[a] + 2;
        else if (!strncmp(argv[a], "-f", 2)) FAILMAX = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-X", 2)) rng_x ^= (uint64_t)atol(argv[a] + 2) * 0x9E3779B97F4A7C15ull;
        else if (!strncmp(argv[a], "-O", 2)) DO_KRO = atoi(argv[a] + 2);
        else if (!strcmp(argv[a], "-v")) PMVERB = 1;
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 1; }
    }
    if (HRESTART < 1) HRESTART = 1;
    for (int c = 0; c < NCAND; c++) { snprintf(CNAMEbuf[c], sizeof CNAMEbuf[c], "%s:%s", SNAME[c / NPRED], QNAME[c % NPRED]); CNAME[c] = CNAMEbuf[c]; }
    while (scanf("%d %d", &n, &m) == 2) {
        if (n > MAXN || n > 64 || m > MAXM) { fprintf(stderr, "n = %d or m = %d too large\n", n, m); return 1; }
        ALLG = m == 128 ? ~(gm)0 : (BIT(m) - 1);
        for (int i = 0; i < n; i++) {
            if (scanf("%d", &d[i]) != 1) return 3;
            R[i] = 0;
            for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) return 3; R[i] |= BIT(gl[i][k]); }
            if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) return 3;
            for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) return 3;
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
        long leaves = 0, runs = 0;
        if (HSTEPS > 0) { hill_core(HSTEPS); continue; }
        if (TAU > 0) {
            int ty[MAXN];
            for (int i = 0; i < n; i++) { if (nt[i] != 1) { fprintf(stderr, "single-profile mode needs one type per agent\n"); return 1; } ty[i] = 0; }
            set_types(ty);
            if (pm_run_leaf()) { fprintf(stderr, "split with a single type per agent\n"); return 1; }
            pm_stat(1); leaves = runs = 1;
        } else if (SAMPLE > 0) {
            uint64_t x = 88172645463325252ull ^ (uint64_t)(n * 131 + m) ^ rng_x;
            for (int i = 0; i < n; i++) for (int k = 0; k < d[i]; k++) x = x * 6364136223846793005ull + (uint64_t)(gl[i][k] + 17 * k + 1);
            int ty[MAXN];
            for (long s = 0; s < SAMPLE; s++) {
                for (int i = 0; i < n; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; ty[i] = (int)(x % (uint64_t)nt[i]); }
                set_types(ty);
                if (pm_run_leaf()) { fprintf(stderr, "split with singleton type sets\n"); return 1; }
                pm_stat(1); leaves++; runs++;
            }
        } else {                           /* exhaustive: rulef.c's odometer over rankings, DFS over type-set splits */
            int rk[MAXN] = {0};
            for (;;) {
                set_ranks(rk);
                static u128 stack[1 << 11][MAXN]; int top = 0;
                for (int i = 0; i < n; i++) { int c = pcnt[i][cp[i]]; stack[0][i] = c == 128 ? ~(u128)0 : (((u128)1 << c) - 1); }
                top = 1;
                while (top) {
                    top--;
                    for (int i = 0; i < n; i++) ts[i] = stack[top][i];
                    runs++;
                    if (pm_run_leaf()) {
                        u128 part[3] = {0, 0, 0}; int i = sp_i;
                        for (int k = 0; k < pcnt[i][cp[i]]; k++) if (ts[i] >> k & 1) {
                            int t = pidx[i][cp[i]][k], xx = tsum(i, t, sp_S) - tsum(i, t, sp_T);
                            part[(xx > 0) - (xx < 0) + 1] |= (u128)1 << k;
                        }
                        for (int s = 0; s < 3; s++) if (part[s]) {
                            if (top >= (1 << 11)) { fprintf(stderr, "stack overflow\n"); return 1; }
                            for (int j = 0; j < n; j++) stack[top][j] = ts[j];
                            stack[top][i] = part[s]; top++;
                        }
                        continue;
                    }
                    leaves++;
                    pm_stat(weight());
                }
                int i = 0;
                while (i < n && ++rk[i] == np[i]) rk[i++] = 0;
                if (i == n) break;
            }
        }
        printf("PLEAVES leaves %ld runs %ld\n", leaves, runs);
        pm_print();
    }
    return 0;
}
