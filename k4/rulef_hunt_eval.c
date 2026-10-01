/* rulef_hunt_eval.c: batch evaluator of rule RK's classes for every first agent (k4/rulef.md §4), for the adversarial
   search k4/rulef_hunt.py (workstream compute/k4-lemmam-hunt). It #includes k4/rulef.c UNCHANGED (its main renamed)
   and calls only rulef.c's own functions: deficits() (Lemma K, KONLY), k1_run() (one rotation, Lemma K at the rotated
   state), c40_run(), lb4r(), phase1()/setup_state()/upgrades()/slots(), bigtop_agent(). The class test per first agent
   is the one of rulef_leaf41 (mode -A41 -E1): K0 = Lemma K deficit <= 0 (or omega <= 0) after need-shrinking or
   envy-free upgrades (with -N1 also without upgrades); K1 = k1_run under one of those policies. The only difference
   from -A41 -E1 is that K1 is not computed for an agent already in K0 (it is not needed to count K0 ∪ K1).

   Input (stdin), tokens:
     C <core in rulef.c's input format: n m, per agent d g_0 .. g_{d-1} T and T lines of d values>
     P id t_0 .. t_{n-1}     evaluate the profile with type t_i of agent i (fast)
     D id t_0 .. t_{n-1}     the same with every detail (every policy, frozen agents, C4^0, LB4r's fewest rotations)
   Output: one line per P/D:
     R id nwork nK0 mindef sumdef cls=c_0,..  def=d_0,..       c_a: 0 K0, 1 K1, 9 neither; d_a: least Lemma K
                                                                deficit over the policies (-100: omega <= 0; 999: none)
     X id a=<agent> bt=<big-top> kN=.. kE=.. k0=.. (deficits by policy) k1N=.. k1E=.. k10=.. c40=.. rot=.. (LB4r's
       fewest rotations with all three policies, -r bound; bound+1: fails) fzN=.. fzE=.. fz0=.. (frozen agents after
       the upgrades of the policy, bit masks) omN=.. omE=.. om0=.. rN=.. rE=.. (last-processed non-upgraded agent)
     with -K1 also rc=r_0,..: the number of single rotations Lemma K certifies, summed over the policies (capped by
     -cN per policy; -1 for an agent in K0, where it is not computed); rc_a > 0 iff a is in K1.
   Options: -Y1 (kept-out sets of Remark 4), -N1 (RK3: the no-upgrade policy too), -rN (LB4r's bound in D lines),
   -K1 (count rotations), -cN (cap of the count, default 1000), -V1 (check the count against k1_run, exit 5 if not). */
#define main rulef_main
#include "rulef.c"
#undef main

static int frozen_mask(int pol, int *om, int *rr) {
    phase1(); setup_state(); upg_mode = pol; upgrades();
    int S = slots(); *om = popc(J) - S;
    int r = -1; for (int i = 0; i < n; i++) if (!upg[i] && (r < 0 || pos[i] > pos[r])) r = i;
    *rr = r;
    int fm = 0; for (int i = 0; i < n; i++) if (frz[i]) fm |= 1 << i;
    return fm;
}
static void set_first(int a) { pre[0] = a; npre = 1; TAILRULE = 0; stop_at = -1; }
static int kdef(int pol) {           /* Lemma K deficit of the run of tau_a (pre[]) under pol; DNEG if omega <= 0 */
    int dummy, om, fz;
    KONLY = 1; deficits(pol, &dummy, &dummy, &om, &fz); KONLY = 0;
    return fa_dK_tmp;
}

/* the number of single rotations (rulef.c's try_rotations order: frozen k, need chains, every base O, through rulef.c's
   apply_chain with KMODE) that Lemma K certifies, up to rc_cap; k1_count(pol) > 0 iff k1_run(pol). apply_chain
   leaves the rotated state on success, so the state is saved and restored around each call. */
static int rc_count, rc_cap = 1000;
static void ext_chain_cnt(void) {
    int x = chain[clen - 1];
    if (clen > 1 && !frz[x]) {
        int more = 1;
        for (int p = 0; more && rc_count < rc_cap; p++) {
            int sY[MAXN], su[MAXN], sf[MAXN], sc[MAXN]; gm sb[MAXN], sN[MAXN], sJ = J;
            memcpy(sY, Y, sizeof Y); memcpy(su, upg, sizeof upg); memcpy(sb, base, sizeof base); memcpy(sN, N_, sizeof N_);
            memcpy(sf, frz, sizeof frz); memcpy(sc, cap, sizeof cap);
            if (apply_chain(p, &more)) {
                rc_count++;
                memcpy(Y, sY, sizeof Y); memcpy(upg, su, sizeof upg); memcpy(base, sb, sizeof base); memcpy(N_, sN, sizeof N_);
                memcpy(frz, sf, sizeof frz); memcpy(cap, sc, sizeof cap); J = sJ;
            }
        }
        return;
    }
    for (int j = 0; j < n && rc_count < rc_cap; j++) {
        int in = 0; for (int q = 0; q < clen; q++) if (chain[q] == j) in = 1;
        if (in || (upg[j] && !CHUP) || Y[x] < 0 || !(N_[j] >> Y[x] & 1)) continue;
        chain[clen++] = j;
        ext_chain_cnt();
        clen--;
    }
}
static int k1_count(int pol) {       /* the run of pre[] under pol, as k1_run */
    phase1(); setup_state(); upg_mode = pol; upgrades(); slots();
    int sr = rot_cap, sd = rot_depth, su = used_rot;
    KMODE = 1; rot_cap = 1; rot_depth = 0; rc_count = 0;
    int fz[MAXN]; memcpy(fz, frz, sizeof fz);
    for (int p = n - 1; p >= 0 && rc_count < rc_cap; p--) for (int k = 0; k < n; k++) if (pos[k] == p && fz[k]) {
        chain[0] = k; clen = 1;
        ext_chain_cnt();
    }
    KMODE = 0; rot_cap = sr; rot_depth = sd; used_rot = su;
    return rc_count;
}
static int COUNTRC = 0;              /* -K1: K1 by k1_count (every certifying rotation counted, up to -cN), printed as rc= */
static int CHECKRC = 0;              /* -V1: check k1_count(pol) > 0 iff k1_run(pol) on every agent evaluated */

static int load_core(void) {
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n > MAXN || m > MAXM) { fprintf(stderr, "n = %d or m = %d too large\n", n, m); exit(1); }
    ALLG = m == 128 ? ~(gm)0 : (BIT(m) - 1);
    for (int i = 0; i < n; i++) {
        if (scanf("%d", &d[i]) != 1) exit(3);
        R[i] = 0;
        for (int k = 0; k < d[i]; k++) { if (scanf("%d", &gl[i][k]) != 1) exit(3); R[i] |= BIT(gl[i][k]); }
        if (scanf("%d", &nt[i]) != 1 || nt[i] > MAXT) exit(3);
        for (int t = 0; t < nt[i]; t++) for (int k = 0; k < d[i]; k++) if (scanf("%d", &tv[i][t][k]) != 1) exit(3);
        np[i] = 0;                   /* group by tie-broken ranking, as rulef.c's main */
        for (int t = 0; t < nt[i]; t++) {
            int o[4]; for (int k = 0; k < d[i]; k++) o[k] = k;
            for (int a = 0; a < d[i]; a++) for (int b = a + 1; b < d[i]; b++)
                if (tv[i][t][o[b]] > tv[i][t][o[a]] || (tv[i][t][o[b]] == tv[i][t][o[a]] && o[b] < o[a])) { int z = o[a]; o[a] = o[b]; o[b] = z; }
            int p;
            for (p = 0; p < np[i]; p++) if (!memcmp(pr[i][p], o, sizeof(int) * d[i])) break;
            if (p == np[i]) { memcpy(pr[i][p], o, sizeof(int) * d[i]); pcnt[i][p] = 0; np[i]++; }
            if (pcnt[i][p] >= MAXG) { fprintf(stderr, "group too large\n"); exit(1); }
            pidx[i][p][pcnt[i][p]++] = t;
        }
    }
    return 1;
}

static void eval_fast(long id) {
    int cls[MAXN], dm[MAXN], rc[MAXN], nwork = 0, nk0 = 0, mind = DINF, sumd = 0;
    for (int a = 0; a < n; a++) rc[a] = -1;
    if (setjmp(env)) { printf("SPLIT %ld\n", id); fflush(stdout); return; }
    rot_depth = 0;
    for (int a = 0; a < n; a++) {
        set_first(a);
        int kN = kdef(1), best = kN;
        if (best > 0) { set_first(a); int kE = kdef(2); if (kE < best) best = kE; }
        if (best > 0 && NONEPOL) { set_first(a); int k0 = kdef(0); if (k0 < best) best = k0; }
        dm[a] = best;
        if (best <= 0) { cls[a] = 0; nk0++; nwork++; }
        else if (!COUNTRC) {
            set_first(a);
            int k1 = k1_run(1); if (!k1) { set_first(a); k1 = k1_run(2); }
            if (!k1 && NONEPOL) { set_first(a); k1 = k1_run(0); }
            cls[a] = k1 ? 1 : 9; if (k1) nwork++;
        } else {                     /* -K1: count the certifying rotations under every policy */
            int tot = 0;
            for (int q = 0; q < (NONEPOL ? 3 : 2); q++) {
                const int pols[3] = {1, 2, 0};
                set_first(a); int c = k1_count(pols[q]); tot += c;
                if (CHECKRC) { set_first(a); int k = k1_run(pols[q]); if ((c > 0) != (k != 0)) { fprintf(stderr, "RC MISMATCH %ld a=%d pol=%d count=%d k1_run=%d\n", id, a, pols[q], c, k); exit(5); } }
            }
            rc[a] = tot;
            cls[a] = tot ? 1 : 9; if (tot) nwork++;
        }
        if (best < mind) mind = best;
        sumd += best < -3 ? -3 : (best > 12 ? 12 : best);
    }
    printf("R %ld %d %d %d %d cls=", id, nwork, nk0, mind, sumd);
    for (int a = 0; a < n; a++) printf("%d%s", cls[a], a + 1 < n ? "," : "");
    printf(" def=");
    for (int a = 0; a < n; a++) printf("%d%s", dm[a], a + 1 < n ? "," : "");
    if (COUNTRC) { printf(" rc="); for (int a = 0; a < n; a++) printf("%d%s", rc[a], a + 1 < n ? "," : ""); }
    printf("\n"); fflush(stdout);
}

static void eval_detail(long id) {
    if (setjmp(env)) { printf("SPLIT %ld\n", id); fflush(stdout); return; }
    rot_depth = 0;
    for (int a = 0; a < n; a++) {
        int kd[3], k1[3], fm[3], om[3], rr[3];
        const int pols[3] = {1, 2, 0};
        for (int q = 0; q < 3; q++) {
            set_first(a); kd[q] = kdef(pols[q]);
            set_first(a); k1[q] = k1_run(pols[q]);
            set_first(a); fm[q] = frozen_mask(pols[q], &om[q], &rr[q]);
        }
        set_first(a); int c40 = c40_run();
        set_first(a); int ok = lb4r(ROT), rot = ok ? used_rot : ROT + 1;
        printf("X %ld a=%d bt=%d kN=%d kE=%d k0=%d k1N=%d k1E=%d k10=%d c40=%d rot=%d fzN=%d fzE=%d fz0=%d omN=%d omE=%d om0=%d rN=%d rE=%d\n",
               id, a, bigtop_agent(a), kd[0], kd[1], kd[2], k1[0], k1[1], k1[2], c40, rot, fm[0], fm[1], fm[2],
               om[0], om[1], om[2], rr[0], rr[1]);
    }
    fflush(stdout);
}

int main(int argc, char **argv) {
    ROT = 2;
    for (int a = 1; a < argc; a++) {
        if (!strncmp(argv[a], "-Y", 2)) XKEEP = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-N", 2)) NONEPOL = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-r", 2)) ROT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-K", 2)) COUNTRC = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-c", 2)) rc_cap = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-V", 2)) CHECKRC = atoi(argv[a] + 2);
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 1; }
    }
    if (ROT < 0 || ROT > MAXROT) { fprintf(stderr, "-r: 0 .. %d\n", MAXROT); return 1; }
    char cmd[8]; int have = 0;
    while (scanf("%7s", cmd) == 1) {
        if (cmd[0] == 'C') { have = load_core(); if (!have) return 3; continue; }
        if (cmd[0] != 'P' && cmd[0] != 'D') { fprintf(stderr, "bad command %s\n", cmd); return 1; }
        if (!have) { fprintf(stderr, "no core\n"); return 1; }
        long id; int ty[MAXN];
        if (scanf("%ld", &id) != 1) return 3;
        for (int i = 0; i < n; i++) { if (scanf("%d", &ty[i]) != 1 || ty[i] < 0 || ty[i] >= nt[i]) return 3; }
        set_types(ty);
        if (cmd[0] == 'P') eval_fast(id); else eval_detail(id);
    }
    return 0;
}
