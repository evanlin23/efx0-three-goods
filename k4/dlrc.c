/* k4/dlrc.c -- Conjecture DL_RC on data (compute/k4-rc). EVIDENCE only.

A copy of k4/dlrt4.c (compute/k4-rt4, sha256 fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae, unchanged:
the n = 5 DL_RT4 failures cite it) that adds the frozen-chain role swap (T3+) and the key-graph form. Everything dlrt4.c
computes is computed here by dlrt4.c's code, unchanged: its "K" and "L" lines and its B, G, M, Z, C, Y tables are
dlrt4.c's on the same input (k4/dlrc_ref.py compares them), and its "S" line is dlrt4.c's followed by the new fields.

(T3+) the frozen-chain role swap P -> P' (both min-frozen): ch = the agents whose base differs;
  NA' = NA; exactly one agent x of ch is frozen in P and free in P' (U = {x}); exactly one z of ch is free in P and
  frozen in P' (Z = {z}); W = the agents of ch frozen in P and in P'; Y = the agents of ch free in P and in P', |Y| <= 1,
  and each agent of Y gives up a good (B_y \ B'_y nonempty); the bases of W + {z} in P' are exactly the bases of
  W + {x} in P (frozen goods permuted, x out, z in; implied by NA' = NA, tested anyway); and z needs its new good in P
  (B'_z inside N_z(B_z)). With W empty this is dlrt4.c's T3 (T3p / T3h); "T3c" (chain) below is T3+ with W nonempty.
  "T3w" (weak, for information only) is the same without the condition that z needs its new good.
R_C = T1 + T2 + T3+ + T4 = RT4 + T3c. Conjecture DL_RC: at f >= 1, every min-frozen P with def(P) > 0 has an R_C
neighbour P' (min-frozen) with def(P') < def(P). DL_RC at a state: DL_RT4 there, or an improving T3c move.
Every RT4 and R_C move keeps NA (T1, T2 and T3 keep the frozen agents' goods; T3+ and T4 require it).

Key-graph form (k4/dl13.md section 2.3 Remark, proof/k4-dl13): the key of P is kappa(P) = (NA, the frozen agents and
their goods); def*(kappa) = the least deficit of a min-frozen P with key kappa; N(kappa) = the keys reached by one T3+
or T4 move (any move, improving or not) from some state of kappa; kmin(kappa) = min over N(kappa) of def*. DL on the
key graph at a key kappa with def*(kappa) > 0: kmin(kappa) < def*(kappa). At a state P with def(P) > 0 the key form
("R_key", P' with kappa(P') in N(kappa(P)) + {kappa(P)} and def(P') < def(P)) holds iff def*(kappa(P)) < def(P) or
kmin(kappa(P)) < def(P). kmin is computed for the keys with def* > 0 (f >= 1) only; elsewhere it is printed as 999998.
kminw: the same with weak T3+ (T3w) edges added to T3+ and T4. DL_RC at a state with def(P) = def*(kappa(P)) implies the
key form there (an improving R_C move from it is T3+ or T4); a violation is counted ("rcnokey", must be 0).

Per state, besides dlrt4.c's fields: t3c (an improving T3c move), s3c (its least |ch|), wmin (the least |W| of an
improving T3+ move, 0 if a T3 move improves; 99 none), t3w and wminw (the same for weak T3+ moves, T3+ included), rdc
(the least |ch| of an improving R_C move), nrc (the number of improving R_C moves), bestrc (the least deficit of one),
dstar = def*(kappa(P)), kmin, kminw, keyok (the key form holds at P). Consistency: an improving T3+ move with W empty is
exactly an improving T3p / T3h move of dlrt4.c's test; a disagreement is counted ("anomc", must be 0).

Options (besides dlrt4.c's -v -s -rR -oO -SS):
  -H       per evaluated profile a line "H tag p_0 .. p_{n-1} f st1 rt4fail rcfail chain chain3 chainw2 mingap c3 minmv
           keyfail keyfailk maxw" (f: the profile's f, -1 if not evaluated; st1: its def > 0 states (if f >= 1);
           rt4fail / rcfail: those where DL_RT4 / DL_RC fails; chain: those where DL_RT4 fails and DL_RC holds (the only
           repairs are T3c moves); chain3: those with f >= 3; chainw2: those whose least improving |W| is >= 2;
           mingap: the least def(P) - bestrc over the states (0 where DL_RC fails; 999999 if no state); c3: the states
           whose least R_C repair changes >= 3 agents; minmv: the least nrc; keyfail: states where the key form fails;
           keyfailk: keys with def* > 0 where it fails; maxw: the largest wmin over the chain states, 0 if none)
  -s       dlrt4.c's "S" line followed by " t3c s3c wmin t3w wminw rdc nrc bestrc dstar kmin kminw keyok"
Dumps ("D" records): every f >= 1 state where DL_RT4 fails (DL_RC failures and chain states), each with every better
min-frozen P' (at most 400) and its shape (sizes of U, Z, W, Y; NA kept; its R_C kind) and the improving T3c moves (at
most 100: x, z, W, Y, def); the first f >= 1 state of each (signature, R_C branch) cell; -rR / -oO as in dlrt4.c; the
first 5 f = 0 states where RT4 fails. Every record also has "rc" (the R_C branches), "wmin", "dstar", "kmin", "keyok".
Output per block: dlrt4.c's "K" and "L" lines, then
  "LC tag st1 N rcfail N rt4fail N chain N chain3 N t3c N t3w N t3wonly N w0 N w1 N w2 N w3 N cw1 N cw2 N cw3 N
   keyfail N keyfailk N keyfailw N keyspos N rcnokey N anomc N"
  (f >= 1 states: all; DL_RC fails; DL_RT4 fails; chain states; of them with f >= 3; with an improving T3c / T3w move;
  where only a T3w move (no R_C move) improves; by the least improving |W| 0, 1, 2, >= 3; chain states by their least
  |W| 1, 2, >= 3; states where the key form fails; keys with def* > 0 where it fails; states where the weak key form
  fails; keys with def* > 0; DL_RC holding at a deficit-minimal state of its key while the key form fails there (must
  be 0); T3+ / T3 disagreements (must be 0)),
  then dlrt4.c's tables, then "W f|rc branch|wmin count" (f >= 1 states by R_C branch and least improving |W|; branches
  T1, T2, T3p, T3h, T4, T3c joined by "+", "none" if DL_RC fails).

For large classes (more than BIGPP min-frozen P) the candidates of P are dlrt4.c's RT4 candidates together with every P'
with the same NA and a smaller deficit (a superset of the improving R_C moves: every R_C move keeps NA). The key graph
scans, for each state of a key with def* > 0, the states with the same NA by increasing def* of their key. A -DBIGPP=0
build gives the same output (k4/dlrc_ref.py compares it).

The rest of this header is dlrt4.c's.

--- dlrt4.c's header: k4/dlrt4.c -- Conjecture DL_RT4 on data (compute/k4-rt4). EVIDENCE only.

A copy of k4/dl13.c (compute/k4-dl13; itself a copy of k4/dl2.c with the R_13 test), which stays unchanged (the ledger
and results/k4_dl13/ cite it by SHA-256), with the R_13 test replaced by the RT4 test. The min-frozen class, def(P), the
distance pass, the obstruction signature and the Pareto flag are dl13.c's (= dl2.c's) code, so the "K" line here is
dl13.c's "K" line on the same input (k4/dlrt4_ref.py compares them).

Objects (dl2.c's header has the details): for one strict profile, P ranges over the valid pre-allocations with the
fewest frozen agents f (the min-frozen class); def(P) is the removal-only deficit (+inf when every agent is frozen);
only profiles with omega = f - (2n - m) >= 1 are evaluated. A *state* is a min-frozen P with def(P) > 0.

RT4 = T1 + T2 + T3 + T4, i.e. R_T of k4/dl2.md section 3 (code "RTr" of k4/dl2_relations.py) plus T4. For min-frozen P,
P' let ch be the agents whose base differs, NA, NA' the needed sets, and "nt" mean that some agent outside ch changes its
frozen status (frozen = a one-good base inside the needed set). RT4(P, P') holds iff one of
  (T1) |ch| = 1 and not nt (one agent y re-bases keeping the needed set; y is free in P and in P' by Lemma 1(a) of
       k4/dl2.md; a violation is counted as an anomaly, "anom", and still counted as T1, as dl13.c and
       k4/dl2_relations.py do);
  (T2) |ch| >= 2, every agent of ch free in P and in P', and not nt (a rotation of free agents: any re-partition of
       J + their bases, NA kept; RTr's second clause);
  (T3) not nt; among ch exactly one x is frozen in P and free in P' (B_x = {g}), exactly one z is free in P and frozen
       in P', none is frozen in both, at most one h (the helper) is free in both; B'_z = {g}; g in N_z(B_z); and the
       helper gives up a good (B_h \ B'_h nonempty) -- dl13.c's T3, unchanged ("T3p" without, "T3h" with a helper);
  (T4) |ch| >= 2, every agent of ch frozen in P and in P', and NA' = NA: the agents of ch permute their singleton bases
       (then automatically: every other base unchanged, the frozen set and the needed set kept). Any permutation is
       allowed; its cycle type (the cycle lengths, e.g. "2", "3", "2+2") is recorded. A move with every agent of ch
       frozen in both but NA' != NA is not T4 (it is not a permutation of the frozen goods).
These four are disjoint. DL_RT4 at a state P: some min-frozen P' with def(P') < def(P) and RT4(P, P'). DL_RT4 (the
conjecture) is about the profiles with f >= 1; f = 0 states are evaluated too and counted apart (at f = 0 every pair of
min-frozen P is a T1/T2 move, and Theorem Z covers them).

Per state: the branches that hold (some improving move of that kind): "T1", "T2", "T3p", "T3h", "T4", joined by "+"
("none" = DL_RT4 fails at P); per branch the least |ch| of an improving move of that kind, and rd = the least |ch| of
any improving RT4 move (the smallest move size). Move types:
  T1: "rel" (B'_y strictly inside B_y), "grow" (B_y strictly inside B'_y), "pool" (otherwise);
  T2: "k2", "k3", ... (|ch|);
  T3: x's new base inside J ("xJ"), inside J + B_z and not J ("xZ"), or using a good of B_h ("xH"); the helper: none
      ("h-"), a pure release ("hR"), a swap with the pool ("hJ"), or taking a good of B_z ("hZ") (dl13.c's types);
  T4: the cycle type of the permutation ("2", "3", "2+2", "4", ...; parts in decreasing order).
  The witness of a state: among its improving RT4 moves, the one with the smallest def(P'), then the fewest moved goods
  (sum of |B_i xor B'_i|), then the first in the enumeration order of P.

Input (stdin): dl2.c's blocks (k4/gap.c's format): "n m tag" / n lines "d g1 .. gd" / "K_0 .. K_{n-1}" / per agent K_i
lines of d values / "P" and, if P < 0, -P lines of n domain indices. P = 0: every profile; P > 0: P random profiles
(seeded by -S and tag, the same stream as dl2.c and dl13.c); P < 0: the listed profiles.
Options:
  -v       per evaluated profile dl2.c's line "V tag p_0 .. p_{n-1} kstar nmin npos mindef"
  -s       with -v: per state "S f b_0 .. b_{n-1} def dist rd t1 t2 t3p t3h t4 s2 s3p s3h s4 t1mask t2mask t3mask
           t4cyc t4cycmin dW pm sig" (b_i: masks of the goods; def, dW 999999 = inf; dist, rd, s* 99 = none; s2, s3p,
           s3h, s4: the least |ch| of an improving T2 / T3p / T3h / T4 move; t1mask: bit k = T1 type k (rel, grow,
           pool); t2mask: bit c = a T2 move with |ch| = c; t3mask: bit 4 * xs + hk as in dl13.c; t4cyc: the cycle types
           of the improving T4 moves, t4cycmin: those of the improving T4 moves with |ch| = s4, comma-separated, "-" if
           none; dW: def of the witness)
  -rR      dump (as "D {json}") every R-th f >= 1 state that needs a branch outside R_13 (DL_RT4 holds, no T1 or T3 move),
           counted over the whole process (the 1st, (R+1)-th, ...; R = 0: none)
  -oO      the same for the other f >= 1 states at which DL_RT4 holds, O = 0: none
           Besides these, every f >= 1 state at which DL_RT4 fails, the first f >= 1 state of each (signature, branch)
           cell and the first 5 f = 0 states at which RT4 fails are dumped (per process).
  -SS      seed for P > 0.
Output per block: dl2.c's "K ..." counters, then
  "L tag st0 N st1 N fail0 N fail1 N t1 N t2 N t3p N t3h N t4 N t1only N t2only N t3only N t4only N rtfail N r13fail N
   r134fail N anom N anom4 N rdnone N rd1 N rd2 N rd3 N rd4 N"
  (states with f = 0 / f >= 1; DL_RT4 failures with f = 0 / f >= 1; among the f >= 1 states: with an improving T1 /
  T2 / T3p / T3h / T4 move; with T1 / T2 / T3 (p or h) / T4 as the only branch; at which R_T = T1 + T2 + T3, R_13 =
  T1 + T3, R_134 = T1 + T3 + T4 has no improving move; anomalies (T1 with a frozen agent; a T4 candidate that is not a
  permutation, impossible); by the least size rd of an improving RT4 move: none, 1, 2, 3, >= 4),
  then the tables (f >= 1 states only; f is the profile's f):
  "B f|sig|branch count"       states by signature and branch,
  "G f|k|branch count"         states by the nearest distance k (any move, dl2.c's k(P)) and branch,
  "M f|branch|rd count"        states by branch and the least size rd of an improving RT4 move,
  "Z f|T|s count"              per branch T available at a state, the least size s of an improving T move,
  "C f|s4|cycles count"        states with T4, by the least T4 size and the cycle types of the T4 moves of that size,
  "Y f|branch|type count"      states by branch, counted once for each move type available among their improving
                               RT4 moves.
Build: gcc -O2 k4/dlrt4.c (m <= 32, n <= 16); -DWIDE for m <= 64. With more than BIGPP (3000) min-frozen P the
candidates are generated (dl13.c's T1 and T3 candidates; for T2 every P with the same frozen agents and frozen goods; for
T4 every P with the same frozen agents, needed set and free agents' bases) and looked up in the class; otherwise every
min-frozen P is scanned. Both give the same output (k4/dlrt4_ref.py compares a -DBIGPP=0 build).  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
#define INF 999999
#ifdef WIDE                                         /* 64-bit masks: m <= 64 (H_3 has m = 33) */
#define MAXM 64
typedef uint64_t msk;
#define pc(x) __builtin_popcountll(x)
#define ctz(x) __builtin_ctzll(x)
#else
#define MAXM 32
typedef uint32_t msk;
#define pc(x) __builtin_popcount(x)
#define ctz(x) __builtin_ctz(x)
#endif
#define BIT(g) ((msk)1 << (g))

static int n, m, tag;
static int deg[MAXN], R[MAXN][4];
static msk Rm[MAXN], ALL;
static int K[MAXN], *dom[MAXN];
static int v[MAXN][MAXM], cur[MAXN];
static int VERB = 0, SVERB = 0, HVERB = 0, RT = 0, RO = 0; static uint64_t SEED = 1;


/* per agent: subset tables over the positions of its goods */
static int ssum[MAXN][16], smin[MAXN][16];
static int topg[MAXN], bigtop[MAXN], rk[MAXN][4];   /* rk: goods by decreasing value */
static inline int sidx(int i, msk X) { int s = 0; for (int k = 0; k < deg[i]; k++) if (X >> R[i][k] & 1) s |= 1 << k; return s; }
static inline int val(int i, msk X) { return ssum[i][sidx(i, X)]; }
/* X threatens i holding a bundle of value h: max over h' in X of v_i(X \ h') > h */
static inline int threat(int i, msk X, int h) {
    if (!X) return 0;
    int s = sidx(i, X);
    if (X & ~Rm[i]) return ssum[i][s] > h;           /* a good of X outside R_i is worth 0: remove it */
    return ssum[i][s] - smin[i][s] > h;
}
static inline msk needs(int i, msk X) {
    int b = val(i, X); msk N = 0;
    for (int k = 0; k < deg[i]; k++) { int g = R[i][k]; if (!(X >> g & 1) && v[i][g] > b) N |= BIT(g); }
    return N;
}

/* ---------- the min-frozen pre-allocations (dl2.c) ---------- */
static msk opt[MAXN][11], optN[MAXN][11]; static int optv[MAXN][11], nopt[MAXN];
static int bestf, sigma;
static unsigned char cidx[MAXN];
static unsigned char *PP = 0; static long npp = 0, capp = 0;

static int found_small;
static void dfs_small(int i, msk used, msk NA, msk S1, msk S2) {   /* is there a valid P with |NA| <= sigma? */
    if (found_small || pc(NA) > sigma || (NA & S2)) return;
    if (i == n) { if (!(NA & ~S1)) found_small = 1; return; }
    for (int t = 0; t < nopt[i] && !found_small; t++) { msk B = opt[i][t]; if (B & used) continue;
        dfs_small(i + 1, used | B, NA | optN[i][t], pc(B) == 1 ? S1 | B : S1, pc(B) == 2 ? S2 | B : S2); }
}
static void dfsP(int i, msk used, msk NA, msk S1, msk S2) {
    if (pc(NA) > bestf || (NA & S2)) return;        /* (V2): a needed good in a pair base stays there */
    if (i == n) {
        if (NA & ~S1) return;                        /* (V1)+(V2): every needed good is a one-good base */
        int f = pc(NA);
        if (f < bestf) { bestf = f; npp = 0; }
        if (npp == capp) { capp = capp ? 2 * capp : 1024; PP = realloc(PP, capp * MAXN); if (!PP) { fprintf(stderr, "oom\n"); exit(2); } }
        memcpy(PP + npp * MAXN, cidx, MAXN); npp++;
        return;
    }
    for (int t = 0; t < nopt[i]; t++) { msk B = opt[i][t]; if (B & used) continue;
        cidx[i] = (unsigned char)t;
        dfsP(i + 1, used | B, NA | optN[i][t], pc(B) == 1 ? S1 | B : S1, pc(B) == 2 ? S2 | B : S2); }
}

/* ---------- per P: deficit, owners, exposures (dl2.c) ---------- */
typedef struct {
    int def;                 /* INF = +inf */
    int bestown[MAXN];       /* per owner: least |C| - S_o(C) (INF if o frozen or no safe bundle) */
    msk frozen, J, NA;
    msk expo[MAXN];          /* agents exposed w.r.t. free owner o */
} pinfo_t;
static pinfo_t *PI = 0; static long capi = 0;

static void eval_P(const unsigned char *ix, pinfo_t *pi) {
    msk B[MAXN], N[MAXN], NA = 0, U = 0; int hv[MAXN];
    for (int i = 0; i < n; i++) { B[i] = opt[i][ix[i]]; N[i] = optN[i][ix[i]]; hv[i] = optv[i][ix[i]]; NA |= N[i]; U |= B[i]; }
    msk J = ALL & ~U, F = 0; int S = 0;
    for (int i = 0; i < n; i++) { if (pc(B[i]) == 1 && (B[i] & NA)) F |= BIT(i); else S += 2 - pc(B[i]); }
    pi->frozen = F; pi->J = J; pi->NA = NA;
    for (int o = 0; o < n; o++) { pi->bestown[o] = INF; pi->expo[o] = 0; }
    if (pc(J) <= S) { pi->def = pc(J) - S; return; }
    int best = INF;
    for (int o = 0; o < n; o++) {
        if (F >> o & 1) continue;
        msk NAo = 0; for (int j = 0; j < n; j++) if (j != o) NAo |= N[j];
        msk Wo = B[o] | J;
        for (int x = 0; x < n; x++) if (x != o && threat(x, Wo, hv[x])) pi->expo[o] |= BIT(x);
        int bo = INF;
        msk C = J;                                       /* every C inside J (removed junk) */
        for (;;) {
            msk X = B[o] | (J & ~C); int ok = 1;
            for (int x = 0; x < n && ok; x++) if (x != o && (pi->expo[o] >> x & 1) && threat(x, X, hv[x])) ok = 0;
            if (ok) {
                msk NA2 = NAo | needs(o, X);
                int sl = 0;
                for (int j = 0; j < n; j++) if (j != o) sl += (pc(B[j]) == 1 && (B[j] & NA2)) ? 0 : 2 - pc(B[j]);
                int d = pc(C) - sl;
                if (d < bo) bo = d;
            }
            if (!C) break;
            C = (C - 1) & J;
        }
        pi->bestown[o] = bo;
        if (bo < best) best = bo;
    }
    pi->def = best;
}

/* chain ends of frozen x: free agents reached from x by need edges (w needs the good of the current agent) */
static msk chain_ends(const unsigned char *ix, int x, msk F) {
    msk N[MAXN]; for (int i = 0; i < n; i++) N[i] = optN[i][ix[i]];
    msk seen = BIT(x), fr = BIT(x), ends = 0;
    while (fr) {
        int y = ctz(fr); fr &= fr - 1;
        msk g = opt[y][ix[y]];
        for (int w = 0; w < n; w++) if ((N[w] & g) && !(seen >> w & 1)) { seen |= BIT(w); if (F >> w & 1) fr |= BIT(w); else ends |= BIT(w); }
    }
    return ends;
}

enum { C_E1, C_E2, C_E3, C_FO, C_G, C_G1, C_L, C_O, C_D2, C_ALLF, C_PM, NCLS };
static const char *CLSNAME[NCLS] = {"e1", "e2", "e3", "fO", "G", "G1", "L", "O", "D2", "allfrozen", "PM"};

static int classify(const unsigned char *ix, const pinfo_t *pi, int x, int o) {
    msk Bx = opt[x][ix[x]], Bo = opt[o][ix[o]], J = pi->J;
    if (!(pi->frozen >> x & 1)) {
        if (pc(Bx) == 1 && !(Rm[x] & J) && pc(Bo) == 2 && !(Bo & ~(Rm[x] & ~Bx))) return C_E1;
        if (deg[x] == 4 && pc(Bx) == 2) {
            int a = rk[x][0], b = rk[x][1], c = rk[x][2], d = rk[x][3];
            if (Bx == (BIT(b) | BIT(c)) && (Bo >> a & 1) && (J >> d & 1) && v[x][a] + v[x][d] > v[x][b] + v[x][c]) return C_E2;
            if (!(Rm[x] & J) && (Rm[x] & ~Bx) == Bo) return C_E3;
        }
        return C_FO;
    }
    int g = ctz(Bx);
    msk JR = J & Rm[x];
    if (pc(JR) >= 2 && val(x, JR) > v[x][g]) return C_G;
    msk ends = chain_ends(ix, x, pi->frozen);
    if (ends >> o & 1) {
        if (bigtop[x] && g == topg[x] && !((Rm[x] & ~Bx) & ~(J | Bo))) return C_G1;
        return C_O;
    }
    return C_L;
}

/* ---------- a tiny string -> count map (dl2.c) ---------- */
typedef struct { char *k; long c; } kv_t;
typedef struct { kv_t *t; long cap, cnt; } map_t;
static uint64_t hstr(const char *s) { uint64_t h = 1469598103934665603ull; while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ull; } return h; }
static long *mslot(map_t *M, const char *k) {       /* the counter of k (created at 0) */
    if (M->cnt * 2 >= M->cap) {
        long oc = M->cap; kv_t *o = M->t; M->cap = M->cap ? 2 * M->cap : 1024; M->t = calloc(M->cap, sizeof(kv_t)); M->cnt = 0;
        for (long i = 0; i < oc; i++) if (o[i].k) { uint64_t h = hstr(o[i].k) & (M->cap - 1); while (M->t[h].k) h = (h + 1) & (M->cap - 1); M->t[h] = o[i]; M->cnt++; }
        free(o);
    }
    uint64_t h = hstr(k) & (M->cap - 1);
    while (M->t[h].k) { if (!strcmp(M->t[h].k, k)) return &M->t[h].c; h = (h + 1) & (M->cap - 1); }
    M->t[h].k = strdup(k); M->t[h].c = 0; M->cnt++;
    return &M->t[h].c;
}
static void mclear(map_t *M) { for (long i = 0; i < M->cap; i++) if (M->t[i].k) { free(M->t[i].k); M->t[i].k = 0; } M->cnt = 0; }
static map_t TAB = {0, 0, 0};        /* per block: the B, G, Y tables */
static map_t SEEN = {0, 0, 0};       /* per process: the (signature, branch) cells already dumped */
static map_t SEENC = {0, 0, 0};      /* per process: the (signature, R_C branch) cells already dumped (dlrc.c) */

/* ---------- neighbours by hashing (large classes; dl2.c) ---------- */
#ifndef BIGPP
#define BIGPP 3000                                  /* above this many min-frozen P, use the hash */
#endif
static uint64_t *HK = 0; static long *HV = 0; static long hsz = 0;
static uint64_t pkey(const unsigned char *ix) { uint64_t k = 0; for (int i = 0; i < n; i++) k |= (uint64_t)ix[i] << (4 * i); return k; }
static uint64_t hmix(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdull; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ull; k ^= k >> 33; return k; }
static void hbuild(void) {
    long need = 4; while (need < 2 * npp) need <<= 1;
    if (need > hsz) { hsz = need; HK = realloc(HK, sizeof(uint64_t) * hsz); HV = realloc(HV, sizeof(long) * hsz); }
    for (long i = 0; i < hsz; i++) HV[i] = -1;
    for (long p = 0; p < npp; p++) {
        uint64_t k = pkey(PP + p * MAXN), h = hmix(k) & (hsz - 1);
        while (HV[h] >= 0) h = (h + 1) & (hsz - 1);
        HK[h] = k; HV[h] = p;
    }
}
static long hfind(uint64_t k) {
    uint64_t h = hmix(k) & (hsz - 1);
    while (HV[h] >= 0) { if (HK[h] == k) return HV[h]; h = (h + 1) & (hsz - 1); }
    return -1;
}
static long *cand = 0; static long capc = 0, ncand;
static void cpush(long q) { if (ncand == capc) { capc = capc ? 2 * capc : 1024; cand = realloc(cand, sizeof(long) * capc); } cand[ncand++] = q; }
/* the candidates P' for P = PP[p]: every other min-frozen P (all = 1 or a small class), else those within distance 2 */
static void fill_cand(long p, int all) {
    ncand = 0;
    if (all || npp <= BIGPP) { for (long q = 0; q < npp; q++) if (q != p) cpush(q); return; }
    unsigned char ix[MAXN]; memcpy(ix, PP + p * MAXN, MAXN);
    for (int i = 0; i < n; i++) {
        int ti = ix[i];
        for (int t = 0; t < nopt[i]; t++) if (t != ti) {
            ix[i] = (unsigned char)t; long q = hfind(pkey(ix)); if (q >= 0) cpush(q);
            for (int j = i + 1; j < n; j++) {
                int tj = ix[j];
                for (int u = 0; u < nopt[j]; u++) if (u != tj) { ix[j] = (unsigned char)u; long q2 = hfind(pkey(ix)); if (q2 >= 0) cpush(q2); }
                ix[j] = (unsigned char)tj;
            }
        }
        ix[i] = (unsigned char)ti;
    }
}
/* candidates without repeats (large classes): a stamp per P */
static long *stamp = 0, capst = 0, curst = 0;
static void cpush_u(long q) { if (stamp[q] != curst) { stamp[q] = curst; cpush(q); } }
/* T2 / T4 groups (large classes): P sorted by (key, NA); for T2 the key keeps the frozen agents' bases (free agents ->
   15), for T4 the free agents' bases (frozen agents -> 15; nopt <= 11, so 15 marks the other part) and NA is compared */
typedef struct { uint64_t k; msk na; long p; } gk_t;
static gk_t *GK2 = 0, *GK4 = 0; static long capgk = 0;
static int gkcmp(const void *a, const void *b) {
    const gk_t *x = a, *y = b;
    if (x->k != y->k) return x->k < y->k ? -1 : 1;
    if (x->na != y->na) return x->na < y->na ? -1 : 1;
    return (x->p > y->p) - (x->p < y->p);
}
static uint64_t pkey_part(const unsigned char *ix, msk F, int frozen_part) {
    uint64_t k = 0;
    for (int i = 0; i < n; i++) { int fr = (int)(F >> i & 1); uint64_t t = fr == frozen_part ? ix[i] : 15; k |= t << (4 * i); }
    return k;
}
static void gbuild(void) {
    if (npp > capgk) {
        capgk = npp; GK2 = realloc(GK2, capgk * sizeof(gk_t)); GK4 = realloc(GK4, capgk * sizeof(gk_t));
        if (!GK2 || !GK4) { fprintf(stderr, "oom\n"); exit(2); }
    }
    if (npp > capst) { capst = npp; stamp = realloc(stamp, capst * sizeof(long)); if (!stamp) { fprintf(stderr, "oom\n"); exit(2); } }
    for (long p = 0; p < npp; p++) {
        const unsigned char *ix = PP + p * MAXN; msk F = PI[p].frozen;
        GK2[p].k = pkey_part(ix, F, 1); GK2[p].na = 0; GK2[p].p = p;
        GK4[p].k = pkey_part(ix, F, 0); GK4[p].na = PI[p].NA; GK4[p].p = p;
        stamp[p] = -1;
    }
    qsort(GK2, npp, sizeof(gk_t), gkcmp); qsort(GK4, npp, sizeof(gk_t), gkcmp);
}
static void gpush(const gk_t *G, uint64_t k, msk na) {
    long lo = 0, hi = npp;
    while (lo < hi) { long mid = (lo + hi) / 2; if (G[mid].k < k || (G[mid].k == k && G[mid].na < na)) lo = mid + 1; else hi = mid; }
    for (long i = lo; i < npp && G[i].k == k && G[i].na == na; i++) cpush_u(G[i].p);
}
/* the RT4 candidates for P = PP[p] in a large class: dl13.c's R_13 candidates (one agent re-based; or a frozen x, a
   free z needing x's good taking it, x any other base, and at most one further agent any other base), every P' of p's
   T2 group and every P' of p's T4 group (a superset of the RT4 moves; rt4() decides) */
static void fill_candrt4(long p) {
    ncand = 0; curst = p;
    stamp[p] = p;                                       /* never P itself */
    unsigned char ix[MAXN]; memcpy(ix, PP + p * MAXN, MAXN);
    msk F = PI[p].frozen;
    for (int i = 0; i < n; i++) {
        int ti = ix[i];
        for (int t = 0; t < nopt[i]; t++) if (t != ti) { ix[i] = (unsigned char)t; long q = hfind(pkey(ix)); if (q >= 0) cpush_u(q); }
        ix[i] = (unsigned char)ti;
    }
    for (int x = 0; x < n; x++) {
        if (!(F >> x & 1)) continue;
        msk g = opt[x][ix[x]]; int tx0 = ix[x];
        for (int z = 0; z < n; z++) {
            if (z == x || (F >> z & 1) || !(optN[z][ix[z]] & g)) continue;
            int tz0 = ix[z], tz = -1;
            for (int t = 0; t < nopt[z]; t++) if (opt[z][t] == g) tz = t;
            if (tz < 0) continue;
            ix[z] = (unsigned char)tz;
            for (int tx = 0; tx < nopt[x]; tx++) if (tx != tx0) {
                ix[x] = (unsigned char)tx;
                long q = hfind(pkey(ix)); if (q >= 0) cpush_u(q);
                for (int h = 0; h < n; h++) {
                    if (h == x || h == z) continue;
                    int th0 = ix[h];
                    for (int t = 0; t < nopt[h]; t++) if (t != th0) { ix[h] = (unsigned char)t; long q2 = hfind(pkey(ix)); if (q2 >= 0) cpush_u(q2); }
                    ix[h] = (unsigned char)th0;
                }
            }
            ix[x] = (unsigned char)tx0; ix[z] = (unsigned char)tz0;
        }
    }
    const unsigned char *ip = PP + p * MAXN;
    gpush(GK2, pkey_part(ip, F, 1), 0);
    gpush(GK4, pkey_part(ip, F, 0), PI[p].NA);
}

/* ---------- the RT4 test ---------- */
static long ANOM, ANOM4;
/* the cycle code of a T4 permutation: its cycle lengths in decreasing order, 5 bits each, the longest in the lowest bits */
static uint64_t cyc_code(int *len, int k) {
    for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) if (len[b] > len[a]) { int t = len[a]; len[a] = len[b]; len[b] = t; }
    uint64_t c = 0; for (int a = 0; a < k; a++) c |= (uint64_t)len[a] << (5 * a);
    return c;
}
static void cyc_str(uint64_t c, char *s) { s[0] = 0; while (c) { char b[8]; snprintf(b, sizeof b, s[0] ? "+%d" : "%d", (int)(c & 31)); strcat(s, b); c >>= 5; } }
/* RT4(P, P') for P = PP[a], P' = PP[b]: 0 (not), 1 (T1), 2 (T2), 3 (T3 without helper), 4 (T3 with a helper), 5 (T4);
   *ty: the type (T1: 0 rel, 1 grow, 2 pool; T2: |ch|; T3: 4 * xs + hk, xs 0 xJ / 1 xZ / 2 xH, hk 0 h- / 1 hR / 2 hJ /
   3 hZ; T4: the cycle code) */
static int rt4(long a, long b, uint64_t *ty) {
    const unsigned char *ia = PP + a * MAXN, *ib = PP + b * MAXN;
    msk Fa = PI[a].frozen, Fb = PI[b].frozen;
    msk ch = 0;
    for (int i = 0; i < n; i++) if (ia[i] != ib[i]) ch |= BIT(i);
    if (!ch) return 0;
    int nch = pc(ch);
    if (nch >= 2 && !(ch & ~(Fa & Fb))) {                  /* every changed agent frozen in P and in P' */
        if (PI[a].NA != PI[b].NA) return 0;                 /* not T4, and no other kind either */
        int to[MAXN], len[MAXN], k = 0;                    /* to[i]: the agent whose good of P agent i holds in P' */
        for (int i = 0; i < n; i++) if (ch >> i & 1) {
            msk g2 = opt[i][ib[i]]; to[i] = -1;
            for (int j = 0; j < n; j++) if ((ch >> j & 1) && opt[j][ia[j]] == g2) to[i] = j;
            if (to[i] < 0) { ANOM4++; return 0; }          /* impossible: NA' = NA forces a permutation */
        }
        msk seen = 0;
        for (int i = 0; i < n; i++) if ((ch >> i & 1) && !(seen >> i & 1)) {
            int l = 0, j = i;
            while (!(seen >> j & 1)) { seen |= BIT(j); l++; j = to[j]; }
            if (j != i) { ANOM4++; return 0; }             /* not a permutation */
            len[k++] = l;
        }
        *ty = cyc_code(len, k);
        return 5;
    }
    if ((Fa ^ Fb) & ~ch) return 0;                          /* nt: an unchanged agent changes its frozen status */
    if (nch == 1) {
        int y = ctz(ch);
        if ((Fa | Fb) >> y & 1) ANOM++;                    /* impossible by Lemma 1(a) */
        msk B = opt[y][ia[y]], B2 = opt[y][ib[y]];
        *ty = !(B2 & ~B) ? 0 : !(B & ~B2) ? 1 : 2;
        return 1;
    }
    if (!(ch & (Fa | Fb))) { *ty = (uint64_t)nch; return 2; }   /* T2: every changed agent free in P and in P' */
    msk U = ch & Fa & ~Fb, Z = ch & ~Fa & Fb, W = ch & Fa & Fb, Y = ch & ~Fa & ~Fb;
    if (pc(U) != 1 || pc(Z) != 1 || W || pc(Y) > 1) return 0;
    int x = ctz(U), z = ctz(Z);
    msk g = opt[x][ia[x]];
    if (opt[z][ib[z]] != g) return 0;                       /* z takes x's good */
    if (!(optN[z][ia[z]] & g)) return 0;                    /* z needs it in P */
    msk J = PI[a].J, Bz = opt[z][ia[z]], Bx2 = opt[x][ib[x]];
    int hk = 0, h = -1;
    if (Y) {
        h = ctz(Y);
        msk Bh = opt[h][ia[h]], Bh2 = opt[h][ib[h]];
        if (!(Bh & ~Bh2)) return 0;                         /* the helper gives up a good of its base */
        hk = !(Bh2 & ~Bh) ? 1 : !(Bh2 & ~(Bh | J)) ? 2 : 3;
    }
    int xs = !(Bx2 & ~J) ? 0 : !(Bx2 & ~(J | Bz)) ? 1 : 2;
    *ty = (uint64_t)(4 * xs + hk);
    return Y ? 4 : 3;
}
static const char *KNAME[6] = {"none", "T1", "T2", "T3p", "T3h", "T4"};

/* ---------- the T3+ test (dlrc.c) ---------- */
static msk XU, XZ, XW, XY;                                  /* the sets U, Z, W, Y of the last t3x() call */
static long ANOMC;
/* T3+(P, P') for P = PP[a], P' = PP[b], written from the definition (header): 0 (not), 1 (the T3+ shape but z does not
   need its new good in P: weak only), 2 (T3+); *wn = |W| */
static int t3x(long a, long b, int *wn) {
    const unsigned char *ia = PP + a * MAXN, *ib = PP + b * MAXN;
    if (PI[a].NA != PI[b].NA) return 0;
    msk Fa = PI[a].frozen, Fb = PI[b].frozen, ch = 0;
    for (int i = 0; i < n; i++) if (ia[i] != ib[i]) ch |= BIT(i);
    msk U = ch & Fa & ~Fb, Z = ch & ~Fa & Fb, W = ch & Fa & Fb, Y = ch & ~Fa & ~Fb;
    if (pc(U) != 1 || pc(Z) != 1 || pc(Y) > 1) return 0;
    for (msk t = Y; t; t &= t - 1) { int y = ctz(t); if (!(opt[y][ia[y]] & ~opt[y][ib[y]])) return 0; }   /* y gives up a good */
    int x = ctz(U), z = ctz(Z);
    msk g1 = opt[x][ia[x]], g2 = opt[z][ib[z]];             /* frozen bases are distinct singletons: compare the unions */
    for (msk t = W; t; t &= t - 1) { int w = ctz(t); g1 |= opt[w][ia[w]]; g2 |= opt[w][ib[w]]; }
    if (g1 != g2 || pc(g1) != pc(W) + 1) return 0;
    XU = U; XZ = Z; XW = W; XY = Y; *wn = pc(W);
    msk h = opt[z][ib[z]];
    return (optN[z][ia[z]] & h) == h ? 2 : 1;               /* z needs its new good in P */
}
/* T4(P, P'): NA kept, some agent changes, every changed agent frozen in P and in P' (then the frozen goods are permuted) */
static int t4x(long a, long b) {
    const unsigned char *ia = PP + a * MAXN, *ib = PP + b * MAXN;
    if (PI[a].NA != PI[b].NA) return 0;
    msk F = PI[a].frozen & PI[b].frozen; int any = 0;
    for (int i = 0; i < n; i++) if (ia[i] != ib[i]) { if (!(F >> i & 1)) return 0; any = 1; }
    return any;
}

/* ---------- keys and the key graph (dlrc.c) ---------- */
static long *KID = 0, *NGk = 0, *NGd = 0, *NGlo = 0, *NGhi = 0; static int *KDEF = 0, *KMIN = 0, *KMINW = 0;
static long nkeys = 0, capk = 0;
static gk_t *GKK = 0;
static int ngcmp_k(const void *x, const void *y) {          /* (NA, def* of the key, p) */
    long a = *(const long *)x, b = *(const long *)y;
    if (PI[a].NA != PI[b].NA) return PI[a].NA < PI[b].NA ? -1 : 1;
    int da = KDEF[KID[a]], db = KDEF[KID[b]];
    if (da != db) return da < db ? -1 : 1;
    return (a > b) - (a < b);
}
static int ngcmp_d(const void *x, const void *y) {          /* (NA, def, p) */
    long a = *(const long *)x, b = *(const long *)y;
    if (PI[a].NA != PI[b].NA) return PI[a].NA < PI[b].NA ? -1 : 1;
    if (PI[a].def != PI[b].def) return PI[a].def < PI[b].def ? -1 : 1;
    return (a > b) - (a < b);
}
/* the keys of the class, def*, and (f >= 1) kmin / kminw of every key with def* > 0 */
static void keygraph(void) {
    if (npp > capk) {
        capk = npp;
        KID = realloc(KID, capk * sizeof(long)); NGk = realloc(NGk, capk * sizeof(long)); NGd = realloc(NGd, capk * sizeof(long));
        NGlo = realloc(NGlo, capk * sizeof(long)); NGhi = realloc(NGhi, capk * sizeof(long));
        KDEF = realloc(KDEF, capk * sizeof(int)); KMIN = realloc(KMIN, capk * sizeof(int)); KMINW = realloc(KMINW, capk * sizeof(int));
        GKK = realloc(GKK, capk * sizeof(gk_t));
        if (!KID || !NGk || !NGd || !NGlo || !NGhi || !KDEF || !KMIN || !KMINW || !GKK) { fprintf(stderr, "oom\n"); exit(2); }
    }
    for (long p = 0; p < npp; p++) { GKK[p].k = pkey_part(PP + p * MAXN, PI[p].frozen, 1); GKK[p].na = PI[p].NA; GKK[p].p = p; }
    qsort(GKK, npp, sizeof(gk_t), gkcmp);
    nkeys = 0;
    for (long i = 0; i < npp; i++) {
        if (i == 0 || GKK[i].k != GKK[i - 1].k || GKK[i].na != GKK[i - 1].na) { KDEF[nkeys] = INF; KMIN[nkeys] = KMINW[nkeys] = 999998; nkeys++; }
        long p = GKK[i].p; KID[p] = nkeys - 1;
        if (PI[p].def < KDEF[nkeys - 1]) KDEF[nkeys - 1] = PI[p].def;
    }
    for (long p = 0; p < npp; p++) { NGk[p] = p; NGd[p] = p; }
    qsort(NGk, npp, sizeof(long), ngcmp_k); qsort(NGd, npp, sizeof(long), ngcmp_d);
    for (long i = 0; i < npp; ) {                           /* the NA groups (the same ranges in NGk and NGd) */
        long j = i; while (j < npp && PI[NGk[j]].NA == PI[NGk[i]].NA) j++;
        for (long t = i; t < j; t++) { NGlo[NGk[t]] = i; NGhi[NGk[t]] = j; }
        i = j;
    }
    if (bestf < 1) return;
    for (long k = 0; k < nkeys; k++) if (KDEF[k] > 0) KMIN[k] = KMINW[k] = INF;
    for (long p = 0; p < npp; p++) {
        long k = KID[p];
        if (KDEF[k] <= 0) continue;
        for (long i = NGlo[p]; i < NGhi[p]; i++) {
            long q = NGk[i]; int dq = KDEF[KID[q]];
            if (dq >= KMIN[k]) break;
            if (KID[q] == k) continue;
            int wn, t = t3x(p, q, &wn);
            if (t == 2 || t4x(p, q)) { KMIN[k] = dq; if (dq < KMINW[k]) KMINW[k] = dq; break; }
            if (t == 1 && dq < KMINW[k]) KMINW[k] = dq;
        }
    }
}
/* the candidates for P = PP[p] in a large class: dlrt4.c's RT4 candidates and every P' with NA(P') = NA(P) and a smaller
   deficit (a superset of the improving R_C moves) */
static void fill_candrc(long p) {
    fill_candrt4(p);
    for (long i = NGlo[p]; i < NGhi[p]; i++) { long q = NGd[i]; if (PI[q].def >= PI[p].def) break; cpush_u(q); }
}
static const char *RCNAME[7] = {"none", "T1", "T2", "T3p", "T3h", "T4", "T3c"};
static const char *T1NAME[3] = {"rel", "grow", "pool"};
static const char *XSNAME[3] = {"xJ", "xZ", "xH"};
static const char *HKNAME[4] = {"h-", "hR", "hJ", "hZ"};
#define MAXC 64                                             /* cycle types per state (partitions of <= 16 without 1s: < 64) */
static void cyadd(uint64_t *S, int *ns, uint64_t c) { for (int i = 0; i < *ns; i++) if (S[i] == c) return; if (*ns < MAXC) S[(*ns)++] = c; }
static void cyset_str(uint64_t *S, int ns, char *out) {     /* the cycle types, by increasing code, comma-separated; "-" if none */
    for (int a = 0; a < ns; a++) for (int b = a + 1; b < ns; b++) if (S[b] < S[a]) { uint64_t t = S[a]; S[a] = S[b]; S[b] = t; }
    out[0] = 0;
    for (int a = 0; a < ns; a++) { char s[64]; cyc_str(S[a], s); if (a) strcat(out, ","); strcat(out, s); }
    if (!ns) strcpy(out, "-");
}

/* ---------- per profile ---------- */
typedef struct { long prof, om1, small, ks[6], kn, kiso, ktrap, pos, pd[6], piso, ptrap, pmpos, pm3, maxmin; } cnt_t;
/* dl2.c's counters: ks: profiles with k* = 0, 1, 2, 3, >= 4, inf; kn: with k* = n; kiso / ktrap: with k* >= 3 (finite)
   where every P at distance >= 3 is isolated / some is not; pd: P with def > 0 at distance 1, 2, 3, >= 4, inf; piso /
   ptrap: P at distance >= 3, isolated / not; pmpos / pm3: P with def > 0 that are Pareto-maximal / and at distance >= 3 */
static cnt_t CN;
typedef struct { long st0, st1, fail0, fail1, t[6], only[6], rtfail, r13fail, r134fail, anom, anom4, rd[5]; } cntrt4_t;
static cntrt4_t CL;
static long nNew = 0, nOther = 0, nfail0dump = 0;   /* per process: dump counters */
typedef struct { long st1, rcfail, rt4fail, chain, chain3, t3c, t3w, t3wonly, w[4], cw[4], keyfail, keyfailk, keyfailw, keyspos,
                 rcnokey; } cntrc_t;
static cntrc_t CC;                                   /* dlrc.c's counters (the "LC" line) */
static void hline_skip(void) {                       /* -H for a profile that is not evaluated */
    if (!HVERB) return;
    printf("H %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]);
    printf(" -1 0 0 0 0 0 0 999999 0 999999 0 0 0\n");
}

static void pmaskj(FILE *f, msk M) { int first = 1; fputc('[', f); for (int g = 0; g < MAXM; g++) if (M >> g & 1) { fprintf(f, first ? "%d" : ",%d", g); first = 0; } fputc(']', f); }
static void pbases(FILE *f, const unsigned char *ix) { fputc('[', f); for (int i = 0; i < n; i++) { if (i) fputc(',', f); pmaskj(f, opt[i][ix[i]]); } fputc(']', f); }
static void pcyjson(FILE *f, uint64_t *S, int ns) {        /* a JSON list of cycle-type strings (S sorted by cyset_str) */
    fputc('[', f); for (int a = 0; a < ns; a++) { char s[64]; cyc_str(S[a], s); fprintf(f, a ? ",\"%s\"" : "\"%s\"", s); } fputc(']', f);
}
static void profile(void) {
    for (int i = 0; i < n; i++) for (int k = 0; k < deg[i]; k++) v[i][R[i][k]] = dom[i][cur[i] * deg[i] + k];
    for (int i = 0; i < n; i++) {
        int d = deg[i];
        for (int s = 0; s < (1 << d); s++) { int su = 0, mn = 1 << 30; for (int k = 0; k < d; k++) if (s >> k & 1) { su += v[i][R[i][k]]; if (v[i][R[i][k]] < mn) mn = v[i][R[i][k]]; } ssum[i][s] = su; smin[i][s] = s ? mn : 0; }
        for (int k = 0; k < d; k++) rk[i][k] = R[i][k];
        for (int a = 0; a < d; a++) for (int b = a + 1; b < d; b++) if (v[i][rk[i][b]] > v[i][rk[i][a]]) { int t = rk[i][a]; rk[i][a] = rk[i][b]; rk[i][b] = t; }
        topg[i] = rk[i][0];
        bigtop[i] = d == 4 && v[i][rk[i][0]] > v[i][rk[i][1]] + v[i][rk[i][2]];
        nopt[i] = 0;
        for (int t = 0; t < (1 << d); t++) if (pc(t) <= 2) {
            msk B = 0; for (int k = 0; k < d; k++) if (t >> k & 1) B |= BIT(R[i][k]);
            opt[i][nopt[i]] = B; optN[i][nopt[i]] = needs(i, B); optv[i][nopt[i]] = val(i, B); nopt[i]++;
        }
    }
    CN.prof++;
    sigma = 2 * n - m;
    if (sigma >= 0) { found_small = 0; dfs_small(0, 0, 0, 0, 0); if (found_small) { CN.small++; if (VERB) { printf("V %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]); printf(" -2 0 0 0\n"); } hline_skip(); return; } }
    bestf = 1 << 20; npp = 0;
    memset(cidx, 0, sizeof cidx);
    dfsP(0, 0, 0, 0, 0);
    int omega = bestf - sigma;
    if (omega <= 0) { fprintf(stderr, "internal: omega <= 0 after the small test\n"); exit(3); }
    CN.om1++;
    if (npp > capi) { capi = npp; PI = realloc(PI, capi * sizeof(pinfo_t)); if (!PI) { fprintf(stderr, "oom\n"); exit(2); } }
    int mindef = INF, npos = 0;
    for (long p = 0; p < npp; p++) { eval_P(PP + p * MAXN, &PI[p]); if (PI[p].def < mindef) mindef = PI[p].def; if (PI[p].def > 0) npos++; }
    int kstar = 0;
    static int *dd = 0, *nn = 0;
    static long capd = 0;
    if (npp > capd) { capd = npp; dd = realloc(dd, sizeof(int) * capd); nn = realloc(nn, sizeof(int) * capd); }
    int anytrap = 0;
    if (npp > BIGPP) hbuild();
    /* first pass (dl2.c): distances */
    for (long p = 0; p < npp; p++) {
        dd[p] = -1; nn[p] = -1;
        if (PI[p].def <= 0) continue;
        int best = 99, near = 99; const unsigned char *ia = PP + p * MAXN;
        for (int pass = 0; pass < 2 && best == 99; pass++) {    /* pass 1 (large classes only): every other P */
            if (pass == 1 && npp <= BIGPP) break;
            fill_cand(p, pass);
            for (long c = 0; c < ncand; c++) {
                long q = cand[c];
                const unsigned char *ib = PP + q * MAXN; int d = 0;
                for (int i = 0; i < n; i++) d += ia[i] != ib[i];
                if (d < near) near = d;
                if (PI[q].def < PI[p].def && d < best) best = d;
            }
        }
        dd[p] = best; nn[p] = near;
        if (best == 99) kstar = 99; else if (kstar != 99 && best > kstar) kstar = best;
        CN.pd[best == 99 ? 5 : best >= 4 ? 4 : best]++;
        if (best >= 3) { if (near >= 3) CN.piso++; else { CN.ptrap++; if (best != 99) anytrap = 1; } }
    }
    if (kstar == 99) CN.ks[5]++; else CN.ks[kstar >= 4 ? 4 : kstar]++;
    if (kstar == n) CN.kn++;
    if (kstar >= 3 && kstar != 99) { if (anytrap) CN.ktrap++; else CN.kiso++; }
    CN.pos += npos;
    if (CN.om1 == 1 || mindef > CN.maxmin) CN.maxmin = mindef;
    if (VERB) {
        printf("V %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]);
        printf(" %d %ld %d %d\n", kstar == 99 ? -1 : kstar, npp, npos, mindef);
    }
    /* second pass: RT4 (and R_C) and the signature of every P with def > 0 */
    if (npp > BIGPP) gbuild();
    keygraph();                                       /* dlrc.c: keys, def*, kmin */
    long hst1 = 0, hrt4f = 0, hrcf = 0, hch = 0, hch3 = 0, hchw2 = 0, hc3 = 0, hkf = 0, hkfk = 0; int hgap = INF, hmv = INF, hmaxw = 0;
    if (bestf >= 1) for (long k = 0; k < nkeys; k++) if (KDEF[k] > 0) { CC.keyspos++; if (KMIN[k] >= KDEF[k]) { CC.keyfailk++; hkfk++; } }
    for (long p = 0; p < npp; p++) {
        if (PI[p].def <= 0) continue;
        const unsigned char *ia = PP + p * MAXN;
        /* RT4 */
        int fl[6] = {0, 0, 0, 0, 0, 0}, sz[6] = {99, 99, 99, 99, 99, 99}, t1m = 0, t3m = 0, rd = 99;
        unsigned t2m = 0;
        uint64_t cy[MAXC], cm[MAXC]; int ncy = 0, ncm = 0;
        long wit = -1; int wdef = INF, wmov = 1 << 20, wk = 0, wsz = 0;
        /* R_C (dlrc.c) */
        int t3c = 0, s3c = 99, wmin = 99, t3w = 0, wminw = 99, rdc = 99, nrc = 0, bestrc = INF;
        static long chq[100]; static msk chU[100], chZ[100], chW[100], chY[100]; int nch = 0;
        if (npp <= BIGPP) fill_cand(p, 1); else fill_candrc(p);
        for (long c = 0; c < ncand; c++) {
            long q = cand[c];
            if (q == p || PI[q].def >= PI[p].def) continue;
            uint64_t ty = 0; int k = rt4(p, q, &ty);
            const unsigned char *ib = PP + q * MAXN; int d = 0, mov = 0;
            for (int i = 0; i < n; i++) if (ia[i] != ib[i]) { d++; mov += pc(opt[i][ia[i]] ^ opt[i][ib[i]]); }
            int wn = -1, tx = t3x(p, q, &wn);
            if ((tx == 2 && wn == 0) != (k == 3 || k == 4)) ANOMC++;      /* T3+ with W empty is T3 */
            if (tx >= 1) { t3w = 1; if (wn < wminw) wminw = wn; }
            if (tx == 2) {
                if (wn < wmin) wmin = wn;
                if (wn > 0) {
                    if (k) ANOMC++;                                        /* a T3c move is no RT4 move */
                    t3c = 1; if (d < s3c) s3c = d;
                    int slot = nch < 100 ? nch++ : -1;      /* keep the 100 with the smallest index (any candidate order) */
                    if (slot < 0) { slot = 0; for (int c2 = 1; c2 < 100; c2++) if (chq[c2] > chq[slot]) slot = c2; if (chq[slot] < q) slot = -1; }
                    if (slot >= 0) { chq[slot] = q; chU[slot] = XU; chZ[slot] = XZ; chW[slot] = XW; chY[slot] = XY; }
                }
            }
            if (k || tx == 2) { nrc++; if (d < rdc) rdc = d; if (PI[q].def < bestrc) bestrc = PI[q].def; }
            if (!k) continue;
            if (d < rd) rd = d;
            if (k == 5) {
                if (d < sz[5]) ncm = 0;
                if (d <= sz[5]) cyadd(cm, &ncm, ty);
                cyadd(cy, &ncy, ty);
            }
            fl[k] = 1; if (d < sz[k]) sz[k] = d;
            if (k == 1) t1m |= 1 << ty; else if (k == 2) t2m |= 1u << ty; else if (k <= 4) t3m |= 1 << ty;
            if (PI[q].def < wdef || (PI[q].def == wdef && (mov < wmov || (mov == wmov && q < wit)))) { wdef = PI[q].def; wmov = mov; wit = q; wk = k; wsz = d; }
        }
        int ok = fl[1] || fl[2] || fl[3] || fl[4] || fl[5];
        int okrc = ok || t3c;                                  /* DL_RC at P */
        long kp = KID[p]; int dstar = KDEF[kp], kmin = KMIN[kp], kminw = KMINW[kp];
        int keyok = dstar < PI[p].def || kmin < PI[p].def, keyokw = dstar < PI[p].def || kminw < PI[p].def;
        char brc[48]; brc[0] = 0;                               /* the R_C branches */
        for (int k = 1; k <= 5; k++) if (fl[k]) { if (brc[0]) strcat(brc, "+"); strcat(brc, RCNAME[k]); }
        if (t3c) { if (brc[0]) strcat(brc, "+"); strcat(brc, RCNAME[6]); }
        if (!brc[0]) strcpy(brc, "none");
        char cys[512], cms[512]; cyset_str(cy, ncy, cys); cyset_str(cm, ncm, cms);
        /* signature (dl2.c) */
        msk best = 0; int sig = 0;
        if (PI[p].def >= INF) sig |= 1 << C_ALLF;
        else for (int o = 0; o < n; o++) if (PI[p].bestown[o] == PI[p].def) best |= BIT(o);
        for (int o = 0; o < n; o++) if (best >> o & 1) for (int x = 0; x < n; x++) if (PI[p].expo[o] >> x & 1) sig |= 1 << classify(ia, &PI[p], x, o);
        for (int x = 0; x < n; x++) if (PI[p].frozen >> x & 1) { int c = 0; for (int o = 0; o < n; o++) if (PI[p].expo[o] >> x & 1) c++; if (c >= 2) sig |= 1 << C_D2; }
        int pm = 1;
        for (long q = 0; q < npp && pm; q++) {
            if (q == p) continue;
            const unsigned char *ib = PP + q * MAXN; int ge = 1, gt = 0;
            for (int i = 0; i < n && ge; i++) { int a = optv[i][ia[i]], b = optv[i][ib[i]]; if (b < a) ge = 0; else if (b > a) gt = 1; }
            if (ge && gt) pm = 0;
        }
        if (pm) { sig |= 1 << C_PM; CN.pmpos++; if (dd[p] >= 3) CN.pm3++; }
        char sigs[128]; sigs[0] = 0;
        for (int c = 0; c < NCLS; c++) if (sig >> c & 1) { if (sigs[0]) strcat(sigs, ","); strcat(sigs, CLSNAME[c]); }
        char br[40]; br[0] = 0;
        for (int k = 1; k <= 5; k++) if (fl[k]) { if (br[0]) strcat(br, "+"); strcat(br, KNAME[k]); }
        if (!br[0]) strcpy(br, "none");
        if (SVERB) {
            printf("S %d", bestf); for (int i = 0; i < n; i++) printf(" %llu", (unsigned long long)opt[i][ia[i]]);
            printf(" %d %d %d %d %d %d %d %d %d %d %d %d %d %u %d %s %s %d %d %s", PI[p].def, dd[p], rd, fl[1], fl[2], fl[3], fl[4],
                   fl[5], sz[2], sz[3], sz[4], sz[5], t1m, t2m, t3m, cys, cms, wdef, pm, sigs[0] ? sigs : "-");
            printf(" %d %d %d %d %d %d %d %d %d %d %d %d\n", t3c, s3c, wmin, t3w, wminw, rdc, nrc, bestrc, dstar, kmin, kminw, keyok);
        }
        int dumpit = 0;
        int r13 = fl[1] || fl[3] || fl[4];
        if (bestf == 0) {
            CL.st0++;
            if (!ok) { CL.fail0++; if (nfail0dump < 5) { nfail0dump++; dumpit = 1; } }
        } else {
            CL.st1++;
            if (!ok) { CL.fail1++; dumpit = 1; }
            for (int k = 1; k <= 5; k++) if (fl[k]) CL.t[k]++;
            int nb = (fl[1] != 0) + (fl[2] != 0) + (fl[3] || fl[4]) + (fl[5] != 0);
            if (nb == 1) CL.only[fl[1] ? 1 : fl[2] ? 2 : fl[5] ? 5 : 3]++;
            if (!(fl[1] || fl[2] || fl[3] || fl[4])) CL.rtfail++;
            if (!r13) CL.r13fail++;
            if (!(r13 || fl[5])) CL.r134fail++;
            CL.rd[rd >= 4 ? (rd == 99 ? 0 : 4) : rd]++;
            char key[640];
            snprintf(key, sizeof key, "B %d|%s|%s", bestf, sigs, br); (*mslot(&TAB, key))++;
            snprintf(key, sizeof key, "G %d|%d|%s", bestf, dd[p] == 99 ? -1 : dd[p], br); (*mslot(&TAB, key))++;
            snprintf(key, sizeof key, "M %d|%s|%d", bestf, br, rd == 99 ? -1 : rd); (*mslot(&TAB, key))++;
            for (int k = 1; k <= 5; k++) if (fl[k]) { snprintf(key, sizeof key, "Z %d|%s|%d", bestf, KNAME[k], sz[k]); (*mslot(&TAB, key))++; }
            if (fl[5]) { snprintf(key, sizeof key, "C %d|%d|%s", bestf, sz[5], cms); (*mslot(&TAB, key))++; }
            for (int k = 0; k < 3; k++) if (t1m >> k & 1) { snprintf(key, sizeof key, "Y %d|%s|T1:%s", bestf, br, T1NAME[k]); (*mslot(&TAB, key))++; }
            for (int k = 2; k <= MAXN; k++) if (t2m >> k & 1) { snprintf(key, sizeof key, "Y %d|%s|T2:k%d", bestf, br, k); (*mslot(&TAB, key))++; }
            for (int k = 0; k < 12; k++) if (t3m >> k & 1) { snprintf(key, sizeof key, "Y %d|%s|T3:%s.%s", bestf, br, XSNAME[k / 4], HKNAME[k % 4]); (*mslot(&TAB, key))++; }
            for (int a = 0; a < ncy; a++) { char s[64]; cyc_str(cy[a], s); snprintf(key, sizeof key, "Y %d|%s|T4:%s", bestf, br, s); (*mslot(&TAB, key))++; }
            snprintf(key, sizeof key, "%s|%s", sigs, br);
            long *seen = mslot(&SEEN, key);
            if (!*seen) { *seen = 1; dumpit = 1; }
            if (ok && !r13) { nNew++; if (RT > 0 && (nNew - 1) % RT == 0) dumpit = 1; }
            else if (ok) { nOther++; if (RO > 0 && (nOther - 1) % RO == 0) dumpit = 1; }
            /* dlrc.c */
            CC.st1++; hst1++;
            if (!okrc) { CC.rcfail++; hrcf++; }
            if (!ok) { CC.rt4fail++; hrt4f++; }
            if (!ok && okrc) {
                CC.chain++; hch++; if (bestf >= 3) { CC.chain3++; hch3++; }
                if (wmin >= 2) hchw2++;
                CC.cw[wmin >= 3 ? 3 : wmin]++; if (wmin > hmaxw) hmaxw = wmin;
            }
            if (t3c) CC.t3c++;
            if (t3w) CC.t3w++;
            if (!okrc && t3w) CC.t3wonly++;
            if (wmin != 99) CC.w[wmin >= 3 ? 3 : wmin]++;
            if (!keyok) { CC.keyfail++; hkf++; }
            if (!keyokw) CC.keyfailw++;
            if (okrc && !keyok && PI[p].def == dstar) CC.rcnokey++;
            int gap = okrc ? PI[p].def - bestrc : 0; if (gap < hgap) hgap = gap;
            if (nrc < hmv) hmv = nrc;
            if (rdc >= 3) hc3++;
            snprintf(key, sizeof key, "W %d|%s|%d", bestf, brc, wmin == 99 ? -1 : wmin); (*mslot(&TAB, key))++;
            snprintf(key, sizeof key, "%s|%s", sigs, brc);
            long *seenc = mslot(&SEENC, key);
            if (!*seenc) { *seenc = 1; dumpit = 1; }
        }
        if (dumpit) {
            printf("D {\"tag\":%d,\"prof\":[", tag); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", cur[i]);
            printf("],\"f\":%d,\"omega\":%d,\"nmin\":%ld,\"B\":", bestf, omega, npp); pbases(stdout, ia);
            printf(",\"def\":%d,\"k\":%d,\"nn\":%d,\"pm\":%d,\"sig\":\"%s\",\"br\":\"%s\",\"rd\":%d,\"size\":{",
                   PI[p].def >= INF ? -1 : PI[p].def, dd[p] == 99 ? -1 : dd[p], nn[p] == 99 ? -1 : nn[p], pm, sigs, br, rd == 99 ? -1 : rd);
            int f1 = 1; for (int k = 1; k <= 5; k++) if (fl[k]) { printf(f1 ? "\"%s\":%d" : ",\"%s\":%d", KNAME[k], sz[k]); f1 = 0; }
            printf("},\"t1types\":["); f1 = 1;
            for (int k = 0; k < 3; k++) if (t1m >> k & 1) { printf(f1 ? "\"%s\"" : ",\"%s\"", T1NAME[k]); f1 = 0; }
            printf("],\"t2sizes\":["); f1 = 1;
            for (int k = 2; k <= MAXN; k++) if (t2m >> k & 1) { printf(f1 ? "%d" : ",%d", k); f1 = 0; }
            printf("],\"t3types\":["); f1 = 1;
            for (int k = 0; k < 12; k++) if (t3m >> k & 1) { printf(f1 ? "\"%s.%s\"" : ",\"%s.%s\"", XSNAME[k / 4], HKNAME[k % 4]); f1 = 0; }
            printf("],\"t4cyc\":"); pcyjson(stdout, cy, ncy);
            printf(",\"t4cycmin\":"); pcyjson(stdout, cm, ncm);
            printf(",\"frozen\":"); { msk F = PI[p].frozen; int ff = 1; printf("["); for (int i = 0; i < n; i++) if (F >> i & 1) { printf(ff ? "%d" : ",%d", i); ff = 0; } printf("]"); }
            printf(",\"NA\":"); pmaskj(stdout, PI[p].NA);
            printf(",\"J\":"); pmaskj(stdout, PI[p].J);
            printf(",\"own\":["); f1 = 1;
            for (int o = 0; o < n; o++) if (!(PI[p].frozen >> o & 1)) { printf(f1 ? "[%d,%d]" : ",[%d,%d]", o, PI[p].bestown[o] >= INF ? -1 : PI[p].bestown[o]); f1 = 0; }
            printf("],\"exp\":["); f1 = 1;
            for (int o = 0; o < n; o++) for (int x = 0; x < n; x++) if (PI[p].expo[o] >> x & 1) { printf(f1 ? "[%d,%d,\"%s\"]" : ",[%d,%d,\"%s\"]", o, x, CLSNAME[classify(ia, &PI[p], x, o)]); f1 = 0; }
            printf("]");
            if (wit >= 0) { printf(",\"W\":"); pbases(stdout, PP + wit * MAXN); printf(",\"defW\":%d,\"wkind\":\"%s\",\"wsize\":%d", PI[wit].def, KNAME[wk], wsz); }
            if (!ok) {                                      /* every min-frozen P' with a smaller deficit (at most 400) */
                printf(",\"better\":["); f1 = 1; int cnt = 0;
                for (long q = 0; q < npp && cnt < 400; q++) if (PI[q].def < PI[p].def) {
                    if (!f1) printf(",");
                    f1 = 0; printf("{\"B\":"); pbases(stdout, PP + q * MAXN);
                    printf(",\"def\":%d,\"frozen\":", PI[q].def); { msk F = PI[q].frozen; int ff = 1; printf("["); for (int i = 0; i < n; i++) if (F >> i & 1) { printf(ff ? "%d" : ",%d", i); ff = 0; } printf("]"); }
                    printf(",\"NA\":"); pmaskj(stdout, PI[q].NA);
                    {                                       /* dlrc.c: the shape of P -> P' and its R_C kind */
                        const unsigned char *ib = PP + q * MAXN; msk ch = 0, Fa = PI[p].frozen, Fb = PI[q].frozen;
                        for (int i = 0; i < n; i++) if (ia[i] != ib[i]) ch |= BIT(i);
                        long a0 = ANOM, a4 = ANOM4; uint64_t ty = 0; int k = rt4(p, q, &ty); ANOM = a0; ANOM4 = a4;
                        int wn, tx = t3x(p, q, &wn);
                        printf(",\"sh\":[%d,%d,%d,%d],\"nak\":%d,\"kind\":\"%s\"}", pc(ch & Fa & ~Fb), pc(ch & ~Fa & Fb),
                               pc(ch & Fa & Fb), pc(ch & ~Fa & ~Fb), PI[q].NA == PI[p].NA,
                               k ? RCNAME[k] : tx == 2 ? RCNAME[6] : tx == 1 ? "T3w" : "-");
                    }
                    cnt++; }
                printf("]");
            }
            /* dlrc.c */
            printf(",\"rc\":\"%s\",\"wmin\":%d,\"wminw\":%d,\"nrc\":%d,\"bestrc\":%d,\"dstar\":%d,\"kmin\":%d,\"kminw\":%d,\"keyok\":%d",
                   brc, wmin == 99 ? -1 : wmin, wminw == 99 ? -1 : wminw, nrc, bestrc >= INF ? 999999 : bestrc, dstar, kmin, kminw, keyok);
            printf(",\"chains\":["); f1 = 1;
            for (int a = 0; a < nch; a++) for (int b = a + 1; b < nch; b++) if (chq[b] < chq[a]) {
                long tq = chq[a]; chq[a] = chq[b]; chq[b] = tq; msk t;
                t = chU[a]; chU[a] = chU[b]; chU[b] = t; t = chZ[a]; chZ[a] = chZ[b]; chZ[b] = t;
                t = chW[a]; chW[a] = chW[b]; chW[b] = t; t = chY[a]; chY[a] = chY[b]; chY[b] = t; }
            for (int c = 0; c < nch; c++) {
                printf(f1 ? "{\"B\":" : ",{\"B\":"); f1 = 0; pbases(stdout, PP + chq[c] * MAXN);
                printf(",\"def\":%d,\"x\":%d,\"z\":%d,\"W\":", PI[chq[c]].def, ctz(chU[c]), ctz(chZ[c]));
                printf("["); int ff = 1; for (int i = 0; i < n; i++) if (chW[c] >> i & 1) { printf(ff ? "%d" : ",%d", i); ff = 0; } printf("]");
                printf(",\"Y\":["); ff = 1; for (int i = 0; i < n; i++) if (chY[c] >> i & 1) { printf(ff ? "%d" : ",%d", i); ff = 0; } printf("]}");
            }
            printf("]");
            printf("}\n");
        }
    }
    if (HVERB) {
        printf("H %d", tag); for (int i = 0; i < n; i++) printf(" %d", cur[i]);
        printf(" %d %ld %ld %ld %ld %ld %ld %d %ld %d %ld %ld %d\n", bestf, hst1, hrt4f, hrcf, hch, hch3, hchw2, hgap, hc3, hmv,
               hkf, hkfk, hmaxw);
    }
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-v")) VERB = 1;
        else if (!strcmp(argv[a], "-s")) SVERB = VERB = 1;
        else if (!strcmp(argv[a], "-H")) HVERB = 1;
        else if (!strncmp(argv[a], "-r", 2)) RT = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-o", 2)) RO = atoi(argv[a] + 2);
        else if (!strncmp(argv[a], "-S", 2)) SEED = strtoull(argv[a] + 2, 0, 10);
        else { fprintf(stderr, "unknown option %s\n", argv[a]); return 2; }
    }
    while (scanf("%d %d %d", &n, &m, &tag) == 3) {
        if (n > MAXN || m > MAXM) { fprintf(stderr, "n or m too large\n"); return 2; }
        ALL = m == MAXM ? ~(msk)0 : BIT(m) - 1;
        for (int i = 0; i < n; i++) { if (scanf("%d", &deg[i]) != 1) return 2; Rm[i] = 0;
            if (deg[i] < 1 || deg[i] > 4) { fprintf(stderr, "degree\n"); return 2; }
            for (int k = 0; k < deg[i]; k++) { if (scanf("%d", &R[i][k]) != 1) return 2; Rm[i] |= BIT(R[i][k]); } }
        memset(v, 0, sizeof v);
        for (int i = 0; i < n; i++) if (scanf("%d", &K[i]) != 1) return 2;
        for (int i = 0; i < n; i++) { dom[i] = realloc(dom[i], sizeof(int) * K[i] * deg[i]);
            for (int t = 0; t < K[i] * deg[i]; t++) if (scanf("%d", &dom[i][t]) != 1) return 2; }
        long P; if (scanf("%ld", &P) != 1) return 2;
        memset(&CN, 0, sizeof CN); memset(&CL, 0, sizeof CL); ANOM = 0; ANOM4 = 0; memset(&CC, 0, sizeof CC); ANOMC = 0;
        mclear(&TAB);
        if (P == 0) {
            memset(cur, 0, sizeof cur);
            for (;;) {
                profile();
                int i = n - 1; while (i >= 0 && ++cur[i] == K[i]) cur[i--] = 0;
                if (i < 0) break;
            }
        } else if (P > 0) {
            rs = SEED * 0x9E3779B97F4A7C15ull + (uint64_t)tag * 0xBF58476D1CE4E5B9ull + 1;
            for (long q = 0; q < P; q++) { for (int i = 0; i < n; i++) cur[i] = rnd() % K[i]; profile(); }
        } else {
            for (long q = 0; q < -P; q++) { for (int i = 0; i < n; i++) if (scanf("%d", &cur[i]) != 1) return 2; profile(); }
        }
        CL.anom = ANOM; CL.anom4 = ANOM4;
        printf("K %d prof %ld om1 %ld small %ld kstar0 %ld kstar1 %ld kstar2 %ld kstar3 %ld kstar4 %ld kstarinf %ld kstarn %ld "
               "kiso %ld ktrap %ld pos %ld pd1 %ld pd2 %ld pd3 %ld pd4 %ld pdinf %ld piso %ld ptrap %ld pmpos %ld pm3 %ld maxmin %ld\n",
               tag, CN.prof, CN.om1, CN.small, CN.ks[0], CN.ks[1], CN.ks[2], CN.ks[3], CN.ks[4], CN.ks[5], CN.kn,
               CN.kiso, CN.ktrap, CN.pos, CN.pd[1], CN.pd[2], CN.pd[3], CN.pd[4], CN.pd[5], CN.piso, CN.ptrap, CN.pmpos, CN.pm3, CN.maxmin);
        printf("L %d st0 %ld st1 %ld fail0 %ld fail1 %ld t1 %ld t2 %ld t3p %ld t3h %ld t4 %ld t1only %ld t2only %ld t3only %ld "
               "t4only %ld rtfail %ld r13fail %ld r134fail %ld anom %ld anom4 %ld rdnone %ld rd1 %ld rd2 %ld rd3 %ld rd4 %ld\n",
               tag, CL.st0, CL.st1, CL.fail0, CL.fail1, CL.t[1], CL.t[2], CL.t[3], CL.t[4], CL.t[5], CL.only[1], CL.only[2],
               CL.only[3], CL.only[5], CL.rtfail, CL.r13fail, CL.r134fail, CL.anom, CL.anom4, CL.rd[0], CL.rd[1], CL.rd[2],
               CL.rd[3], CL.rd[4]);
        printf("LC %d st1 %ld rcfail %ld rt4fail %ld chain %ld chain3 %ld t3c %ld t3w %ld t3wonly %ld w0 %ld w1 %ld w2 %ld w3 %ld "
               "cw1 %ld cw2 %ld cw3 %ld keyfail %ld keyfailk %ld keyfailw %ld keyspos %ld rcnokey %ld anomc %ld\n",
               tag, CC.st1, CC.rcfail, CC.rt4fail, CC.chain, CC.chain3, CC.t3c, CC.t3w, CC.t3wonly, CC.w[0], CC.w[1], CC.w[2],
               CC.w[3], CC.cw[1], CC.cw[2], CC.cw[3], CC.keyfail, CC.keyfailk, CC.keyfailw, CC.keyspos, CC.rcnokey, ANOMC);
        for (long i = 0; i < TAB.cap; i++) if (TAB.t[i].k) printf("%s %ld\n", TAB.t[i].k, TAB.t[i].c);
        fflush(stdout);
    }
    return 0;
}
