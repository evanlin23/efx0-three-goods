# Referee report on `k4/zmove_pot.md` (PR #87, proof/k4-zmove-pot)

An independent review, by an AI session that did not write the notes, of the written proofs of `k4/zmove_pot.md`
(§3: Lemmas Z0, R0; §4: (F1), (F2), Lemmas S, S′, C₀–C₃, Proposition ℛ, Theorem AR, Corollary AR and the fragility
lemma; §5: Lemma S⁺ and the exposure claim) and of the numbers of §2, §5 and the PR. Each step was checked against the
definitions it cites: `k4/c4x.md` §1 (𝒫, needs, validity, removal-only deficit), `k4/c4min.md` §1 (configurations,
admissibility, Lemma 1), `k4/c4min_reduce.md` §1–§2 (keys, Lemma T, Theorem Z′), `k4/sx.md` §1–§3, §6 (moves, Z′-maxima,
θ-b, Lemmas A–C′, F⁺), `k4/dl2.md` §4 (Lemma H1 in the form used there, (V), (M1), (M2), Lemmas 1, 1′, 6),
`k4/dl13.md` §2.1 (Lemmas 8, 9, 11) and `k4/hall.md` §1–§2 (Lemmas H1, H2, H3). Ledger rows: K4.ZMP.Z0, K4.ZMP.AR (both
stay CONJECTURE: one review, written proofs, no Lean), K4.ZMP.POT, K4.ZMP.X.

**Verdict.**
- **Lemma Z0 (a), (b), (c) and Lemma R0: correct**, no change needed.
- **Theorem AR with (F1), (F2), Lemmas S, S′, C₀, C₁, C₂, C₃ and Proposition ℛ, and Corollary AR: correct.** Every
  step follows from the cited results; one remark on wording (below) was applied.
- **The fragility lemma ("one more constraint on the residual"): the proof is correct** (one citation fixed), **but its
  stated consequence was too strong.** The notes, the ledger row K4.ZMP.AR and the PR said that every terminal is
  fragile in every residual case. The lemma gives this only in (E), in the first form of (R3), and in the second form of
  (R3) when v_x(q) + v_x(r) < v_x(g); in the second form of (R3) with v_x(q) + v_x(r) > v_x(g) no good e qualifies.
  Fixed in `k4/zmove_pot.md` §4, §6 and in the ledger row. The overstated part is unproved, not shown false (no
  instance of the residual is known), so no `attempts/` file applies. In (E) the fragility stands, and it agrees with
  PR #91's Corollary E (E1) (`k4/zmove_f1.md` §3, merged), proved there differently.
- **"(E) and (R3) need four agents" was stated without proof.** It is true: (R3) has x and three terminals; in (E) the
  goods p, q, r of U_x are valued by no terminal, so at n = 3 they would be three private goods of x, against (C3) of
  K4.CORE. The argument is now in §4.
- **Lemma S⁺ and the exposure claim of §5: correct.** The description of "what is left" when one free agent is not
  robust omitted the case S = 0 with every terminal θ-b (Lemmas C₀–C₃ use Lemma R0 for every free agent other than the
  owner, τ and x); added.
- **§2's description of core 4515 had four inaccuracies** (the data themselves reproduce): see §3 below.
- **Every number that cites a committed log matches it**; the scratch-only numbers were rerun with the committed tool,
  and two of its key counts differ (§3).

No status changes: K4.ZMP.Z0 and K4.ZMP.AR stay CONJECTURE (written proofs, refereed once by an independent AI session).

## 1. Line by line

**Setting (§1).** States, U_y, robustness, Λ′, local optimality and zm(P) are as in `k4/sx.md` §2 at the state level.
Λ′ uses ℓ_y over the subsets of R_y, as `k4/sx.md` §2 and the tool (`model.Inst.level`) do.

**Lemma Z0.**
- (a), (b): the re-base B′ (B_y plus a junk good of R_y, or a better set of at most two goods of (B_y ∪ J) ∩ R_y) lies
  in U_y (J misses 𝒩 by (V1); a free base misses 𝒩), has larger value, so N_y(B′) ⊆ N_y(B_y) ⊆ 𝒩 by (M2); this is
  `k4/dl2.md` Lemma 1(c), which the proof re-derives. Λ′ rises strictly (B_y ⊆ R_y is one of the subsets counted in
  ℓ_y(B′) but not in ℓ_y(B_y)); r′ does not fall (the computation in the proof needs B_y, B′ ⊆ U_y, which holds).
  Correct, at every f.
- (c): the fillings exist (|J| = S + ω); Q_y ∩ U_y = B_y uses (a) for one-good bases and U_y = ∅ for empty bases
  (N_y(∅) = R_y ⊆ 𝒩); |L| = ω; P_Q = P. For any configuration Q′, Q′_y ∩ R_y = H′_y because Q′_y ⊆ M ∖ 𝒩, so (r′, Λ′)
  of Q′ (`k4/sx.md` §2) equals (r′, Λ′) of the state P_{Q′}, which is a state of κ by the argument of `k4/c4min.md`
  Lemma 1(a) (the frozen agents keep their bases, the free agents' needs lie in 𝒩 by admissibility; validity of an owner
  is not used). The converse direction (every Z′-maximum is a filling) holds because Q′_y ∖ H′_y misses every base of
  P_{Q′}, hence lies in its junk. Correct.
- Checked by brute force (§2 of this report): (a), (b) at every (r′, Λ′)-maximal state, and (c) as an equality of sets
  (the Z′-maximal configurations, enumerated from `k4/c4min.md` §1, are exactly the fillings of the maximal states).

**Lemma R0.** Z ∩ R_y ⊆ U_y ∖ B_y when Z misses 𝒩 ∪ B_y, and θ_y(Z) ≤ v_y(Z ∩ R_y). Correct. The remark that every
owner bundle of a move that keeps y's base misses 𝒩 ∪ B_y is right because (T3⁺) moves keep the needed set.

**(F1).** |W_o| = |B_o| + S + ω ≥ ω + 2; W_o misses 𝒩 and the other free bases, so by (H_AR)(i) and Lemma R0 it
threatens no free agent other than o; at f = 1 the only frozen agent is x; if W_o spared x it would be a safe bundle and
Lemma H1 would give def(P) ≤ 0. The admissible set is the first part of `k4/dl13.md` Lemma 9 (Z ⊆ W_o misses 𝒩 and
threatens x holding {g}). Correct.

**(F2).** `k4/dl2.md` Lemma 6 with z = τ (τ needs g, so N_τ({g}) ⊆ 𝒩), H = ∅, A admissible: P′ is min-frozen with frozen
set {τ}. The bundles are those of `k4/dl13.md` Lemma 8 (x: A ⊆ Y ⊆ G = J ∪ B_τ) and Lemma 11 (o ≠ τ: B_o ⊆ Y ⊆ B_o ∪ J′).
Safety in P′ concerns τ on {g}, x on A (when the owner is not x) and the unchanged free agents, which are robust, so
Lemma R0 disposes of them (their bases are unchanged and Y misses them and 𝒩). The move is (T3) without helper
(`k4/sx.md` §1: ch = {x, τ}, B′_τ = B_x ⊆ N_τ(B_τ)). Correct.

**Lemma S.** The case list of admissible bases of a terminal ({u₁}, {u₁, u₂}, {u₁, u₃}, {u₂, u₃}; for |R_τ| = 3,
{u₁}, as B_τ = U_τ would be worth more than g) is complete, and in each case local optimality (ii) keeps the better
goods out of J, so (J ∪ B_τ) ∩ R_τ is worth at most v_τ(B_τ) < v_τ(g), or is U_τ with |J| = 1 (θ = v(u₁) + v(u₂) after
removing u₃), or the state is θ-b. |Y| = S + ω + |B_τ| ≥ ω + 2. Correct.

**Lemma S′.** Correct (any two goods of U_τ are worth less than g for a θ-b terminal, as τ needs g and holds {u₁, u₂}).
Remark (applied): the sentence "in configuration terms, c goes into the slot of a free agent" holds for c = u₃ only (the
other choices of c are in B_τ); the lemma itself allows every c ∈ U_τ ∖ A.

**The case S = 0, Lemma C₀.** (a): A ⊆ Y since c ∉ U_x; |Y| = ω + 1; v_x(Y) = v_x((J ∪ B_τ) ∩ U_x) > v_x(g) by (F1) for
o = τ, so g ∉ N_x(Y); in P′ no agent other than x needs g (T = {τ}, the other free agents keep their bases, τ holds g);
so τ is counted in u′_x(Y). (b): U_x = U_τ (|U_τ| = 3 ≥ |U_x|); n ≥ 3 by the count m = 4, ω = 1 for n = 2, which uses
(C5) of K4.CORE (every good relevant to someone); B_o misses U_x = U_τ ⊆ J ∪ B_τ and g, so Y ∩ R_τ = Y ∩ R_x = {r}.
Correct.

**Lemma C₁.** |Y| ≥ ω + 2 in both cases (C = {c} with c ∈ U_τ ∖ A ⊆ J′); B_o misses U_τ ⊆ J ∪ B_τ, so Y ∩ R_τ ⊆
U_τ ∖ (A ∪ C), at most two goods; Y ∩ R_x ⊆ U_x ∖ A (B_o may meet U_x, but not A), worth at most v_x(A). Correct.

**Lemma C₂.** A is admissible and robust; w ∈ U_τ lies in J′ (A misses U_τ); |Y| = ω + 1; B_τ′ misses U_τ and U_x;
U_τ′ ⊆ Y because u₃^τ′ ∉ A ∪ {w}; so g ∉ N_τ′(Y) by balance, and in P′ nobody else needs g (g ∉ N_x(A) since
v_x(A) > v_x(g); τ holds g; T = {τ, τ′}). τ is counted, def(P′) ≤ 0. Correct.

**Lemma C₃.** {p} is admissible (N_x({p}) = {g}); c ∈ U_τ ⊆ J′; Y ∩ R_x = D ∖ {p} because B_τ, B_τ′ ⊆ U_τ, U_τ′ miss
U_x; Y ∩ R_τ ⊆ U_τ ∖ {c}. Correct (the proof uses only τ ≠ τ′, not |T| ≥ 3).

**Proposition ℛ.** If s ∈ U_x ∩ U_τ, then |S_τ| ∈ {2, 3} gives a set A for Lemma C₁ (robust: at most one good of U_x
is left, worth less than g, resp. less than p). Hence U_x ∩ U_τ = ∅ for every terminal, S_τ = D, v_x(D) > v_x(g) by (F1).
|U_x| = 2 would make {p} a C₁-set. For |T| = 2, no pair of D beats g (else C₂), so D = U_x (three goods), x is big-top,
and not-C₁ for {p} gives v(p) < v(q) + v(r). For |T| ≥ 3, not-C₃ gives the two forms of (R3). Correct.

**Theorem AR, Corollary AR.** The case split is exhaustive (T ≠ ∅ by Lemma T). In the corollary, (H_AR)(ii) at P_Q
follows from Lemma Z0 (a), (b) (and U_y = ∅ for an empty base); def(P_Q) ≥ def*(κ) ≥ 1. Correct.

**The fragility lemma.** The proof is correct: {u₁} ⊆ B_τ is admissible with N_τ({u₁}) = {g}, so the re-base is
`k4/dl2.md` Lemma 1(c) (the notes cited "the argument of Lemma Z0 (a)", which needs a value increase; fixed); the
bundle Y = B_τ′ ∪ ((J ∪ {u₂}) ∖ {e}) has ω + 2 goods, meets R_x in D ∖ {e} and R_τ in {u₂, u₃}, and misses the other
free bases (all robust by (H_AR)(i), which Proposition ℛ's setting includes). **The consequence was overstated** (see
the verdict); corrected.

**Lemma S⁺.** The proof of Lemma S goes through with the hypothesis "W_τ threatens no free agent other than τ" in place
of Lemma R0 (Y = W_τ itself), and (F1) for o = τ holds because W_τ is then safe for every free agent other than τ.
Correct. **Exposure claim:** `k4/hall.md` Lemma H3 uses Pareto-maximality only through (U) and (U₂), and both hold at
every (r′, Λ′)-maximal state by Lemma Z0 (a), (b) (an empty base has U_y = ∅). Correct.

## 2. Computational checks by the referee

`k4/zmove_pot_referee.py` (new; written from the definitions, imports nothing from the repository, shares no code with
`k4/zmove_pot.py` or `k4/suite/model.py`): its own enumeration of 𝒫, the deficit both by Lemma H1 and by the raw
removal-only definition of `k4/c4x.md` §1 (asserted equal at every min-frozen state), and at every state of every key:
Lemma R0, Lemma Z0 (a), (b), (c), the exposure claim; at f = 1 and def(P) ≥ 1: Lemma S⁺, and under (H_AR) every lemma of
§4 whose hypotheses hold, **with the owner and the bundle the lemma names**, for every admissible A and every choice of
c, w, o the lemma allows (bundle of the owner, safe in P′, |Y| + u′(Y) ≥ ω + 2, and the exact def(P′) ≤ 0), Lemma S's
bound θ_τ(J ∪ B_τ) ≤ v_τ(g), Proposition ℛ's conclusions, and the fragility lemma's certificate. `k4/zmove_pot.py`
checks only that the case's move reaches def ≤ 0; this checks each lemma as stated.

Results (0 violations of any check in any log; "certificates" counts owner–bundle checks, one per admissible A and
per choice the lemma allows):

| log (`results/k4_zmove_pot/`) | input | f ≥ 1 profiles | states (H1 = raw) | AR states | certificates S / S′ / C₁ / C₂ / fragility / S⁺ |
|---|---|---|---|---|---|
| `referee_n3.log` | every 10th profile of PR #80's exhaustive n = 3 hunts | 6,221 | 151,822 | 7,922 | 26,369 / 0 / 959 / 0 / 0 / 46,741 |
| `referee_random_design.log` | 4,000 profiles built around a designed state of §4 (θ-b terminals, no slot), n = 3, 4 | 2,860 | 148,021 | 1,218 | 3,094 / 83 / 3,622 / 24 / 8 / 7,428 |
| `referee_random_design_t1.log`, `referee_random_design_t3.log` | the same with one, resp. three terminals (aimed at C₀, C₃) | 442 + 1,500 | 139,077 | 569 | 2,644 / 0 / 2,120 / 0 / 0 / 5,356 |
| `referee_random_top.log` | 4,000 random profiles, n = 3, 4, many agents with the same top | 2,313 | 107,293 | 710 | 2,874 / 0 / 320 / 4 / 0 / 5,107 |

Also in every log, at every state: Lemma R0 (1,870,831 checks), Z0 (a) and (b) at every (r′, Λ′)-maximal state
(5,388 and 101,354), Z0 (c) at every key with at most three free agents (38,891 keys, including 24 at f = 2), (F1)
(22,424), and the exposure claim at every state with every free agent locally optimal (147,595). The deficit of
`k4/c4x.md` §1 (raw removal-only) equals Lemma H1's at all 546,213 min-frozen states.

**Coverage gaps.** Lemmas C₀ (one θ-b terminal, no slot) and C₃ (three or more terminals, x's best good alone) never
occur, neither in any data set of `k4/zmove_pot.md` §2 (`k4/zmove_pot.py`'s cases 3x, 3x= and 3p are 0 in every log)
nor in the referee's random profiles, including the runs aimed at them; the residual (E), (R3) never occurs either.
Their proofs were checked line by line only. In the referee's checker, Lemma S′ occurs only in the designed random
profiles (4 states, 83 certificates; in the data it is `k4/zmove_pot.py`'s case 2 at 638 states, checked there against
exact deficits only), and so does the fragility lemma (8 certificates); Lemma C₂ occurs in 28 random certificates and,
as case 3C′, at 874 states of the data.

## 3. Numbers

Re-run with the committed tools on this branch (after merging main at d21d3f7; main's later merge of #91 at 9d065e3
touches none of the files used):
- `python3 k4/zmove_pot.py …` with the commands of `k4/zmove_pot.md` §7 reproduces `run_hunts_n4n5.log` and
  `run_rc.log` line for line (only the "# time" line differs), and `attempts/k4_zmove_pot_attempts.py` reproduces
  `attempts.log` byte for byte. Every number of the notes, the ledger and the PR that cites these logs matches them
  (4,477 and 2 keys; 369 and 2,152 keys; 4,673 / 42 / 42 / 403 states without zm; 7,853 + 1,712 = 9,565 states
  cross-checked; AR cases 6,496 + 633 + 308 + 844 + 1,107 = 9,388 states).
- The data that the PR had run "only with a scratch evaluator" were rerun with the committed tool (logs below); the
  numbers that changed are in "Mismatches".

| log (`results/k4_zmove_pot/`) | what | keys with def* > 0 | states without zm in R / RLAM | AR states (cases) | second implementation |
|---|---|---|---|---|---|
| `run_hunts_n4n5_v2.log` | as `run_hunts_n4n5.log`, with the new counters | 4,477 f = 1, 2 f = 2 | 0 / 0 | 8,281 (1, 2, 3C, 3C′) | 7,853 states |
| `run_rc_v2.log` | as `run_rc.log` (without `--tmax`), with the new counters | 369 f = 1, 2,152 f = 2 | 0 / 0 | 1,107 (1) | 1,712 states |
| `run_n3.log` (new) | PR #80's n = 3 hunts, all 62,208 profiles (exhaustive at n = 3) | 62,208 f = 1 | 0 / 0 | 74,740 (1, 3C) | 4,034 states |
| `run_pr80_f2.log` (new) | PR #80's f ≥ 2 inputs and the T1-stuck profiles | 1,241 / 191 / 46 (f = 1 / 2 / 3) | 0 / 0 | 1,533 (1, 2, 3C, 3C′) | 2,360 states |
| `run_cover.log` (new) | compute/k4-cover's f = 2 and n = 5 hunts and seeds | 18 / 1,244 / 1,761 / 10 (f = 1 / 2 / 3 / 4) | 0 / 0 | 50 (1, 2, 3C′) | 613 states |

No class R, RU, RPARETO, LAM or RLAM failure anywhere; the failures of ALL, U, PARETO and TRL are those of `run_rc.log`
(cores 4604 and 4515) only, in particular none at n = 3. `k4/zmove_pot_referee_rc.py` (new, log `referee_rc.log`)
checks §2's description of cores 4515 and 4604 state by state.

**Mismatches and corrections.**
- **f ≥ 2 data (the PR's "should be rerun with the committed tool").** Done (rows 3–5 above). Verdicts unchanged: no
  Z′-maximum and no r′-maximal state without a one-move repair. Two scratch key counts are not reproduced: "PR #80's
  f ≥ 2 inputs and T1-stuck keys (1,522 keys)" is 1,478 keys with the committed tool (1,241 f = 1, 191 f = 2,
  46 f = 3; each profile counted once: the f = 2 catalogue profiles are among the T1-stuck ones); "compute/k4-cover's
  f = 2 hunt (3,871 keys)" is 1,243 keys on the committed input (1,611 records, 1,243 distinct profiles). The cause of
  the scratch counts cannot be recovered (the scratch evaluator was not committed).
- **"428 all-robust, locally optimal f = 2 states need a helper"**: reproduced exactly (`run_cover.log`), plus 2 at
  compute/k4-cover's two COVER⁺ failures. New: at f = 3, 1,758 of 1,804 such states need a (T3⁺) move with W ≠ ∅.
- **§5's statistic** (74% / 26% / 3 keys, a scratch sample of 22,358 keys) is now counted by the committed tool on all
  68,313 f = 1 keys of the five logs: 50,635 (74%) / 17,666 (26%) / 12.
- **The 9,388 AR states** of the first version are those of the first two logs; over all five logs the tool
  asserts 85,711 (0 violations). The 9,565 cross-checked states are now 16,572.
- **§2, core 4515** (`referee_rc.log`): (1) "r′ = 2" at the stuck states is r′ = 2 when B₃ is a pair and r′ = 1 when it
  is a singleton; (2) the trade "agent 1 takes {1,10} or {1,11}, agent 2 takes {3}, {3,10} or {3,11}" does not always
  keep agent 2 robust: with agent 2 on {3} it does not (r′ unchanged), and the r′-raising variants ({1,10} with {3,11},
  {1,11} with {3,10}) include a Pareto improvement at 4,136 of the 4,304 stuck states; at the other 168 none is one, and
  one of them lowers agent 2's value while agent 1 gains; (3) "the stuck states with B₃ = {6,7} are Pareto-maximal and
  locally optimal (the 42 failures)": the 42 have B₃ = {5,6} (13), {5,7} (17) and {6,7} (12), all among the 168; (4) the
  nearest repair of compute/k4-rc trades in the variant with agent 2 on {3}, which does not raise r′; so "the r′-raising
  move is the extra helper of the nearest repair" holds at core 4604 (agent 1's (T1) move to {1,12}, r′ 3 → 4, at all
  369 profiles) but at 4515 only in the sense that the same two agents move. Corrected in `k4/zmove_pot.md` §2 and the
  ledger row K4.ZMP.POT.
- **`attempts/k4-zmove-pot-pareto.md`** said that Lemma F's forest (no threat cycle) follows from Pareto-maximality or
  local optimality; only pool-optimality follows (from local optimality). Removed.
- **Stale references** after the merges of #82, #88, #89, #90 and #91: updated (PR #88's Lemma EX is refereed and part
  of the PROVED row K4.ZMH.S1C3; `results/k4_rc/` and `k4/f2.md` are on main; PR #91's Corollary E (E1) is the
  fragility of (E), proved differently).

## 4. What this review does not do

It does not prove ZMOVE, and it does not upgrade K4.ZMP.Z0 or K4.ZMP.AR: they are written proofs refereed once, by one
AI session, with no Lean formalization. Lemmas C₀ and C₃ are checked only on paper (see "Coverage gaps"). The data are
EVIDENCE (single model `k4/suite/model.py` plus the repo-free cross-check on a sample, and the referee's own checker on
the n = 3 sample and random profiles).
