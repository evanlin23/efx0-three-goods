# Lemma M by exchange between first agents

Workstream `proof/k4-lemmam-x` (ledger rows K4.LMX.*; target K4.RF.M, `k4/rulef.md` §6 Step 3: items M1–M3 and
(G2)). Builds on `k4/rulef.md` (PR #72, merged: Lemmas K, K′, KR, S, PROVED as K4.RF.K, K4.RF.KR, K4.RF.S; rule
RK, Lemma M), `k4/c4.md` (Lemma E, Theorems A₄, B₄, Lemma R; row K4.C4.AB.L), `k4/c4one.md` §6 (Lemmas Ω, Ψ; rows
K4.C4.OM, K4.C4.PSI) and `k4/lb4.md`. Notation as there. Nothing here changes K4.D, K4.T or K4.RF.M's status.

Tools: `k4/lemmam_x.c` (`k4/rulef.c` of #72 verbatim plus modes `-A43` to `-A46`: the class of every first agent,
and for every bad first agent the roles of the other agents in its run and the candidates a′ of §2; the adaptive
rule of §7), `k4/lemmam_x_run.py`, `k4/lemmam_x_adp.py` and `k4/lemmam_x_cores.py` (drivers, one worker,
resumable), `k4/lemmam_x_check.py` (second implementation on PR #33's model `k4/c4_verify_H/lb4r.py` with #72's
`k4/rulef_model.py`, without code from `k4/lemmam_x.c`), `k4/lemmam_x_inst.py` (H_t and HH_t),
`k4/lemmam_x_realize.py` (§5.2), `k4/lemmam_x_l46greedy.py` (§7.3). Lean: `lean/EFX/Adaptive.lean` (§7.4).

**Status** (rows K4.LMX.*; Lemmas 1–5 and Proposition R were refereed in the PR #77 review and found correct,
Proposition R conditionally on PR #83).
- **Lemma M is false if Proposition HH holds** (`k4/lemmam_bt.md` §3, PR #83, refereed correct, not yet merged: on
  HH₃, two copies of H₃ sharing one good, n = 26, no first agent is in K0 or K1). Then no exchange between first
  agents can prove it. Before HH₃ the
  exchange works on the data with the right partner (§2): the **needer at the end of a need chain** from an exposed
  frozen agent — the end shared by the most exposed frozen agents, or of least index — is good whenever a is bad (every
  strict profile with n ≤ 3 and n = 4 with at most two 4-good agents: 26,248 weighted bad pairs of the C code,
  25,960 in PR #33's model; the suite; H₃–H₅). The other proposed partners fail: the exposed frozen 4-good agent and the leader of r's
  block at n = 3, m = 6, r itself on H₄ (n = 17, both implementations) (`attempts/k4-lemmam-x-exchange.md`). The
  exchange agent's run follows Lemma Ψ's fall chain in only 12% of the bad pairs: LB's P-step key reorders it (§5.2).
- **Written proofs (refereed in the PR #77 review)**, using K4.C4.AB.L and Lemmas K, S (K4.RF.K, K4.RF.S): **Lemma 1**, a bad first
  agent's envy-free run has ω ≥ 1, an exposed frozen agent, and an exposed 4-good agent or (G2) (M3 reduces to (G2));
  **Lemma 2**, in (G2) a bad first agent forces k*'s two lower goods to be goods of r (r moves up to its top or its b
  and is then threatened by k*'s new base itself), and otherwise LB⁺'s rotation along a longest chain is certified
  (K1) with r served by a slot good of its own; **Lemma 3**, the failure of M1 is a shortage of slots: the exposed
  frozen agents need more kept-out goods than the unexposed terminals other than r have slot places (in particular a
  Hall violation against their chain ends); **Lemma 4**, the first block decides (two runs whose first blocks have the
  same agents and goods agree afterwards).
- **The repair: choose the inserted agent at every insertion step** (§6–§7). **Proposition R** (written proof,
  extending Proposition HH's count; refereed correct conditionally on PR #83): on HH_t with 2t − 2 > 3d no first agent
  works with at most d rotations, so no fixed rotation bound saves a rule that chooses only the first agent.
  **Lemmas 5, 5′** (refereed): a *block count*, computed when a block closes from the block and the goods still
  unpicked (and only falling afterwards), certifies the run without rotation when every block has count 0; at k = 3
  every block but the last has count 0 (conditions (1)–(2) of LB⁺'s bad case, block by block). **Conjecture M_ad**:
  some insertion sequence succeeds with at most one rotation; it is K4.LB4 relaxed to LB₄ʳ's three upgrade policies,
  so K4.LB4.E is evidence for it. In Lean `∃ τ, EFX.LB4R.SucceedsR 1 v agents goods τ`; `lean/EFX/Adaptive.lean`
  proves that it gives C₄∃ and TARGET₄ (§7.4).
- **Data for M_ad** (§7.3, EVIDENCE). No counterexample: M_ad holds wherever Lemma M does (all of §2's data), it is
  K4.LB4 relaxed (K4.LB4.E: 1.14·10¹² profiles), and on H₁–H₅, HH₃, HH₄ (with relabelings) the greedy rule "insert the
  agent whose block has the least count" finds Proposition HH's choices by itself (x_{1,2} of each copy first), every
  block at count 0, no rotation. Lemma 5 never fails (918,392,554 runs with every chain-end count 0, 959,476,926 with
  every slot count 0, all certified without rotation). But no block count is yet a local invariant (one
  implementation, smallest instances by hand): **(L0)** "after blocks of count 0 some agent starts a block of count 0"
  is false at n = 3, m = 6 for both counts; the greedy rule needs two rotations on 11,520 profiles (n = 3, m = 6
  smallest; both implementations); and **(L1∃)** "some insertion sequence has every non-last block at count 0" holds
  at n ≤ 3 and with one 4-good agent but fails at n = 4 with two 4-good agents, on 65,720 profiles for the chain-end
  count (m = 6 smallest) and 34,080 for the slot count (m = 7 smallest), all of them profiles where the greedy run needs
  no rotation. The per-block form M_ad^blk is implied by M_ad and untouched by every test here; its local form (L2)
  is the open step.
- **Found on the way**: `k4/rulef.c` (hence `k4/lemmam_x.c`) gives a rotated agent with a one-good base no slot in its
  Lemma K count and ω, while LB₄ʳ's text and Lean's `Output` give it one; so that code's "bad" (neither K0 nor K1) is
  an upper bound: 132 of the 1,420 bad leaves at n = 4 are K1 in PR #33's model (§2; notes added to K4.RF.K, K4.RF.RK
  and `k4/rulef.md`).

## 1. Setting

A k = 4 core with a strict profile. For an agent a, τ_a is "a first, then index order" (rule F's sequences,
`k4/rulef.md` §1), Phase 1 uses LB's P-step key, and P_a^ns, P_a^ef are the states after need-shrinking and after
envy-free upgrades to their fixpoints (LB₄ʳ's order). As in `k4/rulef.md` §4, a is in **K0** if some policy, owner o
and kept set K give Lemma K deficit ≤ 0 at P_a^pol, or ω(P_a^pol) ≤ 0; in **K1** if some single rotation of LB₄ʳ (every
frozen k, need chain and base O) from P_a^pol reaches a state with Lemma K deficit ≤ 0 for some owner (or ω ≤ 0 and no
base of three goods); pol ranges over need-shrinking and envy-free upgrades (RK₃ adds no upgrades, which only enlarges
the classes). Lemma K is taken with the kept-out sets of `k4/rulef.md` §2 Remark 4 (`-Y1`), the lemma as stated
(K4.RF.K). Call a **good** if a ∈ K0 ∪ K1 and **bad** otherwise. Then

> **Lemma M** (K4.RF.M, open). Every strict profile of every k = 4 core has a good first agent.

The exchange form asked for (`k4/rulef.md` §6 Step 3): *if a is bad, a specific agent a′ = c(a), read off a's run, is
good.* Any such map c proves Lemma M (take any a; if it is bad, c(a) is good). A weaker form also suffices: *if a is
bad, c(a) is good or c(a) is "smaller" than a in a fixed well-founded order* (then a minimal agent is good); §2 tests
both (the second as "iterated": follow c from a until a good agent, a repeat, or n steps).

For a bad a write P := P_a^ef. Then (Lemma 1 below) ω(P) ≥ 1, and with the notation of `k4/c4.md` §1–§2: r is the
last-processed agent that is not upgraded (not frozen, by (A1)), W := B_r ∪ J, an agent x ∉ U, x ≠ r, is *exposed*
(x ∈ E) if it is threatened by W with its base, F, T, U are the frozen, terminal and upgraded agents, B* is r's block
and k* its leader. A *need chain* from a frozen x is x = x₀ → x₁ → … → x_t with x_{i+1} ∉ U needing Y_{x_i}, x₀, …,
x_{t−1} ∈ F and x_t ∈ T; it lies in x's block and increases in processing order ((A4), (B2)); its last agent is an
*end* of x.

## 2. Which a′ works: the data

`k4/lemmam_x.c -A43 -r1 -Y1` (driver `k4/lemmam_x_run.py`) computes the class of every first agent, and for every bad
a the class of its envy-free run (`k4/c4.md`'s cases) and the candidates a′:
- (x1) *EF4*: the exposed frozen 4-good agent of least index;
- (x2) *the leader of r's block*;
- (x3) *the needer at the end of a need chain* from an exposed frozen agent, chosen in five ways: the end into which the
  most exposed frozen agents chain (ties: earliest processed; *maxload*), the end of least index, the end of a chain
  from the exposed frozen agent of least index, the earliest-processed end, the end of a chain from the
  earliest-processed exposed frozen agent;
- (x4) *r*;
- the earliest-processed free agent that does not hold its top.

| data | profiles | with a bad first agent | bad pairs (profile, a) | (x1) good | (x2) good | (x3) maxload, least index, end of least-index EF | (x3) earliest end | (x4) r good |
|---|---|---|---|---|---|---|---|---|
| every strict profile, n ≤ 3 and n = 4 with ≤ 2 four-good agents | 1,032,121,440 | 14,408 | 26,248 | 0 (of 25,448) | 0 | 26,248 | 26,248 | 26,248 |
| the same, classes recomputed in PR #33's model (`k4/lemmam_x_check.py`) | (the 1,420 bad leaves) | 14,408 | 25,960 | 0 | 0 (it is a) | 25,960 | 25,960 | 25,960 |
| the suite's 153 strict cores (all but H₅) | 153 | 9 | 11 | 1 (of 8) | 0 | 11 | 11 | 11 |
| H₃, H₄, H₅ (n = 13, 17, 21) | 3 | 3 | 2, 6, 10 | 2, 6, 10 | 0 | 2, 6, 10 | 2, 4, 7 (all, iterated) | 2, 0, 0 |
| HH₃ (n = 26), PR #83 | 1 | 1 | 26 | — | — | — | — | — |

(`results/k4_lemmam_x/exh_n2_n3_n4_12.log`, `check_bad_n234.log`, `suite.log`, `H2_H5_classes.log`; H₂ is in the
suite. On HH₃ every first agent is bad if Proposition HH of PR #83 holds (refereed correct, not yet merged; not
recomputed here, §6): then Lemma M fails there and no partner can be good. `k4/lemmam_x_check.py` has no candidate
(x2); in the model (x2) fails only because every bad run there is a single block, so the leader of r's block is a.)

*The two implementations differ in one convention, and `k4/lemmam_x.c` is the conservative one.* `k4/rulef.c` (hence
`k4/lemmam_x.c`) gives an upgraded or rotated agent no slot in its Lemma K count and its ω (`slots()` gives an
upgraded agent cap 0, `k4/rulef.c` line 305, and `apply_chain` marks the rotated head upgraded, line 333), while LB₄ʳ's text and
Lean's `Output` give a rotated agent with a one-good base O a slot (cap = 2 − |O|, `lean/EFX/LB4R.lean`, choice 5),
as PR #33's model does. So every K0/K1 certificate of the C code is one of the model, but not conversely: on 132 of
the 1,420 bad leaf profiles (288 of the 26,248 weighted pairs, all n = 4, m = 7 or 8) the model certifies with one
rotation a first agent the C code calls bad. Smallest: agents {0, 2, 3, 6}, {1, 2, 5}, {1, 4, 5, 6}, {3, 4, 6} with
values (2, 8, 3, 4), (2, 4, 3), (2, 8, 5, 4), (3, 4, 2); τ₁ and τ₃ give picks 6, 2, 5, 4 with Lemma K deficit 1, and
the rotation of 3 along 3 → 2 with O = {3} (2 takes 4, 3 keeps good 3 and gets a slot) has deficit 0 with owner 0;
the completion (0: {0, 1, 6}, 1: {2}, 2: {4}, 3: {3, 5}) is EFX₀ (checked). So the C code's "bad" verdicts are upper
bounds; the conclusions below hold for both.

Findings on the exhaustive data:
- No profile without a good first agent (Lemma M holds there, as `k4/rulef.md` §5.1 found).
- Every bad run is in (G2) (160 pairs) or has exactly one exposed 4-good agent (25,448 frozen, 640 free); none is of
  class A₄ or B₄ (Lemma 1(c) predicts none); every bad run is a single block, and r is a 4-good agent holding its b or
  c.
- (x1) is never good where it is defined; (x2) is a itself on every bad pair; every rule of (x3) and r are good on every
  bad pair. At n ≤ 4 the end of the chain *is* r.
- The second implementation (`k4/lemmam_x_check.py`, PR #33's model with #72's `rulef_model.py`) recomputes the classes
  of every first agent, the run classes, the candidates and the conclusions of Lemmas 1–3 on every bad leaf profile of
  the exhaustive run (1,420 distinct leaves standing for the 14,408 profiles): no profile without a good first agent;
  the classes agree except on the 132 leaves above, where the model certifies more; on the model's 1,612 bad leaf
  pairs (25,960 weighted) the conclusions of Lemmas 1–3 fail nowhere, the runs are (G2) (56 leaf pairs), one exposed
  frozen 4-good agent (1,292) or one free (264), every one a single block with r a 4-good agent holding its b (580) or
  its c (1,032), and the candidates are as in the table (`results/k4_lemmam_x/check_bad_n234.log`).

So on these data the exchange works with a′ = the needer at the end of the chain, but which end matters beyond
n = 4: on H₄ and H₅ r (the last end) is bad for every bad first agent, while the end shared by the most exposed frozen
agents (y₁, the y of the first gadget the cascade from ℓ reaches) is good; on H_t also (x1) (x_{1,1}) is good. And on
HH₃ there is nothing to exchange with if Proposition HH holds. The failed partners are recorded in
`attempts/k4-lemmam-x-exchange.md`.

## 3. What the run of a bad first agent looks like

**Lemma 1.** Let a be bad and P = P_a^ef. Then
- (a) ω(P) ≥ 1, and r is a terminal with |B_r| ≤ 1;
- (b) some exposed agent is frozen (E ∩ F ≠ ∅); so every bad run has an exposed frozen agent, and the ends of its
  need chains, the "needers at the end of a need chain" of §2, exist;
- (c) some 4-good agent is exposed, or the run is in (G2): LB⁺'s bad case of Theorem A₄ (E ∩ B* = {k*}, k* ≠ r, every
  need chain from k* ends at r, the sets π_x = {b_x, c_x} ∩ J of the exposed agents pairwise disjoint), r has four
  goods, and r is exposed after LB⁺'s rotation (k* takes O := {b_k*, c_k*}) along every need chain k* → r.

*Proof.* (a) ω(P) ≤ 0 puts a in K0. r is not frozen and holds at most its pick by (A1) of `k4/c4.md` §1 (K4.C4.AB.L).

(b) Under envy-free upgrades an upgraded agent holds an envy-free base, so it is never threatened (`k4/c4.md` §1), and
an agent without a pick is not threatened (Lemma E). So if E ∩ F = ∅, every agent of E is free in the sense of Lemma S
(`k4/rulef.md` §6, K4.RF.S: unmarked, not frozen, a one-good base), and Lemma S with o = r and the empty service σ of
the agents of E that are not free gives deficit(r, ∅) ≤ |σ| − κ₀ = −κ₀ ≤ 0: a ∈ K0.

(c) Suppose no 4-good agent is exposed. Outside LB⁺'s bad case Theorem A₄'s proof (K4.C4.AB.L) gives H ⊆ J with
|H| ≤ S − cap(r) meeting every π_x, x ∈ E, where every x ∈ E is a 3-good block leader holding a_x with
R_x ∩ W = {b_x, c_x} (Lemma E(i)). Serve x by the kept-out set {h}, h ∈ H ∩ π_x: W ∖ {h} meets R_x in one good, worth
less than a_x, so x is not threatened. This is a ∅-service of Lemma K for owner r of size ≤ |H| ≤ S − cap(r) = κ^∅
(r is not frozen, so N_r^∅ = N_r and κ^∅ counts the slot places of the agents other than r): a ∈ K0. In the bad case,
if r is not a 4-good agent exposed after LB⁺'s rotation along some chain k* → r, Theorem B₄ (K4.C4.AB.L) makes the
rotation a valid `RotStep` with ω′ ≤ 0, or gives the hitting set H′ of B₄(c), which serves the agents exposed w.r.t.
the owner k* by singletons in the same way, with |H′| ≤ S′ = κ′ (k* has no slot): a ∈ K1, since class K1 tries every
single rotation. So a bad run with no exposed 4-good agent is in (G2). ∎

(c) is the remark "C40 ⊆ K0 ∪ K1" of `k4/rulef.md` §4 and §6 Step 1 (made by the PR #72 referee), stated for one run.
So M3 of `k4/rulef.md` §6 reduces to (G2), which §4 treats.

Where the deficit of M1 sits is a count of slots. For x ∈ X := E ∩ F let ρ(x) be the least size of a kept-out set
D ⊆ J serving x (x not threatened by W ∖ D with its base; ∞ if none), let D(x) be the set of ends of need chains
from x that are neither r nor exposed, and let κ₀ be the number of slot places (cap(y) = max(0, 2 − |B_y|)) of the
agents y ≠ r that are neither frozen nor exposed.

**Lemma 3 (the overloaded ends).** Let a be bad and P = P_a^ef. Then Σ_{x ∈ X} ρ(x) > κ₀. In particular some
nonempty X′ ⊆ X has Σ_{x ∈ X′} ρ(x) > |⋃_{x ∈ X′} D(x)| (a Hall violation against the chain ends).

*Proof.* Serve each x ∈ X by a least kept-out set D_x; these serve all agents of E that are not free in the sense of
Lemma S (upgraded agents and agents without a pick are not exposed), with |σ| ≤ Σ_x ρ(x). By Lemma S (o = r, not
frozen, |B_r| ≤ 1), σ extends to a ∅-service of E at most one good larger per free agent of E, placed in that agent's
own slot place. Lemma K's κ for owner r counts the slot places of every agent other than r that is not frozen: at
least one for every free agent of E and, separately, the κ₀ places of the agents that are neither frozen nor exposed.
So the deficit of (r, ∅) is at most Σ ρ(x) − κ₀, and Σ ρ(x) ≤ κ₀ would put a in K0. For the second claim: if Hall's
condition held (each x taken ρ(x) times), there would be pairwise disjoint T_x ⊆ D(x) with |T_x| = ρ(x); the agents
of ⋃ T_x are ends of need chains, so terminals (unmarked, not frozen, other than r), not exposed, each with at least
one slot place, and Σ ρ(x) = |⋃ T_x| ≤ κ₀. ∎

At k = 3 every x ∈ X is a 3-good block leader with ρ(x) = 1 and an end in its own block, and the ends of distinct
leaders are distinct; X′ can only be {k*} with D(k*) = ∅ (all ends equal to r): conditions (1)–(2) of LB⁺'s bad case.
Lemma 3 does not see condition (3): when a junk good lies in π_x for two exposed agents, one kept-out good serves both,
while Σ ρ counts it twice. At k = 4 the
violating sets of the data are of three kinds: an end shared by several exposed frozen agents of one block (the gadgets
of H_t: X′ = {x_{j,1}, x_{j,2}, x_{j,3}}, D(X′) = {y_j}); all ends equal to r (every bad run with n ≤ 4); and an end
that is itself exposed (`k4/c4.md` §6.1 item 3). The candidates a′ of §2 are read off these ends.

## 4. (G2)

(G2) of `k4/c4.md` §6: no 4-good agent is exposed, LB⁺'s bad case holds (conditions (1)–(3) of Theorem A₄), r has four
goods, and after LB⁺'s rotation along any need chain k* → r (each chain agent takes its predecessor's pick, k* takes
O := {b_k*, c_k*} ⊆ W, Y_r returns to the junk) r is exposed w.r.t. the new owner k*. Theorem B₄ (K4.C4.AB.L) then
gives nothing. Lemma 2 shows that for a bad first agent this can only happen in a rigid shape: k*'s two lower goods are
goods of r. Otherwise one rotation (LB⁺'s, along a longest chain) is certified by Lemma K, with r served by a slot good
of its own; this is the step Theorem B₄ misses, since it serves exposed agents by kept-out goods only.

**Lemma 2.** Let a be bad, P = P_a^ef in (G2), and k* = x₀ → x₁ → … → x_t = r a longest need chain from k*
(t ≥ 1); put Y′ := Y_{x_{t−1}}, O := {b_k*, c_k*}, L := R_r ∩ W, and let P′ be LB⁺'s rotation along this chain. Then
- (a) in P no agent other than r needs Y′, and in P′ the agent r is a terminal (unmarked, not frozen, base {Y′}) and
  exposed;
- (b) O ⊆ R_r; precisely, either Y′ = b_r and O = {c_r, d_r}, or Y′ = a_r, O ⊆ {b_r, c_r, d_r} and L ⊆ O ∪ {d_r}.

*Proof.* (a) Let z ≠ r need Y′ in P. Upgraded agents need nothing under envy-free upgrades (`k4/c4.md` §1), so
z ∉ U, and by (B2) z is processed after x_{t−1}, in the same block; so z is none of x₀, …, x_{t−1}. If z ∈ T, then
x₀ → … → x_{t−1} → z is a need chain from k* that ends at z ≠ r, against (2) of the bad case. If z ∈ F, follow needs
from z: its pick is in NA, so some agent outside U needs it and is processed after z (B2); repeat while the agent
reached is frozen. Processing positions increase, so this stops at a terminal, and x₀ → … → x_{t−1} → z → … is a need
chain from k* (distinct agents, increasing positions) of length more than t; by (2) it ends at r, against the choice
of a longest chain. So only r needs Y′ in P.
In P′ (Lemma R, K4.C4.AB.L: NA′ ⊆ NA, and chain agents get the needs of their new picks): an agent off the chain needs
what it needed in P, hence not Y′. A chain agent x_i, 1 ≤ i ≤ t − 2, was processed before x_{t−1}, when Y′ was still
there, so it ranks Y′ below its old pick Y_{x_i} (if it values Y′ at all), hence below its new pick Y_{x_{i−1}}, which
it needed. x_{t−1} (if t ≥ 2) now holds Y_{x_{t−2}}, which it ranks above Y′ = its old pick. k* holds O, an envy-free
pair of a 3-good balanced agent, and needs nothing. So nobody needs Y′ in P′: r, which holds it, is not frozen, and it
is unmarked (`RotStep` marks only k*). It is exposed in P′ because P is in (G2).

(b) Suppose (b) fails; we certify P′ with owner k* and K = ∅ (Lemma K), so that a ∈ K1, a contradiction. P′ is a
valid pre-allocation reached by one `RotStep` (Theorem B₄(a)), every base but O has at most two goods, and k* is not
frozen. W′ := O ∪ J′ = W (Lemma R(a)). Let E′ be the agents other than k* threatened by W with their base in P′.
Upgraded agents are not threatened, and by Lemma R(c) (no 4-good agent is exposed in P, so no chain agent is exposed in
P′) E′ ⊆ (E ∖ {k*}) ∪ {r}.
- *x ∈ E′ ∖ {r}.* By (1) of the bad case x ∉ B*, so x is off the chain (which lies in B*) and keeps its base; by
  Lemma E(i) x is a 3-good leader holding a_x with R_x ∩ W = {b_x, c_x}. If {b_x, c_x} ⊆ O, then {b_x, c_x} = O and
  π_x = O ∩ J = π_k*, which is not empty (at most one good of O is Y_r), against (3). So some h_x ∈ {b_x, c_x} lies in
  W ∖ O = J′; the kept-out set {h_x} serves x (W ∖ {h_x} meets R_x in one good, worth less than a_x).
- *r, if r ∈ E′.* NA′ ⊆ NA and W ∩ NA = ∅, so the goods of L are ranked below Y′ (the goods above it are r's needs);
  r is threatened, so |L| ≥ 2 and Y′ ∈ {a_r, b_r}. We find a slot good g ∈ L ∩ J′ with r not threatened by W ∖ {g}
  when it holds {Y′, g} ((s) of Lemma K; r is a terminal of P′ with one slot place by (a)):
  - Y′ = b_r: L = {c_r, d_r}; as (b) fails, one of them is not in O, so it is in J′; take it as g. W ∖ {g} meets R_r in
    one good, worth less than b_r.
  - Y′ = a_r, b_r ∈ L ∩ J′: g = b_r; W ∖ {g} meets R_r in at most {c_r, d_r}, and v(c) + v(d) < v(a) + v(b).
  - Y′ = a_r, b_r ∉ L ∩ J′, c_r ∈ L ∩ J′: g = c_r; W ∖ {g} meets R_r in at most {b_r, d_r}, and v(b) + v(d) <
    v(a) + v(c).
  - Y′ = a_r, b_r, c_r ∉ L ∩ J′: then L ⊆ O ∪ {d_r}; as (b) fails, O ⊄ R_r, so |L ∩ O| ≤ 1, and |L| ≥ 2 gives
    d_r ∈ L ∩ J′ with L ∖ {d_r} a single good; g = d_r leaves one good, worth less than a_r.
- *Count.* The service has size at most |E ∖ B*| + 1 (one kept-out good per x ∈ E′ ∖ {r} ⊆ E ∖ B*, and g). Lemma K's
  κ′ counts the slot places of the agents other than k* that are not frozen in P′. Among them: r (one place, by (a));
  and for each x ∈ E ∖ B* the end τ(x) of a need chain from x (x itself if x ∈ T), a terminal of x's block (A4) with
  at least one place. These ends are distinct (one exposed 3-good agent per block, Lemma E(i)), lie outside B* (so
  they are not r and not on the chain, and keep their bases), and stay non-frozen since NA′ ⊆ NA. So
  κ′ ≥ |E ∖ B*| + 1, and the deficit of (P′, k*, ∅) is at most 0 (or ω′ ≤ 0). Class K1 tries every single rotation of
  LB₄ʳ, this one among them, so a ∈ K1. ∎

So for a bad first agent, (G2) is the configuration "k* is a 3-good leader whose two lower goods are goods of the
4-good r, which moves up to its top or to its b along the chain and is then threatened by k*'s new base O itself" (the
mechanism of `k4/c4.md` §6.1 item 4 and `attempts/k4-c4-lbplus-rotation.md`, here shown to be the only one). In the
case Y′ = b_r it is completely rigid: R_r = {a_r, Y′, b_k*, c_k*}, r's old pick is one of b_k*, c_k*, and a_r is held
by a frozen agent (r needs it). No rotation of the same run repairs it on the data: (G2) occurs in bad runs (§2), and
there the exchange of §2 repairs it; on every one of them, a′ = r (the needer at the end of the chain) is good.
What is open for (G2) is the exchange itself (§5).

## 5. The exchange: mechanism, Ω and Ψ, and what remains

### 5.1 A standalone step: the first block decides

**Lemma 4.** Let a, a′ be agents, β and β′ the first blocks of the runs of τ_a and τ_{a′}. If β and β′ have the same
agents and their agents pick the same set of goods (in any assignment), then after the first block the two runs
process the same agents in the same order with the same picks. Their Phase 1 states differ only in which agent of β
holds which good of the common set, and they have the same junk J₀.

*Proof.* When the first block ends, both runs have the same set G of remaining goods and the same unprocessed agents.
From there Phase 1 is a function of (G, unprocessed agents): a P-step takes the agent of least LB key (rank of its
favourite good of G, number of its goods in G, index), an insertion step the first unprocessed agent in index order
(τ_a and τ_{a′} have length one), and every agent takes its favourite good of G. By induction the two runs agree. ∎

(The upgrades can still differ outside β, since NA changes with the picks of β.) Lemma 4 reduces an exchange whose
first block keeps its agents and goods to a statement about that block. On the data this is the common case at
n ≤ 4, where the bad runs are single blocks and the exchange permutes the picks (§5.2); on H_t it is not (the exchange
agent lies in another gadget, and its run has a different block structure).

### 5.2 How the exchange agent's run relates to the bad run (data)

On the exhaustive data every bad run is a single block (§2) and the exchange agent a′ (the needer at the end; it is r
there) lies in it, so Lemma 4 says nothing and the question is how the block of τ_{a′} relates to that of τ_a. Lemma
Ψ (`k4/c4one.md` §6, K4.C4.PSI) predicts one shape: a′ takes its top, the agent that held it falls along one chain
(each takes its best good outside the goods already taken, until junk or a′'s old pick), and every other agent keeps
its pick; a second natural shape is a rotation of the picks along a cycle. `k4/lemmam_x_realize.py` compares, in
PR #33's model, on the 26,248 weighted bad pairs of the C code (25,960 in PR #33's model): τ_{a′}'s picks are Ψ's prediction on 3,032 (1,820 of them also a
cycle) and neither on 23,216 (`results/k4_lemmam_x/realize_maxload.log`, `realize_r.log`; the two partners coincide
at n ≤ 4). Smallest "neither": agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8),
(3, 5, 7, 6), (2, 3, 4, 8), a = 0, a′ = 2. τ₀ gives 0: 5, 1: 4, 2: 3; Ψ predicts 2: 5, 0: 4, 1: 3; but in τ₂ LB's key
processes 1 before 0 (its favourite 4 is its top, 0's is not) and gives 2: 5, 1: 4, 0: 1. So the exchange agent's run
is governed by LB's key, not by Ψ's fall chain, and an exchange proof along Ψ would need a version of Ψ for LB's key,
which Ω and Ψ do not provide. Since Lemma M is false if Proposition HH holds (§6), this is recorded only as the reason the exchange was not
completed.

## 6. No fixed rotation bound for a single chosen first agent

Proposition HH of `k4/lemmam_bt.md` §3 (PR #83, refereed correct, not yet merged) refutes Lemma M on HH₃ if it
holds: HH_t is two
copies A, B of H_t with ℓ_B's good u identified with ℓ_A's u (n = 8t + 2, m = 20t + 5, every agent 4-good, none
big-top), and for t ≥ 3 no first agent a makes LB₄ʳ(τ_a) succeed with at most one rotation. The same count, with q
rotations in place of one, bounds the rotations of every first agent.

**Proposition R.** For every d ≥ 0 and every t with 2t − 2 > 3d, on HH_t no first agent a makes LB₄ʳ(τ_a) succeed
with at most d rotations (under each upgrade policy, every owner or none, the owner's needs from its base or its
bundle, chains ending at any agent that is not frozen). So no fixed bound on the rotations makes a rule that chooses
only the first agent work: d = 1 fails on HH₃, d = 2 on HH₅, d = 3 on HH₆, and so on. (So every first agent of HH_t
needs at least (2t − 2)/3 rotations; PR #83's Corollary HH states (t − 1)/2. The difference is the per-gadget bound
below.) The proof uses PR #83's Lemma P and Lemmas 1–2; the PR #77 referee found it correct conditionally on them.

*Proof.* Fix a and let D be the copy containing a, C the other one. We use from `k4/lemmam_bt.md` §1, §3 (PR #83):
Lemma P (protecting goods: if forced agents have protecting sets Π(f) disjoint except for c goods each in two of them,
and own-slot sets Σ(f) disjoint from all Π's, then their number is at most the slot places of the free agents other
than the owner plus c), the forced agents (F1) (an x holding exactly its a, its b, c junk) and (F2) (an ℓ holding g₁,
u and u′ junk), with c = 1 (u is in Π(ℓ_A) ∩ Π(ℓ_B)); and Lemmas 1, 2 there (Phase 1 and upgrades of HH_t: C runs
exactly as H_t's index run and admits no upgrade, so all its gadgets are *untouched* (α): y_j on e_j, each x_{j,i} on
{a_{j,i}}, frozen; in D, gadgets before a's gadget j are (α), gadget j is (β1) or (β2), later ones (β2)).

*Needs stay in gadgets, after any number of rotations.* By induction on the rotations, as in Proposition H's proof
(`k4/c4.md` §7): every need of an agent is an a of its own gadget and each ℓ keeps g₁ and needs nothing; a chain
agent takes a good it needed, an a of its gadget; a rotated head takes O ⊆ R_k ∩ (J ∪ B_end), and validity keeps its
value-based needs among the a's. The copies share only u, which only the ℓ's value. So every need chain, hence every
RotStep, lies in one gadget of one copy.

*Balance per gadget.* For a completion X with owner o, the balance of a group of agents is (slot places of its free
agents other than o) − (its forced agents). Then: ℓ_A, ℓ_B at most 0 each; an untouched (α) gadget exactly −2 (y one
place, three frozen forced x's); and **every gadget of any valid state in which its agents' needs are a's of the
gadget has balance at most +1.** Bases stay nonempty (every agent of HH_t picks in Phase 1, by Lemmas 1–2 of #83; upgrades only add
goods, and a RotStep gives its head a nonempty O, `RotStep` requires O ≠ [], and every other chain agent its
predecessor's pick), so no agent has two slot places. Hence only y and an x whose base is a single good other than its
a can contribute +1 (an x on {a} is frozen or forced: at most 0; a base of two or more goods, or the owner, gives 0). Such an x values
its a (8) above its base (at most 6), so it needs a, which must then be a one-good base, held by y (frozen, 0); y
holds one good, so at most one x is of this kind, and then y gives 0. If that x is the owner with its needs from its
bundle, it gives 0 and y at most +1. So the gadget gives at most +1. In D the Phase 1 balances are at most −2 for
gadgets before j, +1 for j and 0 for later ones (Lemma 2 of #83 and the count there, every policy), so D starts at
most at 1.

*Count.* Let q_C, q_D ≤ d be the rotations in C and in D. At most q_C gadgets of C and q_D of D are touched. An
untouched gadget keeps its Phase 1 balance (−2 in C; at most −2, +1, 0 in D as above), a touched one gives at most +1,
so each touched gadget raises its copy's bound by at most 3. So the total balance is at most
(−2t + 3q_C) + (1 + 3q_D) + 0 ≤ −2t + 1 + 3d < −1 when 2t − 2 > 3d. Lemma P with c = 1 needs at least −1. An output
of LB₄ʳ is such a completion with an owner (ω = |NA| − σ ≥ −σ = 4t + 1 ≥ 1, and a base of three or more goods makes
its agent the owner), so there is none. ∎

The bound is a count, so it is the same for Lemma K's classes (whose certificates are outputs): on HH_t with
2t − 2 > 3d no first agent is certified with d rotations. On HH₃ (d = 1) the classes are those of PR #83 (every first
agent in neither K0 nor K1, `k4/rulef.c` and `k4/lemmam_bt.py`); they are not recomputed here (with the kept-out
sets of Remark 4 one first agent of HH₃ takes minutes, and the 26 together exceed the ~20 minutes allowed per run).
Note that `k4/rulef.c`'s "neither" is an upper bound in the sense of §2 (rotated agents get no slot there), so on HH₃
the written count is the stronger evidence. Larger d is a statement about HH₅ (n = 42) and beyond, where the count is
the evidence; a direct search with two nested rotations on HH₃ is out of reach here.

## 7. The repaired target: the insertion agent chosen at every insertion step

HH_t needs a chosen insertion step in each copy (x_{1,2} in each, then index order: no rotation, `k4/lemmam_bt.md` §3),
and Proposition R shows that no fixed number of rotations replaces those choices. The natural repair keeps the
rotations per block bounded and chooses every insertion step.

A *run* is now Phase 1 with any insertion sequence τ (the agent inserted at each insertion step chosen freely; P-steps
by LB's key, as in LB₄ʳ and Lean's `phase1State`). Its blocks β₁, …, β_k: each starts at an insertion step and is
closed under P-steps; agents of later blocks value no good picked in an earlier one (B1), and a need chain stays in
its block (A4). So the blocks are the natural unit for a local statement. In LB⁺ (k = 3) every block but the last is
automatically fine (Theorem A: each exposed leader has a terminal of its own block), and only the last can be one
slot short (the bad case, one rotation). At k = 4 a block can be short, and the insertion choice is what fixes it.

### 7.1 The block count, and why it certifies

Let a run have just closed a block β, and let G be the set of goods not yet picked. Take the state *without upgrades*
(each agent holds its pick; RK₃'s third policy). The following depend on β and G only:
- *frozen:* an agent of β whose pick is needed by another agent of β (by (B2) nobody outside β ever needs it);
- X_β: the frozen agents of β threatened by W_β with their pick, where W_β := G, and for the last block (when no agent
  is left) W_β := G ∪ {Y_r}, r its last-processed agent (the owner);
- ρ_β(x) for x ∈ X_β: the least s such that, for every good h ∈ G ∩ R_x (the owner's future pick, not known yet, cannot
  be kept out; in the last block no h), some D ⊆ (G ∩ R_x) ∖ {h} with |D| ≤ s leaves x not threatened by W_β ∖ D;
- κ₀(β): the slot places (one for an agent holding a pick, two for an agent without one) of the agents of β that are
  not frozen, not threatened by W_β with their pick, and other than r;
- the **block count** δ(β) := max(0, Σ_{x∈X_β} ρ_β(x) − κ₀(β)).

The first version of the count (the *chain-end count*, `k4/lemmam_x.c`'s default; every log made without `-G1`
uses it) had, in place of κ₀(β), the ends of need chains: with D_β(x) the ends of need chains from x inside β
that are not threatened by W_β with their pick, other than r, δᵉ(β) := max(0, max over nonempty X′ ⊆ X_β of
Σ_{x∈X′} ρ_β(x) − |⋃_{x∈X′} D_β(x)|). The ends are agents counted in κ₀(β), so δ(β) ≤ δᵉ(β) (take X′ = X_β), and
everything below holds for δᵉ too. The slot count δ is the PR #77 referee's repair (§7.3, (L1∃)).

**Lemma 5 (block counts certify).** If every block of a run has block count 0, its Phase 1 state (no upgrades) has
Lemma K deficit at most 0 with owner r and K = ∅. So LB₄ʳ(τ) succeeds without rotation (no-upgrade policy).

*Proof.* Without upgrades r, the last-processed agent, is not frozen ((A1): an agent needing Y_r would come after r).
Let W := J ∪ {Y_r} be the final W, E the exposed agents and X = E ∩ F. For x in a block β_i other than the last, W ⊆ G_i
(the goods unpicked when β_i closed; r's pick is among them), and for the last block W = W_β. Frozen status is final:
by (B2) the needs of every agent lie in its own block. So, by monotonicity of threats, every x ∈ X lies in some X_{β_i},
and every agent counted in κ₀(β_i) is, in the final state, an unmarked agent other than r that is neither frozen nor
exposed.
For x ∈ X ∩ β_i (not the last block) take h := Y_r if Y_r ∈ R_x (else any h), and D ⊆ (G_i ∩ R_x) ∖ {h} of size at most
ρ_{β_i}(x) as in the definition; then D_x := D ∩ J is a kept-out set of Lemma K: W ∖ D_x ⊆ (G_i ∖ D) ∪ {Y_r} = G_i ∖ D
(Y_r ∉ D, and Y_r ∈ G_i), so x is not threatened. In the last block D ⊆ G = J directly. So the agents of X are served
with at most Σ_{x∈X} ρ(x) goods. The free exposed agents cost at most their own places (Lemma S, owner r with
|B_r| ≤ 1), and Lemma K's κ for owner r counts, besides their places, the places of the agents counted in the κ₀(β_i)
(different blocks have different agents). So the deficit of (r, ∅) is at most
Σ_i (Σ_{x∈X_{β_i}∩X} ρ(x) − κ₀(β_i)) ≤ Σ_i δ(β_i) = 0 (as in Lemma 3's proof). ∎

At k = 3 every block but the last has count 0 whatever its leader: a non-leader has lost a good, so at most one of its
goods below its pick is unpicked and it is not threatened by G; the leader x, if frozen and exposed, has
ρ = 1 (if h is b_x keep c_x out, and conversely) and an end in its block that is not r and not exposed. The last block
has count at most 1, and count 1 only under conditions (1)–(2) of LB⁺'s bad case. So Lemma 5 gives, block by block,
the part of LB⁺'s Theorem A that conditions (1)–(2) describe; it does not see condition (3) (a junk good shared by two
π_x serves both).

The count of a block closed earlier can be taken again later, against the goods G′ ⊆ G still unpicked then (with the
same robust ρ while agents remain; once every agent is processed, against the final W = J ∪ {Y_r} with D ⊆ J ∩ R_x and
no h). Call it δ_i(G′), and the *cumulative count* after block β_j the sum Σ_{i≤j} δ_i(G′) with G′ the goods unpicked
after β_j.

**Lemma 5′ (the counts only fall).** For every block β_i, δ_i(G′) does not increase as goods are picked, up to and
including the final count; and if every block has final count 0 (in particular, if the cumulative count of the
complete run is 0), the conclusion of Lemma 5 holds. The same holds for the chain-end count δᵉ.

*Proof.* Let G″ ⊆ G′ be the unpicked goods at two times after β_i closes, with agents still left at both (so r is
unprocessed and Y_r ∈ G″). Frozen status is the same. X shrinks (threats by a subset). For x ∈ X and h ∈ G″ ∩ R_x, a
set D ⊆ (G′ ∩ R_x) ∖ {h} serving x against G′ ∖ D gives D ∩ G″, which serves x against G″ ∖ D ⊆ G′ ∖ D; and h ranges
over fewer goods. So ρ falls. An agent not threatened by G′ is not threatened by G″, so κ₀ (and D(x)) grows. Hence
δ_i(G″) ≤ δ_i(G′). For the final count, take h := Y_r (if Y_r ∈ R_x, else any h): D ∩ J serves x against
W ∖ (D ∩ J) = (J ∖ D) ∪ {Y_r} ⊆ G″ ∖ D, and the agents counted other than r (r is not in β_i unless β_i is the last
block, whose only count is the final one) only gain. The second claim is Lemma 5's proof with the final W in place of
G_i: it used only, for each block, ρ and κ₀ (or D) taken against the final W. ∎

### 7.2 Adaptive Lemma M

**Conjecture M_ad (one rotation in all).** For every strict profile of every k = 4 core some insertion sequence τ
(the inserted agent chosen at every insertion step) makes LB₄ʳ(τ) succeed with at most one rotation. In Lean:
`∃ τ, EFX.LB4R.SucceedsR 1 v agents goods τ` (`TheoremAdaptive`, §7.4).

**Conjecture M_ad^K (its certificate form).** Some τ and some upgrade policy reach, with at most one rotation, a state
of Lemma K deficit ≤ 0 (or ω ≤ 0 and no base of three goods). M_ad^K ⟹ M_ad, since Lemma K's certificates are outputs
of LB₄ʳ (K4.RF.K). The data of §7.3 test M_ad^K.

**Conjecture M_ad^blk (one rotation per block).** Some τ makes LB₄ʳ(τ) succeed with rotations whose heads lie in
pairwise distinct blocks of the Phase 1 run (each rotation is charged to its head's Phase 1 block; after a RotStep
whose head takes O worth less than its pick, the head's new needs may leave its block, so a rotation is not confined
to a block). So with at most as many rotations as blocks, that is, insertion steps. M_ad ⟹ M_ad^blk. Its Lean
relaxation is `∃ τ d, d ≤ (insertion steps of τ's run) ∧ SucceedsR d v agents goods τ`; it gives C₄∃ through
`succeeds_of_succeedsR` while d ≤ 3, and beyond that needs `sound_of_succeeds` for every rotation bound (§7.4). The
data below do not separate M_ad from M_ad^blk: every profile tested satisfies M_ad itself. HH_t does not either: two
insertion choices and no rotation (PR #83's sequence (x^A_{1,2}, x^B_{1,2}); the greedy rule below finds it).

**What is known about it.** M_ad is K4.LB4 relaxed (as the PR #77 referee observed): LB₄ (`k4/lb4.md` §2) tries every
insertion sequence with need-shrinking upgrades and one rotation, so "LB₄ never fails" (K4.LB4, CONJECTURE) gives
M_ad with LB₄ʳ's three policies in place of need-shrinking alone. Its evidence K4.LB4.E is far larger than ours:
no failure on any strict profile of any core with n ≤ 4, or with n = 5 and at most two 4-good agents
(1,139,100,918,624 profiles; `k4/lb4.c`, one implementation). K4.AD.OPT (a) measures M_ad directly in LB₄ʳ's form (n ≤ 3,
and n = 4 with one to three 4-good agents: the fewest rotations over every insertion sequence is at most one). Lemma M
is the case τ = (a), so M_ad also holds wherever Lemma M does (every profile of §2's data), and on H_t and HH_t by the
runs of §7.3. No counterexample is known. In Lean, the special cases `TheoremC4` (every τ) and `TheoremC4index`
(τ = []) are false (H₅, Proposition H), and `TheoremRuleF` (τ = [a]) and `LemmaM` (`lean/EFX/RuleFK.lean`, #81:
some first agent in K0 or K1, which gives `TheoremRuleF`) are false if Proposition HH holds (HH₃); `TheoremC4exists`
(K4.D on strict cores, `C4exists_iff`) is the conclusion. M_ad's own statement is `TheoremAdaptive` (§7.4).

**Local forms.** Call a block *last* if it processes every agent still unprocessed. A local form says how to build
the run block by block with Lemma 5 (or 5′) as the certificate:
- (L0) *after any prefix of blocks of count 0, some unprocessed agent starts a block of count 0* (the last block
  included). **False** at n = 3, m = 6 (§7.3; one implementation, `k4/lemmam_x.c`, and by hand): every first block has
  count 1, for the slot count δ, the chain-end count δᵉ and the cumulative count (a last block included).
- (L1) *after any prefix of blocks of count 0, some unprocessed agent starts a non-last block of count 0, or a last
  block whose run succeeds with at most one rotation.*
- (L1∃) *some insertion sequence has every non-last block at count 0 and succeeds with at most one rotation.* (L1)
  implies (L1∃), and (L1∃) implies M_ad (for (L1∃) the cumulative count of Lemma 5′ is the same as the count at
  closing). True at n ≤ 3 and at n = 4 with one 4-good agent; **false** at n = 4 with two 4-good agents, for the
  chain-end count (m = 6) and for the slot count (§7.3; a non-existence claim of one implementation, `k4/lemmam_x.c`,
  with the smallest instances checked by hand), on profiles where M_ad holds without rotation.

So neither block count of §7.1 is the local invariant. The chain-end count fails already where Lemma K's deficit
without upgrades is negative (it ignores the slots of unexposed agents that end no chain; the slot count repairs this,
the PR #77 referee's diagnosis); the slot count still fails where ω ≤ 0 makes an owner unnecessary (the smallest failure, m = 7: the run is completed without owner, while the counts charge every threat by the junk to the owner's bundle). A local form needs a count that sees
more of Lemma K (upgrades, other owners, kept sets K), or the per-block repair of M_ad^blk: *(L2) after any prefix of
repaired blocks some unprocessed agent starts a block that one rotation inside it repairs.* (L2) is not tested here;
a block count of 1 alone does not give it (§7.3: a single block of count 1 can need two rotations).

Whatever the count, the step is what an exchange lemma would prove: at an insertion step where the agent of least
index starts a bad block, show that another agent, read off that block (an overloaded end, Lemma 3), starts a good
one. Ω and Ψ (`k4/c4one.md` §6) are moves of this kind (they change the agent inserted at the start of one block and
keep the prefix), but their new block has P-steps in their order, not LB's key's, and they bound ω, not a block count,
so they do not give the step as they stand. And for the count of §7.1 the overloaded end is the wrong partner (§7.3:
it starts a block of count 0 at 39% of the steps where some agent does at 80%).

### 7.3 Data (EVIDENCE)

`k4/lemmam_x.c -A44` builds the run greedily: at each insertion step it simulates the block of every unprocessed
agent, takes the least block count (ties: least index), and at the end reports the least number d ≤ cap of nested
rotations after which Lemma K certifies the run under some policy (`k4/lemmam_x_adp.py`). The count is the
chain-end count δᵉ by default and the slot count δ with `-G1` (`-W1`: the cumulative count of Lemma 5′). `-A46`
searches all insertion sequences whose non-last blocks have count 0 (L1∃) for the least d. Lemma K, the rotations, the
counts and the (L1∃) search are those of `k4/lemmam_x.c` (`-Y1 -r1`), one implementation; the greedy's rotation
counts are rechecked in PR #33's model by `k4/lemmam_x_check.py --adp` (all 96 chain-end runs with d ≥ 2 and every
60th of those with d = 1: the same d on every one, `results/k4_lemmam_x/check_adp_d2.log`,
`check_adp_d1_sample.log`).

| data, greedy rule | profiles | every block count 0 | d = 0 | d = 1 | d ≥ 2 | some non-last block > 0 |
|---|---|---|---|---|---|---|
| every strict profile, n ≤ 3 and n = 4 with ≤ 2 four-good agents, chain-end count δᵉ | 1,032,121,440 | 918,392,554 | 1,030,069,300 | 2,040,620 | 11,520 | 4,377,332 |
| the same, slot count δ (`-G1`) | 1,032,121,440 | 959,476,926 | 1,030,584,820 | 1,525,100 | 11,520 | 2,607,312 |
| H₁–H₅, each with two relabelings (δᵉ) | 15 | 15 | 15 | 0 | 0 | 0 |
| HH₃, HH₄, each with one relabeling (δᵉ) | 4 | 4 | 4 | 0 | 0 | 0 |

(`results/k4_lemmam_x/adp_exh_n2_n3_n4_12.log`, `adpG_n2_n3_n4_1.log`, `adpG_n4_2a.log`, `adpG_n4_2b.log`,
`adp_Ht.log`, `adp_HH.log`, `adp_HH4.log`; on HH₄ with `-V1`, Lemma 5's certificate.)

Findings:
- *Lemma 5 never fails*: the runs with every block count 0 (918,392,554 for δᵉ, 959,476,926 for δ) are certified by
  Lemma K without rotation (the search was run, not Lemma 5).
- *On H_t and HH_t the greedy rule finds Proposition HH's choices by itself*: on H₅ τ = (2, 0, 6, 7, 10, 11, …) inserts
  x_{1,2} first, on HH₃ τ = (3, 0, 7, 8, 11, 12, 15, 1, 19, 20, 23, 24) inserts x_{1,2} of each copy before its ℓ
  (agents 0, 1 are ℓ_A, ℓ_B; A's gadgets are 2–13, B's 14–25, each x_{j,1}, x_{j,2}, x_{j,3}, y_j); every block has
  count 0 and no rotation is needed, also after relabeling. These are the instances on which every rule choosing only
  the first agent fails (§6), if Proposition HH holds.
- *The greedy rule is not itself a proof route*: 11,520 profiles need two rotations after its run (both counts; both
  implementations). Smallest: n = 3, m = 6 (core 17 of `results/k4_certs_3.json.gz`), agents {0, 1, 4, 5},
  {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (3, 5, 7, 6), (2, 3, 4, 8): every agent starts a single block
  (it is last) of count 1, the tie goes to agent 0, whose run needs two rotations, while another first agent needs at
  most one (Lemma M holds there). So a last block's count does not decide its rotations; (L1) chooses the last block
  by its rotations, not its count.
- *(L0) is false* (one implementation, `k4/lemmam_x.c`; this instance also by hand and by `k4/lemmam_x_blocks.py`,
  which recomputes the counts on PR #33's model). Agents {0, 2, 4, 5}, {1, 3, 5}, {2, 3, 4, 5}
  with values (3, 5, 7, 6), (2, 3, 4), (4, 2, 8, 3) (n = 3, m = 6, core 27 of `results/k4_certs_3.json.gz`).
  Inserting 0: 0 takes 4, then 2 (it lost 4) takes 2; the block {0, 2} is not last; 0 is frozen (2 needs 4) and
  threatened by G = {0, 1, 3, 5} (v₀ = 3 + 6 = 9 > 7), ρ = 1 ({0} or {5} kept out, whichever the owner does not take),
  and the only other agent, 2, is threatened by G (v₂ = 2 + 3 = 5 > 4): κ₀ = 0, count 1 (for δᵉ too: 2 is 0's only
  end). Inserting 1: 1 takes 5, then 0 takes 4 and 2 takes 2, a last block with r = 2; 0 is frozen, threatened by
  W = {0, 1, 2, 3} (8 > 7), ρ = 1, and 1 is threatened (3 + 2 > 4): κ₀ = 0, count 1. Inserting 2: 2 takes 4, 0 takes
  5, 1 takes 3, a last block with r = 1; 0 is frozen (1 needs 5), threatened by W = {0, 1, 2, 3} (8 > 6), ρ = 1, and 2
  is frozen too: κ₀ = 0, count 1. (The greedy run is τ = (0, 1) with counts 1, 0 and needs one rotation.) On the
  exhaustive data the greedy run has a non-last block of positive count on 4,377,332 profiles (δᵉ; 4,351,436 of them
  still need no rotation, 25,896 one) and on 2,607,312 (δ).
- *The local exchange by the overloaded end* (δᵉ): at the 22,006,832 (weighted) insertion steps where index order's
  block is not last and has positive count, the block of its overloaded end (the end of chains from the most exposed
  frozen agents) has count 0 at 8,592,608, and some agent's block at 17,671,224.

**(L1∃) on the exhaustive data** (`-A46`, the least d over every insertion sequence whose non-last blocks have count
0; a non-existence claim of one implementation, `k4/lemmam_x.c`, wherever it says "none"; the smallest instances
also by hand and by `k4/lemmam_x_blocks.py`):

| count | n ≤ 3 (300,026,592) and n = 4 with one 4-good agent (7,247,232): d = 0 / 1 / none | n = 4 with two 4-good agents (724,847,616): d = 0 / 1 / no such sequence |
|---|---|---|
| chain-end δᵉ | 306,884,800 / 389,024 / 0 | 724,547,466 / 234,430 / 65,720 |
| slot δ (`-G1`) | 306,884,800 / 389,024 / 0 | 724,579,458 / 234,078 / 34,080 |

(`results/k4_lemmam_x/l46_n2_n3.log`, `l46_n4_1.log`, `l46_n4_2a.log`, `l46_n4_2b.log`, `l46G_n2_n3_n4_1.log`,
`l46G_n4_2.log`.) So (L1∃) holds at n ≤ 3 and with one 4-good agent, and fails at n = 4 with two 4-good agents for
both counts.
- *Chain-end count*: smallest failure m = 6 (core 77 of `results/k4_certs_4_n4_2.json.gz`, checked by hand): agents
  {0, 2, 5}, {0, 3, 4, 5}, {1, 2, 4, 5}, {1, 3, 5} with values (2, 4, 3), (5, 2, 8, 4), (5, 2, 8, 4), (2, 4, 3).
  Every first block leaves one agent out and has δᵉ = 1: inserting 0 or 2 gives the block {0, 1, 2} (2 holds 4,
  needed by 1, which holds 0; 2 is threatened by G = {1, 3, 5}, 5 + 4 > 8, and its only end 1 is threatened,
  4 + 2 > 5); inserting 1 or 3 gives {1, 2, 3} (1 holds 4, needed by 2, which holds 1; 1 is threatened by
  G = {0, 2, 5}, 5 + 4 > 8, and its only end 2 is threatened, 2 + 4 > 5). The diagnosis (the PR #77 referee's): with
  τ = (0, 3), say, Lemma K's deficit for owner r without upgrades is −1, because agent 0 (in the first block, free,
  unexposed, not a chain end) has an unused slot place; δᵉ fails only because it counts chain ends. The slot count δ
  counts that place: on this profile δ gives counts (0, 0) and the run needs no rotation. On all 65,720 profiles the
  greedy run with δᵉ succeeds with d = 0 (`results/k4_lemmam_x/l46greedy_n4_2.log`, `k4/lemmam_x_l46greedy.py`, one
  implementation; the PR #77 audit found the same with its own script).
- *Slot count*: 34,080 profiles without such a sequence. Smallest (agents {0, 2, 3, 4}, {1, 3, 5, 6}, {2, 5, 6}, {4,
  5, 6} with values (6, 3, 7, 5), (6, 7, 3, 5), (4, 2, 3), (4, 2, 3) (n = 4, m = 7, core 123 of
  `results/k4_certs_4_n4_2.json.gz`)): every first block leaves an agent out and has positive slot count (inserting 0
  or 1 gives a block of two agents with δ = 2: the frozen one needs two goods kept out, its partner is threatened;
  inserting 2 or 3 gives a block of three with δ = 1; by hand and by `k4/lemmam_x_blocks.py`). Yet every first agent
  is in K0 there (both implementations), and the greedy run τ = (2, 3) (counts 1, 0) has ω = 0 without upgrades: its
  three junk goods fit the slot places of the three free agents, so it is completed without an owner, while both
  counts charge every threat by the junk to the owner r's bundle. On all 34,080 the greedy run with δ succeeds with d
  = 0 (`results/k4_lemmam_x/l46greedyG_n4_2.log`, `k4/lemmam_x_l46greedy.py -G1`, one implementation).

(L1), with "every prefix", is not tested separately. With the cumulative count the (L1∃) numbers are those of the
count at closing (`l46W_n2_n3.log`), necessarily: along a sequence whose earlier blocks have count 0, the cumulative
count after a new block is that block's count at closing. The greedy rule's numbers with the cumulative count are the
same at n ≤ 3 too (`adpW_n2_n3.log` against `adp_n2_n3_after_W.log`: at n ≤ 3 runs have few blocks).

### 7.4 Lean

`lean/EFX/LB4R.lean` and `lean/EFX/RuleF.lean` already contain what M_ad needs: `phase1State v agents goods τ` takes
any insertion sequence (its j-th entry picks the (τ_j mod u)-th unprocessed agent in index order, so a sequence of
agents, as `k4/lemmam_x.c` prints it, translates by replaying Phase 1, as `k4/lemmam_x_check.py` does), and
`SucceedsR d v agents goods τ` is "LB₄ʳ(τ) succeeds with at most d rotations". `lean/EFX/Adaptive.lean` (the text
compiled first by the PR #77 referee; ledger K4.LMX.AD.LEAN, `lean/check.sh` passes) states M_ad and proves what it
gives:

    def TheoremAdaptive (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
      ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup →
        IsCore4 v agents goods → Strict v agents goods → ∃ τ : List Nat, SucceedsR 1 v agents goods τ

    theorem C4exists_of_adaptive (h : TheoremAdaptive A G) : TheoremC4exists A G
    theorem adaptive_of_ruleF (h : TheoremRuleF A G) : TheoremAdaptive A G
    theorem target4_of_adaptive (I : Inst) (hn : 0 < I.n) (h : TheoremAdaptive (Fin I.n) (Fin I.m))
        (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X

The proofs are those of `C4exists_of_ruleF` and `target4_of_ruleF` with `⟨τ, hτ⟩` for `⟨a, -, ha⟩`; the same edit
of `C4existsConn_of_ruleFConn` would give `AdaptiveConn ⟹ C4existsConn ⟹ TARGET₄` (`AdaptiveConn` with `Connected`
and a 4-good agent, as `RuleFConn`; not added). M_ad^blk needs `SucceedsR d` for unbounded d: `sound_of_succeeds`
generalizes at once (`rotReach_inv` holds for every d), but `succeeds_of_succeedsR` needs d ≤ 3, so that version
would need a short `sound_of_succeedsR`. Lemma K's certificates are `Output`s (`k4/rulef.md` §7, step 1;
`EFX.LB4R.output_of_lemmaK`, K4.RF.K.LEAN), so Lemmas 5, 5′ and the data of §7.3 are statements about `SucceedsR 0`
and `SucceedsR 1`.

## 8. Reproduce

One worker throughout; each line under ~20 minutes except where noted. `k4/lemmam_x_run.py` and `k4/lemmam_x_adp.py`
compile `k4/lemmam_x.c` into the temporary directory under a name made from a hash of the source and print the hash
at the top of every log; `--checkpoint=FILE` makes the exhaustive runs resumable.

*Which version made which log.* The source grew by additions only: after the first version (hash 4138c78766bce0e0,
commit 8724474: `exh_n2_n3_n4_12.log`) each later one adds modes or options (`-A44`–`-A46`, `-U`, `-V`, `-W`, `-G`)
and raises MAXN from 40 to 48; the code of `-A43` and every line of `k4/rulef.c` are unchanged (a diff of the
versions shows only added lines). Hashes: eac6b06d1052bd78 (8fa75d1: `adp_Ht.log`, `adp_HH.log`), f4b4e32ba2ab3fd5
(7e58583: `adp_HH4.log`, `adp_exh_n2_n3_n4_12.log`), aab69414c3a7f21e (e05267d: `H2_H5_classes.log`, `suite.log`,
`adpW_n2_n3.log`, `adp_n2_n3_after_W.log`, `l46*_n*.log` without G, `l46_core77_n4_2.log`), ea801dd6ee8ba1fb (the
current source, with `-G`: `adpG_*.log`, `l46G_*.log`, `l46greedy*.log`). `adp_n2_n3_after_W.log` checks numerically
that aab69414 reproduces f4b4e32b's `-A44` statistics at n ≤ 3; `-G` only adds a branch taken when `-G1` is given.
```
# §2: classes of every first agent, roles and candidates in the bad runs (exhaustive, ~32 min, resumable)
python3 k4/lemmam_x_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz \
    results/k4_certs_4_n4_2.json.gz -A43 -r1 -Y1 -D43 --data=BAD.txt --checkpoint=CK.jsonl
python3 k4/lemmam_x_check.py --profiles=BAD.txt            # second implementation on the bad leaves (seconds)
python3 k4/lemmam_x_inst.py SUITE > SUITE.txt;      python3 k4/lemmam_x_run.py --profiles=SUITE.txt -A43 -r1 -Y1 -D43
python3 k4/lemmam_x_inst.py H2 H3 H4 H5 > HT.txt;   python3 k4/lemmam_x_run.py --profiles=HT.txt -A43 -r1 -Y1 -D43
python3 k4/lemmam_x_inst.py H4 > H4.txt;  python3 k4/lemmam_x_check.py --profiles=H4.txt --agents=0,16   # model
python3 k4/lemmam_x_realize.py BAD.txt --cand=endEF_maxload   # §5.2 (and --cand=r)
# §7: the adaptive rule (block counts) on H_t, HH_t with relabelings, and exhaustively (~22 min, resumable)
python3 k4/lemmam_x_inst.py H1 H2 H3 H4 H5 --relabel=2 > HT2.txt; python3 k4/lemmam_x_adp.py --profiles=HT2.txt -Y1 -r1
python3 k4/lemmam_x_inst.py HH3 --relabel=1 > HH.txt;  python3 k4/lemmam_x_adp.py --profiles=HH.txt -Y1 -r1
python3 k4/lemmam_x_inst.py HH4 --relabel=1 > HH4.txt; python3 k4/lemmam_x_adp.py --profiles=HH4.txt -Y1 -r1 -V1
python3 k4/lemmam_x_adp.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz \
    results/k4_certs_4_n4_2.json.gz -Y1 -r1 --checkpoint=CK2.jsonl --data=ADPBAD.txt
grep ' d=2 ' ADPBAD.txt > D2.txt; python3 k4/lemmam_x_check.py --adp=D2.txt      # the rotation counts in the model
python3 k4/lemmam_x_adp.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -Y1 -r1 -W1        # cumulative count
python3 k4/lemmam_x_adp.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -Y1 -r1 -A46 [-W1] # (L1∃)
python3 k4/lemmam_x_adp.py results/k4_certs_4_n4_2.json.gz -Y1 -r1 -A46 --range=0:150 --checkpoint=CK3.jsonl  # n = 4
python3 k4/lemmam_x_adp.py results/k4_certs_4_n4_2.json.gz -Y1 -r1 -G1 -A46     # (L1∃) with the slot count (~2 min)
python3 k4/lemmam_x_adp.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz \
    results/k4_certs_4_n4_2.json.gz -Y1 -r1 -G1 --checkpoint=CK4.jsonl                # greedy, slot count (~5 min)
python3 k4/lemmam_x_l46greedy.py results/k4_certs_4_n4_2.json.gz -Y1 -r1 [-G1]  # profiles without (L1∃): greedy d
python3 k4/lemmam_x_cores.py results/k4_certs_3.json.gz 17 -A44 -Y1 -r1 -D47     # the greedy rule's 2 rotations
python3 k4/lemmam_x_cores.py results/k4_certs_3.json.gz 27 -A44 -Y1 -r1 -G1 -D47 # (L0)'s core
```
`-V1` takes Lemma 5's certificate when every block count is 0 instead of searching Lemma K's classes again (on HH₄,
m = 85, that search exceeds the time allowed; on the exhaustive data it is run, and agrees, §7.3).
