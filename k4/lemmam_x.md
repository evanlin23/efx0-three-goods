# Lemma M by exchange between first agents

Workstream `proof/k4-lemmam-x` (ledger rows K4.LMX.*; target K4.RF.M, `k4/rulef.md` §6 Step 3: items M1–M3 and
(G2)). Builds on `k4/rulef.md` (PR #72, branch `proof/k4-rulef` at aebd620: Lemmas K, K′, KR, S, rule RK, Lemma M),
`k4/c4.md` (Lemma E, Theorems A₄, B₄, Lemma R; row K4.C4.AB.L), `k4/c4one.md` §6 (Lemmas Ω, Ψ; rows K4.C4.OM,
K4.C4.PSI) and `k4/lb4.md`. Notation as there. Nothing here changes K4.D, K4.T or K4.RF.M's status.

Tools: `k4/lemmam_x.c` (`k4/rulef.c` of #72 verbatim plus a mode `-A43`: the class of every first agent, and for every
bad first agent the roles of the other agents in its run and the candidates a′ of §2), `k4/lemmam_x_run.py` (driver,
one worker, resumable), `k4/lemmam_x_check.py` (second implementation on PR #33's model `k4/c4_verify_H/lb4r.py` with
#72's `k4/rulef_model.py`, without code from `k4/lemmam_x.c`).

**Status.** STATUS_PLACEHOLDER

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

PLACEHOLDER_DATA

## 3. What the run of a bad first agent looks like

**Lemma 1.** Let a be bad and P = P_a^ef. Then
- (a) ω(P) ≥ 1, and r is a terminal with |B_r| ≤ 1;
- (b) some exposed agent is frozen (E ∩ F ≠ ∅); so every bad run has an exposed frozen agent, and the ends of its
  need chains, the "needers at the end of a need chain" of §2, exist;
- (c) some 4-good agent is exposed, or the run is in (G2): LB⁺'s bad case of Theorem A₄ (k* ∈ E ∩ F, k* ≠ r, every
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

## 4. (G2)

PLACEHOLDER_G2

## 5. The exchange: mechanism, Ω and Ψ, and what remains

PLACEHOLDER_EXCHANGE

## 6. Reproduce

PLACEHOLDER_REPRO
