# TARGET₄¹: at most one 4-good agent (proof focus from 2026-11-28)

Workstream `proof/k4-one4`. This synthesizes where TARGET₄ for instances with at most one 4-good agent q stands, and
what is left. Everything cited is on main: `k4/c4.md` (PR #33), `k4/c4one.md` (PR #37), K4.ONE.FRAME (Lean, PR #39).

## The reduction chain (all proved except one link)

TARGET₄¹ ⟸ C₄¹∃ (K4.ONE.FRAME, Lean) ⟸ **Exchange Lemma X** (or its state form X\*) + the theorems of K4.C4.AB / K4.C4.AO
(`k4/c4one.md` §6, Corollary; written, refereed). Lemma X:
- a run of Phase 1 that the theorems do not cover (ω ≥ 1 and none of A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺(o) applies)
- can be changed at one insertion step so that the run is covered or key(τ) = (ω, q frozen, −pos(q)) drops.

**Lemma X is the only open link.** It holds on all data: every insertion sequence of every certified core with one
4-good agent and n ≤ 5 (5.78·10⁹ run–profile pairs at n = 5), also over runs with P-steps in any order. The stronger
X′ holds from index order on all 26,866 n = 6 cores (5.47·10¹⁰ profiles).

## What is proved toward Lemma X (X\* form)

The four moves Ω, Ω_q, Ψ, Ψ_q (`k4/c4one.md` §6) give a key-decreasing move on the share of uncovered runs below:

| runs | n = 3 | n = 4 | n = 5 |
|---|---|---|---|
| LB's P-step key | 90% | 80% | 80% |
| P-steps in any order | 90% | 73% | 62% |

## The residual cases: where a proof of X must add a move

`k4/one4_residual.py` lists the uncovered runs to which none of Ω (any x), Ω_q, Ψ, Ψ_q applies. Log
`results/k4_one4_residual_n3.log`, LB's key, n = 3.
- **218 residual runs at n = 3:** 206 in class G2 (LB⁺'s bad case with r = q exposed after the rotation) and 12 in
  "q frozen, no need chain to r". This matches `k4/c4one.md` (2,134 − 1,916).
- **Smallest residual instance** (class G2): n = 3, m = 5, sets [[0,2,3,4],[1,3,4],[2,3,4]], q = agent 0.
  - Values: q = (good 0: 3, good 2: 6, good 3: 5, good 4: 7); agent 1 = (1: 2, 3: 3, 4: 4); agent 2 = (2: 3, 3: 2, 4: 4).
  - Insertion order (1, 2, 0) gives picks q → 3 (its c), 1 → 4, 2 → 2 (q's top a = 4 and b = 2 are taken), with junk
    {0, 1} and agents 1, 2 frozen (q needs both their picks).
  - This is not a rotation along one need chain: q's two needed goods are held by two different agents, each holding
    its own top or second good.
  - The same sets carry the G2 instance quoted in `k4/c4one.md` §6 that Lemma Ψ handles, with values
    [[2,8,3,4],[2,3,4],[4,2,3]].

## 2. Two new moves: Lemmas Ω⁺ and Ψ⁺ (written proofs, 2026-11-28; not yet refereed)

Both relax one hypothesis of a refereed lemma of `k4/c4one.md` §6, keeping that lemma's run ρ′ (Step 1), and change
only its count. Notation as there: P is the state after a run ρ of Phase 1 (P-steps in any order) and envy-free
upgrades, ω = |J| − S, and "needs" means "ranks above its own pick".

**Compensation condition (C).** Besides a_x, x needs a good g that is the pick Y_h of an agent h with h ∉ U, h ≠ x,
h not on the move's chain, and in P no agent other than x needs g. This needs x to need at least two goods, so x holds
its third good or lower: a 3-good agent holding its c, or q holding c_q or d_q. In the residual runs it is usually q.

**Lemma Ω⁺.** Assume Lemma Ω's hypotheses (H1), (H2), (H2c), (H4) and (H5′). In place of (H3), assume that (H3) holds
or (C) holds for the need chain. Then the conclusion of Lemma Ω holds: some run ρ′ of Phase 1, equal to ρ before β,
followed by envy-free upgrades, reaches P′ with ω(P′) ≤ ω(P) − 1.

*Proof.* Lemma Ω's Step 1 (the run ρ′) and Step 2 (replay ρ's upgrades, then upgrade ℓ with c_ℓ, giving P″) never use
(H3), so they stand. Its count gives |J(P″)| = |J(P)| − 1 without (H3). (H3) was used only to keep x's slot. If (H3)
fails, use (C):
- *x:* in P, x is free with a pick (H2), so it has cap 1. In P″ it holds a_x and may be frozen: it loses at most 1.
- *h:* in P, h is frozen (x needs g = Y_h) and has no slot. In P″, h still holds g: it is off the chain and not
  upgraded, and Step 1 keeps every other agent's pick. Nobody needs g in P″:
  - x holds its top, so it needs nothing;
  - ℓ is upgraded;
  - a middle chain agent x_i needs only goods it ranks above Y_{x_{i−1}}, which by (H2c) are picks of chain agents,
    and h is off the chain;
  - every off-chain agent keeps its pick, so its needs are those of P, which exclude g by (C).

  So h is free with a pick: it gains 1.
- *Everyone else:* NA(P″) ⊆ NA(P) (Lemma Ω, Step 2), and every off-chain agent other than x keeps its base. So none of
  them loses a slot. The chain agents ℓ, x₁, …, x_{s−1} had no slot in P.

So S(P″) ≥ S(P) and ω(P″) ≤ ω(P) − 1. Further envy-free upgrades never raise ω. ∎

**Lemma Ψ⁺.** Assume Lemma Ψ's hypotheses (Ψ1), (Ψ2) and (Ψ5) for x and its fall chain y₀, …, y_k. In place of (Ψ3)
and (Ψ4), assume (C) for the fall chain. Then some run ρ′ of Phase 1, equal to ρ before β, followed by envy-free
upgrades, reaches P′ with ω(P′) ≤ ω(P) − 1. In ρ′, x takes a_x, each y_i takes g_i, and y_k is not upgraded.

*Proof.* Lemma Ψ's Step 1 uses only (Ψ1), (Ψ2) and (Ψ5), so it stands. Replay ρ's upgrades, valid as in Lemma Ψ, and
skip y_k's upgrade. Call the result P″.
- *Junk:* J(P″) = (J(P) ∪ {Y_x}) ∖ {g_k}. If g_k = Y_x this is J(P). Otherwise g_k ∈ J(P) and Y_x ∉ J(P). Either way
  |J(P″)| = |J(P)|.
- *y_k* holds g_k, and nobody needs g_k in P″:
  - g_k is junk in P (I2) or equals Y_x (Ψ1), so off-chain agents, whose needs are unchanged, do not need it;
  - each y_i needs only goods in {Y_{y₀}, …, Y_{y_i}} (Lemma Ψ, Step 2), and g_k is none of them;
  - x needs nothing.

  y_k was frozen in P (Ψ2), so it gains 1.
- *x* had cap 1 in P (Ψ1) and may now be frozen (y₀ needs a_x): it loses at most 1.
- *h* gains 1, by the argument of Lemma Ω⁺: the fall chain's agents need only chain picks, and h is off the chain.
- *Everyone else:* NA(P″) ⊆ NA(P), so no other off-chain agent loses a slot. y₀, …, y_{k−1} were frozen in P.

So S(P″) ≥ S(P) + 1 and ω(P″) ≤ ω(P) − 1. Further envy-free upgrades never raise ω. ∎

**Checked** (`k4/one4_omega_plus.py`; logs `results/k4_one4_omega_plus_n3.log`, `results/k4_one4_omega_plus_n4.log`;
LB's P-step key, every insertion sequence). The check reuses `k4/c4tools/c4omega1.py`'s verification, replacing only
the (H3) test (Ω⁺) and the (Ψ3)/(Ψ4) tests together with the upgrade of y_k (Ψ⁺), by source substitution. For every
residual run where the new hypotheses hold, it rebuilds ρ′, checks that it is a run of Phase 1 with the stated picks,
replays the upgrades, and checks ω′ ≤ ω − 1. There were **0 proof-step failures**.

| n | residual runs (no Ω, Ω_q, Ψ, Ψ_q) | handled by Ω⁺ / Ψ⁺ | uncovered runs with a key-decreasing move: before → after |
|---|---|---|---|
| 3 | 218 | 142 (44 / 98) | 1,916 → 2,058 of 2,134 (89.8% → 96.4%) |
| 4 | 5,843 | 1,640 (384 / 1,256) | 24,058 → 25,698 of 29,901 (80.5% → 85.9%) |

By class at n = 4, Ω⁺/Ψ⁺ handle:
- G2: 862 of 2,657;
- q frozen, (i)/(ii) of B₄ʷ fail: 154 of 892;
- q frozen, no chain to r: 624 of 2,134;
- (Tb): 0 of 160.

Still residual at n = 3: 64 G2 runs and 12 "q frozen, no chain to r" runs. In the latter, q leads its block, so
neither lemma applies with x = q.

## 3. What is left at n = 3 after Ω⁺ and Ψ⁺ (2026-11-28 17:40 UTC)

There are 76 residual runs on 76 distinct profiles (12 + 64). For each, every EFX₀ allocation was enumerated by brute
force (k3algo.raw_efx0). Write q's goods a > b > c > d; q is *flat* if a < c + d.

| class | profiles | q flat | some EFX₀ allocation gives q its top |
|---|---|---|---|
| q frozen, no chain to r | 12 | 12 | 8 (4 have none) |
| G2 | 64 | 16 | 64 |

- **q frozen, q leads its block (12).** q is flat in every one. In 4 of them no EFX₀ allocation lets q keep its top:
  q must take a lower pair. Phase 1 cannot produce that. Whenever q loses a good it gets a P-step at once, and so it
  ends on a or b. And q's pair {c, d} is never envy-free for q (c + d < a + b), so no envy-free upgrade gives it. So the covered runs
  that Lemma X′ finds for them (on the data) must reach that allocation through the rotation theorems: B₄ʷ, with q
  rotated and taking its goods in W as owner, or an owner holding the lower set. A move for this class must likewise
  use q *refusing* its top for {c, d}, the upper-set phenomenon of `k4/vm.md` §5.3 (S1). That is not a run of Phase 1
  alone.
  - Smallest: n = 3, m = 6, sets [[0,2,4,5],[1,3,5],[3,4,5]], vals [[3,5,7,6],[2,3,4],[3,4,2]] (q = agent 0: a = good
    4 (7), b = 5 (6), c = 2 (5), d = 0 (3)), insertion order (0, 2, 1).
  - All 12 EFX₀ allocations give good 4 to agent 2, for example ({0, 2}, {1, 5}, {3, 4}).
- **G2 (64).** These are mostly non-flat q (48 of 64), and some EFX₀ allocation always gives q its top. They need a move
  of another kind than Ω⁺/Ψ⁺: Ω fails on (H2) (no chain from the leader ending at a_q), and Ψ⁺ fails on (C) or (Ψ5).

## 4. Lemma Ψᵘ: the falling chain with an upgraded grabber (written proof, 2026-11-28; not yet refereed)

All 64 G2 runs left at n = 3 have one shape (§3, `k4/one4_psi_u.py`): q holds b_q, and exactly one other agent u ranks
b_q above its Phase 1 pick. That agent is upgraded, and b_q is its top. Lemma Ψ fails there on (Ψ1) alone. In the
smallest case (n = 3, m = 6, sets [[0,2,4],[1,3,5],[2,3,4,5]], vals [[2,3,4],[2,3,4],[2,4,5,8]], order (1, 2, 0)),
inserting q first gives q its top, u its top b_q (u returns its pair), and the holder of a_q a junk good that it upgrades
with. That gives ω 1 → 0.

**Lemma Ψᵘ.** Let P, x ∉ U with Y_x below a_x, and the fall chain y₀ (the holder of a_x), …, y_k be as in Lemma Ψ.
Suppose:
- **(Ψᵘ1)** Exactly one agent u ≠ x ranks Y_x above its Phase 1 pick. Moreover:
  - u ∈ U, with base {Y_u, g_u};
  - Y_x = a_u;
  - no agent other than u ranks Y_u above its Phase 1 pick.
- **(Ψ2)** As in Lemma Ψ (the y_i lie in x's block, are not upgraded, are frozen in P, and are distinct and ≠ x; also
  u is not on the chain). In addition, **g_k is junk in P**, so g_k ≠ Y_x.
- **(Ψ3), (Ψ4)** As in Lemma Ψ.
- **(R)** This order is a run of Phase 1 in the general sense of `k4/c4.md` §1: ρ's prefix before x's block β; x;
  y₀, …, y_k; then every other agent in ρ's order. At each step, if some unprocessed agent has lost a good, the
  processed agent is one of them.

Then some run ρ′ of Phase 1 followed by envy-free upgrades reaches P′ with ω(P′) ≤ ω(P) − 1. In ρ′:
- x takes a_x;
- y_i takes g_i;
- u takes Y_x = a_u;
- every other agent keeps its pick.

*Proof. The picks.* Take ρ′ to be the order of (R).
- x is inserted at β's start. Every good of β's agents is then available (B1), and a_x = Y_{y₀} with y₀ ∈ β, so x
  takes a_x.
- The y_i then take the g_i, as in Lemma Ψ's Step 1.
- For every later agent p, compare the goods taken in ρ′ before p's turn with those taken in ρ before p's turn.
  ρ′ has taken more of the following:
  - chain picks;
  - g_k (junk);
  - a_x (taken by x).

  In ρ, p either found these taken or did not prefer them to Y_p: in ρ every good p ranks above Y_p was gone at p's
  turn. So none of them changes p's choice.
- ρ′ may have taken fewer of the following:
  - Y_x, until u's turn: by (Ψᵘ1) only u ranks it above its pick;
  - Y_u, once u has passed: by (Ψᵘ1) no other agent ranks it above its pick.
- And Y_p itself is not taken before p's turn. x, the y_i and u take a_x, the g_i and Y_x, none of which is Y_p.
- So every p ≠ u takes Y_p, and u, finding its top Y_x available, takes it.

*The state.* Replay ρ's upgrades except u's. Each stays valid: the agent keeps its pick and its needs; its second good
is still junk (it lies in J₀ and is not g_k, since g_k ∈ J(P)); and NA only shrinks. The last point holds because:
- x and u need nothing (they hold their tops);
- each y_i needs only goods in {Y_{y₀}, …, Y_{y_i}}, by the definition of g_i, and these were needed in ρ;
- everyone else keeps its pick.

Then upgrade y_k with {g_k, c} (Ψ3). g_k is needed by nobody, since it is junk in P (I2) and the chain agents need only
chain picks. Call the result P″.

*Counting.*
- **Junk:** J(P″) = (J(P) ∪ {g_u, Y_u}) ∖ {g_k, c}, with g_u, Y_u ∉ J(P) and g_k ≠ c in J(P). So |J(P″)| = |J(P)|.
- **u** had no slot in P (upgraded). In P″ it holds a_u = Y_x, and nobody needs Y_x:
  - x holds a_x;
  - a chain agent y_i ranking Y_x above g_i would have g_i = Y_x by the definition of g_i, contradicting (Ψ2);
  - everyone else ranks Y_x as in P, and by (Ψᵘ1) only u ranked it above its pick.

  So u is free with a pick: **+1**.
- **x** had one slot in P: only u ∈ U ranked Y_x above its pick, so Y_x ∉ NA(P).
  - If k = 0, y₀ is upgraded and needs nothing, and by (Ψ4) nobody else needs a_x. So x keeps its slot.
  - If k ≥ 1, x may lose its slot (y₀ needs a_x). But y_{k−1} gains one: it now holds Y_{y_k}, which y_k (upgraded)
    does not need, which no off-chain agent needs (Ψ4), and which no y_j with j < k − 1 ranks above g_j.
- **y_k** has no slot in P (frozen) or in P″ (upgraded).
- **Everyone else** keeps its base, and NA(P″) ⊆ NA(P) on their picks, so none of them loses a slot.

So S(P″) ≥ S(P) + 1 and ω(P″) ≤ ω(P) − 1. Further envy-free upgrades never raise ω. ∎

(R) is assumed, not derived. Lemmas Ω and Ψ derive their (R) from (H4) and (H5′), and a version of Lemma Ψᵘ with u
handled inside (H4) is the natural next step. On the data (R) always holds where the other hypotheses do.

**Checked** (`k4/one4_psi_u.py`, own realization and count check, c4trace's upgrades). On the 64 G2 runs left at n = 3
after Ω⁺/Ψ⁺ it applies to all 64: (R) holds, the picks are as stated, and ω drops. Log `results/k4_one4_psi_u_n3.log`.
At n = 4 (`results/k4_one4_psi_u_n4.log`), on the 4,203 runs Ω⁺/Ψ⁺ leave, it applies to 448:
- G2: 248 of 1,795;
- q frozen with (i)/(ii) of B₄ʷ failing: 144 of 738;
- q frozen with no chain to r: 56 of 1,510.

In 72 further q-frozen runs the other hypotheses hold but the order of (R) is not a run of Phase 1 (an insertion while
an agent has lost a good). These are outside the lemma's scope, not counterexamples to it. Share at n = 4: 26,146 of
29,901 (87.4%).

**After Ω⁺, Ψ⁺ and Ψᵘ, 12 runs remain at n = 3**, all "q frozen, q leads its block" with flat q (§3). Share of uncovered
n = 3 runs with a key-decreasing move: 2,122 of 2,134 (99.4%).

## 5. Re-rooting: the 12 q-frozen runs at n = 3 are covered by Theorem B₄ʷ (2026-11-28, computational)

In the 12 runs left at n = 3 (q frozen, q leads its block, no need chain to r, q flat), q's need chains end at a terminal
t ≠ r. **The move: insert first, in q's place, the agent z holding b_q** (`k4/one4_reroot.py`).
- q then loses b_q, gets a P-step at once, and takes a_q.
- The agent needing a_q comes last and becomes the new r, so there is a need chain q → … → r.

In all 12 runs, at the new run's state (after envy-free upgrades to a fixpoint), every hypothesis of **Theorem B₄ʷ**
(`k4/c4.md` §4a, refereed) holds:
- q is frozen and exposed;
- there is a need chain to r;
- (i) holds, and (ii) holds in one of its simple forms;
- r has three goods.

So the rotation (q takes O = R_q ∩ W, as owner) gives a valid owner. As an independent check, a brute-force search
finds an EFX₀ completion of the rotated pre-allocation in each case. Log `results/k4_one4_reroot_n3.log`.

This step is *not* yet a lemma. Whether B₄ʷ applies after re-rooting is checked case by case, not proved in general.
In the smallest case (n = 3, m = 6, §3) the B₄ʷ completion is ({0, 2}, {1, 5}, {3, 4}): q takes its lower pair {c, d}
(8 > 7 = a), which is exactly the upper-set allocation that §3 said a Phase 1 run cannot reach without a rotation.

**Status at n = 3 (one 4-good agent, LB's key, every insertion sequence).** Every uncovered run (2,134) now has one of:
- a move proved in writing: Ω, Ω_q, Ψ, Ψ_q (refereed); Ω⁺, Ψ⁺, Ψᵘ (§2, §4, not yet refereed);
- or a re-rooting after which the refereed Theorem B₄ʷ applies, checked per case (12 runs).

Turning the re-rooting into a lemma, with its B₄ʷ hypotheses derived, would make Lemma X\* at n = 3 a written
argument case by case.

## Next steps (proof, kill rule 3 bursts per sub-idea)

1. ~~Hand-analyze the smallest residual G2 run~~ done: it gave Lemmas Ω⁺ and Ψ⁺ (§2). Next, the smallest run still
   residual after them (64 G2 and 12 q-frozen runs at n = 3). Original step: Find the insertion change that covers it (X′ says one exists) and
   state the move as a lemma in the style of Ω/Ψ: hypotheses, the new run ρ′, the key drop. Check it with a script on
   all 206 n = 3 G2 residuals, then on n = 4.
2. The same for the 12 "q frozen, no chain to r" residuals.
3. Each proved move goes into this file with its coverage numbers. The target is a set of moves covering every
   residual class, followed by a proof that the classes are exhaustive.
