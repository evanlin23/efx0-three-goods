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

## Next steps (proof, kill rule 3 bursts per sub-idea)

1. ~~Hand-analyze the smallest residual G2 run~~ done: it gave Lemmas Ω⁺ and Ψ⁺ (§2). Next, the smallest run still
   residual after them (64 G2 and 12 q-frozen runs at n = 3). Original step: Find the insertion change that covers it (X′ says one exists) and
   state the move as a lemma in the style of Ω/Ψ: hypotheses, the new run ρ′, the key drop. Check it with a script on
   all 206 n = 3 G2 residuals, then on n = 4.
2. The same for the 12 "q frozen, no chain to r" residuals.
3. Each proved move goes into this file with its coverage numbers. The target is a set of moves covering every
   residual class, followed by a proof that the classes are exhaustive.
