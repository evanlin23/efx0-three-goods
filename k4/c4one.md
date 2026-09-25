# Conjecture C₄¹: at most one 4-good agent

Workstream `proof/k4-c4one` (ledger row K4.C4.1, open item 18). Builds on `k4/c4.md` (PR #33, under review): notation,
Lemma E, Theorems A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ and the conventions of its §1.1.

## Statement

**C₄¹ (existence form).** For every strict profile of every k = 4 core in which at most one agent has four relevant
goods, there is a valid pre-allocation with a completion satisfying (OC₄) in which frozen agents hold exactly their
bases and only the owner's bundle has more than two goods. This is PR #35's `EFX.LB4R.TheoremC4exists` restricted to
such cores. With Theorem 1′₄ (K4.LB4.S), K4.CORE (whose peeling never adds a 4-good agent) and K4.TIE it gives
**TARGET₄ for every instance in which at most one agent values four goods**.

**C₄¹ (LB₄ʳ form, `k4/c4.md` §6.2).** For every run of Phase 1 on such a core: after envy-free upgrades, some free
agent is a valid owner with its needs from its base, or one rotation (any frozen k, any need chain, any
O ⊆ R_k ∩ (J ∪ B_{x_t})) gives a valid pre-allocation that needs no owner or has a valid owner. Evidence: every strict
profile and every insertion sequence of every such core with n ≤ 4 (`results/k4_c4_variants.log`).

## Status

Work in progress. Known from `k4/c4.md`: with no 4-good agent, Corollary C₄⁰ (LB⁺'s Theorem C) proves it; with one
4-good agent q, Theorems A₄, B₄, B₄ʷ, A₄ᵀ and A₄⁺ prove it on 94.5% of the n = 4 runs that need an owner. What is left:
q exposed and frozen with no need chain to r or with (i)/(ii) of B₄ʷ failing; q exposed and free with (Tc) or (Tb) of
A₄ᵀ; and LB⁺'s bad case with r = q exposed after the rotation.
