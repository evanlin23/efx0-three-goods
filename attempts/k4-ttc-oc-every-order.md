# Counterexample: OC and OC₁ "for every order" fail on a strict connected k = 4 core in the K4.MC2 class (n = 5, m = 9)

Workstream `proof/k4-ttc` (`k4/ttc.md` §13). **Status:**
- *Refuted*, on a strict connected k = 4 core with no agent holding two private goods (the class of K4.MC2):
  - Conjecture OC (K4.SDC.OC, `k4/sdc.md` §29: from every order, the picks extend, or after one improving move they
    extend, with a *free* completion);
  - Conjecture OC₁ (one absorber);
  - the variants OC₁ᵖ, OC₁-ED and OC₁-ED\*.
- *Not refuted:* MD, SD-C, TARGET₄, and every R1-priority form (OC₁ and OC for R1-priority orders, SD-C-R1). The
  coordinator's OC₁^max (orders whose picks form a maximum matching) is not refuted either: the failing picks match
  only 3 of the ν = 5 agents.

The core is in K4.MC0's class as well: n = 5 with three 4-good agents.

**Verified three times, independently:**
- here: SAT, and the brute-force replay `k4/ttc/refute_oc1.py`, which uses no SAT and no shared code and puts no cap on
  set or base sizes;
- by the Hall session (`claude/k4-oc1-hall`, `k4/oc1_hall.md` §18, `results/k4_oc1_hall/verify_ttc_mc2_cex.log`), with
  its own raw brute force and a written count.

## The core (`results/k4_ttc/oc1_mc2_counterexample.json`)

Goods: yᵢ = i, aᵢ = 3 + i, bᵢ = 6 + i (i = 0, 1, 2), with indices of b taken mod 3.

| agent | goods (value) |
|---|---|
| i = 0, 1, 2 | yᵢ (10), aᵢ (6), bᵢ (5), bᵢ₋₁ (7) |
| 3 | y₀ (4), y₁ (3), y₂ (2) |
| 4 | y₀ (2), y₁ (4), y₂ (3) |

**Core conditions** (K4.CORE):
- `is_core4` returns [].
- *Degrees:* 4, 4, 4, 3, 3.
- *Strictly balanced:* 10 < 6 + 5 + 7 = 18 for the 4-good agents, and 4 < 5 for the 3-good ones.
- *Private goods:* only aᵢ is private to agent i, since bᵢ is shared by agents i and i + 1. So no agent has two
  private goods (the K4.MC2 class).
- *Strict:* for (10, 6, 5, 7), no two disjoint subsets have equal value. Singles 10, 6, 5, 7; 10 vs the pairs 11, 13,
  12; 6 vs 12, 5 vs 13, 7 vs 11; the pairs 15 vs 13, 16 vs 12, 17 vs 11; the triple 18 vs 10. For (4, 3, 2), 4 vs 5.
- *Connected:* yes.

## The failing order

Order (0, 1, 2, 3, 4). Picks (y₀, y₁, y₂, none, none), junk {a₀, a₁, a₂, b₀, b₁, b₂}.
- **Frozen agents.** Agents 3 and 4 hold nothing and want every yᵢ, so agents 0, 1, 2 are frozen. By Lemma 2(a) of
  `k4/sdc.md` §2, a frozen agent keeps its pick alone. The pickless agents value no junk, so they cannot compensate a
  frozen agent either.
- **Danger triangles.** Agent i's junk goods {aᵢ, bᵢ, bᵢ₋₁} pairwise beat its pick: 6 + 5 = 11, 6 + 7 = 13,
  5 + 7 = 12, all > 10. So a bundle of three or more goods may contain at most one good of each triangle (Lemma 2(b)).
- **The count** (the Hall session's written argument, which I agree with). The six junk goods go to the two pickless
  agents.
  - A bin of exactly two goods is harmless.
  - But then the other bin has at least four goods, and holds two goods of some triangle.
  - With a split of 3 + 3, every triangle splits 2–1, so a bin again holds two goods of a triangle.
  - So the picks have **no completion at all**: neither a free one nor a one-absorber one.
- **No move helps.** `python3 k4/ttc/refute_oc1.py results/k4_ttc/oc1_mc2_counterexample.json 0` (log
  `results/k4_ttc/refute_oc1_mc2.log`) enumerates 232 improving moves: 21 additions, 186 chains, 25 rings.
  - After none of them do the bases have a free completion or a one-absorber completion.
  - OC₁ᵖ fails too, by SAT.
  - In words: a move hands a pick to a pickless agent, which then becomes frozen, because the other pickless agent
    wants that pick. It removes at most one triangle, and the other two still collide in the remaining bins.

## What still holds there (`results/k4_ttc/mc2_cex_context.log`, SAT)

- *MD:* a complete EFX₀ allocation value-dominates the failing picks.
- *Two moves* (`de_free.search`, chains and rings, free completion) reach a completion.
- *Other orders:* of the 11 plain serial-dictatorship outcomes, only this one fails. The Hall session finds 12 of the
  120 plain orders failing, all with these picks.
- *R1-priority orders:* every one gives a start that satisfies OC₁ (6 distinct outcomes here; all 120 orders in the
  Hall session's check). After agent 0 takes y₀, R1 priority makes the agents 3 and 4, which have lost a good, pick
  before agent 1. So the starving pick vector never arises.
- *SD-C* holds.

## How it was found

`k4/ttc/mc2_hand.py` (log `results/k4_ttc/mc2_hand.log`) tries hand-made variants of the earlier counterexamples.
- *Setup:* three frozen agents with one private good each, the second danger good shared with the next frozen agent,
  and two pickless agents.
- *Result:* 24 of the 75 variants that are MC2-class cores fail OC₁. This is one of them, with the shared good
  bᵢ₋₁ valued at 7.
- *Why it fails:* when the shared good is valued low (2), a chain lets agent i take {aᵢ, bᵢ, bᵢ₋₁} and break two
  pairs at once, and OC₁ holds (`oc1_mc2_candidate.json`). Valued at 7, the junk becomes a triangle, and no single
  absorption breaks enough.

The MC2-class climb `core_climb.py 6 400 30 91 5 5 seeded seed=oc1_mc2_candidate.json mc2`
(`core_climb_mc2_seeded.log`) found 63 OC₁ failures in 9 distinct MC2-class instances. Each fails OC and OC₁ for some
plain order, and none fails for any R1-priority order (`results/k4_ttc/mc2_climb_failures_r1.log`).

## What this says

- **"From every order" is too strong at k = 4.** The order (0, 1, 2, 3, 4) starves two agents (picks match only 3 of
  ν = 5 agents). Their wants freeze everyone else, and the junk then has only two bins. This is not about the shape of
  the completion: it fails with a free completion too.
- **The orders that matter.** LB's Phase 1 (R1 priority) and maximum-matching orders, the coordinator's OC₁^max, both
  avoid starving agents here. In housing-market terms the failing picks form a Pareto-optimal matching that is not
  maximum. Abraham et al. (ISAAC 2004, Thm 1) compute a *maximum* Pareto-optimal matching in O(√n·m), and by their
  §6 Lemma 1 it is a serial-dictatorship outcome. Thm 3 gives Pareto-optimal matchings of every size in between.
- **Climbs against the surviving forms** (`k4/ttc.md` §13): R1-priority orders in the MC2 class, seeded from this core
  (6 runs × 400 steps, 40 orders each, `core_climb_mc2_r1_seeded.log`), found nothing. Random n = 6–7 and the OC₁^max
  climbs are running.
