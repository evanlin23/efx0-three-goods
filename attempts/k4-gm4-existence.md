# GM₄∃: some maximum of the level sum admits a placement (an existence proof of TARGET₄)

Workstream `proof/k4-gm4` (`k4/gm4.md` §2.4).

**Approach.** GM₄ fails: some maxima of the level sum Σℓ are dead ends (`attempts/k4-gm4-level-sum.md`). But in every counterexample to GM₄, *another* maximum admitted a placement. The weaker statement GM₄∃ says every strict profile has a Σℓ-maximum that admits a placement. Equivalently, the largest Σℓ over junk-free EFX₀ partial allocations is attained by the valued part of a complete EFX₀ allocation. With K4.TIE and K4.CORE it would still give TARGET₄, as an existence argument: take a good maximum and place its pool. A tie-break among the maxima (Σℓ², leximax) could have made it constructive.

**Where it breaks (pure n = 4, m = 7).** Agents and values:
- agent 0: goods 0:3, 2:6, 5:2, 6:10;
- agent 1: goods 1:1, 4:6, 5:8, 6:4;
- agent 2: goods 2:3, 3:6, 5:8, 6:4;
- agent 3: goods 3:6, 4:3, 5:4, 6:8.

The only Σℓ-maximum is {0, 2} | {1, 4} | {5} | {6}, with pool {3} and Σℓ = 21. Good 3 fits nowhere (`k4/gm4.md` §2.4 checks each agent by hand). The profile has 16 complete EFX₀ allocations, and the largest level sum of their valued parts is 20. The maximum is also reached by 4 single-agent rebundles.

**Consequence.** No argument that takes a Σℓ-maximum, with any tie-break, proves TARGET₄. Every run of LS4⁺_n that reaches a maximum of this profile fails. LS4⁺'s default rule still completes it, by stopping at a placeable state with Σℓ = 17.

Found by searching around the GM₄ counterexamples: the profiles that change one agent's type (`results/k4_gm4_around1_4.log`) or two agents' types (`results/k4_gm4_around2_4.log`: 148 distinct such profiles in 2,260,332). None appeared in the random runs of `k4/gm4.md` §4.

Smallest configuration found: pure n = 4, m = 7. It has the same core as instance A, and only agent 2's type differs. Smaller classes: GM₄ itself holds for n ≤ 3 and for n = 4 with one 4-good agent (exhaustive), so GM₄∃ does too. With two 4-good agents at n = 4, GM₄∃ holds for all 724,847,616 profiles (exhaustive, `results/k4_gm4_4_n4_2.log`). So a counterexample needs n ≥ 4 and at least three 4-good agents; the one found is pure.

Reproduce: `python3 k4/gm4_counterexample.py` (instance G).
