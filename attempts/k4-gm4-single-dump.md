# GM₄ˢ: at a maximum of the level sum, one dump suffices

Workstream `proof/k4-gm4` (`k4/gm4.md`).

**Approach.** In the runs of #29, every Σℓ-maximum with a nonempty pool was completed by the empty-bundle dump or by a single dump at one source. The sharper conjecture GM₄ˢ says this always holds. It would reduce GM₄ to choosing the right source, for example by one of the rules of `k4/gm4.md` §5.

**Where it breaks (n = 4, m = 6, one 4-good agent).** Agents and values:
- agent 0: goods 0:1, 2:6, 3:4, 4:8;
- agent 1: goods 1:2, 2:3, 5:4;
- agent 2: goods 1:3, 4:4, 5:2;
- agent 3: goods 3:3, 4:2, 5:4.

The maximum Y = {4} | {5} | {1} | {3}, with pool {0, 2} and Σℓ = 13, has no empty bundle, and no agent can take the whole pool with an EFX₀ result. The only placements split the pool: 0 → agent 2 and 2 → agent 3, or 0 → agent 3 and 2 → agent 2.

**Consequence.** Even at a maximum, Phase 2 must be able to split the pool, as it must at LS4-stable states (`attempts/k4-ls-single-dump.md`). No rule that picks a single dump source can prove GM₄. GM₄ itself fails too (`attempts/k4-gm4-level-sum.md`).

Counts (one implementation, `k4/gm4_fast.c`):
- n ≤ 3: never (exhaustive, 9,227,950 maxima with a pool);
- n = 4 with one 4-good agent: 2 of 1,131,363 maxima with a pool (exhaustive; both in this core);
- 10 of 4,385,569 in random n = 4 profiles with one to three 4-good agents;
- 5 of 2,583,713 in random pure n = 4 profiles.

Smallest configuration found: n = 4, m = 6, one 4-good agent. It is the smallest possible n, and the fewest 4-good agents, since n ≤ 3 is exhausted. Among cores with one 4-good agent at n = 4, both failures have m = 6.

Reproduce: `python3 k4/gm4_counterexample.py` (instance S).
