# Local search with elementary moves and single-agent rebundles, without champion moves

Workstream `proof/local-search` (`proofs/local_search.md` §2, §6.1).

**Approach.** Moves E, S, R, A, plus U: one agent takes a new bundle made of its own bundle, pool goods and goods that other agents hold without valuing them (junk). The potential is (sum of levels, number of allocated goods). U repairs the n = 2 failure of `local-search-elementary-moves.md`.

**Where it breaks (smallest configuration: n = 3, m = 5).** Core {0, 2, 3}, {1, 2, 4}, {0, 1, 2} (goods 3, 4 private). Rankings (a, b, c): agent 0 (2, 0, 3), agent 1 (2, 1, 4), agent 2 (0, 1, 2). State: {0} {2} {1, 3}, pool {4}.
- Agent 0 holds its b (0), and its top 2 is alone. Agent 1 holds its top 2. Agent 2 holds its b (1) plus junk 3, and its top 0 is alone.
- Good 4 is agent 1's c.
- Adding it to agent 0 makes 0 non-alone, and agent 2 needs 0 free.
- Adding it to agent 1 makes 2 non-alone, and agent 0 needs 2 free.
- Adding it to agent 2 gives {1, 3, 4}, which contains agent 1's b and c.
- No single agent can rebundle profitably.

What works is a champion move along the envy path 2 → 0 → 1. Agent 2 takes {0}, agent 0 takes {2}, and agent 1 takes {1, 4} out of agent 2's old bundle and the pool; good 3 returns to the pool.

28 stuck states at n = 3, m = 5 (28 profiles, core above); none at m = 3, 4, 6.

Adding the champion move C removes every stuck state for n ≤ 5 (Result 6.1). The next failure is at n = 6: `local-search-one-phase-n6.md`.

Reproduce: `python src/local_search.py allstates 3 --flags="-m ESRAU -l 2" --jobs=1`
