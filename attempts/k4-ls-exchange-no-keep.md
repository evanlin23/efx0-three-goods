# k = 4 two-phase local search with exchange cycles that do not keep own goods (champion cycles included)

Workstream `proof/k4-localsearch` (`k4/local_search4.md`).

**Approach.** Phase 1 as in `attempts/k4-ls-no-exchange.md` (moves M1 and R), plus the k = 3 augmented envy cycle carried over literally. On distinct agents i_0, …, i_{L−1}, each i_t takes a set Z_t of its own goods drawn from the next agent's bundle Y_{i_{t+1}} and the pool, meeting Y_{i_{t+1}}. The Z_t are disjoint, every agent strictly improves, and the result is EFX₀.
- Special case: the champion cycles. For a source s whose bundle cannot take the whole pool, the agent h that envies a smallest subset Z ⊆ Y_s ∪ U takes Z, and envy paths compensate s.
- Phase 2 places the pool as junk.

**Where it breaks (n = 3, m = 6).** Agents and values:
- agent 0: goods 0:6, 1:4, 2:8, 5:5;
- agent 1: goods 1:4, 3:8, 4:2, 5:5;
- agent 2: goods 2:6, 3:10, 4:3, 5:2.

Phase 1 reaches Y = {0, 5} | {3} | {2, 4} with U = {1}. The values are 11, 8, 9.
- No M1, R or keep-free exchange cycle improves Y (brute force over all cycles and all sets).
- No complete EFX₀ allocation extends Y, even if good 1 may go to an agent that values it:
  - at agent 2, agent 0 values {1, 2, 4} minus good 4 at 12 > 11;
  - at agent 0, agent 1 values {0, 1, 5} minus good 0 at 9 > 8;
  - at agent 1, agent 2 values {1, 3} minus good 1 at 10 > 9.
- The repair keeps an own good. In the cycle 0 → 2 → 1 → 0, agent 0 keeps good 0 and takes good 2 (14). Agent 2 takes good 3 (10). Agent 1 takes good 5 from agent 0's bundle and the pool good 1 (9). The result {0, 2} | {1, 5} | {3} is Pareto-better, with goods 4 in the pool. It is completed by giving 4 to agent 2 (valued) or placing it as junk.

**Champion cycles.** A champion cycle takes, for each source s, the agent envying a smallest subset of Y_s ∪ U; that agent takes the subset, and envy paths compensate s. It is an exchange cycle without keep, so the failing state above (no move, no completion) is also one for champion cycles, and `k4/ls4.c -c` reaches it.

An *illustration* (not a failure) of how champion cycles get blocked. In the n = 3 profile agent 0 (0:6, 2:8, 4:4, 5:5), agent 1 (1:2, 3:10, 4:6, 5:7), agent 2 (2:3, 3:4, 5:2), take the state Y = {0, 5} | {3} | {2}, U = {1, 4}.
- The two sources' champions both need the pool good 4: agent 1 wants {4, 5} ⊆ Y_0 ∪ U, and agent 0 wants {2, 4} ⊆ Y_2 ∪ U. So the champion cycle 1 → 0 → 2 → 1 is not disjoint. At k = 3 this cannot happen, because a dirty good is a single good per source and a system of distinct representatives separates them.
- An exchange cycle with keep still improves this state: agent 0 takes {0, 2}, agent 1 takes {4, 5}, agent 2 takes {3}.
- LS4's Phase 2 completes the state as it is: good 1 as junk at agent 0 and good 4 as junk at agent 2 give the EFX₀ allocation {0, 1, 5} | {3} | {2, 4}. This is a dump plus a solo good, and it is the only completion (brute force).

Counts (single implementation, `k4/ls4.c -x` without `-k`): 40 of 5,100,000 random strict n = 3 profiles end in such a dead end. There are 0 at n = 2 (exhaustive). The smallest n is 3; whether m = 6 is the smallest m at n = 3 was not searched.

Reproduce: `python3 k4/ls4_attempts.py` (independent brute force from the raw definition).
