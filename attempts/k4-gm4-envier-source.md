# H1: at a maximum, a source that envies someone admits the single dump

Workstream `proof/k4-gm4` (`k4/gm4.md` §5).

**Approach.** On the n = 3 maxima every source that envies some agent admitted the single dump: 67,045 of 67,045 in 1,020,000 random profiles. The sources that failed were always envy-isolated. At a maximum with a nonempty pool the envy graph always had an edge (H0; no exception found). A backward envy walk then ends at a source that envies someone. So H0 and H1 would give GM₄ˢ, and a proof of H1 would have used the envied agent to build a level-sum-raising re-division.

**Where it breaks (n = 4, m = 6, one 4-good agent).** Agents and values:
- agent 0: goods 0:4, 1:2, 4:8, 5:7 (goods 0 and 1 private, 4 + 2 < 8 + 7);
- agent 1: goods 2:4, 3:2, 5:3;
- agent 2: goods 2:4, 4:2, 5:3;
- agent 3: goods 3:3, 4:4, 5:2.

The maximum Y = {4} | {5} | {2} | {3}, with pool {0, 1} and Σℓ = 12, has sources 1 and 3, and both envy someone. The single dump works at 3 but not at 1.

**Consequence.** Which source can take the pool is not decided by envy alone. GM₄ˢ is false anyway (`attempts/k4-gm4-single-dump.md`).

Counts (one implementation, `k4/gm4_explore.c`):
- n = 3: 0 of 67,045 envier sources fail (sample);
- pure n = 4: 100 of 27,914 (438,000 random profiles);
- n = 4 with one to three 4-good agents: 947 of 194,709 (1,566,000 random profiles).

Smallest configuration found: n = 4, m = 6, one 4-good agent. n = 3 was only sampled.

Reproduce: `python3 k4/gm4_counterexample.py` (instance H).
