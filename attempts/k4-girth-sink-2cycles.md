# The LSS architecture with 2-cycles: orientation, then a sink

Workstream `proof/k4-girth` (`k4/girth.md` §5). **Approach:** keep LSS's Algorithm 2 (any vertex 0 and labeling), and
repair its completion for 2-cycles: choose the sink after Algorithm 2 among all non-envied agents (Lemma SINK), and
orient a leftover good to a non-envied valuer only if nobody then envies it (G5 repair, `complete_safe_sink`).

**Result: fails at n = 2.** On the k = 4 core with two agents valuing the same four goods equally, (8, 5, 4, 2), the only
EFX₀ allocations are {a, d} | {b, c} (either way round). The holder of {a, d} (worth 10) is envied by the holder of
{b, c} (worth 9), which EFX₀ allows only because the envier values both goods. The architecture never gives an envied
agent a second good: Algorithm 2 serves only envied agents (one of them takes U_i, which here is worse than its top),
and the completion only adds goods to non-envied bundles. No labeling and no sink choice works (all are checked).

This is the k = 4 face of the repository's P1 refutation (`k4/sdc.md` §1): the brute force of `k4/girth/brute.py`
confirms that on GM4-E, which has 2-cycles, some Pareto-maximal partial EFX₀ orientation has no EFX₀ completion. On
linear instances no such state has been found (`k4/girth.md` §4). So the girth-≥ 3 part of the LSS argument is not a
technicality: with 2-cycles, envied agents must be allowed bundles of two goods, both valued by their enviers.

**Reproduce:** `python3 attempts/k4_girth_attempts.py` (part 3).
