# Adaptive insertion by least ω (k4/adaptive.md §5)

**Idea.** ω = |NA| − σ counts the goods an owner must take beyond two; the fewer frozen agents, the fewer goods to keep
out of the owner's bundle. So at each insertion step, insert the agent whose choice gives the least ω after the rest
of Phase 1 in index order and the upgrades (a rollout; `k4/adaptive.c -A2` with envy-free upgrades, `-A4` need-shrinking,
`-A5` none); variants break ties by the number of frozen 4-good agents (`-A10`), use #37's key generalized to several
4-good agents, (ω, frozen 4-good agents, −position of the last 4-good agent) (`-A11`), or apply the rule at the first
step only (`-A13`). These rules are polynomial (a few runs of Phase 1 per step).

**Where it breaks.** With at most one rotation each fails at n = 3 (with two, LB₄ʳ succeeds): `-A2`, `-A4`, `-A10`,
`-A11`, `-A13` on 11,520 profiles, `-A5` on 12,040 (`results/k4_adaptive_rules_n23.log`). On H_1–H_8 they need no
rotation (`results/k4_adaptive_cheap_H.log`: `-A1` and `-A2` on H_1–H_8 and five relabelings each), so the
failure is not the cascade of Proposition H but a tie that ω cannot break.

**Smallest failing configuration** (n = 3, m = 6; `results/k4_adaptive_smallest.log`). Agents 0 = {0, 1, 4, 5},
1 = {2, 3, 4, 5}, 2 = {2, 3, 4, 5} with values (1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4). With envy-free upgrades
(`-A2`) or none (`-A5`) every first agent gives ω = 2, so the rules insert agent 0 first (index order on the tie); with
need-shrinking upgrades (`-A4`) the first agents 0, 1, 2 give ω = 1, 2, 1, so the least ω picks agent 0 outright. The
run with agent 0 first (and with agent 2 first) needs two nested rotations under every policy, while inserting agent 1
first needs one (rule F). Brute force: 5 EFX₀ allocations, all
with at most one bundle of more than two goods, so K4.D holds there.

Reproduce: `python3 attempts/k4_adaptive_attempts.py` (checks each rule's failure with `k4/adaptive.c` and in PR #33's
independent model `k4/c4_verify_H/lb4r.py`, and the brute force; `results/k4_adaptive_attempts.log`).
