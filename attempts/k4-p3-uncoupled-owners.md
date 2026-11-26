# Two uncoupled free agents as owners, no rotation (Claim X)

**Idea** (`k4/p3.md` §5, workstream proof/k4-p3). In the two-owner framework, the failures of "two owners, no rotation"
on the suite come from the owners' picks (a junk good threatening together with both owners' picks). Claim X: in the
Phase 1 state (index insertion, no upgrade) of a (4, 3) core, any two free agents whose picks no frozen agent values
are a valid pair of owners, i.e. the bases extend to an EFX₀ allocation in which every other agent holds at most two
goods. It held on 1,500 states with such a pair (suite, screen, certified cores, random cores; `k4/p3/claim_x.py`).

**Where it breaks.** The owners' views of each other's bundles. Smallest failure found: a certified (4, 3) core with
n = 4, m = 8 (`k4_certs_4_n4_3_p3.json.gz`), strict balanced types, every good with at most two valuers:

| agent | goods (values) | ranking |
|---|---|---|
| 0 | 0 (3), 1 (10), 2 (6), 6 (8) | 1 > 6 > 2 > 0 |
| 1 | 1 (8), 2 (4), 5 (6), 7 (3) | 1 > 5 > 2 > 7 |
| 2 | 3 (7), 4 (6), 5 (10), 6 (2) | 5 > 3 > 4 > 6 |
| 3 | 3 (2), 4 (4), 7 (3) | 4 > 7 > 3 |

Phase 1: agent 0 takes 1; agent 1 (lost 1) takes 5; agent 2 (lost 5) takes 3; agent 3 (lost 3) takes 4. Junk 0, 2, 6, 7.
Agents 0 and 1 are frozen (agent 1 needs 1, agent 2 needs 5); agents 2 and 3 are free and their picks 3, 4 are valued by
no frozen agent. Agent 0 (holding 10) is threatened by {6, 2} and {6, 0}, agent 1 (holding 6) by {2, 7}, so with owners
2 and 3 the colouring is forced up to swapping: 6, 7 to one owner, 0, 2 to the other. Owner 3 with {4, 0, 2} sees
{3, 7} in X_2 = {3, 6, 7} (5 > 4); owner 2 with {3, 0, 2} sees {4, 6} in X_3 = {4, 6, 7} (8 > 7). The two owners value
each other's picks, and the frozen agents' threats push each owner's own junk into the other's bundle. In fact no EFX₀
allocation keeps these four bases at all (brute force over the 4⁴ placements of the junk), so a rotation is required.

Since every good has at most two valuers, the failure is not specific to p = 3.

**Refinement tested next:** Claim X′, the same with the owners' picks also not valued by the other owner
(`k4/p3/claim_x.py --mutual`).

Reproduce: `python3 k4/p3/claim_x_cex.py` (brute force, under a second; `results/k4_p3x/claim_x_cex.log`);
`python3 k4/p3/claim_x.py cores --count=400 --seed=7` finds it (fixed sampler; `results/k4_p3x/claim_x.log`).
