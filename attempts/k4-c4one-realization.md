# Inserting q first in its block as a rotation, in case (Tc)

**Claim tried** (`k4/c4one.md` §6, part (a) of the proof route for Lemma X′ with q free). Take a run of Phase 1 in
case (Tc), with q the unique 4-good agent. Insert q at the insertion step that started its block, and use index
order afterwards. Then the new picks would be those of the old run rotated along a need chain ℓ_q = x₀ → … → x_s = q:
- each x_i (i ≥ 1) takes Y_{x_{i−1}};
- the old leader ℓ_q ends on a good it ranks lower;
- every other agent keeps its pick.

If so, part (b) would be a statement about one explicit rotated state.

**Where it holds** (`k4/c4tools/c4realize.py`, `results/k4_c4one_realize.log`; distinct cases as `k4/c4check.c -Z3 -K4`
prints them):
- every (Tc) case at n ≤ 4 (7,364 cases);
- 195,296 of the 203,592 (Tc) cases at n = 5 (96%).

Inserting q covers every one of these runs, including those where the rotation is not reproduced.

**Why it fails: obstacle (D1).** When ℓ_q, having lost its top to q, takes its b, any agent of a later block that
also has that good loses it. That agent is pulled into the new block and takes its best remaining good. This is its
top, which need not be its old pick. From there the later picks change.

**Smallest configuration.** n = 5 (none at n ≤ 4), m = 8, one 4-good agent q = 0:
- sets [[0,1,3,4],[2,3,6],[2,6,7],[4,5,7],[5,6,7]];
- values [[2,4,3,8],[3,2,4],[4,2,3],[4,2,3],[2,4,3]] (in the order of each agent's goods).

*The old run* (leaders 3, then 4):
- Agent 3 takes 4, q's top. q takes 1, its b.
- Agent 4 takes 6. Agent 2 takes 2. Agent 1 takes 3.
- J = {0, 5, 7} and ω = 1.
- q is free and exposed, and the run is in case (Tc).

*Insert q first.*
- q takes 4. ℓ_q = 3 takes 7, its b.
- Agents 2 and 4 of the old later block have lost 7 and are pulled into the first block.
- Agent 1 now gets its top 6, and agent 4 gets 5.
- ℓ_q cannot upgrade, since its c = 5 is taken, and ω stays 1.

The only need chain from ℓ_q to q is 3 → 0. The new picks differ from that rotation at agents 1 and 4.

**Consequence.** Part (a) needs an extra hypothesis (no agent of a later block holds the good that ℓ_q falls back to,
or that agent's old pick was its top), or a proof of part (b) that does not go through the realization. In this
example ω does not drop, so the move is not a step down in key(τ), which is Lemma X's potential. Lemma X′ still
holds here, since the new run is covered.

Reproduce: `python3 attempts/k4_c4one_attempts.py realization` (under 1 s).
