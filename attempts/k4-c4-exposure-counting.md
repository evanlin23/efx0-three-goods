# LB⁺'s Theorem A counting at k = 4 (exposed agents, one per block)

**Idea.** In `proofs/lb_last_step.md` Theorem A, every agent threatened by the owner r's largest bundle W = J ∪ {Y_r}
(an *exposed* agent) is a block leader holding its top, needs one good kept out of X_r, and each earlier block has its
own terminal for it; so r fails only in the "bad case" of the last block, with a deficit of one slot. Carry this to
k = 4 cores (`k4/c4.md` §2–§3; state after Phase 1 and envy-free upgrades).

**What survives.** For 3-good agents all of it: Lemma E(i) and Theorem A₄ of `k4/c4.md` (r fails only in LB⁺'s bad
case or when some 4-good agent is exposed; checked on every run for n ≤ 3 and n = 4 with at most two 4-good agents).

**Where it breaks: exposed 4-good agents.** Each of the three steps of the counting fails, already at n ≤ 3:
1. *An exposed agent need not lead its block* (n = 3, m = 5). Agents 0 = {0, 1, 3, 4} with values (3, 6, 8, 4),
   1 = {2, 3, 4} and 2 = {2, 3, 4} with (2, 3, 4); insertion choices (7, 4, 6) (agent 2 first). Agent 2 takes 4 (agent
   0's c); agent 0 (lost 4) takes its top 3; agent 1 (lost 3, 4) takes 2. Agent 0 is frozen (agent 1 needs 3) and
   exposed by {1, 0} = {b, d} (c + d < a < b + d: 6 + 3 > 8), although it is not a leader. r = agent 1 has no spare
   slot and fails.
2. *One exposed agent can need two goods kept out* (n = 2, m = 5). Agents 0 = {0, 2, 3, 4} with (2, 7, 10, 4) and
   1 = {1, 2, 3, 4} with (6, 3, 7, 5), agent 1 inserted first. Agent 1 ranks 3 > 1 > 4 > 2 with values
   7, 6, 5, 3 and is flat (7 < 5 + 3: every pair of its other goods beats its top); it takes 3 and is frozen; agent 0 takes 2 and is r. W = {2, 0, 1, 4} holds agent 1's goods 1, 4 and 2 = Y_r, so both 1
   and 4 must stay out of X_r: **owner r's deficit is 2** (the least number of extra slots that would make r valid),
   while at k = 3 it is at most 1.
3. *A free exposed 4-good agent uses up the terminal of its block, and the deficit sits in an earlier block*
   (n = 3, m = 6). Agents 0 = {0, 1, 2, 3} with (3, 4, 2, 8), 1 = {2, 4, 5} with (2, 4, 3), 2 = {3, 4, 5} with
   (4, 2, 3); insertion choices (6, 3, 1). Block 0: agent 2 takes 3, agent 0 (lost its top 3) takes 1. Block 1: agent 1
   takes 4 and is r. Agent 2 (3-good leader, frozen) needs 5 kept out; agent 0 (free, holding its b with
   c + d = 5 > 4 = b) is exposed by {0, 2} and must use its one slot for itself (`k4/lb4.md` Lemma 2₄). One slot, two
   demands, both in block 0, r alone in block 1: r fails with deficit 1. At k = 3 an earlier block never has a deficit.

In all three the failing run is repaired by LB₄ʳ (another owner or a rotation of the 4-good agent; `k4/c4.md` §6.2).
What this shows: a Theorem A₄ for all runs must count 4-good exposed agents against the terminals *across* blocks, and
allow deficits of 2 per agent; no such count is known (`k4/c4.md` §6).

**Smallest failing configurations**: the three above (n = 3, m = 5; n = 2, m = 5; n = 3, m = 6).
Reproduce: `python3 attempts/k4_c4_attempts.py exposure-counting`.
