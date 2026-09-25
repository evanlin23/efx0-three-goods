# LB⁺'s rotation with one 4-good agent, in runs of Phase 1 other than `lb4.c`'s

**Claim tried** (`k4/c4.md` §6.1 item 4 as first written). With at most one 4-good agent, a 4-good r that is exposed
after LB⁺'s rotation never makes k* fail.

**What holds.** The claim holds for the runs that `lb4.c` makes: P-steps in LB's key order, upgrades in
smallest-index order, and the first need chain. On those runs, with n = 3 and one 4-good agent, the check logs
`E4_after_rot_k_fails=0` (`results/k4_c4_check_n3_split.log`). With n = 4 and one 4-good agent it logs
`E4_after_rot_k_fails=0` in `results/k4_c4_check.log`.

**What fails.** For runs of Phase 1 with another P-step order, the claim is false. This was found by the referee of
PR #33 (finding F4).

**The run.** n = 4, m = 7, sets [[0,2,5],[1,5,6],[2,3,4,6],[3,4,6]], values [[2,3,4],[2,4,3],[8,4,3,6],[2,3,4]] (listed
in the order of each agent's goods). The processing order is 3, 1, 0, 2.
- Agent 3 takes 6.
- Agents 1 and 2 have lost 6, and agent 1 takes 5.
- Now agents 0 and 2 have lost goods. LB's key would take agent 2, whose top 2 is still free, but this run takes agent
  0. Agent 0 takes 2, agent 2's top.
- Agent 2, the only 4-good agent, takes 3 and is r.

**LB⁺'s bad case.** E_r = {3}. k* = 3 is frozen and its only need chain is 3 → 2.

**After LB⁺'s rotation.** Agent 3 takes O = {3, 4}. r = 2 takes 6, and ω′ = 1, so k*'s bundle is O plus a junk good
outside R_2. Agent 2 values O at 7, more than 6, its base. So r strongly envies every bundle k* can get, and k* is not a
valid owner.

**C₄¹ is not broken here.** Rotating agent 0 along 0 → 2 with O = {0} works (owner 0), and so does the rotation
1 → 0 → 2 with O = {1}.

**Consequence for `k4/c4.md`.** In (G2), "r exposed after LB⁺'s rotation" is not harmless with one 4-good agent in
general. The §6.1 statement now reads "(runs of §5)".

**Smallest configuration:** the run above, n = 4, m = 7.
Reproduce: `python3 attempts/k4_c4_attempts.py g2-other-runs` (under 1 s).
