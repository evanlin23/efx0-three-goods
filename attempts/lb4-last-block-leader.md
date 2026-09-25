# LB₄ with only the last block's leader searched, for every run of Phase 1 (the shape of LB⁺'s Theorem C)

**Idea.** LB⁺'s Theorem C holds for every run of Phase 1, and its Theorem A puts the whole difficulty in the last
block. At k = 4 a fixed insertion order fails with one rotation (`attempts/lb4-fixed-insertion.md`), but perhaps it is
enough, whatever the earlier insertion choices, to choose the leader of the last block: for every run of Phase 1, LB₄
on the run, or on the run with the last block's leader replaced by another agent of that block, succeeds
(`k4/lb4.c -i9 -u1 -r1 -w1 -c1`: every insertion sequence τ, and for each, LB₄ᴸ(τ) of `k4/lb4.md` §2).

**Evidence for it.** It holds for every core with n ≤ 3 (strict and ties), n = 4 with at most two 4-good agents, and
n = 5 with one (`results/k4_lb4_i9_run.log`).

**Where it breaks.** n = 4 with three 4-good agents: 3 of the 339 cores fail, 20,640 (run, profile) pairs
(`results/k4_lb4_i9_run.log`).

**Smallest failing configuration** (n = 4, m = 8). Agents 0 = {0, 2, 7} (3 goods), 1 = {1, 2, 3, 7},
2 = {1, 4, 5, 6}, 3 = {3, 4, 5, 6}; values 0: (2, 3, 4), 1: (8, 2, 4, 7), 2: (7, 3, 5, 6), 3: (2, 4, 5, 8) on the goods
in that order. Of the 4 runs of Phase 1 of this profile, the one that inserts agent 1 first fails: agent 1 takes its
top 1; agent 2 (lost its top 1) takes 6; agent 3 (lost 6) takes 5 and is upgraded with 4 ({5, 4} is worth 9 > 8);
then agent 0, which has lost nothing, is inserted alone in a second block and takes 7. Agent 1 is frozen (agent 2 needs
1), the junk is {0, 2, 3}, ω = 1, and no owner or rotation works. The last block is agent 0 alone, so there is nothing
to choose there; the first block's leader has to change. (The index run, which inserts agent 0 first, puts all four
agents in one block; it fails too, but another leader of that block works, which is what `-i8` finds.) Brute force: 50
EFX₀ allocations with at most one large bundle, e.g. {0, 1, 2} | {3, 7} | {4, 5} | {6}.

So, with one rotation, the insertion choices of earlier blocks matter at k = 4, not only the last one.

Reproduce: `python attempts/lb4_variants.py last-block-leader` (its counts are (run, profile) pairs).
