# LB₄ with only the last block's leader searched (the shape of LB⁺'s Theorem C)

**Idea.** LB⁺'s Theorem C holds for every run of Phase 1, and its Theorem A puts the whole difficulty in the last
block. At k = 4 a fixed insertion order fails (`attempts/lb4-fixed-insertion.md`), but perhaps it is enough to choose
the leader of the last block: for every run of Phase 1, LB₄ on the run, or on the run with the last block's leader
replaced by another agent of that block, succeeds (LB₄ᴸ, `k4/lb4.md` §2). As a construction with index insertion
(`k4/lb4.c -i8`) this is polynomial: at most n runs of Phase 1.

**Evidence for it.** Both forms hold for every core with n ≤ 3 (strict and ties), n = 4 with at most two 4-good
agents, and n = 5 with one; `-i8` also for n = 5 with two (`results/k4_lb4_i8_run.log`, `results/k4_lb4_i9_run.log`).

**Where it breaks.** n = 4 with three 4-good agents: with index insertion (`-i8`) 1 of the 339 cores fails (8,640
profiles); over every run of Phase 1 (`-i9`), 3 cores (20,640 run–profile pairs). Full backtracking over insertion
sequences (LB₄, `-i2`) fails nowhere.

**Smallest failing configuration** (n = 4, m = 8, `-i8`). Agents 0 = {0, 2, 7} (3 goods), 1 = {1, 2, 3, 7},
2 = {1, 4, 5, 6}, 3 = {3, 4, 5, 6}; values 0: (2, 3, 4), 1: (8, 2, 4, 7), 2: (7, 3, 5, 6), 3: (2, 4, 5, 8) on the goods
in that order. By index, agent 1 is inserted and takes 1; agent 2 (lost its top 1) takes 6; agent 3 (lost 6) takes 5
and is upgraded with 4 ({5, 4} is worth 9 > 8); the last block is agent 0 alone, taking 7. Agent 1 is frozen (agent 2
needs 1), junk {0, 2, 3}, ω = 1, and no owner or rotation works. The last block has a single agent, so there is nothing
to choose there; another leader of the *first* block is needed. Brute force: 50 EFX₀ allocations with at most one
large bundle, e.g. {0, 1, 2} | {3, 7} | {4, 5} | {6}.

So at k = 4 the insertion choices of earlier blocks matter too, not only the last one.

Reproduce: `python attempts/lb4_variants.py last-block-leader`.
