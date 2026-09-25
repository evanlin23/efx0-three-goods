# LB₄ with only the last block's leader searched (the shape of LB⁺'s Theorems C and A)

**Idea.** LB⁺'s Theorem C holds for every run of Phase 1, and its Theorem A puts the whole difficulty in the last
block. At k = 4 a fixed insertion order fails with one rotation (`attempts/lb4-fixed-insertion.md`), but perhaps it is
enough, whatever the earlier insertion choices, to choose the leader of the last block: for every run of Phase 1, LB₄
on the run, or on the run with the last block's leader replaced by another agent of that block, succeeds
(`k4/lb4.c -i9 -u1 -r1 -w1 -c1`: every insertion sequence τ, and for each, LB₄ᴸ(τ) of `k4/lb4.md` §2).

The weaker, polynomial form fixes the insertion order: LB₄ᴸ(index order), at most n runs of Phase 1
(`k4/lb4.c -i8 -u1 -r1 -w1 -c1`).

**Evidence for it.** Every run of Phase 1 (`-i9`): every core with n ≤ 3 (strict and ties), n = 4 with at most two
4-good agents, and n = 5 with one (`results/k4_lb4_i9_run.log`). Index order (`-i8`): every core with n ≤ 3 (strict
and ties), n = 4 with at most three 4-good agents, and n = 5 with at most two (`results/k4_lb4_i8.log`).

**Where it breaks.**
- Every run of Phase 1 (`-i9`): n = 4 with three 4-good agents, 3 of the 339 cores, 20,640 (run, profile) pairs.
- Index order (`-i8`): pure n = 4, 4 of the 219 cores (m = 8, 9, 9, 10), 119,200 profiles (`results/k4_lb4_i8.log`).
  (An earlier version of `-i8` stopped trying leaders as soon as one changed the number of insertion steps, and
  reported a failure at n = 4 with three 4-good agents; with that fixed, it has none there.)

**Smallest failing configuration found, every run** (n = 4, m = 8, `-i9`; `-i9` was not run on pure n = 4, whose cores go down to m = 4). Agents 0 = {0, 2, 7} (3 goods), 1 = {1, 2, 3, 7},
2 = {1, 4, 5, 6}, 3 = {3, 4, 5, 6}; values 0: (2, 3, 4), 1: (8, 2, 4, 7), 2: (7, 3, 5, 6), 3: (2, 4, 5, 8) on the goods
in that order. Of the 4 runs of Phase 1 of this profile, the one that inserts agent 1 first fails: agent 1 takes its
top 1; agent 2 (lost its top 1) takes 6; agent 3 (lost 6) takes 5 and is upgraded with 4 ({5, 4} is worth 9 > 8);
then agent 0, which has lost nothing, is inserted alone in a second block and takes 7. Agent 1 is frozen (agent 2 needs
1), the junk is {0, 2, 3}, ω = 1, and no owner or rotation works. The last block is agent 0 alone, so there is nothing
to choose there; the first block's leader has to change. (The index run, which inserts agent 0 first, puts all four
agents in one block; it fails too, but another leader of that block works, which is what `-i8` finds.) Brute force: 50
EFX₀ allocations with at most one large bundle, e.g. {0, 1, 2} | {3, 7} | {4, 5} | {6}.

**Smallest failing configuration, index order** (pure n = 4, m = 8, `-i8`). Agents 0 = {0, 2, 4, 6},
1 = {0, 2, 5, 6}, 2 = {1, 3, 4, 7}, 3 = {1, 3, 5, 7}; values 0: (2, 4, 8, 7), 1: (5, 6, 3, 7), 2: (3, 5, 7, 6),
3: (4, 5, 2, 8) on the goods in that order (agents 1 and 2 are flat). By index, agent 0 is inserted and takes its top 4;
agent 2 (lost its top 4) takes 7; agent 3 (lost its top 7) takes 3 and is upgraded with 1 ({3, 1} is worth 9 > 8);
agent 1, which has lost nothing, is inserted alone in a second block and takes 6. Agent 0 is frozen (agent 2 needs 4),
the junk is {0, 2, 5}, ω = 1, and no owner or rotation works. Again the last block is one agent, so there is nothing to
choose there. 43,200 of this core's 6,879,707,136 profiles fail. Brute force: 63 EFX₀ allocations with at most one
large bundle, e.g. {0, 6} | {1, 2, 5} | {3, 4} | {7}.

So, with one rotation, the insertion choices of earlier blocks matter at k = 4, not only the last one, for the index
order too.

Reproduce: `python attempts/lb4_variants.py last-block-leader` (its counts are (run, profile) pairs) and
`python attempts/lb4_variants.py last-block-leader-index`.
