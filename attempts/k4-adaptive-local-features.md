# Adaptive insertion by a local feature (k4/adaptive.md §5)

**Idea.** Choose the next agent at each insertion step from the state alone: the least number of goods needed alone by
the agents of the block it starts (`k4/adaptive.c -A1`, lb4.c's block lookahead `-i3`), 4-good agents first (`-A6`),
3-good agents first (`-A7`), the agent whose top is valued by the fewest (`-A8`) or most (`-A9`) other unprocessed
agents. Ties go to the lower index. On H_t the block lookahead and least-contested top avoid the cascade of
Proposition H (they need no rotation on H_1–H_8 and relabelings, `k4/adaptive.md` §2), which is why they were tried.

**Where it breaks.** With at most one rotation each fails at n = 3, m = 6 (with two, LB₄ʳ succeeds): `-A1` and `-A6`
on 12,040 profiles, `-A7` on 12,160, `-A8` on 11,520, `-A9` on 13,720 (`results/k4_adaptive_rules_n23.log`). Where
index order needs a rotation, the first agent that works is often one reached from the index leader along need
chains, holding a lower good in the index run (`results/k4_adaptive_mine_n3.log`); none of these features sees that.

**Smallest failing configurations** (n = 3, m = 6; `results/k4_adaptive_smallest.log`):
- `-A1`, `-A6`, `-A8`: agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5}, values (1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4);
  first agent 0, two rotations; agent 1 first needs one.
- `-A7`: agents {0, 1, 2, 5}, {2, 3, 4, 5}, {3, 4, 5}, values (1, 4, 8, 6), (8, 2, 3, 4), (2, 3, 4); first agent 2 (the
  3-good agent), two rotations; agent 1 first needs none.
- `-A9`: agents {0, 1, 2, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}, values (1, 4, 8, 6), (1, 4, 6, 8), (8, 2, 3, 4); first agent
  1, two rotations; agent 2 first needs none.

Brute force finds EFX₀ allocations with at most one large bundle on each (K4.D holds).

Reproduce: `python3 attempts/k4_adaptive_attempts.py` (`results/k4_adaptive_attempts.log`: each failure with
`k4/adaptive.c` and in PR #33's independent model, and the brute force).
