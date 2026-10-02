# Local forms of adaptive Lemma M (M_ad) by block counts: what fails

Workstream `proof/k4-lemmam-x` (PR #77, `k4/lemmam_x.md` §7). Ledger rows K4.LMX.X (refuted forms), K4.LMX.AD (M_ad,
open), K4.LMX.L5 (Lemmas 5, 5′).

**The idea.** Lemma M is false if Proposition HH (PR #83, refereed correct, merging) holds. The repair chooses the
inserted agent at every insertion step. A run of Phase 1 is a sequence of blocks; when a block closes, its *block
count* (`k4/lemmam_x.md` §7.1) is computed from the block and the unpicked goods: the kept-out goods its frozen agents
threatened by the unpicked goods need, minus the slot places κ₀ of its other agents that are neither frozen nor
threatened (the *slot count* δ, the PR #77 referee's), or minus, Hall-wise, its unthreatened chain ends (the
*chain-end count* δᵉ ≥ δ, the first version). Lemma 5: if every block has count 0, LB₄ʳ succeeds without rotation. A
local form of M_ad would choose each block so that its count is 0, leaving at most the last block to one rotation.

**What fails.** (The block counts and the (L1∃) search are one implementation, `k4/lemmam_x.c`; the smallest
instances are also checked by hand in `k4/lemmam_x.md` §7.3.)
- *(L0) "after blocks of count 0, some unprocessed agent starts a block of count 0".* False at n = 3, m = 6 for both
  counts (one implementation, and by hand): agents {0, 2, 4, 5}, {1, 3, 5}, {2, 3, 4, 5} with values (3, 5, 7, 6),
  (2, 3, 4), (4, 2, 8, 3) (core 27 of `results/k4_certs_3.json.gz`). Every first block has count 1: inserting 0 gives
  the block {0, 2} with 0 frozen and threatened and 2, its only other agent and its only end, threatened; inserting 1
  or 2 gives a last block in which every agent other than the frozen 0 is threatened, frozen or r. The cumulative
  count of Lemma 5′ is the same at the first step.
- *The greedy rule "insert the agent whose block has the least count, ties by index" as a rule for M_ad.* Its run needs
  two rotations on 11,520 profiles, for both counts (n = 3, m = 6 smallest, core 17 of `results/k4_certs_3.json.gz`:
  agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (3, 5, 7, 6), (2, 3, 4, 8); every agent
  starts a single last block of count 1, the tie goes to agent 0, whose run needs two rotations; both implementations,
  `results/k4_lemmam_x/check_adp_d2.log`). A last block's count does not decide its rotations.
- *(L1∃) "some insertion sequence has every non-last block at count 0 (and succeeds with at most one rotation)"*, a
  non-existence claim of one implementation. True at n ≤ 3 and at n = 4 with one 4-good agent, for both counts. False
  at n = 4 with two 4-good agents:
  - *chain-end count*: 65,720 of the 724,847,616 profiles have no such sequence (`results/k4_lemmam_x/l46_n4_2a.log`,
    `l46_n4_2b.log`). Smallest (m = 6, core 77 of `results/k4_certs_4_n4_2.json.gz`, by hand): agents {0, 2, 5},
    {0, 3, 4, 5}, {1, 2, 4, 5}, {1, 3, 5} with values (2, 4, 3), (5, 2, 8, 4), (5, 2, 8, 4), (2, 4, 3): every first
    block leaves one agent out and has δᵉ = 1. The cause (the PR #77 referee's diagnosis): in the first block of
    τ = (0, 3) agent 0 is free, unexposed and not a chain end, so its slot place serves the frozen exposed agent 2,
    and Lemma K's deficit with owner r is −1 without upgrades; δᵉ, which counts only chain ends, misses that place.
    The slot count δ sees it (counts 0, 0 on that run). On all 65,720 profiles the greedy run succeeds with d = 0
    (`results/k4_lemmam_x/l46greedy_n4_2.log`, one implementation).
  - *slot count*: 34,080 profiles have no such sequence (`results/k4_lemmam_x/l46G_n4_2.log`). Smallest (agents {0, 2,
    3, 4}, {1, 3, 5, 6}, {2, 5, 6}, {4, 5, 6} with values (6, 3, 7, 5), (6, 7, 3, 5), (4, 2, 3), (4, 2, 3) (n = 4, m =
    7, core 123 of `results/k4_certs_4_n4_2.json.gz`)): every first block leaves an agent out and has positive slot
    count (inserting 0 or 1 gives a block of two agents with δ = 2: the frozen one needs two goods kept out, its
    partner is threatened; inserting 2 or 3 gives a block of three with δ = 1; by hand and by
    `k4/lemmam_x_blocks.py`). Yet every first agent is in K0 there (both implementations), and the greedy run τ = (2,
    3) (counts 1, 0) has ω = 0 without upgrades: its three junk goods fit the slot places of the three free agents, so
    it is completed without an owner, while both counts charge every threat by the junk to the owner r's bundle. On
    all 34,080 the greedy run with the slot count succeeds with d = 0 (`results/k4_lemmam_x/l46greedyG_n4_2.log`, one
    implementation).

**What survives.** M_ad itself (no counterexample: it holds wherever Lemma M does, it is K4.LB4 relaxed to LB₄ʳ's three
policies, and on H_t, HH₃, HH₄ the greedy rule finds Proposition HH's choices with every block at count 0), Lemmas 5
and 5′ (never contradicted: 918,392,554 runs with every chain-end count 0 and 959,476,926 with every slot count 0, all
certified without rotation). The per-block form M_ad^blk (one rotation per block) and its local step (L2) are untested.

**Smallest failing configurations.** (L0) and the greedy rule: n = 3, m = 6 above (cores 27 and 17 of
`results/k4_certs_3.json.gz`). (L1∃): n = 4, m = 6 for the chain-end count (core 77 of
`results/k4_certs_4_n4_2.json.gz`); n = 4, m = 7 (core 123 of `results/k4_certs_4_n4_2.json.gz`) for the slot count.

Reproduce: `python3 attempts/k4_lemmam_x_attempts.py` (all of the above, about a minute; also the exchange partners of
`attempts/k4-lemmam-x-exchange.md`); `python3 k4/lemmam_x_cores.py results/k4_certs_3.json.gz 17 -A44 -Y1 -r1 -D47`
and `… 27 -A44 -Y1 -r1 -G1 -D47` print the greedy runs (τ, block counts, d) of every profile of those cores;
`python3 k4/lemmam_x_l46greedy.py results/k4_certs_4_n4_2.json.gz -Y1 -r1 [-G1]` lists the profiles without an
(L1∃) sequence and the greedy's d on them; `python3 k4/lemmam_x_check.py --adp=FILE` rechecks the rotations of ADPBAD
lines in PR #33's model.
