# Local forms of adaptive Lemma M (M_ad) by block counts: what fails

Workstream `proof/k4-lemmam-x` (PR #77, `k4/lemmam_x.md` §7). Ledger rows K4.LMX.X (refuted forms), K4.LMX.AD (M_ad,
open), K4.LMX.L5 (Lemmas 5, 5′).

**The idea.** After Lemma M fell (PR #83, Proposition HH), choose the inserted agent at every insertion step. A run
of Phase 1 is a sequence of blocks; when a block closes, its *block count* (`k4/lemmam_x.md` §7.1: the Hall deficit
of its frozen agents threatened by the goods still unpicked, against its unthreatened chain ends) is computed from the
block and the unpicked goods. Lemma 5: if every block has count 0, LB₄ʳ succeeds without rotation. A local form of
M_ad would choose each block so that its count is 0, leaving at most the last block to one rotation.

**What fails.**
- *(L0) "after blocks of count 0, some unprocessed agent starts a block of count 0".* False at n = 3, m = 6: agents
  {0, 2, 4, 5}, {1, 3, 5}, {2, 3, 4, 5} with values (3, 5, 7, 6), (2, 3, 4), (4, 2, 8, 3). Every first block has
  count 1 (by hand in `k4/lemmam_x.md` §7.3: inserting 0 gives the block {0, 2} with 0 frozen and threatened and its
  only end exposed; inserting 1 or 2 gives a last block whose only end is r). The cumulative count of Lemma 5′ is the
  same at the first step.
- *The greedy rule "insert the agent whose block has the least count, ties by index" as a rule for M_ad.* Its run needs
  two rotations on 11,520 profiles (n = 3, m = 6 smallest: agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values
  (1, 4, 6, 8), (3, 5, 7, 6), (2, 3, 4, 8); every agent starts a single last block of count 1, the tie goes to agent
  0, whose run needs two rotations; both implementations, `results/k4_lemmam_x/check_adp_d2.log`). A last block's
  count does not decide its rotations.
- *(L1∃) "some insertion sequence has every non-last block at count 0 (and succeeds with at most one rotation)".*
  True at n ≤ 3 (every profile, `results/k4_lemmam_x/l46_n2_n3.log`), false at n = 4: 65,720 of the 732,094,848
  profiles with n = 4 and at most two 4-good agents have no such sequence (`l46_n4_2a.log`, `l46_n4_2b.log`). Smallest
  (m = 6, by hand in `k4/lemmam_x.md` §7.3): agents {0, 2, 5}, {0, 3, 4, 5}, {1, 2, 4, 5}, {1, 3, 5} with values
  (2, 4, 3), (5, 2, 8, 4), (5, 2, 8, 4), (2, 4, 3): every first block leaves one agent out and has count 1. Yet every
  first agent is in K0 or K1 there (both implementations) and the greedy run τ = (0, 3) is certified by Lemma K without
  rotation, using upgrades or another owner, which the count ignores. The cumulative count changes nothing here
  (along count-0 blocks it equals the count at closing).

**What survives.** M_ad itself (no counterexample: it holds wherever Lemma M does, and on H_t, HH₃, HH₄ the greedy rule
finds Proposition HH's choices with every block at count 0), Lemmas 5 and 5′ (never contradicted: 918,392,554 runs
with every block count 0, all certified without rotation). The block count is too pessimistic to be the local
invariant: it ignores the upgrades and the owners other than r, and at closing it charges a block for threats by goods
that later blocks will pick (Lemma 5′ removes only the latter). The per-block form M_ad^blk (one rotation per block)
and its local step (L2) are untested.

**Smallest failing configurations.** (L0) and the greedy rule: n = 3, m = 6 above. (L1∃): n = 4, m = 6 above
(core 77 of `results/k4_certs_4_n4_2.json.gz`).

Reproduce (one worker, seconds each): `python3 k4/lemmam_x_cores.py results/k4_certs_3.json.gz CORE -A44 -Y1 -r1
-D47` prints the greedy run (τ, block counts, d) of every profile of a core; `python3 k4/lemmam_x_cores.py
results/k4_certs_4_n4_2.json.gz 77 -A46 -Y1 -r1 -D46` prints the profiles of core 77 without a sequence of count-0
blocks; `python3 k4/lemmam_x_check.py --adp=FILE` rechecks the rotations of ADPBAD lines in PR #33's model.
