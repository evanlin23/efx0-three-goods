# One pass of upgrades instead of the upgrade loop

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §4).

**Idea.** Replace K3ALG's upgrade loop with a single pass in draft order. Upgrade each agent that holds its b, whose
c is junk and whose b nobody needs alone at that moment.

**Where it breaks.** An upgrade removes the upgraded agent's needs, so a good needed alone at an agent's turn in the
pass can stop being needed later. Then (UT) fails at the end: some agent holds its b, its c is junk, and nobody
needs its b, yet it is not upgraded. Theorem B (e) needs (UT) for r.

**Smallest failing configuration**, at n = 3, m = 6. Rankings are (0, 1, 2), (0, 1, 2), (1, 3, 4), and good 5 is
worthless.
- The draft gives agent 0 good 0, agent 1 good 1 (its b) and agent 2 good 3 (its b); the junk is {2, 4, 5}.
- The pass skips agent 1, because agent 2 needs 1, then upgrades agent 2 to {3, 4}. Now nobody needs 1, but
  agent 1 has already been passed.
- r = 1, agent 0 is exposed, and no free agent is left, so the rotation gives agent 1 good 0 and agent 0 the goods
  {1, 2}.
- Agent 1 now holds its top, and its b and c are both in agent 0's bundle, so no junk good can protect it. Agent 0
  also absorbs good 5, giving {1, 2, 5}, and v₁({1, 2, 5} ∖ {5}) = 5 > 4. The loop would have upgraded agent 1 to
  {1, 2} at once.
- Without good 5 (m = 5), agent 0's bundle is just {1, 2}, which is harmless: the run is still EFX₀.

Counts (K3S with `single_pass=True`; the raw EFX₀ check of the allocation built anyway, `strict_absorb=False`):
- 0 of the 3,600 profiles with n = 3, m = 5 fail;
- 24 of 14,400 at m = 6, 48 of 44,100 at m = 7, and 80 of 112,896 at m = 8;
- 12 of 150,000 random profiles with n ≤ 8.

K3S with the loop: 0.

Reproduce: `python3 k3/simplify/exp_k3s_opts.py`
