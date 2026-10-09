# Serial dictatorship, then each leftover good to the first agent that values it

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §4). An algorithm proposed by another AI model (DeepSeek) and
pasted into the session. Recorded here because it is a natural simplification and it fails.

**Idea.** Run serial dictatorship in index order, one good each. Then give every leftover good to the first agent
that values it, or to the last agent if nobody values it.

The proposal's argument goes like this. An agent that receives two of its three goods is safe. An agent with at most
one of its goods is safe if every good it prefers to its own is a singleton. It claims those goods "cannot appear"
in a bundle that received leftovers.

**Where it breaks.** That claim is false. A good that agent i prefers to its own is another agent j's pick, and
step 4 can give j leftovers, so the pick is no longer alone. Step 4 can also put i's b and c into the same bundle
of three or more goods. K3ALG's rules exist to prevent exactly these two failures:
- only free agents (whose good nobody needs alone) receive leftovers;
- upgrades require that nobody needs b alone;
- HitSet keeps exposed pairs apart.

**Smallest failing configuration**, at n = 2, m = 3. Both agents rank 0 ≻ 1 ≻ 2, with values 4, 3, 2.
- Step 2 gives agent 0 good 0 and agent 1 good 1. Step 4 gives good 2 to agent 0, the first agent that values it.
- The output is {0, 2}, {1}. Agent 1 holds its b and v₁({0, 2} ∖ {2}) = 4 > 3, so it is not EFX₀.
- The allocation {0}, {1, 2} is EFX₀. The homework example (values 3, 2, 2 and a worthless good) fails the same way.

**Counts** (raw EFX₀, values 4, 3, 2):
- every ranking profile with n = 2, m = 3: 2 of 6 fail;
- n = 3, m = 5: 1,576 of 3,600;
- n = 4, m = 6: 894,204 of 1,728,000;
- every profile of every core with n ≤ 5: 1,529,276 of 2,445,840.

Log: `results/k3_simplify/greedy_leftovers_to_valuers.log`.

Reproduce: `python3 k3/simplify/exp_deepseek.py`
