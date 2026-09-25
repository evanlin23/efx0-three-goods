# LB₄ without a rotation

**Idea.** At k = 3, LB's own runs never needed LB⁺'s rotation on any core searched. Perhaps at k = 4 a search over
the serial-dictatorship runs (every insertion sequence), every upgrade policy (all need-shrinking upgrades, only
envy-free ones, none) and every owner and completion, with the owner's needs taken from its whole bundle, suffices
without a rotation (`k4/lb4.c -i2 -u3 -r0 -w1`).

**Where it breaks.** Every core with n = 2 passes. At n = 3, 16 of the 51 cores fail (263,336 profiles); with the
single upgrade policy of LB₄ (`-i2 -u1 -r0 -w1 -c1`) the same 16. Searching only the last block's leader, for every
earlier insertion sequence, without rotation (`-i9 -u1 -r0 -w1 -c1`): 37 cores fail at n = 3.

**Smallest failing configuration** (n = 3, m = 5). Agents 0 = {0, 1, 3, 4}, 1 = {2, 3, 4}, 2 = {2, 3, 4}; values
0: (3, 5, 7, 6), 1 and 2: (2, 3, 4). Agent 0 is flat (7, 6, 5, 3 on 3, 4, 1, 0: every pair beats every good) and its
private goods 0, 1 together (worth 8) beat its top. Agents 1 and 2 rank 4 > 3 > 2. Every EFX₀ allocation with at most
one large bundle gives agent 0 its private pair, and 3 and 4 to agents 1 and 2 (brute force). In serial dictatorship
with priority to agents that lost a good, agent 0 always picks a shared good: if agent 1 or 2 takes 4 first, agent 0
(its favourite remaining good has rank 0) goes before the other one and takes 3. The pair of private goods is reached
only by a rotation: agent 0 gives 3 to the agent that needs it and takes {0, 1}.

Reproduce: `python attempts/lb4_variants.py no-rotation`.
