# LB₄ with a fixed insertion rule

**Idea.** LB⁺'s Theorem C holds for every insertion order. Perhaps LB₄ also works for a fixed insertion rule, once the
other steps are made as permissive as possible: every upgrade policy, every owner and completion, the owner's needs
from its whole bundle, and up to three rotations whose chains may end at upgraded agents
(`k4/lb4.c -i0 -u3 -r3 -w1 -c1`).

**Where it breaks.** Every core with n = 2 passes. At n = 3 (index insertion), 3 of the 51 cores fail (12,040 profiles).
Other fixed rules fail too, with LB₄'s other steps (`-u1 -r1`): index insertion 25 cores, LB's block lookahead (fewest
goods needed alone, `-i3`) 12, "an agent with a > b + c first" (`-i5`) 25, the sequence with least ω after upgrades
(`-i4`) 16. Trying every insertion sequence (`-i2`) fails nowhere at n = 3.

**Smallest failing configuration** (n = 3, m = 6). Agents 0 = {0, 2, 4, 5}, 1 = {1, 3, 5} (3 goods),
2 = {2, 3, 4, 5}; values 0: (1, 4, 6, 8), 1: (2, 4, 3), 2: (2, 8, 3, 4). Rankings 0: 5 > 4 > 2 > 0, 1: 3 > 5 > 1,
2: 3 > 5 > 4 > 2. Every EFX₀ allocation with at most one large bundle gives agent 2 its top 3, agent 1 its second good 5,
and agent 0 {2, 4} (brute force). By index: agent 0 takes 5, agent 1 (lost its second good) takes its top 3, agent 2
(lost 3 and 5) takes 4 and needs both. To reach a solution, agent 1 must move down from its top to its second good,
which agent 0 holds. A rotation moves every agent of its chain up, and only the rotated agent takes new goods (from the
junk and the chain end's base); up to three rotations do not reach a solution here. Some other insertion sequence
works (`-i2` succeeds on every profile of this core).

So at k = 4 the insertion order matters, unlike Theorem C at k = 3, as far as the rotations tested go.

Reproduce: `python attempts/lb4_variants.py fixed-insertion`.
