# LB₄ with a fixed insertion rule and one rotation

**Idea.** LB⁺'s Theorem C holds for every insertion order. Perhaps LB₄ also works for a fixed insertion rule, once the
other steps are as permissive as possible: every upgrade policy, every owner and completion, the owner's needs from its
whole bundle, and one rotation whose chain may end at an upgraded agent (`k4/lb4.c -i0 -u3 -r1 -w1 -c1`).

**Where it breaks.** With index insertion and every upgrade policy (`-i0 -u3 -r1 -w1 -c1`), every core with n = 2
passes, and 3 of the 51 cores with n = 3 fail (12,040 profiles). Fixed rules with LB₄'s single upgrade policy (options `-u1 -r1 -w1 -c1`); each of
them also fails in 1 of the 5 cores with n = 2 (300 profiles), and at n = 3:

| rule | option | cores failing at n = 3 | profiles |
|---|---|---|---|
| index | `-i0` | 16 | 160,060 |
| LB's block lookahead (fewest goods needed alone) | `-i3` | 4 | 13,780 |
| the sequence with least ω after upgrades | `-i4` | 9 | 32,160 |
| an agent with a > b + c first | `-i5` | 16 | 109,016 |
| if the index run fails, rerun it with the last block led by that run's r | `-i7` | 4 | 13,480 |

With every upgrade policy, `-i7 -u3 -r1 -w1 -c1` fails nowhere at n ≤ 3. Log: `results/k4_lb4_variants.log`.

**Nested rotations repair it at n ≤ 3, with every upgrade policy.** With up to two or three rotations in a row and
every upgrade policy, index insertion fails nowhere at n ≤ 3 (`-i0 -u3 -r2 -w1 -c1`, `-i0 -u3 -r3 -w1 -c1`; lazy
branching and brute force agree, `k4/test_lb4.py`). With LB₄'s single upgrade policy it still fails
(`-i0 -u1 -r3 -w1 -c1`: 1 core with n = 2, 300 profiles; 14 cores with n = 3, 147,240 profiles). Same log. An earlier version of this file claimed the opposite; that came from a bug in `lb4.c`
(the rotation depth was not reset after a type split, and after two rotations a base of three goods could be left
outside the owner's bundle), fixed in the commit that added this paragraph.

**Smallest failing configuration** (n = 3, m = 6, `-i0 -u3 -r1 -w1 -c1`). Agents 0 = {0, 2, 4, 5}, 1 = {1, 3, 5}
(3 goods), 2 = {2, 3, 4, 5}; values 0: (1, 4, 6, 8), 1: (2, 4, 3), 2: (2, 8, 3, 4). Rankings 0: 5 > 4 > 2 > 0,
1: 3 > 5 > 1, 2: 3 > 5 > 4 > 2. Every EFX₀ allocation with at most one large bundle gives agent 2 its top 3, agent 1
its second good 5, and agent 0 {2, 4} (brute force). By index: agent 0 takes 5, agent 1 (lost its second good) takes
its top 3, agent 2 (lost 3 and 5) takes 4 and needs both. To reach a solution, agent 1 must end below its pick, on
the good agent 0 holds. One rotation moves every agent of its chain up, and only the rotated agent takes new goods
(from the junk and the chain end's base), so one rotation does not reach it. Two rotations do. After the upgrade of
agent 2 to {4, 2} (worth 5, so it still needs 3), for example: agent 1 gives 3 to agent 2 (a chain ending at an upgraded
agent), agent 2 releases {4, 2}, and agent 1 keeps only its private good 1; then agent 0 gives 5 to agent 1, which needs
it, and takes {4, 2} (worth 10 > 9); the owner is agent 0, and the result is {0, 2, 4} | {1, 5} | {3}, one of the
brute-force solutions. The second rotation moves agent 1 back up from 1 to 5, below its first pick 3. Another insertion
sequence also works (`-i2` succeeds on every profile of this core).

So with one rotation the insertion order matters at k = 4, unlike Theorem C at k = 3. With nested rotations and every
upgrade policy this is not established: index insertion with `-u3 -r3 -w1 -c1` passes n ≤ 3 and every n = 4 core with
at most three 4-good agents (`results/k4_lb4_nested_n4.log`); pure n = 4 not tested.

Reproduce: `python attempts/lb4_variants.py fixed-insertion`.
