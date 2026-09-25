# One rotation (LB⁺'s shape) at k = 4

**Idea.** LB⁺ needs at most one rotation for every run of Phase 1. At k = 4, with LB₄ʳ's search otherwise as
permissive as possible (every upgrade policy, every owner, every chain and subset O), is one rotation enough?
And with one 4-good agent, is LB⁺'s exact shape (owner r, else one rotation) enough?

**Where it breaks.**
- *Two 4-good agents* (n = 3, m = 6): `lb4.c -i1 -u3 -o0 -r1 -w1 -c1` fails on 2 of the 19 cores with n = 3 and two
  4-good agents (200 (run, profile) pairs). Smallest: agents 0 = {0, 1, 2, 5}, 1 = {2, 3, 4, 5}, 2 = {3, 4, 5}; values
  0: (1, 4, 8, 6), 1: (8, 2, 3, 4), 2: (2, 3, 4); insertion order 2, 0, 1 (one block): agent 2 takes 5, agent 0 its top
  2, agent 1 takes 4; agents 0 and 2 are frozen, ω = 2. Every EFX₀ allocation with at most one large bundle gives
  agent 1 its top 2 and agent 0 its b = 5 (brute force: 5 allocations, e.g. {0, 1, 5} | {2} | {3, 4}), so agent 0 must
  end *below* its pick; one rotation moves every agent of its chain up. Two rotations do it
  (`-i1 -u2 -o0 -r2 -w1 -c1`: 0 failures on every core with n ≤ 3 and two 4-good agents).
- *One 4-good agent, owner r only* (n = 3, m = 6): with envy-free upgrades, owner r, else one rotation
  (`-i1 -u2 -o2 -r1 -w0 -c0`, LB⁺'s shape) 5 of the 14 cores with n = 3 and one 4-good agent fail (20 at n = 4).
  Smallest: agents 0 = {0, 2, 4, 5} (values 2, 4, 8, 3), 1 = {1, 3, 5}, 2 = {3, 4, 5}; values 1: (2, 3, 4),
  2: (2, 4, 3); order 2, 0 | 1 (two blocks). Trying every owner before the rotation (`-o0`) repairs every core with
  one 4-good agent and n ≤ 4 (`k4/c4.md` §6.2, conjecture C₄¹).

So with two 4-good agents nested rotations are needed (as `k4/lb4.md` §3 found for index insertion), and with one,
owners other than r are needed.

**Smallest failing configurations**: the two above (n = 3, m = 6 each).
Reproduce: `python3 attempts/k4_c4_attempts.py one-rotation`.
