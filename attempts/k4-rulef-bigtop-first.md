# Static first-agent rules built on big-top agents (k4/rulef.md §5.2)

**Idea.** A static first-agent rule, read off the profile without running Phase 1: insert first a *big-top* agent
(four goods, top worth more than the next two together, a > b + c). Motivation: on the n = 3 profiles where index
order is not certified by Lemma K, every sampled profile with a big-top agent had its first big-top agent in class K0
or K1 (`results/k4_rulef/features_n3.log`); and a big-top agent that does not get its top keeps needing it, so the
agent holding its top stays frozen until a rotation (remark in `k4/rulef.md` §5.2; cf. (G1) of `k4/c4x.md`, BT1 of
`k4/hall_bt.md`). Variants (`k4/rulef.c -A42 -Q…`):
- `-Q0` the first big-top agent in index order, else agent 0 (index order); `-Q1` else the first agent whose least
  good is another agent's top;
- `-Q2` the first big-top agent, else rule RK (to isolate the big-top part);
- `-Q3` the first big-top agent, else among the agents whose top is another agent's top the one with the fewest private
  goods; `-Q4` the big-top agent with the fewest private goods, else as `-Q3` (built on the data of `-Q0`'s failures:
  of two agents sharing a top, the one with two private goods fails).

**Where it breaks.**
- `-Q0`, `-Q1`: index order without a big-top agent. 9,632 profiles at n = 3 fail with one rotation, all with m = 6 and
  no big-top agent (`results/k4_rulef/bt_n3.log`, `bt1_n3.log`).
- `-Q2`: none open on n ≤ 3 and n = 4 with one or two 4-good agents; with three, 1,096 profiles leave the first
  big-top agent uncertified and 480 of them need two rotations on its sequence, all with two or three big-top agents
  (`results/k4_rulef/btrk_n4_n4_3.log`). With exactly one big-top agent it never fails on these classes.
- `-Q3`, `-Q4`: none fail on n = 3 or n = 4 with one 4-good agent; 4 profiles fail at n = 4 with two
  (`results/k4_rulef/bt3_n34.log`, `bt4_n34.log`): there is no big-top agent, two pairs of agents share their tops, and
  the rule picks a 3-good agent with no private good while the 4-good agent sharing its top is the one that works.

**Smallest failing configurations** (each: LB₄ʳ on the rule's sequence fails with one rotation and succeeds with two,
in `k4/rulef.c` and in PR #33's independent model `k4/c4_verify_H/lb4r.py`, every policy, both owner-needs
conventions; rule RK needs at most one; brute force finds EFX₀ allocations with at most one large bundle):
- `-Q0`, `-Q1` (n = 3, m = 6; none at n = 2 or with m ≤ 5): agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5}, values
  (1, 4, 6, 8), (3, 5, 7, 6), (2, 4, 5, 8); no big-top agent, agent 0 first; rule RK takes agent 2.
- `-Q2` (n = 4, m = 8; the smallest m among the 480): agents {0, 1, 3, 4}, {2, 3, 6, 7}, {2, 5, 7}, {4, 5, 6, 7},
  values (2, 3, 10, 6), (2, 8, 3, 4), (2, 4, 3), (4, 8, 2, 3); agents 0, 1, 3 are big-top, 0 and 1 share the top 3;
  agent 0 (two private goods) first fails, agent 1 (none) is in K0.
- `-Q3`, `-Q4` (n = 4, m = 7): agents {0, 2, 5, 6}, {1, 4, 5, 6}, {2, 3, 5}, {3, 4, 6}, values (2, 8, 4, 5),
  (2, 8, 5, 4), (4, 2, 3), (2, 4, 3); the rules pick agent 2; agent 0 is in K0.

Reproduce: `python3 attempts/k4_rulef_attempts.py` (parts 3–5; `results/k4_rulef/attempts.log`); the counts:
`bash k4/rulef_runs.sh btrk bigtop`.
