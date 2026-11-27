# Attempt: Lemma BOTH for free completions (delete an agent with a private top)

Workstream `proof/k4-sd-induct` (`k4/sd_induct.md` §5). Failed; kept for the record.

**Idea.** Let u hold its top a = Y_u, with nobody wanting a; a private top is the main case. If the picks of
I − u − a have an EFX₀ completion with any number of absorbers, so should the picks of I. With that black-box step:
- SD-C would reduce to instances in which no agent has a private top;
- the reverse-SD insertion would never fail at an unfrozen agent.

The one-absorber form was already refuted (`attempts/k4-sdind-both-one-absorber.md`, r1179). In the free form, every
completion of the sub-instance extended within 4 junk moves on 12,883 cases (screen, suite, random n = 4, 5) and on
6,932 random n ≤ 3 cases (`results/k4_sdind/e12_both_free.log`).

**Result.** Among the 1,693 hard profiles logged in `results/k4_sdc/*.log`, the run `e12_both_free.py logs 5`
(`results/k4_sdind/e12_both_free_logs.log`) finds one where the sub-instance extends and I does not: log174.

**Smallest failing configuration** (log174, n = 3, m = 7; agent: good (value)):
- agent 0: 0 (10), 3 (24), 2 (19), 5 (31). Its top 5 is private.
- agent 1: 0 (35), 2 (43), 1 (33), 6 (40).
- agent 2: 2 (65), 3 (27), 4 (15), 0 (24).

Order (0, 1, 2) gives picks (5, 2, 3) and junk {0, 1, 4, 6}. Agent 2 wants agent 1's pick 2 (65 > 27).
- *Without agent 0* there are 3 free completions. In each, agent 2 holds {3, 4, 0}, worth 66 ≥ 65, and so does not
  strongly envy agent 1. That compensation is what lets agent 1 hold junk, and agent 1 needs junk because {0, 1, 6} is
  worth 108 to it.
- *With agent 0*, agent 0's danger set {3, 0} (34 > 31) lies in agent 2's three-good bundle, and agent 2 needs all
  three of those goods. So the picks of I have no EFX₀ completion at all.

SD-C itself holds here. The only other SD outcome, (5, 6, 2), extends (23 completions), and its sub-outcome extends
too. So a private-top reduction would need a rule choosing which extending outcome of the sub-instance to lift.

**Why.** The same mechanism as r1179. The new agent's danger set is a wanter's compensation, and the wanter's
compensation is what allows the frozen agent to hold junk. Nothing local to the new agent can undo it.

Reproduce (independent brute force): `python3 attempts/k4_sdind_attempts.py bothfree`.
