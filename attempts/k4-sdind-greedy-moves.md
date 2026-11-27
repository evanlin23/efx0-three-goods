# Attempt: greedy move rules for the reverse-SD insertion

Workstream `proof/k4-sd-induct` (`k4/sd_induct.md` §3, §8). Failed; kept for the record.

**Idea.** Insert the agents in reverse SD order (each new agent first among those present). The absorber o = π_n
starts with all the junk, and each newly inserted agent takes at most one junk good from o. If a fixed local rule for
that one good always worked, the reverse-SD insertion would be an algorithm with a one-step-at-a-time proof.

**Rules tried.**
1. *No lookahead* (`k4/sdind/e4_rule.py`, `results/k4_sdind/e4_rule.log`). Each rule moves a good only when the new
   agent is threatened:
   - the new agent takes its best junk good (or its least valuable one);
   - helpers (other present agents) first;
   - keep π_n the absorber.

   Each fails on 4–14 screen starts for every order producing the picks (n ≤ 5).
2. *Lookahead* (`k4/sdind/e19_lookahead.py`, `results/k4_sdind/e19_lookahead.log`):
   - frozen agents are first in π, so every helper arrives before them;
   - each pick-unfrozen agent takes the junk good most demanded by the frozen agents still to come, either counting
     only those that are threatened ('need') or all that value the good ('val').

   It fails on 19 of 792 screen cases (Y, o) and on 14 of 736 suite cases ('need').

**Why.** A frozen agent needs a *specific* set of its danger goods out of the absorber's bundle, and its wanter may need
some of the same goods as compensation. Counting demands does not capture either. The choice is a hitting-set
problem (which goods leave the absorber's bundle) followed by a matching (which free agent takes each): the static
covering of Corollary TP in the note, i.e. the count of `k4/sdc.md` §30.

**Smallest failing configurations.**
- *No lookahead*, c4min-pareto-n3-m7 (n = 3, m = 7):
  - goods (values): agent 0: {0, 1, 2, 3} (3, 2, 10, 6); agent 1: {2, 4, 5, 6} (8, 4, 2, 3); agent 2:
    {3, 4, 5, 6} (3, 2, 6, 10);
  - picks (2, 4, 6), junk {0, 1, 3, 5}.

  With insertion 1, 2, 0, agent 2 must take good 3 (worth 3 to it) rather than good 5 (worth 6), because agent 0
  (frozen; agent 1 wants its pick) needs 3 out of agent 1's bundle when it arrives. "Take the best good" takes 5 and
  reaches a dead end. With insertion 2, 1, 0 no path of single moves exists at all. Reproduce:
  `python3 k4/sdind/show.py '[[[0, 1, 2, 3], [2, 4, 5, 6], [3, 4, 5, 6]], [[3, 2, 10, 6], [8, 4, 2, 3], [3, 2, 6, 10]]]' '[2, 4, 6]'`.
- *Lookahead ('need')*, GM4-C (n = 4, m = 7):
  - goods (values): {0, 2, 5, 6} (2, 4, 8, 3); {1, 2, 3, 6} (2, 4, 7, 10); {1, 4, 5, 6} (1, 6, 4, 8);
    {3, 4, 5, 6} (8, 6, 10, 3);
  - picks (5, 6, 4, 3), absorber 3, every frozen-first order fails.

  Reproduce: `python3 k4/sdind/e19_lookahead.py screen 5` (prints it as LOOKAHEAD FAILS).
