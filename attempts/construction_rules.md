# Simpler insertion rules for construction LB

**Idea.** Construction LB (`src/construct.py`) is a serial dictatorship with an adaptive order followed by a junk placement. The only real choice is which agent takes its top when every remaining agent still has all three goods (a core state). The natural simple rules are:
- `index`: the unprocessed agent of smallest index;
- `fewclaims`: an agent whose top no other remaining agent claims, so nobody loses a top (then index);
- `manyclaims`: an agent whose top the most remaining agents claim, so one good that must stay alone serves many losers (then index);
- `na`: a one-step lookahead, the agent whose insertion (plus the R1 steps it forces) leaves the fewest goods that some agent needs alone (NA).

Phase 2 (upgrades, slots, one overflow bundle) is the same for all of them. By L7, the overflow is |NA| − (2n − m) after upgrades, so each rule tries to keep NA small.

**Where they break.** All four fail. The smallest failing configurations are at n = 3, m = 5, on the core `[[0, 2, 3], [1, 2, 4], [0, 1, 2]]` (goods 3, 4 private).

- `na` fails on 2 of the 648 (core, profile) pairs at n = 3, m = 5. Example (a > b > c): agents `(2, 0, 3)`, `(1, 2, 4)`, `(1, 2, 0)`. Inserting any of the three agents first leaves |NA| = 2, and the index tie-break inserts agent 0. The resulting picks are 0: {2}, 1: {1}, 2: {0} (agent 2 holds its c and needs 1 and 2 alone), with junk {3, 4}. The slack is 2n − m = 1, so one junk good overflows. The only owner that is not frozen is agent 2, and {0, 3, 4} holds agent 0's b = 0 and c = 3 while agent 0 holds only its top. Inserting agent 1 first instead gives picks 1: {1}, 2: {2}, 0: {0} with junk {3, 4}. Agent 0 holds its b = 0 and its c = 3 is junk, so the upgrade gives it {0, 3}, and then only good 1 must stay alone. The result {0, 3}, {1}, {2, 4} is EFX₀ with bundles of at most two goods. The count |NA| ignores that upgrade; construction LB counts NA after the upgrades that are already certain and does not fail here.
- `index` and `manyclaims` fail on 14 pairs at n = 3, m = 5 (the first is the same profile), `fewclaims` on 10. At n = 4 they fail on 376, 386 and 210 of the 20,736 pairs with m = 6, and on 52, 52 and 26 of the 10,368 pairs with m = 7. A typical failure: agents `(0, 1, 4)`, `(2, 3, 5)`, `(0, 2, 3)`, `(2, 3, 1)`. Here the winner of the contested top 0 must be agent 2, whose b = 2 is itself a contested top. If agent 0 wins instead, agent 2 takes 2 as its b, and both claimants of top 2 lose it, which forces a chain that the slack cannot pay for.

**Lesson.** The winner of a contested top should be chosen so that the losers' second choices are not themselves someone's top, and the count of goods needed alone must include the upgrades (case P) that junk c-goods will allow. Construction LB's lookahead does both, and it does not fail on any profile of any connected core with n ≤ 5 (`results/construct_2_5.log`).

Reproduce: `python attempts/construction_rules.py 3 5` (and `python attempts/construction_rules.py 4 6 7`).
