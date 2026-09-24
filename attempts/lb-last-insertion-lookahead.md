# S2.LB from the lookahead at the last insertion step alone

**Idea.** Theorem A of `proofs/lb_last_step.md` reduces LB's last step to one configuration, the *bad case*. In the bad
case, the leader k of the last block holds only its top, and its b and c are free. The need chains from k all end at
r, the last-processed agent that is not upgraded. LB inserts, at every insertion step, an agent whose insertion
leaves the fewest goods needed alone (the lookahead count of `src/construct.py`). The idea was to prove S2.LB using
only the *last* insertion step. The conjecture: whatever the earlier insertion choices, if the last insertion has
minimal lookahead count, then r is a valid owner (so the bad case never arises).

**Evidence for it.** It holds for every run, over all sequences of insertion choices, of every connected core with
n ≤ 5, at every m and every ranking profile (`src/lb_tree.c`).

**Where it breaks.** At n = 6, m = 10, 106 runs over all insertion choices have a count-minimal last insertion and
r is not a valid owner. None of them is LB's own run, and in all of them some other
owner is valid. n = 6 with m ∈ {8, 9, 11, 12} has no such run. The full counts are in `results/lb_tree.log`
(`r_bad_lastmin`).

**Smallest failing configuration** (reproduced by `python attempts/lb_last_insertion.py`, a standalone Python
re-implementation). Core `[[0, 1, 5], [0, 4, 6], [1, 4, 7], [2, 4, 8], [3, 4, 9], [2, 3, 4]]`, profile
(0, 0, 1, 1, 2, 1). The rankings (a, b, c) are (0, 1, 5), (0, 4, 6), (1, 7, 4), (2, 8, 4), (4, 3, 9), (2, 4, 3).
- The first insertion step inserts agent 1, with count 2. The minimum there is 1 (agent 5), so this is not LB's choice.
- The second and last insertion step inserts agent 3. Its count 3 is minimal (tied with agent 5).
- Order 1, 0, 2, 3, 5, 4. Picks 1, 0, 7, 2, 3, 4. Junk 5, 6, 8, 9. Agent 4 is upgraded, agents 0, 1, 3 are frozen.
- r = 5 is not a valid owner. Agents 2 and 4 are.

So minimality at the last step does not control what earlier, non-minimal, insertions left behind.

**Lesson.** A proof of S2.LB through the lookahead would have to use the lookahead at every insertion step, not just
the last one. Conjecture D does not need S2.LB at all. One rotation along a need chain repairs the bad case whatever the
insertion choices (Theorem B of `proofs/lb_last_step.md`), so construction LB⁺ never fails.
