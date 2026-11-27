# Refuted: "frozen slots are not needed after one move" (workstream proof/k4-oc1-hall)

**Claim** (`k4/oc1_hall.md` §13, evidence only). Wherever OC₁ holds, i.e. some state at most one move from the picks
has a one-absorber completion, some state at most one move away has an **S\*** completion. S\* gives frozen agents no
junk. So Lemma 2\* (the S\* count) would be enough for the chain lemma.

**Evidence that looked good.** Every hard start of the n ≤ 5 data sets (§13).

**Counterexample** (found by `proof/k4-matching`, `k4/matching/n4_walk.py`; re-verified here).
- n = 4, m = 8. Sets [[0,2,5,7],[1,5,6,7],[2,3,4,6],[3,4,6,7]], values [[2,10,5,4],[2,3,10,6],[10,6,3,8],[5,3,7,6]],
  order (0, 2, 3, 1), picks (2, 5, 6, 7), D = {0, 2, 3}, J = {0, 1, 3, 4}.
- The picks have no one-absorber completion.
- Five one-move states have a one-absorber completion (the chains (2, 3), (2, 3, 1) and (3, 1), with H₀ = {3, 4}), and
  none has an S\* completion for any owner.
- Example: after (2, 3), the completion [[2],[5,1,7],[3,4],[6,0]] gives frozen agent 3 the junk good 0. This is
  compensated as in Lemma 1's (S1): the wanter, agent 1, is the owner.
- The matching session reports 88 such starts near the n = 4 OC₁^max failures. Two S\* moves repair all of them.

**Smallest failing configuration:** the instance above (n = 4, m = 8).

**Lesson.**
- A proof of OC₁, or of a one-move step, must allow compensated frozen slots: Lemma 1's (S1), not only S\*.
- For OC₂^max, two S\*-shaped moves suffice on the data (matching session).
- The exact count after a move is Lemma M (or Lemma 1's slot form) at the state after the move. That is the
  matching session's EX\*.

**Repro:** `python3 k4/oc1_hall/frozen_slot_cex.py` (log `results/k4_oc1_hall/frozen_slot_cex.log`).
