# Restarting the draft instead of rotating

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §4).

**Idea.** When r is not a valid absorber, let x be the culprit (k*, the last exposed agent). Rather than rotating
along a need chain, start the draft again:
- `pre_x`, `pre_r`: x takes {b_x, c_x} up front and the others redo the draft. The absorber is x first (`pre_x`) or
  the new r first (`pre_r`).
- `demote`: redo the draft with x never chosen as a leader.

That would be easier to state than a need chain.

**Where it breaks.** Taking b_x and c_x out of the pool changes which agents have R1 priority. The redone draft can
differ everywhere, and it can make another agent need b_x or c_x alone, while x holds both in one bundle. The rotation
avoids this because it changes only one need chain. Theorem B shows that the needs then only shrink (NA′ ⊆ NA).

**Smallest failing configurations.**
- `pre_x` and `pre_r` at n = 5, m = 7: rankings (4, 5, 2), (4, 3, 6), (0, 1, 2), (0, 2, 3), (4, 3, 1).
  - The draft is 0, 1, 3, 2, 4 with picks 4, 3, 1, 0 and nothing for agent 4. r = 4, and agent 0 is exposed with no
    free agent for its protecting good.
  - Redo with agent 0 holding {5, 2}. Agent 3 (0 ≻ 2 ≻ 3) has now lost good 2, so it gets R1 priority, and the
    picks become 0 → 2, 3 → 3, 1 → 4, 4 → 1.
  - Agent 3 needs 2 alone, but 2 is in agent 0's bundle {2, 5}, so agent 3 is unsafe in the output
    {2, 5}, {4}, {0}, {3}, {1, 6}.
  - 1 failure in the 92,100 profiles sampled at n = 5; none at n ≤ 4.
- `demote` at n = 4, m = 7: rankings (3, 0, 4), (3, 1, 5), (3, 2, 6), (2, 0, 1). 4 failures at n = 4, 7 in the
  n = 5 sample.

Reproduce:
- `python3 k3/simplify/exp_restart.py 4`
- `python3 k3/simplify/exp_restart.py 5 300 5`
