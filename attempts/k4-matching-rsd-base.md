# Pure reduction as the base case of an induction (k4/matching.md §6)

**Idea** (the coordinator's question, burst 6).
- If reduction steps alone, with a completion at once at the bottom, repaired every hard start, then the induction
  RSD-IND / ROUND-RSD would need no separate one-move lemma (OC₁, "Part 1" of the Hall session's plan).
- A reduction step is a canonical chain from a currently dangerous agent k. Its head takes an improving T inside junk
  plus the end's good, and the reduced start must be a perfect SD outcome.
- Asked as three alternatives: (a) pure reduction with a zero-move base; (b) reduction with base "completes after at
  most one move"; (c) neither.

**Data.** Every one-absorber-hard start with a one-move repair known to the campaign. These are 10,109 distinct starts:
- the proof/k4-oc1max-multi session's 8,383 rows with #D ≥ 2 (8,081 distinct; `results/k4_oc1max_multi/hard2_*.jsonl.gz`);
- the Hall session's 2,071 (1,737 distinct; this note's `results/k4_matching/hard_*.jsonl`, including the 197 with
  #D = 1);
- 291 PW-design starts.

Copies are at `results/k4_matching/data/onemove_hard_{multi,hall2071,pw291}.jsonl.gz`.

**Where (a) breaks.** Pure reduction fails at 35 distinct starts with (L\*) at each step, all with #D ≥ 2. The
smallest is n = 3, m = 6: T3, adaptive-p1, adaptive-p3, and the c4 rotation and gadget starts. Allowing more leaves
fewer failures:
- (L\*) deferred to the final test: 23 starts still fail;
- deleted agents allowed to take junk in the final completion, without deferral: 18 still fail.
  - This variant fixes T3-type starts. Their repair is a reduction whose head must also absorb a junk good it does not
    value, and the base completion of RSD forbids that.
- both together: 6 still fail.

All counts use the one-absorber completion and k4/matching/rsd.py.

At the 6 remaining starts every one-move repair needs a move that a reduction step cannot express. In the repair shown,
a chain agent after the head also takes junk, so that agent holds two goods and the reduced start is not perfect. In
some, the chain's head is not dangerous.

**Smallest failing configuration** (of form (iii), the strongest tested). ls-alt-rule-n4m7 / log794, with n = 4, m = 7:
- Sets [[0,1,2,3],[0,2,5,6],[1,4,5,6],[3,4,5,6]]. Values [[3,6,10,8],[2,8,4,3],[4,2,5,8],[4,3,2,8]].
- Picks (2,5,6,3).
- A one-move repair: the chain (0,1,3). Agent 0 takes {0,3}, 1 takes 0's pick 2, and 3 takes 1's pick 5 *plus junk 4*.
  Owner 0 then takes junk 1.

**Reproduce:** `python3 attempts/k4_matching_rsd_base.py`, output in `results/k4_matching/rsd_base_cex.log`. It is
independent of k4/: raw primitives from `attempts/k4_matching_rsd_n5.py`, brute force over every reduction sequence,
and one-absorber completions over the allowed agents. It tests forms (i)–(iii) on the 6 starts and prints a one-move
repair of each. The first encoding is `k4/matching/rsd.py`, in `results/k4_matching/rsd_onemove_*.log` and
`..._defer_deadrecv.log`.

**Answer: (b).**
- At a one-move start (b) is OC₁ itself, so it holds trivially.
- Pure reduction (a) is not a complete base, even deferred and with deleted agents receiving.
- So Part 1 survives inside the base case. The open core of an induction through reductions is OC₁ under phantom
  constraints (and demands, for the deferred form), together with the reduction step.
