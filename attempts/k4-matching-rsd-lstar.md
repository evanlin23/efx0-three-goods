# Iterated reduction with the lift condition at each step (Conjecture RSD-IND, k4/matching.md §6)

**Idea** (the coordinator's question, burst 5; ledger K4.MATCH.RSDIND).
- Settle one sharer at a time. A canonical chain from a dangerous agent k ends with k holding an improving T inside
  junk plus the end's good.
- (L\*): T must threaten no other present agent at its value then.
- Delete k and T, and recurse on the smaller instance at its perfect SD start. Finish with a completion.
- Lemma LIFT\* (written proof) lifts every level, provided each deleted agent's phantom constraints hold (Lemma
  PHANTOM).
- Conjecture RSD-IND: some such sequence always exists. With LIFT\* it would give TARGET₄ by induction on n.

It holds at every n = 4 start with no one-move repair (K4.MATCH.RSD.N4, certified: two steps, then a completion).

**Where it breaks.** At n = 5, two sharers can each hold a set that threatens an agent which only the *other* sharer's
chain improves. Whichever sharer is settled first, its T threatens an agent at that agent's value at the time, so
(L\*) fails. The threat disappears only after the second chain. So no sequence with (L\*) at each step exists. The two
chains are vertex-disjoint and commute, and applied together they repair.

**Smallest failing configurations** (n = 5, k = 4). Both are sampled two-move starts of compute/k4-oc1max-cert's
chunk 5_pure_s5o0 (commit 259289f9). The certifier's (list, idx) is not unique across m, so m is part of the name.
- **5_pure m = 10, idx 419.**
  - Sets [[0,2,6,7],[1,4,8,9],[3,5,8,9],[4,5,7,9],[6,7,8,9]]. Values [[6,3,10,8],[4,8,2,3],[2,8,4,3],[6,7,5,3],[10,7,2,6]].
  - Picks (6,4,5,9,7), junk {0,1,2,3,8}. Agent 3 is the single holder, holding 9.
  - The chain (0,4): 0 takes {0,7} and 4 takes 6. The set {0,7} is worth 5 to agent 3, which holds 9, worth 3: a
    threat.
  - The chain (1,3): 1 takes {1,8,9} and 3 takes 4. The set {1,8,9} is worth 2 + 6 = 8 to agent 4, which holds 7,
    worth 7: a threat.
  - Each threat is resolved only by the other chain: agent 3 ends with 4, worth 6, and agent 4 ends with 6, worth 10.
- **5_pure m = 11, idx 447.**
  - Sets [[0,2,5,8],[1,6,7,8],[3,6,9,10],[4,7,9,10],[5,8,9,10]]. Values [[3,4,8,6],[1,6,8,4],[2,10,6,3],[2,8,3,4],[10,8,3,6]].
  - Picks (5,1,6,7,8). The chains (0,4), where 0 takes {0,8}, and (2,1), where 2 takes {3,9,10}, again repair only
    together.

**Reproduce:** `python3 attempts/k4_matching_rsd_n5.py`, output in `results/k4_matching/rsd_n5_cex.log`. It is
self-contained, with raw definitions and a brute force over every sequence of reduction steps of any depth. Each
step uses any canonical chain from a currently dangerous agent and any improving T, with the SD check. Each sequence
ends in *any* assignment of the remaining junk to present agents, which is broader than k4/matching/rsd.py's
one-absorber completion.
- With (L\*) at each step: no sequence, at either start.
- With (L\*) deferred to the final test: two steps, with vertex-disjoint chains, each also a move at the picks.

This is the second, independent encoding. The first is `k4/matching/rsd.py`
(`results/k4_matching/rsd_5pure_s5o0_any.log`, `..._any_E.log`).

**What survives.**
- Lemma LIFT\* and Lemma PHANTOM are conditional statements and stand.
- K4.MATCH.RSD.N4 stands: at n = 4 these configurations do not occur.
- The deferred form, RSD-D (ledger K4.MATCH.RSDD), repairs all 280 sampled n = 5 starts of the chunk: two steps, then
  a completion. An induction in that form must carry *demands* as well as phantom constraints. A present agent
  threatened by a deleted T must end with at least v_i(T) − min_T v_i. In matching terms this is Lemma M's exposed slot
  that must be compensated.
- These two starts are also not covered by the multi session's REC-S or by my OC2-REC. They are covered by the
  coordinator's ROUND-P, which runs one round of two simultaneous moves.
