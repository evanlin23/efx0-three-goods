# The free-slot deficiency as the number of chains needed (k4/matching.md §2)

**Idea** (matching-theory angle on OC₁^max, coordinator's brief, 2026-11-26):
- write the one-absorber completion of the picks as a bipartite matching of junk goods into slots (Lemma M,
  `k4/matching.md` §1, which is exact);
- read an improving chain as an augmenting path that raises the matching size by one;
- conclude that the Hall deficiency δ of the picks (König–Egerváry: ν = |H| − δ) is the number of chains needed, so that
  OC₁^max would follow from "δ ≤ 1 at perfect starts when k ≤ 4".

Here δ is the free-slot deficiency: the least number of dummy one-good slots, equivalently of deleted junk goods, after
which some owner has a one-absorber completion.

**Where it breaks.** A chain is not an augmenting path with the demand side fixed. It moves ownership, deletes the
whole demand of its head (at k = 4 a danger triangle demands two kept-out goods), and raises or deletes the demands of
the agents it passes through. Consequences:
- At k = 4, 249 of the 2,371 one-absorber-hard perfect starts tested have δ = 2 or 3, and one chain repairs every one of
  them. The δ = 1 / 2 / 3 counts are 2,122 / 234 / 15, in `results/k4_matching/hard_*.log`.
- So "δ ≤ 1 at perfect starts" is false where OC₁ holds.
- At k = 5 the deficiency fails in the other direction too: RD5 has δ = 1 and no single move repairs it.

**Smallest failing configuration** (n = 3, m = 6, k = 4, in the K4.MC2 class: one private good per agent, shared pool
{3, 4, 5}).
- Instance: gap-ivsetting-n3-m6-n3c23 (screen set). Sets [[0,3,4,5],[1,3,4,5],[2,3,4,5]], values
  [[1,6,4,8],[2,5,4,8],[3,6,5,7]].
- Order (2, 1, 0) gives picks (4, 3, 5) and junk {0, 1, 2}. Agents 1 and 2 are frozen and dangerous.
- δ(Y, o) = 2 for every owner o:
  - with owner 0, X_0 holds the pick 4 and at most one junk good. A second junk good is a strong envy for agent 1 or 2
    (e.g. {4, 0, 1} is worth 6 > 5 to agent 1);
  - a frozen agent cannot take junk, because its wanter 0 cannot be compensated.
- One chain repairs: agent 1 gives its pick 3 to agent 0, which wants it, takes {1, 4} (2 + 4 > 5) and owns.
- Not in the K4.MC2 class but equally small: r36 (random cores, seed 91), sets [[0,2,4,5],[1,3,4,5],[3,4,5]], values
  [[2,4,8,7],[8,10,3,4],[4,3,2]], picks (4, 3, 5): again δ = 2 for every owner and one chain repairs.

**Reproduce:** `python3 attempts/k4_matching_attempts.py` (pruning-free brute force over every placement, raw EFX₀).
Output in `results/k4_matching/attempts_check.log`:
- the two k = 4 instances: deficiency {0: 2, 1: 2, 2: 2}, least deficiency after one move 0;
- PW5: deficiency 2 for every owner, least after one move 1;
- RD5: least deficiency 1, least after one move 1, no repairing move.

**What replaces it:** Lemma EX and Conjecture CM (`k4/matching.md` §3). The condition there is the deficiency of the
picks' slot graph *after the exchange* (ownership moved, the chain agents' demands deleted or raised), compared with the
slots the chain frees.
