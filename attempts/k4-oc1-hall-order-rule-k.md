# OC₁: no rule from the order picks the dangerous agent that starts the chain

Workstream `proof/k4-oc1-hall` (`k4/oc1_hall.md` §6).

**Idea.** On every hard start (no S\* completion at the picks), some improving chain starting at a dangerous frozen
agent k repairs with k as owner (Finding B). A constructive proof would like to name k from the order π, as LB⁺ names
the leader k\* of the last block. Candidate rules:
- every k ∈ D works;
- the first agent of D in π;
- the last agent of D in π;
- the agent of D with the most wanters.

**Result: all fail** (`k4/oc1_hall/which_k.py`, `results/k4_oc1_hall/which_k.log`; owner k):

| rule | screen | logs | random n = 4 | random n = 5 |
|---|---|---|---|---|
| every k ∈ D | 123 / 234 | 694 / 1,470 | 143 / 255 | 12 / 31 |
| first of D in π (per order) | 553 / 773 | 3,232 / 4,849 | 750 / 981 | 322 / 393 |
| last of D in π (per order) | 578 / 773 | 3,162 / 4,849 | 763 / 981 | 278 / 393 |
| most wanters | 195 / 234 | 1,142 / 1,470 | 222 / 255 | 26 / 31 |

**Smallest failing configuration** for "first or last of D" (induct-lbo-owner-only, screen; n = 4, m = 6):
- sets [[0,3,4],[2,3,5],[0,1,3],[1,2,3]];
- values [[2,4,3],[4,2,3],[2,4,3],[3,4,2]];
- order (1, 0, 2, 3), picks (3, 2, 1, none), D = {0, 1, 2}.

Only k = 0, the middle agent of D in the order, has a repairing chain with owner k.

**Consequence.** k has to be chosen by the count (Corollary 2.1), as Lemma K chooses the owner.

**Repro.** `python3 k4/oc1_hall/which_k.py screen`. For the configuration above, the search snippet in this
workstream's session: every hard start, every k ∈ D, `de_free.moves` with all descriptions, `chain_shapes.s_star_owners`.
