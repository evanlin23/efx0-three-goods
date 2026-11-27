# Canonical chains do not suffice when |D| ≥ 2, even single-θ ones (D1-C does not extend)

Workstream `proof/k4-oc1max-multi` (`k4/oc1max_multi.md` §6).

**Idea.** Lemma D-red reduces a canonical chain from a dangerous agent k, with owner k, to three obstacles: HEAD, CROWD
and DEMAND. If the head z has Θ(z) = {k}, DEMAND cannot occur (Corollary TR), so the chain behaves as in the case
|D| = 1. The Hall session's sub-lemma D1-C (`k4/oc1_hall.md` §21) would then give the repair: a chain with CROWD only
is repaired by another minimal H₀ on the same chain.

**Result: false at |D| = 2.** T3 (special set; n = 3, m = 6):
- sets [[5,0,4,2],[3,1,4],[4,1,3,0]];
- values [[1,38,36,6],[12,22,30],[28,20,12,38]];
- order (0, 1, 2), picks (0, 4, 1), J = {2, 3, 5}, D = {0, 1}, D_T = ∅, Θ(2) = {1}.

What happens:
- The only unfrozen agent is 2, so every canonical chain ends at 2.
- The chain 0 → 2 has no improving set: agent 0 values only 2 and 5 in J ∪ {1}, at 6 + 1 < 38.
- The chain 1 → 2 is single-θ. Its only improving set is {1, 3} (22 + 12 > 30). The head 2 then holds 4 (28) and is
  crowded by {1, 3} (20 + 12 > 28). It values no remaining junk good, so it cannot be compensated. No absorber works
  after this chain (raw enumeration).
- So no canonical chain repairs, with any owner. There is no second minimal H₀, which is what D1-C would need.

**What repairs** (all repairing moves, one resulting state):
- the bases ((2, 4), (1, 3), (0)), reached by the ED chain 0 → 2 → 1:
  - agent 2 takes 0;
  - agent 1 takes 2's pick 1 plus junk 3;
  - agent 0 takes 1's pick 4 plus junk 2;
- or by the ring (0, 2, 1), or by chains with a junk-taking middle agent.

It is a ring through both dangerous agents, and any agent can absorb afterwards.

On the data (`results/k4_oc1max_multi/regimes.log`), 79 of the 8,383 hard perfect starts with |D| ≥ 2 have no
canonical repair. All 79 have such an ED repair. This is sub-lemma RING of `k4/oc1max_multi.md` §7.

The weaker fact, that canonical chains alone do not suffice, was known: adaptive-p1, in
`attempts/k4-oc1-hall-canonical-chains.md` on `claude/k4-oc1-hall`. New here:
- it fails on a single-θ chain;
- no alternative H₀ exists;
- so a proof of D1-C has to use that no other frozen agent values junk. In T3, agent 0's pick-danger {4, 2} is what
  blocks the frozen absorber 1 at the picks.

**Repro.** `python3 k4/oc1max_multi/repro.py t3`.
