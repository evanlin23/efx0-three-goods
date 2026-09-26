# Route 2: a rotation that raises "slots minus forced goods" (Proposition H's count as a potential)

**Claim tried.** Whenever, after Phase 1 and upgrades (or after earlier rotations), no owner is valid, some rotation
along a need chain strictly raises the count. With a bounded integer potential, repeated rotations would then reach a
state with a valid owner, which would prove C₄∃ with unboundedly many rotations.

**The two counts** (`k4/c4tools/c4pot.py`):
- **Φ** is the best slack over the non-frozen owners o, as in Theorem A₄⁺ (`k4/c4.md` §4c): the other agents' slots
  minus the demand of the agents exposed w.r.t. B_o ∪ J. A free agent holding a pick that can protect itself (Lemma 2₄)
  counts 1; any other exposed agent counts ρ, the least number of its junk goods to keep out. A rotated one-good base
  gets a slot, the more generous convention. By Theorem A₄⁺, Φ ≥ 0 means some owner is valid.
- **The owner-free count** is Proposition H's: all slots minus the demand of every agent that the junk alone threatens.

**It fails in both forms.** Φ is an integer and Φ ≥ 0 gives a valid owner. So wherever no single rotation reaches a
valid owner but two do, the first rotation cannot raise Φ past −1.

- **Two 4-good agents, n = 3, m = 6** (smallest). Sets [[0,1,2,5],[2,3,4,5],[3,4,5]], values
  [[1,4,8,6],[8,2,3,4],[2,3,4]]; the first insertion picks agent 2. Phase 1 has no valid owner, Φ = −1 and count = 1.
  All four valid rotations leave Φ = −1 and the count at 1 or 0. Two nested rotations reach a valid owner.
- **One 4-good agent, n = 5, m = 9, index insertion** (the counterexample of `k4-c4one-one-rotation.md`). Φ = −1 and
  count = 1. The three valid rotations give Φ = −3, −1, −2 and count = −2, 0, 0. Every working pair of rotations starts
  with one of these; for example, agent 4 rotates to r taking a single good, which freezes all the others.

**Where it does hold.** An exhaustive scan (`lb4.c -i1 -u2 -o0 -r0 -w1 -c1`, one representative profile per failing
leaf, each state rebuilt in the tracer) covers the no-owner states after Phase 1:
- One 4-good agent, n ≤ 4: some rotation raises Φ in every one of the 50,962 states (n = 3: 1,384; n = 4: 49,578).
- The owner-free count fails to rise in 1,493 of those states.
- All cores with n = 3: no rotation raises Φ in 2,184 of 606,042 states; all of these have two or more 4-good agents.

So the local step fails exactly where two rotations are needed, and there the first rotation lowers or keeps every
count of this kind. A potential for route 2 would have to reward preparing moves (an agent rotated to a single good,
which frees a chain for the next rotation). Proposition H's per-gadget count does not.

**Smallest configuration:** n = 3, m = 6 above (two 4-good agents); with one 4-good agent, n = 5, m = 9.
Reproduce: `python3 attempts/k4_c4one_attempts.py potential` (under 1 s).
