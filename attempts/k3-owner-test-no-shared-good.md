# LB⁺'s owner test without the shared good

Workstream `formal/k3-algo` (`proofs/k3_algorithm.md` §4, ledger K3.OWNER).

**Idea.** LB⁺ gives the large bundle to r if some set H of junk goods with |H| ≤ S − cap(r) meets the junk part
π_x = {b_x, c_x} ∩ J of every agent x exposed for r. Otherwise it rotates along a need chain (Theorem B). The
tempting shortcut: take one junk good per exposed pair, so |H| = |E_r|, and test |E_r| ≤ S − cap(r). This avoids
the question of a *smallest* H, which in general is a minimum vertex cover.

**Why it is wrong.** The rotation is sound only in Theorem A's *bad case*, where the sets π_x are pairwise disjoint
(Theorem B (f) uses this). When two exposed agents share a junk good, one good can serve both. Then r is a valid
owner with |H| = |E_r| − 1 = S − cap(r). The shortcut rejects r and rotates outside the bad case. After that
rotation, the pair {b_x, c_x} of an exposed agent can lie inside k*'s new base, and no completion satisfies the
owner constraint. Remark 2 of `proofs/lb_last_step.md` already warns that the shortcut "can overestimate |H| and
reject a valid r". The instance below shows that, inside algorithm K3ALG, it also produces an allocation that is not
EFX₀.

**Smallest failing configuration found** (n = 4, m = 8; `python3 attempts/k3_owner_test.py`).
- Values (agent: good ↦ value):
  - agent 0: 2 ↦ 5, 6 ↦ 4, 5 ↦ 2;
  - agent 1: 0 ↦ 3, 5 ↦ 3, 6 ↦ 2;
  - agent 2: 0 ↦ 3, 1 ↦ 3, 7 ↦ 2;
  - agent 3: 3, 1, 0 ↦ 2 each.

  Good 4 is valued by nobody. All agents are balanced, so no agent is peeled.
- Rankings (a, b, c), ties in index order: (2, 6, 5), (0, 5, 6), (0, 1, 7), (0, 1, 3).
- Phase 1 in `r1Order`:
  - 0 (insertion) takes 2;
  - 1 (insertion) takes 0;
  - 2 takes 1;
  - 3 takes 3.
- NA = {0, 1}, so agents 1 and 2 are frozen. No upgrade applies. The junk is J = {4, 5, 6, 7}, the slot count is
  S = 2, and ω = 2.
- r = 3 with S − cap(r) = 1. The exposed agents are 0 and 1, with π_0 = π_1 = {5, 6}.
- *Exact test* (K3ALG, `hitSet` = [6]): 1 ≤ 1, so r owns the large bundle.
  - Allocation {2, 6}, {0}, {1}, {3, 4, 5, 7}: EFX₀.
- *Naive test*: 2 > 1, so LB⁺ rotates. Here k* = 1 and the chain is 1 → 2 → 3:
  - agents 2 and 3 take 0 and 1;
  - agent 1 takes {5, 6};
  - k* = 1 then owns the large bundle.
  - Allocation {2}, {4, 5, 6, 7}, {0}, {1, 3}. Agent 0 holds only its top, v_0(2) = 5. Agent 1's bundle without good
    4 is worth v_0(5) + v_0(6) = 6 to agent 0. **Not EFX₀.**

**How often.** 3,000,000 random instances with n ∈ {3, 4} (the few-level and uniform generators of `k3/k3algo.py`,
seed 3):
- In 930 runs the shared good decides the exact test.
- In 68 of those the naive variant outputs an allocation that is not EFX₀.
- n = 3 never produced the shared-good case.

Log: `results/k3_owner_test_search.log` (`python3 attempts/k3_owner_test.py --search 3000000 3`).

**Lesson.** The exact test costs little more than the naive one.
- By Theorem A's counting, S − cap(r) ≥ |E_r| − 1. So r is valid iff |E_r| ≤ S − cap(r) or two sets π_x meet
  (Proposition O, `proofs/k3_algorithm.md` §4; Lean `EFX.LB.validOwner_iff`).
- The second condition takes O(|E_r|²) comparisons. No minimum vertex cover is needed.
- The shared good is needed, and it is exactly what `hitSet` provides.
