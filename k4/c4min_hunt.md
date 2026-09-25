# Hunting for a counterexample to C₄ᵐⁱⁿ

Workstream `compute/k4-c4min-hunt` (the refuter side; the prover side is `proof/k4-c4min`, PR #41). Target:
conjecture C₄ᵐⁱⁿ of `k4/c4x.md` §5 (PR #36, branch `proof/k4-c4x`): for every strict profile of every k = 4 core,
some valid pre-allocation in 𝒫 with the fewest frozen agents has deficit ≤ 0 (is removal-only completable, with the
owner's needs from its bundle).

Status: work in progress. Nothing here changes K4.D or K4.T.

Plan:
1. exhaustive checks where feasible: n = 4 with three 4-good agents and pure n = 4 (all strict profiles);
2. adversarial search (hill-climbing the least deficit over the min-frozen pre-allocations) on n = 5 and on random
   cores with n = 6–8;
3. structured families with many 4-good agents (H_t of `k4/c4.md` §7 for t ≥ 4, perturbed values, other gadget
   chains, trees and cycles of gadgets);
4. the weaker forms (some min-frozen P completable with any deficit; K4.D by SAT) wherever C₄ᵐⁱⁿ fails.
