# C₄ᵐⁱⁿ with one frozen agent (f = 1)

Workstream `proof/k4-c4min-f1`, building on `k4/c4min.md` (PR #41, under review): its configurations (§1), Theorem Z
(§3), Theorem F (§3.6), Conjecture Φ′ and the f = 1 roadmap (§4). Ledger rows K4.C4MIN.F1.* (CONJECTURE / EVIDENCE
only). PR #46 (`k4/hall.md`, a separate attack by covering/Hall counting) is cited where used.

**Target.** The local improvement lemma of `k4/c4min.md` §4 for configurations with an exposed frozen agent, starting
with f = 1: every configuration at the fewest frozen agents without a valid owner has a move, from a fixed catalogue,
that raises a potential. Then every maximum of the potential is completable, and C₄ᵐⁱⁿ holds on the profiles with f = 1.

**Status.** Work in progress.

## Plan
1. Measure, on every profile with n ≤ 3 and f = 1 and on n = 4 samples, which of the roadmap's assumptions hold at the
   maxima and on all configurations: t = 0, pool-optimality, injectivity of the threat map, terminals on the path.
2. For each non-completable configuration, test which catalogue move raises which potential; find the smallest
   configuration where no move of the catalogue works.
3. Prove the steps that the data supports, each checked by brute force before use.
