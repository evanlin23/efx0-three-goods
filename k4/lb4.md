# LB₄: construction LB⁺ carried to four goods

Workstream `proof/k4-lb4`, ledger open item 15, route of `k4/SCOUT.md` §5 (steps (a)–(d)). Notation as in
`proofs/construction.md` and `proofs/lb_last_step.md` (k = 3), and `k4/SCOUT.md` (k = 4 cores).

**Status.** Work in progress. Nothing here is PROVED or CERTIFIED yet.

Plan:
1. Define LB₄ precisely (serial dictatorship with priority to agents that lost a good, type-dependent upgrades,
   owner constraint (OC₄) with type-dependent threats, private pairs in the large bundle).
2. Implement it (`k4/lb4.c`) and test it exhaustively on every core with n ≤ 3 (ties included) and on every
   certified core with n = 4 and n = 5, checking every output against the raw EFX₀ definition.
3. Record the smallest failing configurations (`attempts/`), refine until it never fails on the data.
4. Write the proof: soundness (Theorem 1′ analogue), the owner (Theorem A analogue), the rotation (Theorem B
   analogue), completion.
