# Owner validity as a covering problem, and C₄ᵐⁱⁿ by Hall-type arguments

Workstream `proof/k4-hall`, ledger rows K4.HALL.* (CONJECTURE / EVIDENCE only), ledger open item 18. A second,
independent attack on conjecture C₄ᵐⁱⁿ of `k4/c4x.md` §5 (PR #36, branch `proof/k4-c4x`); the other one (branch
`proof/k4-c4min`) uses the walk/cycle technique of Theorem K3 and was not read for this file. Notation as in
`k4/lb4.md` §1 and `k4/c4x.md` §1.

**Status: work in progress.** Nothing here changes K4.D or K4.T.

Plan:
1. Characterize removal-only owner validity exactly as a covering (hitting-set / independent-set) condition in a
   threat hypergraph, and check it against `k4/c4x.c`'s exact test.
2. Classify the minimal violators at pre-allocations with the fewest frozen agents, on n ≤ 3 exhaustively, samples at
   n = 4, and H_1–H_3.
3. Prove an augmenting lemma, or give the sharpest partial result with the exact gap.

Tools: `k4/hall.c` (written from the definitions, independently of `k4/c4x.c`), `k4/hall_run.py` (driver),
`k4/hall_c4x_xcheck.py` (builds `k4/c4x.c` of PR #36 with a per-profile summary line, for the cross-check).
