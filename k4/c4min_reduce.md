# C₄ᵐⁱⁿ at one frozen agent by reduction to Theorem Z

Workstream `proof/k4-c4min-reduce` (builds on PR #41, branch `proof/k4-c4min`, `k4/c4min.md`). Ledger rows
K4.C4MIN.RED.* (CONJECTURE / EVIDENCE only). Notation as in `k4/c4min.md` §1 and `k4/c4x.md` §1.

**Target.** C₄ᵐⁱⁿ on every strict profile whose fewest frozen agents is f = 1, by reducing to Theorem Z
(`k4/c4min.md` §3): remove the frozen agent x and its good g = φ(x), apply Theorem Z to the smaller instance
I′ = I − x − g, and reinsert x with {g}.

**Status.** Work in progress. Nothing here changes any ledger status.

Tools: `k4/red_lib.py` (Python, written from the definitions; shares no code with `k4/c4min.c` or
`k4/c4min_lib.py`).
