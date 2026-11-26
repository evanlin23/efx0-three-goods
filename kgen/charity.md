# Bounded charity in terms of relevant goods (CH(k))

Workstream `proof/kgen-charity` (branch `claude/kgen-charity`). Scripts: `kgen/charity/`; logs: `results/kgen_charity/`.
Everything called evidence is evidence only (PROMPT.md §5 rule 3).

## Status (burst 1, in progress)

- Toolkit: raw EFX₀/charity checker, SAT least charity (encoding checked against the raw definitions,
  `enc_check.log`, 0 mismatches), exact CKMS update rules U0/U1/U2 for EFX₀.
- First observation: CKMS's own rules, run from the empty allocation, stop with one unallocated good on GM4-E
  (k = 4) in 17 of 200 tie-breaks.

## The statement

**CH(k).** There is f(k) such that every additive instance in which every agent positively values at most k goods has
a partial EFX₀ allocation (X, P) with |P| ≤ f(k) and v_i(P) ≤ v_i(X_i) for every agent i ("strong charity", as in
Chaudhury–Kavitha–Mehlhorn–Sgouritsa). The weak form asks only v_i(g) ≤ v_i(X_i) for every g ∈ P.

Known: f(2) = 0 (serial dictatorship), f(3) = 0 (the project's theorem, LEDGER row T). TARGET₄ is f(4) = 0.
