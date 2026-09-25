# LS4⁺ with coalition re-divisions of at most k = 2 or 3 agents

Workstream `proof/k4-ls-plus` (`k4/ls4plus.md` §2, §4).

**Approach.** When LS4 is stuck, allow a *coalition re-division* C_k. At most k agents re-divide their bundles and the pool, each taking a set of its own goods; some may lose; the result must be EFX₀ and the level sum Σℓ must rise.
- Σℓ is still a potential, so the search terminates within Σ_i (2^{d_i} − 1) ≤ 15n moves.
- For fixed k each search is polynomial.
- Every dead end logged so far has such an escape with 2 agents, or 3 in one case (`k4/ls4plus.md` §1).

**Counts** (`k4/ls4alg.c -DCMOVE=k`). On the 19 logged LS4 failure states, k = 2 repairs 13 and k = 3 repairs 17 (`results/k4_lsp_variants_19.log`). On 4,380,000 random pure n = 4 profiles (20,000 per core), k = 2 and k = 3 each fail once, and LS4 alone fails 6 times (`results/k4_lsp_4_pure_20k_c2.log`, `results/k4_lsp_4_pure_20k_c3.log`, `results/k4_ls4_4_pure_20k.log`). With k = n (any coalition) nothing failed (`k4/ls4plus.md` §3).

**Where it breaks (smallest found: n = 4, m = 7, pure core).** Agents and values:
- agent 0: goods 0:2, 1:4, 2:10, 3:7;
- agent 1: goods 0:3, 2:10, 5:2, 6:6;
- agent 2: goods 1:4, 4:3, 5:8, 6:6;
- agent 3: goods 3:6, 4:3, 5:10, 6:2.

LS4 makes 14 moves and reaches Y = {2} | {0, 6} | {5} | {3, 4}, with U = {1}.
- No M1, R or exchange-cycle move improves it.
- No coalition of 2 or 3 agents can raise Σℓ.
- No completion exists.
- 14 re-divisions by all four agents raise Σℓ, for example 0 ← {3}, 1 ← {2}, 2 ← {1, 6}, 3 ← {5}.

Y is not a dead end: a Pareto coalition move of all four agents exists (`results/k4_ls4_failures_4_pure.tsv`, row 2).

Reproduce: `python3 k4/lsp_attempts.py` (independent brute force of the 14 moves, of the C_2, C_3 and C_4 families, of the completions, and of the claim that Y is not a dead end).
