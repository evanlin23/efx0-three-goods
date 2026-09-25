# k = 4 two-phase local search with arbitrary choices: dead ends

Workstream `proof/k4-localsearch` (`k4/local_search4.md`, Algorithm LS4).

**Approach.** Algorithm LS4 as defined in `k4/local_search4.md`.
- Phase 1 applies Pareto moves to a junk-free EFX₀ partial allocation: single-agent rebundles (M1), envy-cycle rotations (R), and exchange cycles in which agents may keep part of their own bundle (X).
- Phase 2 places the pool: an empty-bundle dump, a single dump, or a dump plus solo goods. An exact search over all junk placements is the fallback.
- Like LS2 at k = 3 (`proofs/local_search.md`, Theorem C: "any choice works"), the hope was that every choice of moves leads to a state Phase 2 can complete. Conjecture TP₄ stated this for every stable state.

**Where it breaks (n = 4, m = 7, pure core).** Agents and values:
- agent 0: goods 0:8, 2:10, 5:6, 6:3;
- agent 1: goods 0:5, 3:2, 4:4, 6:8;
- agent 2: goods 1:1, 2:8, 4:6, 6:4;
- agent 3: goods 1:2, 3:3, 5:6, 6:10.

All four agents are strictly balanced (10 < 17, 8 < 11, 8 < 11, 10 < 11) and all types are strict. Goods 0–5 have two valuers each; good 6 is valued by all four agents.

LS4 (`k4/ls4alg.c`, default choice rule) makes 15 single-agent rebundles from the empty allocation. It reaches Y = {2} | {6} | {1, 4} | {3, 5}, with the pool U = {0}. The values are 10, 8, 7, 9.
- Agent 2 envies agent 0 (good 2 is worth 8 > 7). Agent 3 envies agent 1 (good 6 is worth 10 > 9). The sources are agents 2 and 3.
- The pool good 0 cannot be placed anywhere:
  - at agent 2, agent 1 values {0, 1, 4} at 5 + 4 = 9 > 8;
  - at agent 3, agent 0 values {0, 3, 5} at 8 + 6 = 14 > 10;
  - at agent 0 or agent 1 (who value it), and in every other way, brute force finds no EFX₀ completion.
- No M1, R or exchange-cycle move applies. Nor does any coalition move, in which any set of agents re-divides their bundles and the pool so that each strictly gains. This is brute force with the exact validity rule.
- **No complete EFX₀ allocation gives every agent at least its value in Y** (all 4⁷ = 16,384 allocations checked). Y is a *dead end*: from it no sequence of Pareto moves, followed by any placement, reaches an EFX₀ allocation.

The dead end is a property of the four strict types, not of the integer representatives. Safety and the comparisons V_i(X_i) ≥ V_i(Y_i) are comparisons of subset sums of one agent. So it holds for every valuation of these types.

**What this refutes.**
- Conjecture TP₄ of `k4/local_search4.md` as stated for every stable state: Y is stable and has no placement at all.
- Any two-phase local search in which Phase 1 makes Pareto improvements of junk-free EFX₀ partial allocations with arbitrary choices, as Theorem C allows at k = 3. Y is reached with single-agent rebundles alone, which every such move set contains.

It does not refute a local search with a *specific* choice rule. The same profile succeeds under LS4's alternative rule `-DALT` (most valuable rebundle, rotating agent order), in 5 steps. Nor does it refute one that allows non-Pareto moves (some agent loses, as in LB⁺'s rotation).

**How rare.**
- LS4 with its default rule fails on 20 of the 21,900,000 sampled profiles of the 219 pure n = 4 cores (`results/k4_ls4_4_sample.log`; 10 cores, all with m = 7).
- It never fails on:
  - the other n = 4 cores: 33,900,000 sampled profiles with three 4-good agents; exhaustive with one or two;
  - n ≤ 3: exhaustive, ties included;
  - n = 5 with at most two 4-good agents (sampled, or exhaustive with one).
- Dead ends of any kind are junk-free EFX₀ partial allocations with no dominating complete EFX₀ allocation, reachable or not (`k4/ls4_deadend.c`).
  - n = 2: none, exhaustive (`results/k4_ls4_deadend_2.log`).
  - n = 3: none in 1,020,000 random profiles.
  - n = 4, m ≤ 6: none in 424,000 random profiles.
  - n = 4, m = 7: 34 of 576,000 random profiles have one, in 20 of the 288 cores (8 pure, 7 with three 4-good agents, 5 with two). Every one is reachable by single-agent rebundles (`results/k4_ls4_deadend_4_m7_sample.log`).
  - So the smallest dead end has n = 4 and m = 7 among n = 4 cores; n = 3 is not excluded (sampled only).

Reproduce:
- `python3 k4/ls4_attempts.py` is an independent brute force from the raw definition. It replays the 15 steps (each a valid single-agent rebundle), checks that no M1, R, X or coalition move exists, that no completion exists, and that no complete EFX₀ allocation dominates Y.
- `k4/ls4_deadend.c` (driver `python3 k4/ls4alg_run.py CERTS --prog=ls4_deadend`) searches for dead ends reachable by single-agent rebundles.
