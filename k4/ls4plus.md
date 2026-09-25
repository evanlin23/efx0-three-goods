# LS4⁺: escaping the dead ends of LS4 (k = 4)

Workstream `proof/k4-ls-plus`, ledger open item 17 (positive direction). Rows `K4.LSP.*`. Builds on `k4/local_search4.md` (Algorithm LS4, Theorem 1, Proposition 7: dead ends). Notation as there: Y is a junk-free EFX₀ partial allocation, U its pool, ℓ_i the level of agent i (the rank of v_i(Y_i) among the subset sums of R_i), and Σℓ the level sum.

**Status.**
- **Escape study (§1).** Every one of the 8 logged dead ends of LS4 is created by LS4's *last* move, a greedy single-agent add. Each can be escaped by a re-division among only **2 agents** (3 in one case), in which one agent loses and Σℓ rises. The other 11 logged failures are not dead ends; they admit Pareto coalition moves, which in one case need all 4 agents.
- **LS4⁺ (§2).** LS4 plus one move type, used only when LS4 is stuck: a *coalition re-division* C_k, in which at most k agents re-divide their bundles and the pool so that Σℓ rises (some members may lose).
  - Σℓ remains a potential, so termination (≤ Σ_i (2^{d_i} − 1) ≤ 15n moves) and soundness carry over (Theorem 1⁺).
  - With k = n, LS4⁺ can stop only at a placement or at a **global maximum of Σℓ**. So its correctness follows from **conjecture GM₄**: every junk-free EFX₀ partial allocation of a k = 4 core that maximizes Σℓ admits a placement of the pool. With K4.CORE and K4.TIE, GM₄ would give TARGET₄.
- **Evidence (§3), no counterexample.**
  - LS4⁺ with k = n passes the 21.9M sampled pure n = 4 profiles on which LS4 failed 20 times, and the regression classes.
  - GM₄ itself is tested on every maximal state, not only reached ones: n = 2 exhaustive, and large samples at n = 3 and n = 4.
- **Negative (§4, `attempts/k4-lsp-*.md`):**
  - bounded coalitions (k ≤ 3) fail at n = 4, m = 7;
  - stopping at the first placement fails;
  - leximin instead of Σℓ fails: the dead end of Proposition 7 is its own unique leximin maximum.

  So no local move of bounded size was found. The only candidate left is the unbounded coalition move, i.e. conjecture GM₄.
- **Not proved:** GM₄, and any polynomial time bound. C_n and LS4's exchange cycles are searched by enumeration.

## 1. Escape study (`results/k4_ls4_failures_4_pure.tsv`, the 19 logged LS4 failure states)

For each failure state Y (all pure n = 4, m = 7, 8, 9) I computed three things by brute force (scripts in the PR history; claims replayed in `k4/lsp_attempts.py`):
- every complete EFX₀ allocation X, and the set of agents it leaves worse off than Y;
- LS4's trajectory, and on it the first dead state;
- the smallest escape: a junk-free EFX₀ partial allocation Z with Σℓ(Z) > Σℓ(Y) that is not a dead end, with the fewest agents whose bundles differ from Y.

| | count | finding |
|---|---|---|
| dead ends (no complete EFX₀ allocation is weakly better for everyone) | 8 | each has complete EFX₀ allocations with exactly **one** worse-off agent (never the last agent 3). Each became dead at LS4's **last** step, a single-agent add by agent 3 ({5} → {3, 5} and similar). The smallest escape changes **2 agents** in 7 cases and 3 in one, with one loser and Σℓ gains of 1–5 (for example: agent 2 passes good 1 to agent 3, {1, 4} → {4} and {3, 5} → {1, 3, 5}) |
| not dead | 11 | a Pareto coalition move exists (complete EFX₀ allocations weakly better for everyone). In one case every such move needs all 4 agents (`attempts/k4-lsp-bounded-coalitions.md`) |

Classification of the three escape kinds the brief asked for:
- *An earlier different choice* (stop at the first placement instead of the last greedy add) repairs 6 of 19. It fails on the others because no state on LS4's path admits a placement (`attempts/k4-lsp-early-stop.md`).
- *A non-Pareto move in the style of LB⁺'s rotation* (one agent gives up a good or its bundle, and the others gain more in levels) repairs all 8 dead ends with 2–3 agents.
- *A coalition move* (Pareto, possibly with all agents) is what the 11 other states need.

The level-sum-raising coalition re-division C_k covers both of the last two.

## 2. Algorithm LS4⁺ and its soundness

**Move C_k (coalition re-division).** A set A of 2 ≤ |A| ≤ k agents, and pairwise disjoint sets Z_a ⊆ R_a ∩ (U ∪ ⋃_{b∈A} Y_b) (possibly empty), such that:
- the partial allocation Y′ with Y′_a = Z_a (a ∈ A) and Y′_j = Y_j (j ∉ A), and every other good in the pool, is EFX₀;
- Σ_{a∈A} ℓ_a(Z_a) > Σ_{a∈A} ℓ_a(Y_a).

Agents of A may lose. For k = n and A = all agents, C_n reaches every junk-free EFX₀ partial allocation with a larger level sum.

**Algorithm LS4⁺_k.** Run LS4 (`k4/local_search4.md` §2): moves M1, R, the Phase-2 check, then X. When LS4 would stop with failure (no M1, R or X move, no placement), apply a C_k move if one exists and continue. Otherwise stop with failure. Implementation: `k4/ls4alg.c -DCMOVE=k`. It takes the first coalition in order of size, then index, and the first sets in subset order.

**Theorem 1⁺ (soundness and termination).** Every state of LS4⁺_k is a junk-free EFX₀ partial allocation. Every move raises Σℓ by at least 1, so there are at most Σ_i (2^{d_i} − 1) ≤ 15n moves. Every output is a complete EFX₀ allocation. LS4⁺_n fails only at a state that admits no placement and maximizes Σℓ among all junk-free EFX₀ partial allocations.

*Proof.* For M1, R and X this is Theorem 1 of `k4/local_search4.md`: each raises Σℓ, since the movers strictly improve and the others keep their bundles. A C_k move gives a junk-free partial allocation (Z_a ⊆ R_a, disjoint), which is EFX₀ by definition, and it raises Σℓ by definition. So Σℓ strictly increases and is bounded by Σ_i (2^{d_i} − 1). Phase 2 is unchanged, so outputs are complete and EFX₀ (Theorem 1 (iii)).

Suppose LS4⁺_n stops with failure at Y. Then no C_n move applies. Any junk-free EFX₀ partial allocation Z is obtained from Y by the C_n move of all agents that re-divides every good: each agent a takes Z_a ⊆ R_a, and all goods lie in U ∪ ⋃ Y_b. So no such Z has Σℓ(Z) > Σℓ(Y). ∎

**Conjecture GM₄.** For every k = 4 core and strict profile, every junk-free EFX₀ partial allocation that maximizes Σℓ admits a placement of its pool (Phase 2 (a)–(d) of LS4; (a) is sound because a maximum admits no M1 move).

GM₄ implies that LS4⁺_n never fails, hence that every k = 4 core has an EFX₀ allocation. With K4.CORE, K4.TIE and L6 (`k4/SCOUT.md` §2), it implies TARGET₄. Two facts about a maximum Y are immediate from `k4/local_search4.md`:
- Y admits no M1, R, X or coalition move of any kind;
- Lemma 2 applies (F1, F2: nobody envies the pool), and so does Proposition 4. If Y has an empty bundle, or exactly one source, the single dump works.

So a counterexample to GM₄ has at least two sources and no empty bundle.

The variant with the fixed-priority potential (levels in agent order, lexicographic; `k4/ls4_gm.c -DPOT=2`) had no failure either. The leximin variant fails (`attempts/k4-lsp-leximin.md`).

## 3. Evidence (not part of any proof)

RESULTS_TABLE

## 4. Failed designs (`attempts/k4-lsp-*.md`; replayed by `python3 k4/lsp_attempts.py`)

| design | failing configuration | file |
|---|---|---|
| stop at the first placement (`-DEARLY`) | n = 4, m = 7: no state on LS4's path admits a placement; ends in a dead end. Repairs 6 of the 19 logged failures | `attempts/k4-lsp-early-stop.md` |
| coalition re-divisions of at most k = 2 or 3 agents | n = 4, m = 7: only a re-division of all 4 agents raises Σℓ. 1 failure in 4,380,000 pure n = 4 profiles for each k (LS4: 6) | `attempts/k4-lsp-bounded-coalitions.md` |
| leximin of the levels as the potential | n = 4, m = 7: the dead end of Proposition 7 is its unique leximin maximum | `attempts/k4-lsp-leximin.md` |

## 5. Relation to LB₄ (PR #24)

LB₄ (`k4/lb4.md` on `proof/k4-lb4`) is a *construction*: serial-dictatorship bases, a pre-allocation whose needs must stay alone, and a completion with an owner constraint. It has no potential and no moves. LS4⁺ is not LB₄ in local-search form:
- its states are arbitrary junk-free EFX₀ partial allocations;
- its only global object is the level sum;
- its open statement GM₄ is about maxima of Σℓ, not about a construction order.

They share one ingredient. LB⁺'s rotation and LS4⁺'s coalition moves both let an agent lose, which LS4's Pareto moves cannot. What LS4⁺ adds is a termination argument (the potential) that needs no case analysis of the rotation. What it lacks is exactly the analogue of LB⁺'s Theorem A: a proof that a stuck state (a Σℓ-maximum) admits a placement.

## 6. Complexity

- The number of moves is at most 15n, as for LS4.
- C_k takes polynomial time for fixed k: at most n^k coalitions and 16^k set choices, each with an EFX₀ check.
- Bounded k fails already at n = 4 with k = 3 (§4). With k = n, the search is exponential: C_n is a search over all junk-free partial allocations.

So LS4⁺ is an existence argument, conditional on GM₄, with a linear number of moves but no polynomial time bound. A polynomial algorithm would need a structural reason why small coalitions suffice most of the time and a different treatment of the rare states that need large ones.

## 7. Status

- Theorem 1⁺: written proof, pending review (K4.LSP.SOUND, CONJECTURE until reviewed).
- Conjecture GM₄ and LS4⁺_n: EVIDENCE (§3; K4.LSP.GM, K4.LSP.RUN).
- The escape study (§1) and the failed designs (§4): EVIDENCE with independent replay (K4.LSP.VAR).
- Open:
  - a proof of GM₄: its hardest case has ≥ 2 sources, no empty bundle, and no improving move of any kind;
  - whether a bounded move set plus a smarter potential suffices;
  - polynomial time.
