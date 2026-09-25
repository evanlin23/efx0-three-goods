# LS4⁺: a local search designed to escape the dead ends of LS4 (k = 4; it escapes all 8 logged ones)

Workstream `proof/k4-ls-plus`, ledger open item 17 (positive direction). Rows `K4.LSP.*`. Builds on `k4/local_search4.md` (Algorithm LS4, Theorem 1, Proposition 7: dead ends). Notation as there:
- Y is a junk-free EFX₀ partial allocation and U its pool;
- V is the strict type the algorithm uses (`k4/local_search4.md` §0);
- ℓ_i(S) := #{T ⊆ R_i : V_i(T) < V_i(S)} is the *level* of a set S ⊆ R_i for agent i, ℓ_i := ℓ_i(Y_i), and Σℓ is the level sum.

A *placement* of the pool is one of LS4's Phase-2 shapes (a)–(d). At a maximum of Σℓ, (a)–(c) are special cases of (d); see §2.

**Status.**
- **Escape study (§1, `k4/lsp_escape.py`).**
  - Each of the 8 logged dead ends of LS4 is created by LS4's *last* move, a greedy single-agent add. Each can be escaped by a re-division among only **2 agents** (3 in one case), in which one agent loses and Σℓ rises.
  - The other 11 logged failures are not dead ends. There every Pareto improvement changes the bundles of all 4 agents, but a level-sum-raising re-division with one loser exists among 2 agents (6 states), 3 (3), or only all 4 (2).
- **LS4⁺ (§2).** LS4 plus one move type, used only when LS4 is stuck: a *coalition re-division* C_k, in which at most k agents re-divide their bundles and the pool so that Σℓ rises (some members may lose).
  - Σℓ remains a potential, so termination (≤ Σ_i (2^{d_i} − 1) ≤ 15n moves) and soundness carry over (Theorem 1⁺).
  - With k = n, LS4⁺ can stop only at a placement or at a **global maximum of Σℓ**. So its correctness follows from **conjecture GM₄**: every junk-free EFX₀ partial allocation that maximizes Σℓ among all junk-free EFX₀ partial allocations of the same strict profile admits a placement. The converse is not claimed.
  - Equivalently, GM₄ says that *no dead end maximizes Σℓ*. With K4.TIE and K4.CORE, GM₄ would give TARGET₄. GM₄ is refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX; independent replay `k4/gm4_counterexample.py`, log `results/k4_gm4_counterexample.log`). So is its existence form, "some maximum of Σℓ admits a placement" (`k4/gm4.md` §2.4, row K4.GM.E).
- **Evidence (§3), no counterexample in these runs.**
  - LS4⁺ with k = n passes the 21.9M sampled pure n = 4 profiles on which LS4 failed 20 times, and the regression classes.
  - GM₄ itself is tested on every maximal state, not only reached ones: n = 2 exhaustive, and large samples at n = 3 and n = 4.
- **Negative (§4, `attempts/k4-lsp-*.md`):**
  - bounded coalitions (k ≤ 3) fail at n = 4, m = 7;
  - stopping at the first placement fails;
  - leximin instead of Σℓ fails: the dead end of Proposition 7 is its own unique leximin maximum.

  Among the designs tried, no bounded move suffices with the level sum; the unbounded coalition move reduces correctness to GM₄. Bounded moves with another potential are untested.
- **Not proved:** any polynomial time bound. GM₄ is refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX; independent replay `k4/gm4_counterexample.py`, log `results/k4_gm4_counterexample.log`). C_n and LS4's exchange cycles are searched by enumeration.

## 1. Escape study (`results/k4_ls4_failures_4_pure.tsv`, the 19 logged LS4 failure states)

The 19 states are those of LS4's failures on 21,900,000 random pure n = 4 profiles (`results/k4_ls4_4_sample.log`). LS4 failed on 20; the log prints at most 5 failures per core, and one core with m = 7 had 6. For each state Y (m = 7, 8 or 9), `k4/lsp_escape.py` computes by brute force (log `results/k4_lsp_escape.log`):
- every complete EFX₀ allocation X, and the set of agents it leaves worse off than Y;
- LS4's trajectory, each step replayed as a Pareto move, and on it the first dead state;
- the smallest level-sum-raising re-division: a junk-free EFX₀ partial allocation Z with Σℓ(Z) > Σℓ(Y) and the fewest agents whose bundles differ from Y. For dead ends it also computes the smallest such Z that is not a dead end;
- the coalition move that LS4⁺_n applies there.

| | count | finding |
|---|---|---|
| dead ends (no complete EFX₀ allocation is weakly better for everyone) | 8 | each has complete EFX₀ allocations with exactly **one** worse-off agent, and each of agents 0–3 can be that agent in some of them. Each became dead at LS4's **last** step, a single-agent add by agent 3 ({5} → {3, 5} and similar). The smallest escape to a non-dead state changes **2 agents** in 7 cases and 3 in one, with one loser (for example: agent 2 passes good 1 to agent 3, {1, 4} → {4} and {3, 5} → {1, 3, 5}). In the re-division LS4⁺ applies there, the loser is never agent 3, whose add created the dead end; among the other smallest escapes, agent 3 is a loser in rows 9, 14 and 19. The number of complete EFX₀ allocations whose only worse-off agent is agent 3 ranges from 1 to 22 per dead end (`results/k4_lsp_escape.log`) |
| not dead | 11 | complete EFX₀ allocations weakly better for everyone exist, and each changes the bundles of all 4 agents. The smallest Σℓ-raising re-division changes 2 agents in 6 cases, 3 in 3, and all 4 in 2 (TSV rows 2, 5; row 2 is `attempts/k4-lsp-bounded-coalitions.md`). Where it has 2 or 3 agents it has one loser |

Classification of the three escape kinds asked for by the coordinator's brief for this round (an earlier choice, a non-Pareto move, a coalition move):
- *An earlier different choice* (stop at the first placement instead of the last greedy add) repairs 6 of 19 (`results/k4_lsp_variants_19.log`). It fails on the others because no state on LS4's path admits a placement (`attempts/k4-lsp-early-stop.md`).
- *A non-Pareto re-division* (one agent loses, the others gain more in levels) repairs all 19. LS4⁺_n applies exactly one at each, with one loser (13 by 2 agents, 4 by 3, 2 by 4).
- *Pareto coalition moves* exist at the 11 non-dead states but always involve all 4 agents. LS4⁺ never uses one.

## 2. Algorithm LS4⁺ and its soundness

**Move C_k (coalition re-division).** A set A of 2 ≤ |A| ≤ k agents, and pairwise disjoint sets Z_a ⊆ R_a ∩ (U ∪ ⋃_{b∈A} Y_b) (possibly empty), such that:
- the partial allocation Y′ with Y′_a = Z_a (a ∈ A) and Y′_j = Y_j (j ∉ A), and every other good in the pool, is EFX₀;
- Σ_{a∈A} ℓ_a(Z_a) > Σ_{a∈A} ℓ_a(Y_a), with the levels ℓ_a(S) defined above.

Agents of A may lose. For k = n ≥ 2 (cores have n ≥ 2) and A = all agents, C_n reaches every junk-free EFX₀ partial allocation with a larger level sum.

**Algorithm LS4⁺_k.** Run LS4 (`k4/local_search4.md` §2): moves M1, R, the Phase-2 check, then X. When LS4 would stop with failure (no M1, R or X move, no placement), apply a C_k move if one exists and continue. Otherwise stop with failure. Implementation: `k4/ls4alg.c -DCMOVE=k`. It takes the first coalition in order of size, then index, and the first sets in subset order.

**Theorem 1⁺ (soundness and termination).** Every state of LS4⁺_k is a junk-free EFX₀ partial allocation. Every move raises Σℓ by at least 1, so there are at most Σ_i (2^{d_i} − 1) ≤ 15n moves. Every output is a complete allocation that is EFX₀ for V, hence for v. LS4⁺_n fails only at a state that admits no placement and maximizes Σℓ among all junk-free EFX₀ partial allocations.

*Proof.* For M1, R and X this is Theorem 1 of `k4/local_search4.md`: each raises Σℓ, since the movers strictly improve and the others keep their bundles. A C_k move gives a junk-free partial allocation (Z_a ⊆ R_a, disjoint), which is EFX₀ by definition, and it raises Σℓ by definition. So Σℓ strictly increases and is bounded by Σ_i (2^{d_i} − 1). Phase 2 is unchanged, so outputs are complete and EFX₀ for V, hence for v (Theorem 1 (iii)).

Suppose LS4⁺_n stops with failure at Y. Then no C_n move applies. Any junk-free EFX₀ partial allocation Z is obtained from Y by the C_n move of all n ≥ 2 agents that re-divides every good: each agent a takes Z_a ⊆ R_a, and all goods lie in U ∪ ⋃ Y_b. So no such Z has Σℓ(Z) > Σℓ(Y). ∎

**Conjecture GM₄.** For every k = 4 core and every strict profile, every junk-free EFX₀ partial allocation that maximizes Σℓ among all junk-free EFX₀ partial allocations of that strict profile admits a placement of its pool: one of LS4's Phase-2 shapes (a)–(d). Shape (a) is sound here because a maximum admits no M1 move.

GM₄ is refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX; independent replay `k4/gm4_counterexample.py`, log `results/k4_gm4_counterexample.log`).

**Equivalent form (observed by the referee of PR #29).** GM₄ ⟺ *no dead end maximizes Σℓ*.
- (⇒) A placement changes no value, so it gives a complete EFX₀ allocation weakly dominating Y.
- (⇐) Let Y be a maximum and X a complete EFX₀ allocation with v_i(X_i) ≥ v_i(Y_i) for all i. Its valued part X′ (X′_i = X_i ∩ R_i) is junk-free and EFX₀, since θ is monotone and values are unchanged, and ℓ_i(X′_i) ≥ ℓ_i for all i. Maximality forces equality, so X′ = Y (strict types: equal level means equal set). Then X places U as junk, shape (d).
- At a maximum, (a)–(c) are special cases of (d).

GM₄ implies that LS4⁺_n never fails, hence that every strict profile of every k = 4 core has an EFX₀ allocation. K4.TIE extends this to all profiles, and K4.CORE gives TARGET₄ (neither L6 nor the D2 shape is needed).

Two facts about a maximum Y follow from `k4/local_search4.md`. They rest on K4.LS.SOUND and K4.LS.ONE, which are pending review.
- Y admits no M1, R, X or coalition move of any kind.
- Lemma 2 applies (F1, F2: nobody envies the pool), and so does Proposition 4. If Y has an empty bundle, or exactly one source, the single dump works.

So a counterexample to GM₄ has at least two sources and no empty bundle.

*Three-good cores.* If every agent has three goods, GM₄ follows from the proof of Theorem C of `proofs/local_search.md` (row LS3, pending review), exactly as Proposition 3 of `k4/local_search4.md` (row K4.LS.K3). Every step of LS2 would raise Σℓ, so none applies at a maximum, and LS2's Claims 2–4 give a placement of the dump-plus-solo shape.

The variant with the fixed-priority potential (levels in agent order, lexicographic; `k4/ls4_gm.c -DPOT=2`) had no failure on the 19 logged LS4 failure profiles (`results/k4_lsp_variants_19.log`), nor at n = 2 (exhaustive) or on 102,000 random n = 3 profiles (`results/k4_gm_pot2_2.log`, `results/k4_gm_pot2_3_sample.log`); it was tested nowhere else. The leximin variant fails (`attempts/k4-lsp-leximin.md`).

## 3. Evidence (not part of any proof)

**LS4⁺_n** (`k4/ls4alg.c -DCMOVE=8`, i.e. coalitions of any size; every output checked by the raw EFX₀ definition; the same profiles and seeds as LS4's runs in `k4/local_search4.md` §5). After every move the program checks that the level sum rose. Since the computational review it also aborts and reports a run that exceeds Theorem 1⁺'s bound of Σ_i (2^{d_i} − 1) moves. The logs of this table were produced before that cap was added, but any non-raising move would already have been reported:

| class | profiles | how | failures | coalition moves used | log |
|---|---|---|---|---|---|
| n = 4, pure | 21,900,000 | 100,000 random per core | **0** (LS4: 20) | 20: 14 by 2 agents, 4 by 3, 2 by 4, one per LS4 failure | `results/k4_lsp_4_pure_sample.log` |
| n = 4, three 4-good agents | 33,900,000 | 100,000 random per core | 0 | 0 (counters in the log) | `results/k4_lsp_4_n4_3_sample.log` |
| n = 4, one 4-good agent | 7,247,232 | exhaustive | 0 | 0 (counters in the log) | `results/k4_lsp_4_n4_1.log` |
| n = 3 | 299,837,376 (all 24.7·10⁹ tied profiles too) | exhaustive | 0 | 0 | `results/k4_lsp_3_ties.log` |
| n = 2 | 189,216 (all tied profiles too) | exhaustive | 0 | 0 | `results/k4_lsp_2_ties.log` |
| n = 5, two 4-good agents | 54,680,000 | 10,000 random per core | 0 | 0 | `results/k4_lsp_5_n4_2_sample.log` |

**GM₄ directly** (`k4/ls4_gm.c -DPOT=0`). For each profile, all junk-free partial allocations are enumerated and the maximal ones found. Each maximum with a nonempty pool is placed by LS4's Phase 2 (a)–(d), and the placement is then checked independently: complete, disjoint, extending Y, EFX₀ under V and by the raw definition. This covers every maximum, not only those LS4⁺ reaches.

Only the maxima with a nonempty pool test GM₄: a maximum whose pool is empty is already complete.

| class | profiles | how | maximal states | with a nonempty pool (these test GM₄) | placed by (a) / (b) / (c) / (d) | failures | log |
|---|---|---|---|---|---|---|---|
| n = 2 | 189,216 | exhaustive | 236,176 | 2,286 (1.0%) | 0 / 2,286 / 0 / 0 | 0 | `results/k4_gm_2.log` |
| n = 3 | 1,020,000 | 20,000 random per core | 1,323,209 | 65,912 (5.0%) | 0 / 65,912 / 0 / 0 | 0 | `results/k4_gm_3_sample.log` |
| n = 4, one to three 4-good agents | 1,566,000 | 2,000 random per core | 2,174,535 | 175,167 (8.1%) | 6,716 / 168,451 / 0 / 0 | 0 | `results/k4_gm_4_mixed_sample.log` |
| n = 4, pure | 4,380,000 | 20,000 random per core | 6,226,242 | 258,916 (4.2%) | 0 / 258,916 / 0 / 0 | 0 | `results/k4_gm_4_pure_sample.log` |

So 502,281 maxima actually test GM₄. In these runs every one of them was placed by the empty-bundle dump (a) or a single dump (b); the split (c) and the exact search (d) were never needed at a maximum. PR #30 (`k4/gm4.md` §4) found rarer profiles, 4 in 43.8M pure n = 4 profiles and 3 in 39.15M mixed ones, where a maximum has no placement at all (counterexamples to GM₄, which is refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX; independent replay `k4/gm4_counterexample.py`, log `results/k4_gm4_counterexample.log`)), and maxima where only a split works.

*Sensitivity* (`results/k4_gm_sensitivity.log`). With Phase 2 restricted to (a) (`-DP2A_ONLY`), the n = 2 run reports failures, records them in the log, and exits with status 1. The independent placement check was added after the computational review of PR #29. All the logs in this table were re-run with it: 0 bad placements.

The 19 logged LS4 failure profiles also pass, under the level sum and under the fixed-priority order; leximin fails on one (§4; `results/k4_lsp_variants_19.log`). Leximin (`-DPOT=1`) and fixed priority (`-DPOT=2`) were also run at n = 2 (exhaustive) and on 102,000 random n = 3 profiles (`results/k4_gm_pot{1,2}_2.log`, `results/k4_gm_pot{1,2}_3_sample.log`).

## 4. Failed designs (`attempts/k4-lsp-*.md`; replayed by `python3 k4/lsp_attempts.py`)

| design | smallest failing configuration found | file |
|---|---|---|
| stop at the first placement (`-DEARLY`) | n = 4, m = 7: no state on LS4's path admits a placement; ends in a dead end. Repairs 6 of the 19 logged failures (`results/k4_lsp_variants_19.log`) | `attempts/k4-lsp-early-stop.md` |
| coalition re-divisions of at most k = 2 or 3 agents | n = 4, m = 7: only a re-division of all 4 agents raises Σℓ. On the 19 logged failures k = 2 repairs 13 and k = 3 repairs 17 (`results/k4_lsp_variants_19.log`); on 4,380,000 random pure n = 4 profiles each fails once, LS4 6 times (`results/k4_lsp_4_pure_20k_c2.log`, `results/k4_lsp_4_pure_20k_c3.log`, `results/k4_ls4_4_pure_20k.log`) | `attempts/k4-lsp-bounded-coalitions.md` |
| leximin of the levels as the potential | n = 4, m = 7: the dead end of Proposition 7 is its unique leximin maximum (searched only on the 19 logged profiles, at n = 2 and on 102,000 random n = 3 profiles) | `attempts/k4-lsp-leximin.md` |

## 5. Relation to LB₄ (PR #24)

LB₄ (`k4/lb4.md` on `proof/k4-lb4`) is a *construction*: serial-dictatorship bases, a pre-allocation whose needs must stay alone, and a completion with an owner constraint. It has no potential. Its only moves (upgrades, and one rotation along a need chain) sit inside a finite search over insertion sequences. LS4⁺ is not LB₄ in local-search form:
- its states are arbitrary junk-free EFX₀ partial allocations;
- its only global object is the level sum;
- its open statement GM₄ is about maxima of Σℓ, not about a construction order.

They share one ingredient: an agent may give up what it holds.
- In LB⁺'s rotation (`proofs/lb_last_step.md` §5), k gives up its top a_k for {b_k, c_k}, worth at least as much by balance, and the chain agents move up. So nobody's value drops.
- LB₄'s rotation and LS4⁺'s re-divisions *can* lower an agent's value, which LS4's moves cannot.

What LS4⁺ adds is that soundness and termination hold for *any* Σℓ-raising re-division, with no analogue of Theorem B's validity analysis. What it lacks is the analogue of LB⁺'s Theorems A–C: a proof that a Σℓ-maximum admits a placement.

## 6. Complexity

- The number of moves is at most 15n, as for LS4.
- C_k takes polynomial time for fixed k: at most n^k coalitions and 16^k set choices, each with an EFX₀ check.
- Bounded k fails already at n = 4 with k = 3 (§4). With k = n, the search is exponential: C_n is a search over all junk-free partial allocations.

So LS4⁺ was an existence argument conditional on GM₄, which is now refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX), with a linear number of moves but no polynomial time bound. A polynomial algorithm would need a structural reason why small coalitions suffice most of the time and a different treatment of the rare states that need large ones.

## 7. Status

- Theorem 1⁺: written proof, pending review (K4.LSP.SOUND, CONJECTURE until reviewed).
- Conjecture GM₄ (K4.LSP.GM): refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX; independent replay `k4/gm4_counterexample.py`, log `results/k4_gm4_counterexample.log`). LS4⁺_n with its default rule: EVIDENCE (§3; K4.LSP.RUN), no failure known; with arbitrary choices it can fail (`k4/gm4.md` §3).
- The escape study (§1) and the failed designs (§4): EVIDENCE with independent replay (K4.LSP.VAR).
- Open:
  - ~~a proof of GM₄~~: GM₄ is refuted in #30 (`k4/gm4.md` §2, row K4.GM.CEX; independent replay `k4/gm4_counterexample.py`, log `results/k4_gm4_counterexample.log`), and so is its existence form. A proof of LS4⁺'s correctness needs another argument, for example that the default rule stops at a placeable state before any bad maximum (`k4/gm4.md` §3, §7);
  - whether a bounded move set with another potential suffices (untested);
  - polynomial time.
