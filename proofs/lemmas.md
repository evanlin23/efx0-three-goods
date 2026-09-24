# Lemmas L1–L11 (proof sketches)

Copied from PROMPT.md §3. Step 0 expands each sketch into a complete proof here; the ledger rows keep pointing at this file.

**L1 Perturbation.** For fixed (n, m): EFX₀ holds for all additive instances iff EFX holds for all strictly positive additive instances (add ε·w_g to every value; some EFX allocation repeats along ε → 0; the inequalities are closed). So additive EFX results transfer to EFX₀ (e.g. n ≤ 3, m ≤ n + 3), and a counterexample to TARGET would refute the additive EFX conjecture itself. Don't plan around finding one.

**L2 Peeling.** Remove agent i with bundle P. If the rest has an EFX₀ allocation, adding (i, P) keeps it EFX₀, when (with R_i restricted to remaining goods):
- R1: P = {i's favorite remaining good} and v_i(P) ≥ v_i(R_i minus P) [at most 2 remaining relevant goods, or a ≥ b + c, "top-heavy"]; P = ∅ if nothing relevant remains.
- R2: P = the goods relevant to i and to no other remaining agent, |P| ≥ 2, v_i(P) ≥ v_i(R_i minus P).

Proof: bundles built from the remaining goods meet R_i only inside R_i minus P, so i envies none; P is a singleton or worthless to everyone else, so nobody strongly envies it; earlier-peeled agents only see bundles from their own residual. When one agent is left, it takes everything.
Corollary: if |R_i| ≤ 2 for all i, serial dictatorship (each agent takes its favorite remaining good; the last agent takes all leftovers) is EFX₀. At three goods it breaks exactly when a balanced agent (a < b + c) takes a while b and c land together in a bundle of ≥ 3 goods.

**L3 Junk.** Goods relevant to no remaining agent: allocate the rest, eliminate envy cycles (rotation preserves EFX₀), give all junk to a source of the envy graph.

**CORE.** Apply L2–L3 until nothing applies. A remainder with ≥ 2 agents is a core: every agent has exactly 3 relevant goods, is balanced (a < b + c), and has at most one private good (valued by no other core agent); every good is relevant to some core agent. If every core has an EFX₀ allocation, TARGET holds.

**L4 Counting.** In a core, 3n = 2m − π + Σ over shared goods of (deg g − 2), with π ≤ n private goods. So m ≤ 2n. Cores with m ≤ n + 3 are covered by Mahara via L1.

**L5 The core is ordinal.** For a balanced agent with a > b > c: 0 < c < b < a < b+c < a+c < a+b < a+b+c, so EFX₀ in a core depends only on each agent's ranking of its three goods. Call a good "alone" if it is the only good in its bundle. Agent i is safe iff one of:
- T: i holds a together with b or c; or i holds a, and b, c are not together in any bundle of ≥ 3 goods
- P: i holds b and c
- B: i holds b, and a is alone
- C: i holds c, and a and b are alone
- E: a, b, c are all alone

(Checked against the raw definition on 896,400 allocations, zero mismatches.) Ties are WLOG absent by a closedness argument; core agents stay strictly balanced since a = b + c counts as top-heavy.

**L6 Components.** Agents in different connected components of the agent–good incidence graph value nothing in each other's bundles, so components can be solved separately. Minimal open cores are connected.

**L7 Slack.** A connected core's incidence graph (3n edges, n + m vertices) has cyclomatic number β = 2n − m + 1. In an allocation whose bundles all have ≤ 2 goods, with e empty bundles, exactly 2n − m − 2e goods sit alone; if one bundle has D ≥ 3 goods and the rest ≤ 2, exactly 2n − 2 − m + D − 2e do. Cases B, C and E consume alone goods, so the slack 2n − m caps how many chains a size-≤2 allocation supports, and a large bundle buys D − 2 extra alone goods.

**L8 Two own goods.** An agent holding at least two of its own three goods is safe whatever else happens. Hence β = 1 cores (m = 2n: one cycle of agents and shared goods, with pendant private goods) are solved by giving each agent its private good and the next shared good around the cycle.

**L9 Size-2 criterion.** If every bundle has ≤ 2 goods, EFX₀ holds iff each agent values every good lying in someone else's 2-good bundle at most as much as its own bundle (any additive valuations).

**L10 Insertion.** If the instance minus agent i and its top good a_i has an EFX₀ allocation with all bundles ≤ 2, adding {a_i} as i's bundle keeps it EFX₀. Caveat: iterating this loses one unit of slack per step, and residual instances can contain worthless goods, where size-≤2 allocations can fail (see refutations).

**L11 Shapes.** Deleting private goods from a connected core leaves a graph with minimum degree ≥ 2 and cyclomatic number β; so a core is a subdivision of one of finitely many multigraphs with minimum degree ≥ 3 and cyclomatic number β. For β = 2 (m = 2n − 1): a subdivided theta, dumbbell, or figure-eight.

