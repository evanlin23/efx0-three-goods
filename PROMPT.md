# Research task: EFX₀ when every agent has at most three relevant goods (v2)

If you received an earlier version of this prompt, this one supersedes it: conjecture "A" in v1 is false.

You are working on an open problem in fair division, as a semester research project. Success is either a proof, or a sharply delimited partial result stating exactly what is proved, what is computationally certified, what is only conjectured, and where the remaining gap is. A careful partial result is a success; an overclaimed one is a failure. Read everything before starting.

## 1. Problem

Agents N = [n], indivisible goods M = [m], additive valuations v_i(S) = sum of v_i(g) over g in S, with v_i(g) ≥ 0. Relevant set R_i = {g : v_i(g) > 0}. Allocations are complete partitions X = (X_1, ..., X_n) of M.

EFX₀ (strong EFX): for all i ≠ j and every g in X_j, v_i(X_i) ≥ v_i(X_j minus g). The removed good may be worthless to i. This is the notion used in the graph/multigraph EFX papers.

TARGET: if |R_i| ≤ 3 for every agent, a complete EFX₀ allocation exists.

Reformulation: toward a bundle B containing a good outside R_i, agent i needs full envy-freeness, v_i(X_i) ≥ v_i(B); toward B ⊆ R_i, ordinary EFX, v_i(X_i) ≥ v_i(B) − min over g in B of v_i(g). Singleton bundles can never be strongly envied.

## 2. Literature (read before relying on anything; mark what you could not verify)

- Viswanathan–Mehta (AAMAS 2024): ordinary EFX exists when every agent positively values at most four goods. Ordinary EFX only (checked: `proofs/citations.md`; the removed good must be worth > 0 to the envier, and goods nobody values go to an arbitrary agent). It does not imply TARGET.
- Christodoulou–Fiat–Koutsoupias–Sgouritsa (EC 2023): EFX₀ on graphs, general monotone valuations.
- Afshinmehr–Ashuri–Mahmoudkhan–Mehlhorn–Shahrezaei, arXiv 2606.18665: EFX on multigraphs for cancelable valuations, including additive. Not needed for the results below (multigraph cores are included in our exhaustive checks), but a likely source of proof ideas. Read (`proofs/citations.md`): the notion is EFX₀, so it covers every core in which each good is relevant to at most two agents, for every n (ledger T3).
- Mahara (cited as [Mah23] by Alkassar–Fouz–Mehlhorn): complete EFX exists whenever m ≤ n + 3. Verified: arXiv 2107.09901, Theorem 3, for general monotone valuations and in EFX₀ form (`proofs/citations.md`). R1 no longer depends on it; ledger T3 uses it.
- Chaudhury–Garg–Mehlhorn (JACM 2024): EFX for three additive agents.
- Alkassar–Fouz–Mehlhorn, arXiv 2608.08590: EFX₀ for four additive agents with m ≤ 9, via hand-proven reductions plus machine-checked certificates. A model for the methodology.
- Akrami et al., arXiv 2604.18216; Mackenzie–Suzuki, arXiv 2605.06451: EFX fails for general monotone and for submodular valuations. Additive EFX is open.

## 3. Established so far (re-derive each proof before building on it)

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

**R1 n ≤ 6 (certified).** Every connected core with n = 5 (m = 9: 15 hypergraphs up to isomorphism) and n = 6 (m = 10: 211; m = 11: 25), multigraph cores included, under every ranking profile, has an EFX₀ allocation with at most one bundle of more than two goods. Method: per hypergraph, CEGAR over ranking profiles. An outer SAT proposes a profile not yet covered, an inner SAT finds an allocation for it, and the clause excluding covered profiles is computed from the raw EFX₀ definition. Certificate: the allocations found; their coverage of all 6^n profiles is re-checked from per-agent safety masks computed with the raw definition. With L1–L8: **every instance with |R_i| ≤ 3 and n ≤ 6 has an EFX₀ allocation**, conditional only on Mahara's m ≤ n + 3 theorem.

**R2 n = 7, β = 2 (certified the same way).** All 37 connected cores with m = 13 satisfy conjecture D below. (m = 12 and m = 11 not yet done.)

**REFUTED** (each was believable; keep them in mind):
- "Every core has an EFX₀ allocation with all bundles ≤ 2": false at n = 5.
- Conjecture A of v1 ("m ≤ 2n − 2 ⟹ all bundles ≤ 2 suffice"): false.
  - At n = 6, m = 10, 57 of the 211 connected cores have a ranking profile with no such allocation; all 57 were confirmed by a second, independently written encoding.
  - In each of the 57 failing hypergraphs only 1 to 747 of the 46,656 profiles fail (median 22; 7,077 of all 211 × 46,656 hypergraph–profile pairs, 0.07%; `results/fail_density_6_10.log`), which is why ~500 random samples saw nothing.
  - Example (agent: a > b > c): (1,0,6) (1,0,7) (2,0,8) (3,0,9) (2,4,5) (3,4,5). An EFX₀ allocation: {0,6} {1,7,8,9} {2} {3} {4} {5}.
  - Mechanism: there are three top-collisions (goods 1, 2, 3). Agents 0–3 all have good 0 in their bottom pair, and agents 4, 5 share one bottom pair, so at most two collisions can be fixed by case P. The third needs a chain, and chains need more alone goods than the slack 2n − m = 2 allows (L7). The large bundle collects private goods.
- The same statement for arbitrary (non-core) instances: false. Counterexample: four identical agents valuing {x, y, z}, plus three worthless goods.
- "A large bundle of 3 goods always suffices": 3 of the 25 cores at n = 6, m = 11 need at least 4 [single implementation; confirm independently].

**MAIN CONJECTURE D.** Every core has an EFX₀ allocation in which at most one bundle has more than two goods. Certified for n ≤ 6 and for n = 7 at β = 2. D implies TARGET.

## 4. Plan

**Step 0 (keep short).** Re-derive L1–L11. Independently re-implement the core enumeration and cross-check the counts (15; 211 and 25; 37). It is the one trust point of R1 besides the checkers. Re-verify the example above by hand. Verify the Mahara citation. Record everything in the ledger; don't re-verify afterwards.

**Step 1 (frontier).** Finish n = 7 (m = 12, 11), then n = 8 at β = 2 (m = 15). Test each hypergraph exhaustively over all ranking profiles; random profiles miss failures.

**Step 2 (structure of the large bundle).** In the certified solutions, record who holds it, what goes in it (private goods? whose?), and which case each agent uses. Relate the need for it to top-collisions, P-capacity (disjoint bottom pairs) and the slack (L7). Turn this into an explicit construction and test it exhaustively for n ≤ 7.

**Step 3 (proof of D).** Suggested order:
1. β = 2 via L11: three shapes, induction on path length. Show that a long path of degree-2 agents and goods can be shortened without changing existence.
2. General β by a counting or matching argument over collisions, P-capacity and alone goods.
3. Induction via L10 and peeling.

When a step fails, extract the smallest failing configuration, confirm it by computer, and return to Step 2.

**Step 4 (fallbacks, each a legitimate result).** Certified n ≤ 7; D for β = 2; D for β ≤ 3; cores in which no good is the top of three or more agents.

## 5. Working rules

1. **Keep LEDGER.md.** Each claim has one status:
   - PROVED: complete written proof, re-read.
   - CERTIFIED: exhaustive search over a finite set that a PROVED lemma shows is complete, with independently checked certificates.
   - EVIDENCE: random or partial search.
   - CONJECTURE.
   - REFUTED: counterexample saved with a checker.

   Never upgrade a status without the artifact. The final report must match the ledger.
2. **Refute before proving.** Try to break every new lemma on small instances first, exhaustively where feasible. Write proofs only for survivors.
3. **Know what computation proves.** A counterexample refutes. Exhaustive search over a provably complete finite set proves that case. Random testing is evidence only and never enters a theorem statement. In this problem, failures occurred in as few as 1 of 23,000 ranking profiles, and random sampling missed them entirely.
4. **Certificates.** Existence claims come with witness allocations checked by a minimal checker implementing the raw EFX₀ definition, not the L5 model. UNSAT claims need a proof certificate (e.g. DRAT) or two agreeing independent implementations.
5. **Stay on the problem.** If you change the target, say so explicitly and why. Before calling anything new, check it doesn't follow from Viswanathan–Mehta, the multigraph theorems, or L1 plus a known additive result.
6. **Citations.** Cite only what you have read; mark the rest [unverified]. Never invent references, authors, or statements.
7. **No polishing before the math is settled.** No LaTeX beautification, no re-verifying ledger items. Formalization in Lean is its own workstream (`formal/...`, in `lean/`): core Lean only, no `sorry`, standard axioms only (`lean/check.sh`, run by CI). It formalizes PROVED items, never blocks the math, and is recorded in the ledger's Lean column.
8. **Turn discipline.** Start every turn with three lines: current target, last result, next step. On "continue", resume from the ledger without restating. When stuck, report the precise failure point instead of retrying variations.

## 6. Deliverables

- LEDGER.md.
- Complete proofs.
- Code and data (certificates, counterexamples, profiles needing a large bundle) with reproduction instructions.
- A final report listing what is proved, certified, conjectured, and refuted, and the exact remaining gap.

If code files are attached (frontier.py is the main tool), run them, but do Step 0's independent re-implementation rather than trusting them.

## 7. Working in the shared repository

The repository is the record; your chat is not. Assume other agents and humans are working in parallel.

- Layout: LEDGER.md (every claim and its status), PROMPT.md (this brief), src/ (tools; frontier.py is the main one), tools/ (checkers CI runs), results/ (logs, summaries, certificate files), proofs/ (written proofs), lean/ (Lean formalization), attempts/ (failed approaches, each ending with the smallest configuration where it breaks).
- At the start of every session: clone or pull, then read LEDGER.md and the open pull requests. Work on your own branch named after your workstream (compute/..., proof/...); if your environment assigns you a branch, use it and name the workstream in commit messages and the pull request title. Never commit to main. AGENTS.md has the checks to run and the pull-request template.
- Commit small and often, with messages "[workstream] what changed and why". Open a pull request when a unit of work is done; a human reviews and merges.
- A pull request that changes a ledger status must contain the artifact the new status requires (rule 1), and CI must pass. CI lints the ledger, re-checks the committed certificates without SAT, re-runs the n <= 6 search from scratch and re-checks its certificates, and re-confirms the refutation of conjecture A.
- New certified results: commit the certificate file (gzip JSON of hypergraphs and allocations, as written by frontier.py or run7.py) under results/, and make sure tools/check_certs.py accepts it.
- Don't edit another workstream's files. To dispute a claim, open an issue with your counterexample.
- If you cannot push, produce a patch (git format-patch) plus any new data files, and say so; the human will apply them.
- Never commit credentials. If you were given a token, use it only for this repository.
