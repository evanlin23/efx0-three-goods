# Referee report: Theorems CH-A, CH-B (branch `claude/kgen-charity`, `kgen/charity.md` §0–§3)

Referee: `proof/k4-referee`, 2026-11-26. Read: `kgen/charity.md` at `78deef1` (all of it); §2–§3 unchanged at `8862555` except for the new Proposition DU (§5 below), and the two cited sources,
fetched and extracted with `pdftotext` by me:
- CKMS: B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness",
  arXiv 1907.04596v3. Read §2 in full (Algorithms 1–2, Definition 1, Lemma 2, Definition 3, Lemmas 4–7, Theorem 8).
- V. Sivashankar, "A Linear Bound on the Rainbow Cycle Number and Approximate EFX", arXiv 2607.27455v1. Read §1
  (definition of R(d) and of rainbow cycles) and §3 (Theorem 3 with its proof).

Checks: `k4/referee/charity_ref.py`, runs `k4/referee/charity_ref_runs.sh`, log `results/k4_referee/charity_ref.log`.
No code is shared with `kgen/charity/`.

## Verdicts

| item | verdict |
|---|---|
| Lemmas CH0–CH6, Proposition CH-R (used by CH-A, CH-B) | CORRECT |
| Theorem CH-B (\|P\| < e·d when every good has ≤ d valuers) | **CORRECT** |
| Theorem CH-A (\|P\|(\|P\| − 1) ≤ e(k − 2)n; \|P\| = 0 for k ≤ 2) | **CORRECT** |
| (not refereed) CH-M, CH-C, CH-D, CH-E, P1 at k = 3 | – (CH-D's and S′(2, 3)'s states are re-checked below as test data only) |

## 1. The citations

- **CKMS.** The notion is the all-goods EFX (Lemma 5's proof: "for every pair of agents j and k and any good
  g ∈ X′_k"), i.e. EFX₀. Valuations are normalized and monotone, and nothing in §2 assumes positive values. The
  session's description is accurate.
- **U2 has no |P| ≥ n precondition.** Algorithm 2's U2 needs only a cycle: distinct goods, distinct sources and
  distinct agents t_i, with t_i ∈ C(s_i) and t_{i+1} the most envious agent of X_{s_i} ∪ g_i. Algorithm 1 applies
  any applicable rule. So CKMS's output is a stopping state in the sense of `charity.md` §2, and "the output of CKMS's
  algorithm" in CH-B is right.
- **Lemma 7 assumes disjoint paths.** Its proof assumes that the envy paths u^i_0 → ⋯ → u^i_{m_i} are vertex-disjoint
  (line 15 assigns each X′_u once). CKMS's precondition only asks the t_i to be distinct. Lemma CH5 supplies the
  disjointness for a *shortest* rainbow cycle, so using CH5 is the right way to cite Lemma 7.
- **Theorem 8** states "|P| is less than the number of sources". It follows from Lemma 6's construction, which needs
  one fresh pool good per new source.
- **Sivashankar's Theorem 3** is as cited:
  - hypotheses: nonempty classes; every vertex has an in-neighbour in every other class; no directed cycle with at
    most one vertex per class;
  - conclusion: (k − 1)! Σ n_i ≤ Π n_i, and k! ≤ d^{k−1}, so R(d) < ed, if all n_i ≤ d.

  I re-derived the injection proof. The path v₁ → ⋯ → v_k meets every class once, and two permutations with the same
  vertex set would give a closed walk inside it, hence a rainbow cycle.

## 2. The proofs

- **CH0–CH3.** Re-derived.
  - CH1(1): t strongly envies X_s ∪ g only by removing some h ∈ X_s, since s is a source. Weak charity then forces
    v_t(g) > v_t(h) and v_t(X_s ∖ h) > 0.
  - CH1(2): minimality and weak charity force g ∈ Z ⊆ R_t and Z ∖ g ≠ ∅.
  - CH3's "t ∉ C(s)" is U2 with ℓ = 1, which CKMS's precondition allows.
- **CH4.** The injection s ↦ c(s, g) from S into V(g) charges each t at most μ_t times. R_t contains g, a good of
  X_t, and one good from each of μ_t further bundles, all disjoint. Correct.
- **CH5.** If two paths of a shortest rainbow cycle meet at u, then t_b ∈ C(s_a), so the selected option for
  (s_{b−1}, g_{b−1}) is an edge s_{b−1} → s_a. That closes a rainbow cycle of length (b − a) mod ℓ ∈ [1, ℓ − 1].
  Correct. The argument works for the digraph of the *selected* champions as well, which CH-R needs.
- **CH6.** A rotation, U1 or U2 strictly improves some agent and lowers nobody. U0 keeps the values and allocates one
  more good. Correct.
- **CH-R.**
  - (h, s₂) has the in-neighbour (g, σ(c(s₂, g))) ∈ V_g.
  - A rainbow cycle of Γ gives a closed walk in D with distinct colours (in reverse). Its shortest closed sub-walk is
    a rainbow cycle of D, and CH5 makes it executable: a contradiction.
  - The classes are nonempty, because U0 fails at every (s, g) and a source exists.
  - No pool good is valued by nobody at a stopping state, since U0 would add it (CH1). So n_g ≥ 1 and V(g) ≠ ∅.
- **CH-B.** Π n_g / Σ n_g is increasing in each n_g (p ≥ 2), so n_g ≤ d gives (p − 1)! ≤ d^{p−1}/p, i.e.
  p! ≤ d^{p−1}, and p < ed. Correct.
- **CH-A.** A champion values a good of its own bundle and a good of some source's bundle (CH3), so it lies in at
  most k − 2 sets Q_g. Hence Σ n_g ≤ (k − 2)n.
  - AM–GM and (p − 1)! ≥ ((p − 1)/e)^{p−1} give p(p − 1) ≤ e Σ n_g. Correct.
  - The status table's |P| ≤ 1 + √(e(k − 2)n) is weaker than §3's 1/2 + √(e(k − 2)n + 1/4), and both are valid.
  - k ≤ 2 is CH4′.
- **Existence.** A stopping state exists (CKMS's Algorithm 1 terminates, or take a Pareto maximum, CH6), so both
  theorems give existence statements.

## 3. Computation (evidence)

- **The packing inequality, independently.** For every size vector with (p − 1)! Σ n_i > Π n_i (p ≤ 3 with classes
  ≤ 5; p = 4 with classes ≤ 3; p = 5 with classes ≤ 2; 62 vectors), a SAT search over all p-partite digraphs with the
  in-neighbour condition, every rainbow cycle forbidden, finds none.
- **Stopping states that strand goods.** S(σ, k) of CH-D (σ ≤ 5 at k = 3, σ ≤ 4 at k = 4) and S′(σ, k) of CH-E
  (same ranges) were rebuilt from the text. By brute force, the S′(2, 3) state is one of the 9 Pareto maxima of its
  instance. At each state, every claim was checked:
  - strong charity; CH2; CH3 for every champion option;
  - no rainbow cycle in D over every option; CH4 for every pool good;
  - CH-R's in-neighbour condition and absence of rainbow cycles in Γ for up to 64 champion selections;
  - the packing inequality, and the bounds of CH-A and CH-B.

  0 failures (pools of 1–4 goods, n ≤ 40).
- **Pareto maxima of random instances** (550 instances, n ≤ 4, m ≤ 7, k ≤ 4; 5,055 Pareto maxima by brute force): all
  complete, so the lemmas hold vacuously. This agrees with the session's report that random instances never strand.

## 4. For the coordinator

- CH-A and CH-B: CORRECT. They can be recorded as PROVED (exact EFX₀, strong charity), with the citations as read
  here.
- One wording point, optional: wherever CKMS's Lemma 7 is cited, cite it together with CH5. Lemma 7's proof needs
  disjoint envy paths, which CKMS's precondition does not state and CH5 provides.
- CH-M (monotone), CH-C, CH-D, CH-E and the P1 refutation at k = 3 were not refereed. The coordinator has verified
  the last one independently (attack log, 21:35).

## 5. Addendum: Proposition DU (new at `8862555`, checked in passing)

DU: if the incidence graph has ≥ 2 components containing agents, a complete EFX₀ allocation exists. Re-derived:
- take a CKMS stopping state in each component and give its pool P_r to a source s_{r+1} of the next component;
- an agent a of component r then values, in any bundle of another component, only goods of P_r. These are worth
  ≤ v_a(X_a) by strong charity;
- inside its own component, a sees the extra goods as worthless, and the source that received them is unenvied.

**CORRECT.**
