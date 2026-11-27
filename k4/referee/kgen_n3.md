# Referee report: Theorem 2 (two-agent OC₁, t ≥ 0) with Fact L, Lemma M and the Tops Lemma (`kgen/n3.md` §9, branch `claude/kgen-n3`, PR #97)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `kgen/n3.md` at `418f876`: the status block, §1 (definitions), §2 (Lemmas R, P, S) and §9 (Theorem 2, its three
  facts, the proof and remarks).
- Check: `k4/referee/theorem2_ref.py`, log `results/k4_referee/theorem2_ref.log`. It is written from the text; no code
  is shared with `kgen/`, and `kgen/theorem2.py` was not run.

## Verdict: CORRECT

Theorem 2: for two agents, from either serial-dictatorship order, at every k and for any nonnegative additive values
(ties and zeros included), the picks have an EFX₀ completion of OC₁(t ≥ 0) form. It is constructed in O(m log m), and
it no longer uses Lemma T.

**Citation.** Bare existence of an EFX₀ allocation for two agents is Plaut–Roughgarden, arXiv 1707.04769v3,
Theorem 4.3 (see `k4/referee/lit_n2.md`). The new content is the OC₁ shape: the SD picks kept with one absorber (A1),
or one chain a → b (B). Claim T (two agents with distinct tops keep both) is part of it. I found no published source
for Claim T [not searched beyond Plaut–Roughgarden].

## 1. The three facts

- **Fact L (LPT is EFX₀ for the cutter in both directions, any values).** Correct.
  - The last good h placed into a bundle Z is its cheapest for c, since the order is decreasing. When h was placed,
    Z ∖ h was worth no more than the other bundle, which only grew afterwards.
  - So v_c(Z) − min_c(Z) ≤ v_c(other), which is exactly EFX₀ toward Z. Zero-valued goods come last and satisfy the
    same inequality.
  - The remark "if the first good has positive value, the first two goods go to different bundles" is right, with the
    tie rule "first bundle on a tie".
- **Lemma M.** Correct. Moving c's zero-valued goods W from X_c to X_d:
  - leaves c's value unchanged and c unenvious, since v_c(X_d ∪ W) = v_c(X_d) ≤ v_c(X_c);
  - only shrinks d's threats toward X_c ∖ W.
- **Tops Lemma (any n).** Correct; the coordinator's restatement is right. Let X_i = S_i ∪ {t_i}, with S EFX₀ and
  each t_i a top of i.
  - Removing t_j leaves S_j, and v_i(S_j) ≤ (v_i(S_j) − min_i S_j) + v_i(t_i) ≤ v_i(S_i) + v_i(t_i).
  - Removing g ∈ S_j leaves v_i(S_j ∖ g) + v_i(t_j) ≤ v_i(S_i) + v_i(t_i).
  - The weakened hypothesis in the remark (t_i at least every other t_j and some good of each S_j) is what the proof
    uses.

## 2. The proof of Theorem 2

- **Case 0 (degenerate).** Correct.
  - If a or b values nothing, the other takes M.
  - If b values only y_a and v_a(y_a) ≥ v_a(M ∖ y_a): a keeps {y_a} (EFX₀ by the inequality), and b absorbs.
  - Otherwise: (M ∖ y_a, {y_a}) is the chain a → b with t = 1.
    - a passes a nonempty base, b's base is empty, and both gain strictly.
    - Only a holds goods outside its base (its zero goods).
    - EFX₀ holds, since b values a's bundle at 0.
  - The remark about the earlier, buggy version of this case is consistent: handing y_a to a b that values nothing is
    not an improving chain.
- **Case 1, v_b(y_a) > v_b(y_b).** Correct.
  - y_a is b's unique top and y_b the next good in LPT_b's order (the same tie rule as SD), so P ∋ y_a and Q ∋ y_b.
  - a's choice, Fact L for b, and then Lemma M give EFX₀.
  - If a takes P, then X_a ∖ y_a ⊆ J ∩ R_a: shape A1, a t = 0 move at a, with only b outside its base.
  - If a takes Q, then v_a(Q) > v_a(P) ≥ v_a(y_a) and X_a ⊆ (J ∪ {y_b}) ∩ R_a: the chain a → b. b's gain comes from
    v_b(y_a) > v_b(y_b), and a holds exactly its new base.
- **Case 2, v_b(y_a) ≤ v_b(y_b).** Correct.
  - y_a and y_b are tops of a and b over M (ties included).
  - Cut-and-choose on J plus Lemma M gives an EFX₀ allocation of J.
  - The Tops Lemma hands the tops back, giving shape A1.
- **Complexity.** O(m log m): one sort and linear passes.

The definitions match `k4/sdc.md` §29 with t ≥ 0, i.e. a t = 0 move adds H₀ ⊆ J ∩ R_x to the pick. The shapes are OC₁
witnesses in that sense; Lemma R's reduction to "largest H" was re-derived and is used in my check.

## 3. Computation (evidence)

- **The three facts.** 20,000 random LPT cuts (zeros and ties), with Fact L in both directions; 5,522 Lemma M moves;
  54,021 EFX₀ allocations, n = 2–4, with the tops handed back (Tops Lemma). 0 failures.
- **The construction.** Exhaustive over every valuation with entries in {0, 1} (m ≤ 7), {0, 1, 2} (m ≤ 5),
  {0, …, 3} (m ≤ 4) and {0, 2, 3, 5} (m ≤ 4), plus 20,000 random instances with m ≤ 14 (generic, ties, zeros,
  sparse), both orders: **496,162 starts, 0 failures**. Each output is EFX₀ by the raw definition and an OC₁(t ≥ 0)
  witness by my own test: the picks with one absorber, or the bases after a valid t = 0 or t = 1 chain with one
  absorber.
- **Brute-force OC₁(t ≥ 0)**, independent of the construction: every allocation, every chain with t ≤ 1. 3,000 random
  instances with m ≤ 8, both orders: 6,000 starts, 0 failures.
- **Mutation.** The construction without Lemma M (a keeps its zero-valued goods) stays EFX₀ but breaks the
  one-absorber shape on 973 of 40,000 random starts with m = 6–14. The real construction passes all 40,000. So
  Lemma M is needed exactly where the proof uses it.
- **My own bug, for the record.** The first version of my witness test passed the bundles to the EFX₀ check in the
  order (a, b) instead of by agent index, so every start with order (b, a) looked wrong. Fixed; the numbers above are
  after the fix.

## 4. For the coordinator

- Theorem 2, Fact L, Lemma M and the Tops Lemma: CORRECT. They can be recorded as PROVED.
- Cite Plaut–Roughgarden Theorem 4.3 for bare two-agent EFX₀ existence; the OC₁ shape and Claim T are the new part.
- Not refereed here: Lemma T (open, and no longer used), §8, and §10 (the n = 3 lift).
