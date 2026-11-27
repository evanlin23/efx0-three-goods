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

## Addendum: the remaining written items of `kgen/n3.md` (`claude/kgen-n3` at `0bfe9933`, PR #97; coordinator's queue, 2026-11-27)

**Verdict: all CORRECT.** Covered: Lemmas R, P, S (§2), Corollary 3 (§11), Lemmas G1–G4 (§15.2, §15.5),
Proposition A and Corollary A1 (§15.17), Lemmas G6, G7 (§15.18). One wording remark, on G3.
- Scripts: `propA_ref.py` and `lemP_ref.py` (own code), log `results/k4_referee/propA_ref.log`.
- Definitions: DE states, terminals, exposed sets, need chains, Lemma 1, Theorem B\* and (UT), as in `k4/k3_oc1.md`
  §2–§3 (branch `claude/k4-k3-oc1`, refereed).

**§2.**
- *Lemma R (reachability)* is a normalization: replace every H_i by everything its receiver values in its final
  bundle.
  - (⇐) The H\* are disjoint, inside J (or J ∪ B_{x_t}) and the receivers' R, and condition 2 gives the gains. The
    goods outside B\* are free after the chain: the only displaced pick, y_{x_t}, is released. Condition 3 is the
    absorber count.
  - (⇒) H_i ⊆ H\*_i. Adding positively valued goods keeps the gains, and X_a ∖ B\*_a ⊆ X_a ∖ B_a.
  - Correct.
- *Lemma P (peeling).*
  - Agents before z did not take y_z, and agents after z never saw it, so the picks and the junk are unchanged.
  - z's envy is bounded by v_z(M ∖ y_z) ≤ v_z(y_z), and singletons threaten nobody.
  - A chain of I − z − y_z is a chain of I.
  - Correct.
- *Lemma S.* v_i(X_i) ≥ v_i(X_j ∖ h) ≥ v_i(g) for h ∈ X_j ∖ {g}. Correct.

**§11, Corollary 3.**
- Induction with Lemma P, applied to I minus the earlier peeled agents and their picks. There the hypothesis reads as
  stated, and the picks are unchanged.
- When z_r is lifted, the witness bundles lie in M_r ∖ {y_{z_r}}. Singletons added later cause no envy.
- The base case is Theorem 2 (§9), refereed CORRECT at the top of this report.
- Correct.

**§15.2 and §15.5, G1–G4.**
- *G1.*
  - With T = {t}, every k ∈ E_t is frozen (k ∉ U, k ≠ t), and its need chain ends at t, the only terminal. So B\*'s (i)
    and (ii) hold.
  - (iv) with |T| − 1 = 0 forces π_x ⊆ {b_k, c_k} for every other x, hence equality, against (iii), unless
    E_t = {k}.
  - Conversely, π_k ≠ ∅ (base(t) is one good), so h(E_t) = 1 = |T|.
  - Correct.
- *G2.* A t holding a_t wants nothing, so no need chain ends at t. Then there are no frozen agents, and E_t = ∅.
  Correct.
- *G3.*
  - "⊆" is B\* (e). t is excluded by (I1) or (UT).
  - "⊇": an exposed x ≠ k holds its top, so it is off the chain's interior, and its pair lies in W = J′ ∪ π_k.
  - π′_x = π_x ∩ J′ = π_x ∖ π_k.
  - Correct.
  - *Wording remark:* "owner k works after the rotation iff …" is an iff for **Lemma 1 (b)'s condition** at owner k,
    which is a sufficient test for a completion. It is not an iff for "P′ has a completion with owner k".
- *G4.*
  - The receivers hold their tops and want nothing, and k is isolated.
  - A cycle would therefore use only agents whose holdings and wants are unchanged, so it existed in the draft's
    acyclic need DAG.
  - Correct.

**§15.17, Proposition A and Corollary A1.**
- Re-derived from G3, G5 (refereed) and Lemma 1 (b).
- The Rule E chain from the frozen k ends at t.
- g ∈ J′, since g ∈ π_x ⊆ W and g ∉ π_k.
- |T′| ≥ 1: the want graph of P′ is acyclic (G5), and t is not a pair holder.
- By (α) no exposed pair lies inside π_k, and {g} hits every π_x ∖ π_k. So h(k) ≤ 1 ≤ |T′|.
- Corollary A1: with |E_t| = 2 and distinct pairs, π_x ∖ π_k ≠ ∅.
- Correct.

**§15.18, G6 and G7.**
- *G6.*
  - With t σ-last, Rule E chooses t only if no off-chain wanter of g exists.
  - A chain wanter x_j would close a cycle (j ≥ 1), or is k, which holds its top.
  - Wants only shrink, so t is a terminal of P′.
  - Correct.
- *G7.* π_y ⊆ J′ ∪ {g} with g ∉ W. This gives:
  - (a) for y ∈ E_t;
  - (b) for unchanged agents, where π_y ⊄ W forces g ∈ π_y;
  - (c) for a receiver x_i, whose old pick is now held by x_{i+1} unless it is g, which forces i = s − 1.
  - Correct.

**Checks** (evidence; my own k = 3 code, DE's core case). Random strictly balanced 3-good agents, n = 3–7, cores. Only
perfect SD drafts where no LB upgrade applies are used, so P is the draft and (UT) holds trivially. There are 719
drafts with T = {t} and |E_t| ≥ 2, giving 1,307 pairs (draft, k) with (α) and (β):
- the Rule E chain ends at t at all 1,307, and P′ is valid at all, with T′ ≠ ∅;
- Proposition A's completion (g to a terminal of P′, J′ ∖ g to k) is raw EFX₀ for **every** terminal at all 1,307;
- G6 (t σ-last): t is the only wanter of g and a terminal of P′ at all 1,307;
- G7: 247 exposed agents of t in P′, all of kind (a), (b) or (c).

Lemma P and Corollary 3 were checked against my OC₁ test (`cert_ref.oc_depth`, official moves, t ≥ 0 included). On
20,000 random instances (n = 3–4, ties allowed) there are 17,221 top-heavy cases:
- the picks are unchanged by the peeling at all;
- Lemma P has 0 violations;
- Corollary 3 has 0 violations at the 8,353 cases with n = 3.

*Limits.*
- Drafts that need LB upgrades are not exercised by my check.
- Theorem 2 (§9) is used; it is refereed CORRECT at the top of this report.
