# Referee report: Theorem M3, monotone EFX₀ with at most three relevant goods (`monotone/k3.md`, branch `claude/monotone-k`, PR #112)

Referee: `proof/k4-referee`, 2026-11-27.
- Read: `monotone/k3.md` at `06e4b02`, in full. Also LEDGER.md row T (TARGET), and the docstring of
  `monotone/amm_check.py`, used only for its description of the Akrami et al. instance.
- Check: `k4/referee/mono_ref.py`, log `results/k4_referee/mono_ref.log`. Own code, raw EFX₀ for monotone set
  functions. Nothing from `monotone/` was run or imported.

## Verdict: CORRECT

Every instance with normalized monotone valuations and |R_i| ≤ 3 has an EFX₀ allocation, for all n and m. The
reduction to TARGET is sound, and Lemma S3 is exactly what makes it work.

## The proof, step by step

0. **Relevance.** If g is irrelevant, v(S ∪ g) ≤ v(S) for all S, and monotonicity gives equality, so
   v(S) = v(S ∩ R) by removing irrelevant goods one at a time. Correct.
1. **Nondegeneracy.** v^ε = v + ε·Σ_{g_t ∈ S∩R_i} 2^t is normalized and monotone. It depends only on S ∩ R_i, has
   relevant set exactly R_i (strictly increasing there), and is injective on 2^{R_i} for all but finitely many ε (one
   ε per pair S ≠ T).
   - The limit step: finitely many allocations, and each EFX₀ inequality is affine in ε. Correct.
   - The perturbed profile stays 3-limited, which is what Step 4 needs.
2. **Lemma S3.** For a nondegenerate monotone v on |R| ≤ 3, the function is strictly increasing under inclusion
   (monotone + injective), so the singletons are distinct.
   - Disjoint nonempty pairs in a ≤ 3-set have sizes (1, 1) or (1, 2), and pairs with ∅ are trivial.
   - The weights (4, 3, 2) / (6, 3, 2) reproduce the single undetermined comparison v(s₁) vs v(s₂s₃).
   - Every other comparison is forced by strict increase: Y ∋ s₁ beats any singleton x ≠ s₁.
   - Correct.
3. **Ordinality.** X_i ∩ R_i and (X_j ∖ g) ∩ R_i are disjoint, and "≥" is the negation of "<", so the EFX₀ sets of v
   and of w agree. Correct.
4. **TARGET.** Ledger row T covers every nonnegative additive instance with ≤ 3 relevant goods per agent
   (machine-checked over ℕ). The surrogate has natural-number values and the same relevant sets. Correct.

**Remarks.**
- Remark 3, that S3 fails at r = 4: the order a > b > c > d with cd > ab is a linear extension of the Boolean lattice,
  and no additive w with w(a) > w(c), w(b) > w(d) has w(ab) < w(cd). Correct.
- Remark 1, the tie example: correct (an additive surrogate positive on b changes the envy toward {b}).
- Remark 2, the list of project lemmas that use only monotonicity, was not re-checked lemma by lemma.

**The upper bound "k ≤ 8" (Akrami et al., arXiv 2604.18216v4 §3.1.1: not read by me [unverified]).** I implemented
the instance as described in `monotone/amm_check.py`'s docstring (types A, B, C; pair values 6, 5, 4, 3, 2, 1; value
7 on a UVx triple) with my own code:
- u and v are both monotone, and every agent values all 8 goods;
- u has 24 EFX₀ allocations, and **v has 0**.

So the described instance does refute monotone EFX₀ with k = 8. Whether it is the paper's instance is unverified.

## Computation (evidence)

| check | tests | failures |
|---|---|---|
| Lemma S3, every nondegenerate monotone order (linear extensions of the Boolean lattice) | r = 1: 1, r = 2: 2, r = 3: 48 orders | 0 mismatches |
| random monotone 3-limited instances (n = 2–4, m ≤ 7): an EFX₀ allocation exists | 4,000 (2,000 nondegenerate, 2,000 with ties and zeros) | 0 |
| Step 3: EFX₀ sets of v and of the surrogate w coincide (nondegenerate) | 2,000 instances | 0 |
| Step 1: v + ε·w is nondegenerate with relevant set R_i (degenerate inputs) | 5,965 agents | 0 |

## For the coordinator

- Theorem M3: CORRECT. It can be recorded as PROVED.
- The cited k = 8 instance is confirmed as described; the attribution is unverified by me.
