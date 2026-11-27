# Referee report: Proposition H (`kgen/n3.md` §10, branch `claude/kgen-n3`)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `kgen/n3.md` at `eb95583`: §1, §2, §10 (Proposition H and the text around it) and §11 (Corollary 3, which
  cites it). Also PROMPT.md L1.
- Check: `k4/referee/proph_ref.py`, run by `proph_ref_runs.sh`, log `results/k4_referee/proph_ref.log`. Own code, raw
  EFX₀.

## Verdict: CORRECT WITH FIXES (one sign in a displayed inequality; the conclusion is unaffected)

The statement: if every three-agent instance with distinct tops and relevance bound k + 3 has an EFX₀ allocation,
then every three-agent instance with relevance bound k has one. Hence OC₁ at n = 3 for every k (even restricted to
distinct tops) implies EFX₀ for three additive agents.

## The proof, step by step

1. **The lift.** Add t₁, t₂, t₃ with v_i(t_i) = L + δ, v_i(t_j) = L, and L > max_i v_i(M).
   - t_i is i's unique top, so the tops are distinct.
   - Each R_i grows by exactly three goods.

   Correct.
2. **Each agent holds exactly one t.** If i holds none, some j holds two. Then for every g ∈ X_j, X_j ∖ g still
   contains a t, so v_i(X_j ∖ g) ≥ L > v_i(M) ≥ v_i(X_i), contradicting EFX₀. With three agents and three t's, each
   holds exactly one. Correct.
3. **The restriction is EFX₀ up to δ.** EFX₀ for i toward X_j = {t_{σ(j)}} ∪ S_j, removing g ∈ S_j, gives
   > v_i(S_i) ≥ v_i(S_j ∖ g) **+** (v_i(t_{σ(j)}) − v_i(t_{σ(i)})).

   **Fix.** The note writes "− (v_i(t_{σ(j)}) − v_i(t_{σ(i)}))", which has the wrong sign. The difference
   v_i(t_{σ(j)}) − v_i(t_{σ(i)}) lies in {−δ, 0, δ}, so with the correct sign the bound ≥ v_i(S_j ∖ g) − δ follows.
   The note's conclusion is right, but its displayed intermediate step is not what EFX₀ gives.
4. **The limit δ → 0.** L is fixed independently of δ. For δ_n → 0 the allocations S⁽ⁿ⁾ of M range over a finite set,
   so one S repeats infinitely often, and the closed inequalities pass to the limit. Correct.
   - An equivalent finite version: with integer (or rational) values, any δ below the smallest positive gap
     v_i(S_j ∖ g) − v_i(S_i) works directly.
5. **The consequence.** OC₁ at n = 3 for every k produces an EFX₀ allocation on every instance, distinct tops
   included. By 1–4 that gives EFX₀ for every three-agent instance, since the relevance bound is at most m. Correct.
   - The comparison with Chaudhury–Garg–Mehlhorn (EFX for three additive agents) goes through L1 of PROMPT.md, the
     perturbation lemma, which is the EFX₀ ⟺ positive-EFX transfer. I have read PROMPT.md's L1; CGM itself is not
     read here [unverified], as the note says.
6. **The scope remark.** The reduction maps k to k + 3, so it says nothing about fixed small k such as the campaign's
   k = 4. Correct, and important for how the proposition is used.

## Computation (evidence)

- Random three-agent instances: m ≤ 6, values in {0, 1, 2, 3, 5, 9} with zeros and ties, scaled by Q = 100.
- The lift: δ = 1 and L = Q · max_i v_i(M) + 1.
- Every allocation of the lifted instance was enumerated, and checked at every EFX₀ one.

| run | instances | EFX₀ allocations of the lift | not one t each | restriction not EFX₀ | tops/relevance wrong | existence mismatch I vs lift |
|---|---|---|---|---|---|---|
| δ = 1 < Q | 3,000 | 118,295 | 0 | 0 | 0 | 0 |
| δ = 350 > Q (control) | 1,000 | 47,210 | 0 | **24,671** | 0 | 0 |

The control shows that the δ → 0 step (δ below the value gaps) is genuinely used: with a large δ the restriction is
often not EFX₀.

## For the coordinator

- Proposition H: CORRECT WITH FIXES. It can be recorded as PROVED once the sign in step 3 is corrected (a one-character
  fix).
- It calibrates rather than reduces: OC₁ at n = 3 for *all* k is at least as hard as three-agent EFX₀, while fixed
  k = 4 is untouched.
