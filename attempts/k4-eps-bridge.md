# The ε bridge from ordinary EFX to EFX₀ (track A3, 2026-11-27 burst 21): no leverage

**Idea.** Give every good outside R_i the value ε to agent i (v^ε). There are finitely many allocations. So if every
v^ε (ε small) has an ordinary EFX allocation, some allocation X is EFX for a sequence ε_t → 0.

**Lemma (proved).** Such an X is EFX₀ for v.

*Proof.* Under v^ε every value is positive, so EFX constrains the removal of every good. For i ≠ j and g ∈ X_j,
v_i(X_i) + ε·|X_i ∖ R_i| ≥ v_i(X_j ∖ g) + ε·|(X_j ∖ g) ∖ R_i|. Letting ε_t → 0 gives v_i(X_i) ≥ v_i(X_j ∖ g). ∎

**Why it gives nothing.** We hoped Theorem VM (`k4/vm.md` §8, ordinary EFX for 4-limited instances, proved) could be
applied to v^ε. It cannot: under v^ε every agent values every good, so v^ε is not 4-limited.
- VM's rankings, its matchings G_k and Fact 0 ("only X_j ∩ R_i matters") all use 4-limitedness.
- The proof of Theorem VM drops non-valuers in exactly two places (Step 2 and Step 6). Under v^ε, those are the
  places where ε-goods count. So the bridge restates EFX₀ (with a junk-count tie-break) and does not reduce it to
  Theorem VM.

**Smallest failing configuration.** V-M's (S3) instance, n = 2, m = 3 (`k4/vm.md` §5.3): v₀ = {0: 19, 1: 14},
v₁ = {0: 17, 2: 7}. `attempts/k4_eps_bridge.py` (log `results/k4_eps_bridge.log`) lists:
- EFX₀ allocations of v: ({0}, {1, 2}), ({1, 2}, {0}).
- Ordinary EFX allocations of v: those two, plus ({0, 1}, {2}) and ({1}, {0, 2}). V-M's outputs are among these extra
  two.
- Ordinary EFX allocations of v^ε for ε = 10⁻³ and 10⁻⁶: exactly the two EFX₀ allocations, with 3 relevant goods per
  agent.

The good valued only by agent 0 must go to the *other*, unenvied agent. V-M's EFX graph has only valuers as nodes, so
it never considers that placement.

**Verdict.** Track A3 is dropped after one burst. No artifact beyond the lemma above. The gap between Theorem VM and
EFX₀ is the non-valuer placement, already mapped in `k4/vm.md` §5–§7, and its repairs there are rule-type
conjectures.

    python3 attempts/k4_eps_bridge.py
