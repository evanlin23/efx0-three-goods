# Lemma KR for any valid pre-allocation (k4/rulef.md §3, before hypothesis (iii))

**Idea.** State Lemma KR (one rotation along a need chain k → … → o lowers Lemma K's deficit by one) for every valid
pre-allocation in the sense of `k4/lb4.md` §1, where an agent's needs N_i may be any set that contains the goods worth
more than its base. The validity step of the proof argued: "each x_i (i ≥ 1) now holds a pick it ranked above its
old one, so its needs shrink", hence NA′ ⊆ NA and P′ satisfies (V1).

**Where it breaks.** A chain step Y_{x_{i−1}} ∈ N_{x_i} does not say that x_i values Y_{x_{i−1}} above its base when
needs may be a superset of the value-based ones. Then the rotated agent can take a good it values less than its old
base, its new needs (value-based, as `EFX.LB4R.needsOf` gives) contain the old base, and that base returns to the junk:
P′ violates (V1). Found by the PR #72 referee. The fix is hypothesis (iii) of Lemma KR: the needs along the chain are
value-based (N_{x_i} ⊆ {g : v(g) > v(B_{x_i})}, 1 ≤ i ≤ t), which holds in every state of LB₄ʳ (`EFX.LB4R.Inv`,
`needsOf`).

**Smallest failing configuration** (n = 2, the least n with a need chain; the core {0, 1, 2, 3}, {1, 2, 3}):
agent 0 values goods 0, 1, 2, 3 at (7, 6, 5, 3), agent 1 values goods 1, 2, 3 at (4, 3, 2). B₀ = {0}, B₁ = {1},
J = {2, 3}; needs N₀ = {1} (a superset need: agent 0 values good 1 below its base), N₁ = ∅. P is valid (NA = {1}
misses J; agent 1 is frozen, agent 0 is not). k = 1, o = 0, chain 1 → 0 (Y₁ = 1 ∈ N₀), O = {2, 3} ⊆ R₁ ∩ W,
v₁(O) = 5 > 4. E = {1} (W = {0, 2, 3} threatens agent 1), served by the kept-out set {2}: κ = 0, δ = 1; (i) holds (σ
serves only k), and (ii) holds (agent 1, holding {2, 3} worth 5, needs nothing). After the rotation agent 0 holds good
1 with needs {0} (7 > 6), and J′ = {0}: J′ ∩ NA′ = {0}, so (V1) fails.

Reproduce: `python3 attempts/k4_rulef_attempts.py` (part 7; `results/k4_rulef/attempts.log`).
