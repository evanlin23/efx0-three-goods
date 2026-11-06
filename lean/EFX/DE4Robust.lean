import EFX.DE4V3
import EFX.DE4Cor10

/-!
# The robust order (`k4/de4.md` §9–§10; ledger K4.DE4V3R, K4.DE4V3R.IMP, K4.DE4V3R.T)

The states of DE4ᵛ³ ((V1), (V2), (V3)) with DE4's levels, except that a *robust* upper set (worth at least the rest of
the agent's goods) has level 6.

**Definitions.**
- `IsRobust`, `levelR`, `potentialR`, `BetterR`, `IsMaximumR`.
- `ConjRob` (**Conjecture K4.DE4V3R**, a hypothesis): every maximum of the robust order is completable.
- `ClaimT` (**Claim T**, a hypothesis): every non-completable (V3)-valid state of the largest robust level sum is
  all-upper.
- `ThmAllUpper` (the statement of Theorem A′, proved in `DE4RobustA.lean`): every non-completable (V3)-valid state in
  which every agent holds an upper set has a better (V3)-valid state.

**Results.**
- `levelR_mono` (Lemma 1(a) for the robust levels), `exists_maximumR`.
- `target4_of_conjRob`: Conjecture K4.DE4V3R implies TARGET₄.
- `conjRob_of_claimT`: Claim T and Theorem A′ imply Conjecture K4.DE4V3R.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- An upper set is robust if it is worth at least the agent's other goods. -/
def IsRobust (v : A → G → Nat) (i : A) (goods : List G) (S : List G) : Prop :=
  value v i (goods.filter (fun g => decide (g ∉ S))) ≤ value v i S

open Classical in
/-- The robust level: 6 for a robust upper set, DE4's level otherwise. -/
noncomputable def levelR (v : A → G → Nat) (i : A) (goods : List G) (S : List G) : Nat :=
  if IsUpper v i goods S ∧ IsRobust v i goods S then 6 else level v i goods S

/-- The robust level sum. -/
noncomputable def potentialR (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  (agents.map (fun i => levelR v i goods (hold goods base i))).sum

/-- The robust order: a larger robust level sum, or the same with the values Pareto-better. -/
def BetterR (v : A → G → Nat) (agents : List A) (goods : List G) (base' base : G → Option A) : Prop :=
  potentialR v agents goods base < potentialR v agents goods base' ∨
    (potentialR v agents goods base = potentialR v agents goods base' ∧
      (∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i)) ∧
      ∃ i ∈ agents, value v i (hold goods base i) < value v i (hold goods base' i))

/-- A maximum of the robust order among the (V3)-valid states. -/
def IsMaximumR (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ValidV3 v agents goods base ∧ ∀ base', ValidV3 v agents goods base' → ¬ BetterR v agents goods base' base

/-- **Conjecture K4.DE4V3R** (a hypothesis, never an axiom): every maximum of the robust order is completable. -/
def ConjRob (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → Completable v agents goods base

/-- **Claim T** (a hypothesis, never an axiom): a non-completable (V3)-valid state whose robust level sum is the
largest among (V3)-valid states has every agent holding an upper set. -/
def ClaimT (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, ValidV3 v agents goods base →
      (∀ base', ValidV3 v agents goods base' → potentialR v agents goods base' ≤ potentialR v agents goods base) →
      ¬ Completable v agents goods base → ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- The statement of **Theorem A′**: a non-completable (V3)-valid state in which every agent holds an upper set has a
better (V3)-valid state. -/
def ThmAllUpper (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, ValidV3 v agents goods base → (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ¬ Completable v agents goods base → ∃ base', ValidV3 v agents goods base' ∧ BetterR v agents goods base' base

section robust
variable (v : A → G → Nat)

omit [DecidableEq A] in
theorem levelR_le_six (i : A) (goods : List G) (S : List G) : levelR v i goods S ≤ 6 := by
  unfold levelR
  split
  · exact Nat.le_refl _
  · exact Nat.le_trans (level_le_five v i goods S) (by omega)

omit [DecidableEq A] in
theorem level_le_levelR (i : A) (goods : List G) (S : List G) : level v i goods S ≤ levelR v i goods S := by
  unfold levelR
  split
  · exact Nat.le_trans (level_le_five v i goods S) (by omega)
  · exact Nat.le_refl _

end robust


section robust2
variable (v : A → G → Nat)

omit [DecidableEq A] in
/-- The goods outside `S` and those of `S` split the value of all goods. -/
theorem value_compl_add {goods : List G} (hgd : goods.Nodup) (i : A) {S : List G} (hS : S.Nodup)
    (hSg : ∀ g ∈ S, g ∈ goods) :
    value v i (goods.filter (fun g => decide (g ∉ S))) + value v i S = value v i goods := by
  have hsplit := value_filter_add v i (fun g => decide (g ∈ S)) goods
  have h1 : value v i (goods.filter (fun g => decide (g ∈ S))) = value v i S := by
    have a1 := value_le_of_subset v i (hgd.filter (fun g => decide (g ∈ S))) hS (fun g hg => by
      have := (List.mem_filter.mp hg).2; simpa using this)
    have a2 := value_le_of_subset v i hS (hgd.filter (fun g => decide (g ∈ S)))
      (fun g hg => List.mem_filter.mpr ⟨hSg g hg, by simpa using hg⟩)
    omega
  have h2 : goods.filter (fun g => !decide (g ∈ S)) = goods.filter (fun g => decide (g ∉ S)) := by
    apply List.filter_congr; intro g _; simp
  rw [h2] at hsplit
  omega

omit [DecidableEq A] in
/-- An allowed holding worth more than the top is an upper set. -/
theorem isUpper_of_gt_top {i : A} {goods : List G} {T : List G} (hT : Allowed v i goods T)
    (hgt : topV v i goods < value v i T) (hTg : ∀ g ∈ T, g ∈ goods) : IsUpper v i goods T := by
  rcases hT with ⟨hl, _⟩ | hU | hL
  · exfalso
    rcases T with _ | ⟨t, _ | ⟨t', T'⟩⟩
    · simp [value] at hgt
    · rw [value_singleton] at hgt
      have := le_topV v i goods (hTg t (by simp))
      omega
    · simp at hl
  · exact hU
  · exact absurd hgt (Nat.not_lt.mpr (Nat.le_of_lt hL.2.2.2.1))

omit [DecidableEq A] in
/-- **Lemma 1(a) for the robust levels**: among allowed holdings, more value never means a lower robust level. -/
theorem levelR_mono {i : A} {goods : List G} (hgd : goods.Nodup) {S T : List G} (hS : Allowed v i goods S)
    (hT : Allowed v i goods T) (hSnd : S.Nodup) (hTnd : T.Nodup) (hSg : ∀ g ∈ S, g ∈ goods)
    (hTg : ∀ g ∈ T, g ∈ goods) (hST : value v i S < value v i T) :
    levelR v i goods S ≤ levelR v i goods T := by
  by_cases hR : IsUpper v i goods S ∧ IsRobust v i goods S
  · have hTU : IsUpper v i goods T := isUpper_of_gt_top v hT (Nat.lt_trans hR.1.2.1 hST) hTg
    have hTR : IsRobust v i goods T := by
      have e1 := value_compl_add v hgd i hSnd hSg
      have e2 := value_compl_add v hgd i hTnd hTg
      have := hR.2
      unfold IsRobust at this ⊢
      omega
    have h6 : levelR v i goods T = 6 := by unfold levelR; simp [hTU, hTR]
    rw [h6]; exact levelR_le_six v i goods S
  · have h1 : levelR v i goods S = level v i goods S := by unfold levelR; simp [hR]
    rw [h1]
    exact Nat.le_trans (level_mono v i goods hS hT hSg hTg hST) (level_le_levelR v i goods T)

end robust2

section framesR
variable (v : A → G → Nat) (agents : List A) (goods : List G)

/-- A state where nobody's value drops, with more value for someone and every robust level at least as high, is
better in the robust order. -/
theorem betterR_of_monotone {base base' : G → Option A}
    (hlev : ∀ i ∈ agents, levelR v i goods (hold goods base i) ≤ levelR v i goods (hold goods base' i))
    (hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i))
    (hlt : ∃ i ∈ agents, value v i (hold goods base i) < value v i (hold goods base' i)) :
    BetterR v agents goods base' base := by
  have hP : potentialR v agents goods base ≤ potentialR v agents goods base' := sum_map_le hlev
  rcases Nat.lt_or_eq_of_le hP with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hval, hlt⟩

/-- The measure `Φ_R · (V + 1) + Σ_i v_i(Y_i)`, which every `BetterR` state raises. -/
noncomputable def measureR (base : G → Option A) : Nat :=
  potentialR v agents goods base * (bigV v agents goods + 1) + totalValue v agents goods base

theorem potentialR_le (base : G → Option A) : potentialR v agents goods base ≤ 6 * agents.length :=
  sum_map_le_mul (fun i _ => levelR_le_six v i goods _)

theorem measureR_le (base : G → Option A) :
    measureR v agents goods base ≤ 6 * agents.length * (bigV v agents goods + 1) + bigV v agents goods := by
  have h1 := Nat.mul_le_mul_right (bigV v agents goods + 1) (potentialR_le v agents goods base)
  have h2 := totalValue_le v agents goods base
  unfold measureR
  omega

theorem measureR_lt_of_better {base base' : G → Option A} (h : BetterR v agents goods base' base) :
    measureR v agents goods base < measureR v agents goods base' := by
  unfold measureR
  have hT := totalValue_le v agents goods base
  rcases h with hP | ⟨hP, hle, hlt⟩
  · have h1 := Nat.mul_le_mul_right (bigV v agents goods + 1) hP
    rw [Nat.succ_mul] at h1
    omega
  · have : totalValue v agents goods base < totalValue v agents goods base' := sum_map_lt hle hlt
    rw [hP]
    omega

/-- From any (V3)-valid state, descent along `BetterR` reaches a maximum of the robust order. -/
theorem exists_maximumR_of_valid {base : G → Option A} (hb : ValidV3 v agents goods base) :
    ∃ m, IsMaximumR v agents goods m := by
  let M := 6 * agents.length * (bigV v agents goods + 1) + bigV v agents goods
  suffices key : ∀ k, ∀ b, ValidV3 v agents goods b → M - measureR v agents goods b ≤ k →
      ∃ m, IsMaximumR v agents goods m from key _ base hb (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro b hb hk
    refine ⟨b, hb, fun b' _ hbet => ?_⟩
    have := measureR_lt_of_better v agents goods hbet
    have := measureR_le v agents goods b'
    omega
  | succ k ih =>
    intro b hb hk
    by_cases hmax : ∀ b', ValidV3 v agents goods b' → ¬ BetterR v agents goods b' b
    · exact ⟨b, hb, hmax⟩
    · obtain ⟨b', hb'⟩ := Classical.not_forall.mp hmax
      have hv' : ValidV3 v agents goods b' := Classical.byContradiction fun hn => hb' fun h => absurd h hn
      have hbet : BetterR v agents goods b' b := Classical.byContradiction fun hn => hb' fun _ => hn
      have := measureR_lt_of_better v agents goods hbet
      have := measureR_le v agents goods b'
      exact ih b' hv' (by omega)

variable {v agents goods}

/-- Every instance has a maximum of the robust order. -/
theorem exists_maximumR (hag : agents.Nodup) (hgd : goods.Nodup) : ∃ base, IsMaximumR v agents goods base :=
  exists_maximumR_of_valid v agents goods ⟨draft_valid hag hgd, draft_v3 v hag hgd⟩

end framesR

/-- Conjecture K4.DE4V3R gives an EFX₀ allocation of every strict R1-core with at most four relevant goods per agent. -/
theorem exists_efx0_of_conjRob (h : ConjRob A G) (v : A → G → Nat) {agents : List A} {goods : List G}
    (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨base, hmax⟩ := exists_maximumR (v := v) hag hgd
  obtain ⟨X, hX, -, hE⟩ := h v agents goods hne hag hgd hc hs base hmax
  exact ⟨X, hX, hE⟩

/-- **Conjecture K4.DE4V3R implies TARGET₄** (with K4.CORE and K4.TIE, as in Lemma 3). -/
theorem target4_of_conjRob (I : Inst) (hn : 0 < I.n) (h : ConjRob (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _)
    (fun w agents _ hag hgd _ hcore _ hs _ =>
      exists_efx0_of_conjRob h w (fun he => by have := hcore.1; rw [he] at this; simp at this) hag hgd
        (fun i hi => ⟨(hcore.2.1 i hi).1, (hcore.2.1 i hi).2, hcore.2.2.1 i hi⟩) hs) h4

/-- **Claim T and Theorem A′ imply Conjecture K4.DE4V3R**: a non-completable maximum has the largest robust level sum
(a state of larger level sum would be better), so by Claim T every agent holds an upper set, and then Theorem A′ gives
a better state, which a maximum does not have. -/
theorem conjRob_of_claimT (hT : ClaimT A G) (hA : ThmAllUpper A G) : ConjRob A G := by
  intro v agents goods hne hag hgd hc hs base hmax
  refine Classical.byContradiction fun hnc => ?_
  have htop : ∀ base', ValidV3 v agents goods base' →
      potentialR v agents goods base' ≤ potentialR v agents goods base := by
    intro base' hv'
    refine Nat.le_of_not_lt fun hlt => hmax.2 base' hv' (Or.inl hlt)
  have hup := hT v agents goods hne hag hgd hc hs base hmax.1 htop hnc
  obtain ⟨b', hv', hb'⟩ := hA v agents goods hne hag hgd hc hs base hmax.1 hup hnc
  exact hmax.2 b' hv' hb'

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.levelR_le_six
#print axioms EFX.DE4.level_le_levelR
#print axioms EFX.DE4.value_compl_add
#print axioms EFX.DE4.isUpper_of_gt_top
#print axioms EFX.DE4.levelR_mono
#print axioms EFX.DE4.betterR_of_monotone
#print axioms EFX.DE4.potentialR_le
#print axioms EFX.DE4.measureR_le
#print axioms EFX.DE4.measureR_lt_of_better
#print axioms EFX.DE4.exists_maximumR_of_valid
#print axioms EFX.DE4.exists_maximumR
#print axioms EFX.DE4.exists_efx0_of_conjRob
#print axioms EFX.DE4.target4_of_conjRob
#print axioms EFX.DE4.conjRob_of_claimT
