import EFX.Bridge

/-!
# Minimal threats for arbitrary relevance bounds

A minimal threat at threshold `t` is a duplicate-free set worth more than `t` for which
deleting any good leaves value at most `t`. An allocation is EFX₀ precisely when no other
bundle properly contains a minimal threat at the envious agent's own-bundle threshold.
All values are natural numbers; no bound on the number of relevant goods is assumed.
-/

set_option autoImplicit false

namespace EFX
namespace Threats

variable {A G : Type} [DecidableEq G]

/-- An inclusion-minimal set of goods whose value exceeds the threshold. -/
def Minimal (v : A → G → Nat) (i : A) (t : Nat) (T : List G) : Prop :=
  T.Nodup ∧ t < value v i T ∧ ∀ g ∈ T, value v i (T.erase g) ≤ t

theorem value_erase_eq (v : A → G → Nat) (i : A) {S : List G} {g : G}
    (hg : g ∈ S) : value v i S = v i g + value v i (S.erase g) := by
  unfold value
  rw [(List.perm_cons_erase hg).map (v i) |>.sum_nat]
  simp

theorem value_subset (v : A → G → Nat) (i : A) :
    ∀ {S T : List G}, S.Nodup → (∀ g ∈ S, g ∈ T) → value v i S ≤ value v i T
  | [], _, _, _ => by simp
  | g :: S, T, hS, hsub => by
    obtain ⟨hg, hnd⟩ := List.nodup_cons.mp hS
    have hmem := hsub g (by simp)
    have hle := value_subset v i (T := T.erase g) hnd (fun x hx =>
      (List.mem_erase_of_ne (fun h : x = g => hg (h ▸ hx))).mpr (hsub x (by simp [hx])))
    rw [value_cons, value_erase_eq v i hmem]
    omega

/-- Every over-value set contains a minimal threat. -/
theorem exists_minimal (v : A → G → Nat) (i : A) (t : Nat) (S : List G)
    (hnd : S.Nodup) (hval : t < value v i S) :
    ∃ T : List G, T.Sublist S ∧ Minimal v i t T := by
  classical
  by_cases h : ∃ g ∈ S, t < value v i (S.erase g)
  · obtain ⟨g, hg, hgt⟩ := h
    obtain ⟨T, hTS, hmin⟩ := exists_minimal v i t (S.erase g)
      (hnd.sublist List.erase_sublist) hgt
    exact ⟨T, hTS.trans List.erase_sublist, hmin⟩
  · exact ⟨S, List.Sublist.refl _, hnd, hval, fun g hg => by
      have : ¬ t < value v i (S.erase g) := fun hgt => h ⟨g, hg, hgt⟩
      omega⟩
termination_by S.length
decreasing_by
  have := List.length_erase_of_mem hg
  have := List.length_pos_of_mem hg
  omega

/-- A minimal threat contains only relevant goods. -/
theorem minimal_relevant {v : A → G → Nat} {i : A} {t : Nat} {T : List G}
    (h : Minimal v i t T) : ∀ g ∈ T, 0 < v i g := by
  intro g hg
  have := value_erase_eq v i hg
  have := h.2.2 g hg
  have := h.2.1
  omega

/-- Minimal threats form an antichain: containment forces equality as sets. -/
theorem minimal_antichain {v : A → G → Nat} {i : A} {t : Nat} {T U : List G}
    (hT : Minimal v i t T) (hU : Minimal v i t U) (hsub : ∀ g ∈ T, g ∈ U) :
    ∀ g ∈ U, g ∈ T := by
  intro g hg
  apply Classical.byContradiction
  intro hnot
  have hle := value_subset v i hT.1 (T := U.erase g) (fun x hx =>
    (List.mem_erase_of_ne (fun h : x = g => hnot (h ▸ hx))).mpr (hsub x hx))
  have := hU.2.2 g hg
  have := hT.2.1
  omega

/-- A target bundle is safe at threshold `t` when every single-good deletion is affordable. -/
def Safe (v : A → G → Nat) (i : A) (t : Nat) (S : List G) : Prop :=
  ∀ g ∈ S, value v i (S.erase g) ≤ t

/-- A safe but envied bundle is exactly a minimal threat; other safe bundles are unenvied. -/
theorem safe_iff {v : A → G → Nat} {i : A} {t : Nat} {S : List G} (hS : S.Nodup) :
    Safe v i t S ↔ value v i S ≤ t ∨ Minimal v i t S := by
  constructor
  · intro h
    by_cases hv : value v i S ≤ t
    · exact Or.inl hv
    · exact Or.inr ⟨hS, by omega, h⟩
  · intro h g hg
    rcases h with hv | hmin
    · exact Nat.le_trans (value_sublist v i List.erase_sublist) hv
    · exact hmin.2.2 g hg

/-- Exact incremental check for adding one new good to a target bundle. -/
theorem safe_append_iff {v : A → G → Nat} {i : A} {t : Nat} {S : List G} {g : G}
    (hg : g ∉ S) : Safe v i t (S ++ [g]) ↔
      value v i S ≤ t ∧ ∀ h ∈ S, v i g + value v i (S.erase h) ≤ t := by
  constructor
  · intro h
    constructor
    · have hs := h g (by simp)
      simpa [List.erase_append_right [g] hg] using hs
    · intro a ha
      have hs := h a (by simp [ha])
      simpa [List.erase_append_left [g] ha, value, Nat.add_comm] using hs
  · rintro ⟨hS, hrest⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · have hs := hrest a ha
      simpa [List.erase_append_left [g] ha, value, Nat.add_comm] using hs
    · have he : a = g := List.mem_singleton.mp ha
      subst a
      simpa [List.erase_append_right [g] hg] using hS

/-- Adding even a worthless good destroys safety of a safe but envied bundle. -/
theorem minimal_append_unsafe {v : A → G → Nat} {i : A} {t : Nat} {S : List G} {g : G}
    (hS : Minimal v i t S) (hg : g ∉ S) : ¬ Safe v i t (S ++ [g]) := by
  intro h
  have := ((safe_append_iff hg).mp h).1
  have := hS.2.1
  omega

/-- For a worthless new good, absence of full envy is necessary and sufficient. -/
theorem safe_append_zero_iff {v : A → G → Nat} {i : A} {t : Nat} {S : List G} {g : G}
    (hg : g ∉ S) (hz : v i g = 0) : Safe v i t (S ++ [g]) ↔ value v i S ≤ t := by
  rw [safe_append_iff hg]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun a _ => by
      rw [hz, Nat.zero_add]
      exact Nat.le_trans (value_sublist v i List.erase_sublist) h⟩

/-- Deleting some good from `S` exceeds `t` iff `S` properly contains a minimal threat. -/
theorem threat_iff {v : A → G → Nat} {i : A} {t : Nat} {S : List G} (hnd : S.Nodup) :
    (∃ g ∈ S, t < value v i (S.erase g)) ↔
      ∃ T : List G, Minimal v i t T ∧ (∀ g ∈ T, g ∈ S) ∧ ∃ g ∈ S, g ∉ T := by
  constructor
  · rintro ⟨g, hg, hval⟩
    obtain ⟨T, hTS, hmin⟩ := exists_minimal v i t (S.erase g)
      (hnd.sublist List.erase_sublist) hval
    exact ⟨T, hmin, fun x hx => List.mem_of_mem_erase (hTS.subset hx),
      g, hg, fun h => hnd.not_mem_erase (hTS.subset h)⟩
  · rintro ⟨T, hmin, hsub, g, hg, hnot⟩
    have hle := value_subset v i hmin.1 (T := S.erase g) (fun x hx =>
      (List.mem_erase_of_ne (fun h : x = g => hnot (h ▸ hx))).mpr (hsub x hx))
    exact ⟨g, hg, Nat.lt_of_lt_of_le hmin.2.1 hle⟩

/-- The threat in a bundle of size at most `b` has at most `b - 1` goods. -/
theorem exists_small_minimal {v : A → G → Nat} {i : A} {t b : Nat} {S : List G}
    (hnd : S.Nodup) (hsize : S.length ≤ b)
    (h : ∃ g ∈ S, t < value v i (S.erase g)) :
    ∃ T : List G, Minimal v i t T ∧ T.length < b ∧
      (∀ g ∈ T, g ∈ S) ∧ ∃ g ∈ S, g ∉ T := by
  obtain ⟨g, hg, hval⟩ := h
  obtain ⟨T, hTS, hmin⟩ := exists_minimal v i t (S.erase g)
    (hnd.sublist List.erase_sublist) hval
  have hlen := hTS.length_le
  have herase := List.length_erase_of_mem hg
  have hpos := List.length_pos_of_mem hg
  exact ⟨T, hmin, by omega, fun x hx => List.mem_of_mem_erase (hTS.subset hx),
    g, hg, fun h => hnd.not_mem_erase (hTS.subset h)⟩

/-- On bundles of at most two goods, all violations are singleton needs in non-singletons. -/
theorem pair_threat_iff {v : A → G → Nat} {i : A} {t : Nat} {S : List G}
    (hnd : S.Nodup) (hsize : S.length ≤ 2) :
    (∃ g ∈ S, t < value v i (S.erase g)) ↔
      ∃ a ∈ S, t < v i a ∧ ∃ g ∈ S, g ≠ a := by
  constructor
  · intro h
    obtain ⟨T, hmin, hlen, hsub, g, hg, hnot⟩ := exists_small_minimal hnd hsize h
    cases T with
    | nil => have := hmin.2.1; simp at this
    | cons a rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
      subst rest
      refine ⟨a, hsub a (by simp), ?_, g, hg, ?_⟩
      · simpa using hmin.2.1
      · simpa using hnot
  · rintro ⟨a, ha, hv, g, hg, hga⟩
    have hmem : a ∈ S.erase g := (List.mem_erase_of_ne (Ne.symm hga)).mpr ha
    exact ⟨g, hg, Nat.lt_of_lt_of_le hv (le_value_of_mem v i hmem)⟩

section allocations
variable [DecidableEq A]

/-- Exact minimal-threat specification of EFX₀ over arbitrary finite lists. -/
theorem efx0L_iff {v : A → G → Nat} {agents : List A} {goods : List G} {X : G → A}
    (hgoods : goods.Nodup) :
    EFX0L v agents goods X ↔
      ∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → ∀ T : List G,
        Minimal v i (value v i (bundle goods X i)) T →
        (∀ g ∈ T, g ∈ bundle goods X j) → ∀ g ∈ bundle goods X j, g ∈ T := by
  constructor
  · intro h i hi j hj hij T hmin hsub g hg
    apply Classical.byContradiction
    intro hnot
    have hbad := (threat_iff (hgoods.sublist List.filter_sublist)).mpr
      ⟨T, hmin, hsub, g, hg, hnot⟩
    obtain ⟨a, ha, hval⟩ := hbad
    exact Nat.not_lt_of_ge (h i hi j hj hij a ha) hval
  · intro h i hi j hj hij g hg
    apply Classical.byContradiction
    intro hnot
    have hval : value v i (bundle goods X i) < value v i ((bundle goods X j).erase g) := by
      omega
    obtain ⟨T, hmin, hsub, a, ha, hna⟩ :=
      (threat_iff (hgoods.sublist List.filter_sublist)).mp ⟨g, hg, hval⟩
    exact hna (h i hi j hj hij T hmin hsub a ha)

/-- A simultaneous exchange needs new threat certificates only on edges incident to changed
agents. This is a verification theorem, not an assertion that an improving exchange exists. -/
theorem exchange_certificate {v : A → G → Nat} {agents : List A} {goods : List G}
    {X Y : G → A} (hgoods : goods.Nodup) (changed : A → Prop)
    (hX : EFX0L v agents goods X)
    (hkeep : ∀ j ∈ agents, ¬ changed j → bundle goods Y j = bundle goods X j)
    (hown : ∀ i ∈ agents, ¬ changed i →
      value v i (bundle goods X i) ≤ value v i (bundle goods Y i))
    (hcheck : ∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → changed i ∨ changed j →
      ∀ T : List G, Minimal v i (value v i (bundle goods Y i)) T →
        (∀ g ∈ T, g ∈ bundle goods Y j) → ∀ g ∈ bundle goods Y j, g ∈ T) :
    EFX0L v agents goods Y := by
  classical
  intro i hi j hj hij g hg
  by_cases hc : changed i ∨ changed j
  · have hlocal := hcheck i hi j hj hij hc
    apply Nat.le_of_not_lt
    intro hbad
    obtain ⟨T, hmin, hsub, a, ha, hna⟩ :=
      (threat_iff (hgoods.sublist List.filter_sublist)).mp ⟨g, hg, hbad⟩
    exact hna (hlocal T hmin hsub a ha)
  · have hni : ¬ changed i := fun h => hc (Or.inl h)
    have hnj : ¬ changed j := fun h => hc (Or.inr h)
    rw [hkeep j hj hnj] at hg ⊢
    exact Nat.le_trans (hX i hi j hj hij g hg) (hown i hi hni)

end allocations

/-- The characterization refers to the project's original owner-map definition of EFX₀. -/
theorem efx0_iff (I : Inst) (X : I.Alloc) :
    I.EFX0 X ↔ ∀ i j : Fin I.n, i ≠ j → ∀ T : List (Fin I.m),
      Minimal I.v i (I.bundleVal X i i none) T →
      (∀ g ∈ T, X g = j) → ∀ g : Fin I.m, X g = j → g ∈ T := by
  rw [I.efx0_iff X, efx0L_iff (List.nodup_finRange _)]
  simp only [List.mem_finRange, forall_const]
  simp [Inst.bundleVal_none, bundle]

end Threats
end EFX

#print axioms EFX.Threats.exists_minimal
#print axioms EFX.Threats.minimal_relevant
#print axioms EFX.Threats.minimal_antichain
#print axioms EFX.Threats.safe_iff
#print axioms EFX.Threats.safe_append_iff
#print axioms EFX.Threats.minimal_append_unsafe
#print axioms EFX.Threats.safe_append_zero_iff
#print axioms EFX.Threats.threat_iff
#print axioms EFX.Threats.exists_small_minimal
#print axioms EFX.Threats.pair_threat_iff
#print axioms EFX.Threats.efx0L_iff
#print axioms EFX.Threats.exchange_certificate
#print axioms EFX.Threats.efx0_iff
