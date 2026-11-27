import EFX.DE4RobustA

/-!
# Lemma R (repair) in the robust order (`k4/de4.md` §9; ledger K4.DE4V3R.LEAN)

**Lemma R.** From a valid state, repeatedly let an agent holding its lower pair {c, d} while a relevant good below its
top (its b) is leftover take that good alone instead. Each step keeps the state valid and does not lower the robust
level sum, and the process ends in a (V3)-valid state.

**Results.**
- `above_top`: for a lower-pair holder whose relevant good `g` outside the pair is below the top, every relevant good
  worth more than `g` is worth the top (a 4-good agent has no fifth relevant good).
- `repair_step`: one step of Lemma R is valid, changes only the switched agent's holding (to that one good) and does
  not lower the robust level sum.
- `exists_validV3_of_valid` (**Lemma R**): every valid state has a (V3)-valid state of at least its robust level sum.
- `potentialR_le_of_max`: hence a maximum of the robust order has the largest robust level sum among all valid
  states, not only the (V3)-valid ones: tool (M1) of `k4/de4.md` §10.1.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section repair
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem nodup5 {a b c d e : G} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : [a, b, c, d, e].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

omit [DecidableEq A] [DecidableEq G] in
/-- Four relevant goods leave no room for five distinct ones. -/
theorem not_five {u : A} (h4 : (relevant v u goods).length = 4) {a b c d e : G}
    (hnd : [a, b, c, d, e].Nodup) (hsub : ∀ x ∈ [a, b, c, d, e], x ∈ relevant v u goods) : False := by
  have := List.Nodup.length_le_of_subset hnd hsub
  simp at this
  omega

omit [DecidableEq A] [DecidableEq G] in
theorem ne_of_val_lt (v : A → G → Nat) (u : A) {x y : G} (h : v u x < v u y) : x ≠ y := fun e => by subst e; omega

omit [DecidableEq A] [DecidableEq G] in
theorem mem_relevant {u : A} {g : G} : g ∈ relevant v u goods ↔ g ∈ goods ∧ 0 < v u g := by
  simp [relevant]

omit [DecidableEq A] [DecidableEq G] in
/-- For a lower-pair holder `S` and a relevant good `g` outside it below the top, every relevant good worth more than
`g` is worth the top. -/
theorem above_top {u : A} {S : List G} (hlp : IsLowerPair v u goods S) (hSnd : S.Nodup)
    (hSg : ∀ s ∈ S, s ∈ goods) {g : G} (hg : g ∈ relevant v u goods) (hgS : g ∉ S)
    (hgt : v u g < topV v u goods) {x : G} (hx : x ∈ relevant v u goods) (hgx : v u g < v u x) :
    topV v u goods ≤ v u x := by
  refine Nat.le_of_not_lt fun hxt => ?_
  obtain ⟨s1, s2, hS⟩ := pair_of_length hlp.2.1
  subst hS
  have h12 : s1 ≠ s2 := by simp at hSnd; exact hSnd
  have hs1 : v u s1 < v u g := hlp.2.2.2.2.1 s1 (by simp) g hg hgS
  have hs2 : v u s2 < v u g := hlp.2.2.2.2.1 s2 (by simp) g hg hgS
  obtain ⟨t, htg, htv⟩ := exists_topV v u goods (by omega)
  have ht : t ∈ relevant v u goods := mem_relevant.mpr ⟨htg, by omega⟩
  have hr1 : s1 ∈ relevant v u goods := mem_relevant.mpr ⟨hSg s1 (by simp), hlp.2.2.1 s1 (by simp)⟩
  have hr2 : s2 ∈ relevant v u goods := mem_relevant.mpr ⟨hSg s2 (by simp), hlp.2.2.1 s2 (by simp)⟩
  exact not_five hlp.1 (a := s1) (b := s2) (c := g) (d := x) (e := t)
    (nodup5 h12 (ne_of_val_lt v u hs1) (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u hs2)
      (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u hgx) (ne_of_val_lt v u (by omega))
      (ne_of_val_lt v u (by omega)))
    (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption)

omit [DecidableEq A] [DecidableEq G] in
/-- The good `g` of `above_top` has at most one relevant good worth more (so one good has level at least 3). -/
theorem count_above_le_one {u : A} {S : List G} (hgd : goods.Nodup) (hlp : IsLowerPair v u goods S)
    (hSnd : S.Nodup) (hSg : ∀ s ∈ S, s ∈ goods) {g : G} (hg : g ∈ relevant v u goods) (hgS : g ∉ S)
    (hgt : v u g < topV v u goods) :
    ((relevant v u goods).filter (fun g' => decide (v u g < v u g'))).length ≤ 1 := by
  refine length_le_one_of_eq ((hgd.filter _).filter _) fun a ha b hb => Classical.byContradiction fun hab => ?_
  have ha' := List.mem_filter.mp ha
  have hb' := List.mem_filter.mp hb
  have hga : v u g < v u a := of_decide_eq_true ha'.2
  have hgb : v u g < v u b := of_decide_eq_true hb'.2
  obtain ⟨s1, s2, hS⟩ := pair_of_length hlp.2.1
  subst hS
  have h12 : s1 ≠ s2 := by simp at hSnd; exact hSnd
  have hs1 : v u s1 < v u g := hlp.2.2.2.2.1 s1 (by simp) g hg hgS
  have hs2 : v u s2 < v u g := hlp.2.2.2.2.1 s2 (by simp) g hg hgS
  have hr1 : s1 ∈ relevant v u goods := mem_relevant.mpr ⟨hSg s1 (by simp), hlp.2.2.1 s1 (by simp)⟩
  have hr2 : s2 ∈ relevant v u goods := mem_relevant.mpr ⟨hSg s2 (by simp), hlp.2.2.1 s2 (by simp)⟩
  have hra := ha'.1
  have hrb := hb'.1
  exact not_five hlp.1 (a := s1) (b := s2) (c := g) (d := a) (e := b)
    (nodup5 h12 (ne_of_val_lt v u hs1) (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u hs2)
      (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u (by omega)) (ne_of_val_lt v u hga) (ne_of_val_lt v u hgb) hab)
    (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption)

omit [DecidableEq A] [DecidableEq G] in
theorem value_zero {u : A} : ∀ {l : List G}, (∀ x ∈ l, v u x = 0) → value v u l = 0
  | [], _ => by simp [value]
  | x :: t, h => by
    have h1 := h x (by simp)
    have h2 := value_zero (l := t) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [value, List.map_cons, List.sum_cons] at h2 ⊢
    omega

omit [DecidableEq G] in
theorem hold_nodup (hgd : goods.Nodup) (base : G → Option A) (i : A) : (hold goods base i).Nodup :=
  hgd.filter _

/-- **One step of Lemma R.** A lower-pair holder `u` whose relevant good `g` below its top is leftover takes `{g}`
alone: the state stays valid, only `u`'s holding changes, and the robust level sum does not drop. -/
theorem repair_step {base : G → Option A} (hb : Valid v agents goods base) (hgd : goods.Nodup) {u : A}
    (hu : u ∈ agents) (hlp : IsLowerPair v u goods (hold goods base u)) {g : G} (hg : g ∈ relevant v u goods)
    (hgS : g ∉ hold goods base u) (hgt : v u g < topV v u goods) (hgn : base g = none) :
    Valid v agents goods (retake base u (fun h => decide (h = g))) ∧
      hold goods (retake base u (fun h => decide (h = g))) u = [g] ∧
      (∀ i, i ≠ u → hold goods (retake base u (fun h => decide (h = g))) i = hold goods base i) ∧
      potentialR v agents goods base ≤ potentialR v agents goods (retake base u (fun h => decide (h = g))) := by
  have hgg : g ∈ goods := (mem_relevant.mp hg).1
  have hg0 : 0 < v u g := (mem_relevant.mp hg).2
  have hp : ∀ h ∈ goods, decide (h = g) = true → base h = some u ∨ base h = none := by
    intro h _ e
    have : h = g := of_decide_eq_true e
    subst this; exact Or.inr hgn
  have hself : hold goods (retake base u (fun h => decide (h = g))) u = [g] := by
    rw [hold_retake_self]; exact filter_eq_single hgd hgg
  have hother : ∀ i, i ≠ u → hold goods (retake base u (fun h => decide (h = g))) i = hold goods base i :=
    fun i hi => hold_retake_other hp hi
  have hSnd := hold_nodup hgd base u
  have hSg : ∀ s ∈ hold goods base u, s ∈ goods := fun s hs => (mem_hold.mp hs).1
  have hlen2 := hlp.2.1
  -- a good worth more to `u` than `g` is worth the top, so `u` wanted it and it is held alone
  have hwant : ∀ x ∈ goods, v u g < v u x → ∃ j ∈ agents, j ≠ u ∧ hold goods base j = [x] := by
    intro x hx hgx
    have hxr : x ∈ relevant v u goods := mem_relevant.mpr ⟨hx, by omega⟩
    have htop := above_top hlp hSnd hSg hg hgS hgt hxr hgx
    have hw : value v u (hold goods base u) < v u x := Nat.lt_of_lt_of_le hlp.2.2.2.1 htop
    obtain ⟨j, hj, hjx⟩ := hb.v1 u hu x hx hw
    refine ⟨j, hj, fun e => ?_, hjx⟩
    subst e; rw [hjx] at hlen2; simp at hlen2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hself, hother, ?_⟩
  · -- owners
    intro h hh j hj
    unfold retake at hj
    by_cases hpg : decide (h = g) = true
    · simp only [hpg, ite_true, Option.some.injEq] at hj; subst hj; exact hu
    · by_cases hbx : base h = some u
      · simp [hpg, hbx] at hj
      · simp only [hpg, hbx, ite_false, Bool.false_eq_true] at hj
        exact hb.owners h hh j hj
  · -- allowed
    intro i hi
    by_cases hiu : i = u
    · subst hiu; rw [hself]; exact Or.inl ⟨by simp, by simpa using hg0⟩
    · rw [hother i hiu]; exact hb.allowed i hi
  · -- (V1)
    intro i hi x hx hlt
    by_cases hiu : i = u
    · subst hiu
      rw [hself, value_singleton] at hlt
      obtain ⟨j, hj, hju, hjx⟩ := hwant x hx hlt
      exact ⟨j, hj, by rw [hother j hju]; exact hjx⟩
    · rw [hother i hiu] at hlt
      obtain ⟨j, hj, hjx⟩ := hb.v1 i hi x hx hlt
      have hju : j ≠ u := by
        rintro rfl; rw [hjx] at hlen2; simp at hlen2
      exact ⟨j, hj, by rw [hother j hju]; exact hjx⟩
  · -- (V2)
    intro i hi j hj hij h hh
    by_cases hju : j = u
    · subst hju
      rw [hself] at hh ⊢
      simp at hh; subst hh; simp [value]
    · rw [hother j hju] at hh ⊢
      by_cases hiu : i = u
      · subst hiu
        rw [hself, value_singleton]
        by_cases hl : (hold goods base j).length ≤ 1
        · have : ((hold goods base j).erase h).length = 0 := by
            rw [List.length_erase_of_mem hh]; omega
          rw [List.length_eq_zero_iff.mp this]; simp [value]
        · -- a holding of two or more goods has no good of `R_u`
          have hz : ∀ x ∈ hold goods base j, v i x = 0 := by
            intro x hx
            refine Classical.byContradiction fun hx0 => ?_
            have hxm := mem_hold.mp hx
            have hxr : x ∈ relevant v i goods := mem_relevant.mpr ⟨hxm.1, by omega⟩
            have hxS : x ∉ hold goods base i := fun h' => by
              have := (mem_hold.mp h').2; rw [hxm.2] at this; exact hju (Option.some.inj this)
            have hxg : x ≠ g := fun e => by rw [e, hgn] at hxm; exact absurd hxm.2 (by simp)
            by_cases hgx : v i g < v i x
            · obtain ⟨j', _, _, hj'x⟩ := hwant x hxm.1 hgx
              have : base x = some j' := (mem_hold.mp (by rw [hj'x]; simp)).2
              rw [hxm.2] at this
              have hjj : j = j' := Option.some.inj this
              subst hjj
              rw [hj'x] at hl; simp at hl
            · -- `x` is worth at most `g`: with the pair, `g` and the top, five relevant goods
              have hxv : v i x ≤ v i g := Nat.le_of_not_lt hgx
              obtain ⟨s1, s2, hS⟩ := pair_of_length hlp.2.1
              have h12 : s1 ≠ s2 := by rw [hS] at hSnd; simp at hSnd; exact hSnd
              have hs1x : v i s1 < v i x := hlp.2.2.2.2.1 s1 (by rw [hS]; simp) x hxr hxS
              have hs2x : v i s2 < v i x := hlp.2.2.2.2.1 s2 (by rw [hS]; simp) x hxr hxS
              obtain ⟨t, htg, htv⟩ := exists_topV v i goods (by omega)
              have ht : t ∈ relevant v i goods := mem_relevant.mpr ⟨htg, by omega⟩
              have hr1 : s1 ∈ relevant v i goods :=
                mem_relevant.mpr ⟨hSg s1 (by rw [hS]; simp), hlp.2.2.1 s1 (by rw [hS]; simp)⟩
              have hr2 : s2 ∈ relevant v i goods :=
                mem_relevant.mpr ⟨hSg s2 (by rw [hS]; simp), hlp.2.2.1 s2 (by rw [hS]; simp)⟩
              exact not_five hlp.1 (a := s1) (b := s2) (c := x) (d := g) (e := t)
                (nodup5 h12 (ne_of_val_lt v i hs1x) (ne_of_val_lt v i (by omega)) (ne_of_val_lt v i (by omega))
                  (ne_of_val_lt v i hs2x) (ne_of_val_lt v i (by omega)) (ne_of_val_lt v i (by omega)) hxg
                  (ne_of_val_lt v i (by omega)) (ne_of_val_lt v i (by omega)))
                (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption)
          have : value v i ((hold goods base j).erase h) = 0 :=
            value_zero fun x hx => hz x (List.mem_of_mem_erase hx)
          omega
      · rw [hother i hiu]
        exact hb.v2 i hi j hj hij h hh
  · -- the robust level sum
    apply sum_map_le
    intro i _
    by_cases hiu : i = u
    · subst hiu
      rw [hself]
      have hS3 : levelR v i goods (hold goods base i) = 3 := by
        unfold levelR
        have hnu : ¬ (IsUpper v i goods (hold goods base i) ∧ IsRobust v i goods (hold goods base i)) :=
          fun h => by have := h.1.2.1; have := hlp.2.2.2.1; omega
        simp only [hnu, ↓reduceIte]
        rw [level_multi v i goods (by omega)]
        have := hlp.2.2.2.1
        simp only [show ¬ topV v i goods < value v i (hold goods base i) by omega, ↓reduceIte]
      have h1 := count_above_le_one hgd hlp hSnd hSg hg hgS hgt
      have h2 := level_le_levelR v i goods [g]
      rw [level_single] at h2
      omega
    · rw [hother i hiu]; exact Nat.le_refl _
end repair

section lemmaR
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] in
theorem le_zero_mem {l : List A} {f : A → Nat} : (l.map f).sum ≤ 0 → ∀ {i}, i ∈ l → f i = 0 := by
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons a t ih =>
    intro h i hi
    simp only [List.map_cons, List.sum_cons] at h
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · exact ih (by omega) hi

open Classical in
/-- The number of listed agents holding their lower pair. -/
noncomputable def numLP (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  (agents.map (fun i => if IsLowerPair v i goods (hold goods base i) then 1 else 0)).sum

/-- **Lemma R** (repair, `k4/de4.md` §9): every valid state has a (V3)-valid state whose robust level sum is at least
as large. -/
theorem exists_validV3_of_valid (hgd : goods.Nodup) :
    ∀ (k : Nat) (base : G → Option A), numLP v agents goods base ≤ k → Valid v agents goods base →
      ∃ base', ValidV3 v agents goods base' ∧ potentialR v agents goods base ≤ potentialR v agents goods base' := by
  intro k
  induction k with
  | zero =>
    intro base hk hb
    refine ⟨base, ⟨hb, fun i hi hlp => ?_⟩, Nat.le_refl _⟩
    exfalso
    unfold numLP at hk
    have := le_zero_mem hk hi
    simp only [hlp, ite_true] at this
    exact absurd this (by decide)
  | succ k ih =>
    intro base hk hb
    by_cases h3 : V3 v agents goods base
    · exact ⟨base, ⟨hb, h3⟩, Nat.le_refl _⟩
    · obtain ⟨u, hu, hlp, g, hg, hgS, hgt, hgn⟩ : ∃ u ∈ agents, IsLowerPair v u goods (hold goods base u) ∧
          ∃ g ∈ relevant v u goods, g ∉ hold goods base u ∧ v u g < topV v u goods ∧ base g = none :=
        Classical.byContradiction fun hno => h3 fun i hi hlp g hg hgS hgt hn => hno ⟨i, hi, hlp, g, hg, hgS, hgt, hn⟩
      obtain ⟨hb', hself, hother, hpot⟩ := repair_step hb hgd hu hlp hg hgS hgt hgn
      have hlt : numLP v agents goods (retake base u (fun h => decide (h = g))) < numLP v agents goods base := by
        unfold numLP
        apply sum_map_lt
        · intro i _
          by_cases hiu : i = u
          · subst hiu
            have : ¬ IsLowerPair v i goods (hold goods (retake base i (fun h => decide (h = g))) i) := by
              rw [hself]; intro h; have := h.2.1; simp at this
            simp [this]
          · rw [hother i hiu]; exact Nat.le_refl _
        · refine ⟨u, hu, ?_⟩
          have : ¬ IsLowerPair v u goods (hold goods (retake base u (fun h => decide (h = g))) u) := by
            rw [hself]; intro h; have := h.2.1; simp at this
          simp [this, hlp]
      obtain ⟨base'', h1, h2⟩ := ih _ (by omega) hb'
      exact ⟨base'', h1, Nat.le_trans hpot h2⟩

/-- A maximum of the robust order has the largest robust level sum among all valid states (Lemma R). -/
theorem potentialR_le_of_max (hgd : goods.Nodup) {base base' : G → Option A}
    (hmax : IsMaximumR v agents goods base) (hb' : Valid v agents goods base') :
    potentialR v agents goods base' ≤ potentialR v agents goods base := by
  obtain ⟨base'', h1, h2⟩ := exists_validV3_of_valid hgd _ base' (Nat.le_refl _) hb'
  refine Nat.le_trans h2 (Nat.le_of_not_lt fun hlt => hmax.2 base'' h1 (Or.inl hlt))

/-- A *top* state: (V3)-valid, with the largest robust level sum among all valid states. Maxima of the robust order
are top states (`topR_of_maxR`), and so are maxima of the lower-pair order (`EFX.DE4.topR_of_maxLP`); the lemmas that
contradict maximality by a larger robust level sum need only this. -/
def TopR (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ValidV3 v agents goods base ∧
    ∀ base', Valid v agents goods base' → potentialR v agents goods base' ≤ potentialR v agents goods base

theorem topR_of_maxR (hgd : goods.Nodup) {base : G → Option A} (hmax : IsMaximumR v agents goods base) :
    TopR v agents goods base :=
  ⟨hmax.1, fun _ hb' => potentialR_le_of_max hgd hmax hb'⟩

end lemmaR

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.nodup5
#print axioms EFX.DE4.not_five
#print axioms EFX.DE4.above_top
#print axioms EFX.DE4.count_above_le_one
#print axioms EFX.DE4.value_zero
#print axioms EFX.DE4.le_zero_mem
#print axioms EFX.DE4.topR_of_maxR
#print axioms EFX.DE4.repair_step
#print axioms EFX.DE4.exists_validV3_of_valid
#print axioms EFX.DE4.potentialR_le_of_max
