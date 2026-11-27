import EFX.DE4Repair

/-!
# The lower-pair order and the top swap (`k4/de4.md` §10.4; ledger K4.DE4V3R.LP, K4.DE4V3R.L27)

The robust order (largest robust level sum among (V3)-valid states, then value-Pareto) is refuted
(`k4/de4/refute_rob.py`): a non-completable maximum, GM4-B's double clash. The *lower-pair order* breaks ties inside
the largest robust level sum by the number of lower-pair holders, fewest first, and only then by value-Pareto.

**Results.**
- `BetterLP`, `IsMaximumLP`: the order and its maxima.
- `numLP_le`, `exists_maximumLP`: every instance has a maximum of the lower-pair order (descent along `BetterLP`,
  which raises the measure `(Φ_R · (L + 1) + (L − #LP)) · (V + 1) + Σ_i v_i(Y_i)`).
- `exists_validV3_numLP` (**Lemma R, counting lower pairs**): every valid state has a (V3)-valid state of at least its
  robust level sum and at most its number of lower-pair holders. So a maximum of the lower-pair order has the largest
  robust level sum among all valid states (`potentialR_le_of_maxLP`).
- `topSwap_valid`, `top_swap` (**Lemma 27**): if `u` holds its lower pair, `t` holds `[a]` with `a` worth the top to
  `u`, `j` is a leftover good that `t` values just below `a`, and `t` threatens no holding of three or more goods with
  `v_t(j)`, then the state in which `u` holds `[a]` and `t` holds `[j]` is valid, has at least the robust level sum and
  one lower-pair holder fewer.
- `not_maxLP_of_top_swap`: hence such a state is not a maximum of the lower-pair order (Corollary 28(a) when `a` is
  `t`'s top and `j` its b).
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The lower-pair order: a larger robust level sum; or the same with fewer lower-pair holders; or the same with as
many lower-pair holders and the values Pareto-better. -/
def BetterLP (v : A → G → Nat) (agents : List A) (goods : List G) (base' base : G → Option A) : Prop :=
  potentialR v agents goods base < potentialR v agents goods base' ∨
    (potentialR v agents goods base = potentialR v agents goods base' ∧
      numLP v agents goods base' < numLP v agents goods base) ∨
    (potentialR v agents goods base = potentialR v agents goods base' ∧
      numLP v agents goods base' = numLP v agents goods base ∧
      (∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i)) ∧
      ∃ i ∈ agents, value v i (hold goods base i) < value v i (hold goods base' i))

/-- A maximum of the lower-pair order: a (V3)-valid state that no (V3)-valid state is better than. -/
def IsMaximumLP (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ValidV3 v agents goods base ∧ ∀ base', ValidV3 v agents goods base' → ¬ BetterLP v agents goods base' base

/-! ## Existence of maxima -/

section exists_max
variable (v : A → G → Nat) (agents : List A) (goods : List G)

omit [DecidableEq G] in
theorem numLP_le (base : G → Option A) : numLP v agents goods base ≤ agents.length := by
  classical
  unfold numLP
  have := sum_map_le_mul (l := agents) (c := 1)
    (f := fun i => if IsLowerPair v i goods (hold goods base i) then 1 else 0) (fun i _ => by split <;> omega)
  omega

/-- The measure `(Φ_R · (L + 1) + (L − #LP)) · (V + 1) + Σ_i v_i(Y_i)`, which every `BetterLP` state raises. -/
noncomputable def measureLP (base : G → Option A) : Nat :=
  (potentialR v agents goods base * (agents.length + 1) + (agents.length - numLP v agents goods base)) *
    (bigV v agents goods + 1) + totalValue v agents goods base

theorem lex_lt {x y V T T' : Nat} (hT : T ≤ V) (h : x < y) : x * (V + 1) + T < y * (V + 1) + T' := by
  have h1 : (x + 1) * (V + 1) ≤ y * (V + 1) := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at h1
  omega

theorem measureLP_le (base : G → Option A) :
    measureLP v agents goods base ≤
      (6 * agents.length * (agents.length + 1) + agents.length) * (bigV v agents goods + 1) + bigV v agents goods := by
  have h1 := Nat.mul_le_mul_right (agents.length + 1) (potentialR_le v agents goods base)
  have h2 : potentialR v agents goods base * (agents.length + 1) + (agents.length - numLP v agents goods base) ≤
      6 * agents.length * (agents.length + 1) + agents.length := by omega
  have h3 := Nat.mul_le_mul_right (bigV v agents goods + 1) h2
  have h4 := totalValue_le v agents goods base
  unfold measureLP
  omega

theorem measureLP_lt_of_better {base base' : G → Option A} (h : BetterLP v agents goods base' base) :
    measureLP v agents goods base < measureLP v agents goods base' := by
  unfold measureLP
  have hT := totalValue_le v agents goods base
  have hN := numLP_le v agents goods base
  have hN' := numLP_le v agents goods base'
  rcases h with hP | ⟨hP, hlt⟩ | ⟨hP, hNe, hle, hlt⟩
  · apply lex_lt hT
    exact lex_lt (Nat.sub_le _ _) hP
  · apply lex_lt hT
    rw [hP]
    omega
  · have : totalValue v agents goods base < totalValue v agents goods base' := sum_map_lt hle hlt
    rw [hP, hNe]
    omega

/-- From any (V3)-valid state, descent along `BetterLP` reaches a maximum of the lower-pair order. -/
theorem exists_maximumLP_of_valid {base : G → Option A} (hb : ValidV3 v agents goods base) :
    ∃ m, IsMaximumLP v agents goods m := by
  let M := (6 * agents.length * (agents.length + 1) + agents.length) * (bigV v agents goods + 1) +
    bigV v agents goods
  suffices key : ∀ k, ∀ b, ValidV3 v agents goods b → M - measureLP v agents goods b ≤ k →
      ∃ m, IsMaximumLP v agents goods m from key _ base hb (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro b hb hk
    refine ⟨b, hb, fun b' _ hbet => ?_⟩
    have := measureLP_lt_of_better v agents goods hbet
    have := measureLP_le v agents goods b'
    omega
  | succ k ih =>
    intro b hb hk
    by_cases hmax : ∀ b', ValidV3 v agents goods b' → ¬ BetterLP v agents goods b' b
    · exact ⟨b, hb, hmax⟩
    · obtain ⟨b', hb'⟩ := Classical.not_forall.mp hmax
      have hv' : ValidV3 v agents goods b' := Classical.byContradiction fun hn => hb' fun h => absurd h hn
      have hbet : BetterLP v agents goods b' b := Classical.byContradiction fun hn => hb' fun _ => hn
      have := measureLP_lt_of_better v agents goods hbet
      have := measureLP_le v agents goods b'
      exact ih b' hv' (by omega)

variable {v agents goods}

/-- Every instance has a maximum of the lower-pair order. -/
theorem exists_maximumLP (hag : agents.Nodup) (hgd : goods.Nodup) : ∃ base, IsMaximumLP v agents goods base :=
  exists_maximumLP_of_valid v agents goods ⟨draft_valid hag hgd, draft_v3 v hag hgd⟩

end exists_max

/-! ## Lemma R, counting lower pairs -/

section lemmaR'
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **Lemma R, counting lower pairs**: every valid state has a (V3)-valid state whose robust level sum is at least as
large and whose number of lower-pair holders is at most as large. -/
theorem exists_validV3_numLP (hgd : goods.Nodup) :
    ∀ (k : Nat) (base : G → Option A), numLP v agents goods base ≤ k → Valid v agents goods base →
      ∃ base', ValidV3 v agents goods base' ∧ potentialR v agents goods base ≤ potentialR v agents goods base' ∧
        numLP v agents goods base' ≤ numLP v agents goods base := by
  intro k
  induction k with
  | zero =>
    intro base hk hb
    refine ⟨base, ⟨hb, fun i hi hlp => ?_⟩, Nat.le_refl _, Nat.le_refl _⟩
    exfalso
    unfold numLP at hk
    have := le_zero_mem hk hi
    simp only [hlp, ite_true] at this
    exact absurd this (by decide)
  | succ k ih =>
    intro base hk hb
    by_cases h3 : V3 v agents goods base
    · exact ⟨base, ⟨hb, h3⟩, Nat.le_refl _, Nat.le_refl _⟩
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
      obtain ⟨base'', h1, h2, h3⟩ := ih _ (by omega) hb'
      exact ⟨base'', h1, Nat.le_trans hpot h2, by omega⟩

/-- A maximum of the lower-pair order has the largest robust level sum among all valid states. -/
theorem potentialR_le_of_maxLP (hgd : goods.Nodup) {base base' : G → Option A}
    (hmax : IsMaximumLP v agents goods base) (hb' : Valid v agents goods base') :
    potentialR v agents goods base' ≤ potentialR v agents goods base := by
  obtain ⟨base'', h1, h2, _⟩ := exists_validV3_numLP hgd _ base' (Nat.le_refl _) hb'
  exact Nat.le_trans h2 (Nat.le_of_not_lt fun hlt => hmax.2 base'' h1 (Or.inl hlt))

end lemmaR'

/-! ## Lemma 27: the top swap -/

section topswap
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- The state after the top swap: `u` holds `a` alone, `t` holds `j` alone, and `u`'s other goods are released. -/
def topSwap (base : G → Option A) (u t : A) (a j : G) : G → Option A :=
  fun g => if g = a then some u else if g = j then some t else if base g = some u then none else base g

omit [DecidableEq A] [DecidableEq G] in
theorem filter_len_le {l : List G} {p q : G → Bool} (h : ∀ g ∈ l, p g = true → q g = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left h

omit [DecidableEq A] in
theorem filter_len_le_succ {l : List G} (hl : l.Nodup) {p q : G → Bool} {a : G}
    (h : ∀ g ∈ l, p g = true → g = a ∨ q g = true) : (l.filter p).length ≤ (l.filter q).length + 1 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hxt := (List.nodup_cons.mp hl).1
    have htn := (List.nodup_cons.mp hl).2
    by_cases hxa : x = a
    · subst hxa
      have ht : ∀ g ∈ t, p g = true → q g = true := by
        intro g hg hpg
        rcases h g (List.mem_cons_of_mem _ hg) hpg with e | e
        · exact absurd (e ▸ hg) hxt
        · exact e
      have := filter_len_le ht
      by_cases hpx : p x = true <;> by_cases hqx : q x = true <;>
        simp [hpx, hqx] <;> omega
    · have ih' := ih htn (fun g hg hpg => h g (List.mem_cons_of_mem _ hg) hpg)
      by_cases hpx : p x = true
      · have hqx : q x = true := by
          rcases h x (by simp) hpx with e | e
          · exact absurd e hxa
          · exact e
        simp [hpx, hqx]; omega
      · by_cases hqx : q x = true <;> simp [hpx, hqx] <;> omega

omit [DecidableEq G] in
theorem sum_map_ind_zero {l : List A} {u : A} (hu : u ∉ l) (f : A → Nat) :
    (l.map (fun i => f i + if i = u then 1 else 0)).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hxu : x ≠ u := fun e => hu (e ▸ List.mem_cons_self)
    have := ih (fun h => hu (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.sum_cons, hxu, ite_false] at this ⊢
    omega

omit [DecidableEq G] in
theorem sum_map_ind {l : List A} (hl : l.Nodup) {u : A} (hu : u ∈ l) (f : A → Nat) :
    (l.map (fun i => f i + if i = u then 1 else 0)).sum = (l.map f).sum + 1 := by
  induction l with
  | nil => simp at hu
  | cons x t ih =>
    have hxt := (List.nodup_cons.mp hl).1
    by_cases hxu : x = u
    · subst hxu
      have := sum_map_ind_zero hxt f
      simp only [List.map_cons, List.sum_cons, ite_true] at this ⊢
      omega
    · have hut : u ∈ t := by
        rcases List.mem_cons.mp hu with e | e
        · exact absurd e.symm hxu
        · exact e
      have := ih (List.nodup_cons.mp hl).2 hut
      simp only [List.map_cons, List.sum_cons, hxu, ite_false] at this ⊢
      omega

omit [DecidableEq A] in
theorem levelR_single (i : A) (g : G) (hg : g ∈ goods) : levelR v i goods [g] = level v i goods [g] := by
  unfold levelR
  have : ¬ (IsUpper v i goods [g] ∧ IsRobust v i goods [g]) := fun h => by
    have h1 := h.1.2.1
    rw [value_singleton] at h1
    have := le_topV v i goods hg
    omega
  simp only [this, ↓reduceIte]

omit [DecidableEq A] in
theorem levelR_lowerPair {i : A} {S : List G} (hlp : IsLowerPair v i goods S) : levelR v i goods S = 3 := by
  unfold levelR
  have hnu : ¬ (IsUpper v i goods S ∧ IsRobust v i goods S) :=
    fun h => by have := h.1.2.1; have := hlp.2.2.2.1; omega
  simp only [hnu, ↓reduceIte]
  rw [level_multi v i goods (by have := hlp.2.1; omega)]
  have := hlp.2.2.2.1
  simp only [show ¬ topV v i goods < value v i S by omega, ↓reduceIte]

/-- The hypotheses of Lemma 27 on a valid state. -/
structure TopSwapHyp (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (u t : A) (a j : G) :
    Prop where
  hu : u ∈ agents
  ht : t ∈ agents
  hut : u ≠ t
  hlp : IsLowerPair v u goods (hold goods base u)
  ha : a ∈ goods
  hat : v u a = topV v u goods
  hta : hold goods base t = [a]
  hj : j ∈ goods
  hjn : base j = none
  hj0 : 0 < v t j
  hja : v t j < v t a
  /-- `j` is just below `a` for `t`: a good other than `a` worth more than `j` is worth more than `a` -/
  hjust : ∀ g ∈ goods, g ≠ a → v t j < v t g → v t a < v t g
  /-- `t` threatens no holding of three or more goods with `v_t(j)` -/
  htrip : ∀ y ∈ agents, y ≠ u → y ≠ t → 3 ≤ (hold goods base y).length →
    ∀ h ∈ hold goods base y, value v t ((hold goods base y).erase h) ≤ v t j

variable {base : G → Option A} {u t : A} {a j : G}

theorem TopSwapHyp.base_a (H : TopSwapHyp v agents goods base u t a j) : base a = some t :=
  (mem_hold.mp (by rw [H.hta]; simp : a ∈ hold goods base t)).2

theorem TopSwapHyp.eq_a (H : TopSwapHyp v agents goods base u t a j) {g : G} (hg : g ∈ goods)
    (h : base g = some t) : g = a := by
  have : g ∈ hold goods base t := mem_hold.mpr ⟨hg, h⟩
  rw [H.hta] at this; simpa using this

theorem TopSwapHyp.ne_aj (H : TopSwapHyp v agents goods base u t a j) : a ≠ j := by
  intro e; have := H.base_a; rw [e, H.hjn] at this; simp at this

theorem hold_topSwap_u (hgd : goods.Nodup) (H : TopSwapHyp v agents goods base u t a j) :
    hold goods (topSwap base u t a j) u = [a] := by
  have : hold goods (topSwap base u t a j) u = goods.filter (fun g => decide (g = a)) := by
    unfold hold topSwap
    apply List.filter_congr
    intro g _
    by_cases hga : g = a
    · simp [hga]
    · by_cases hgj : g = j
      · simp [hgj, Ne.symm H.hut]
      · by_cases hbu : base g = some u <;> simp [hga, hgj, hbu]
  rw [this]; exact filter_eq_single hgd H.ha

theorem hold_topSwap_t (hgd : goods.Nodup) (H : TopSwapHyp v agents goods base u t a j) :
    hold goods (topSwap base u t a j) t = [j] := by
  have : hold goods (topSwap base u t a j) t = goods.filter (fun g => decide (g = j)) := by
    unfold hold topSwap
    apply List.filter_congr
    intro g hg
    by_cases hga : g = a
    · subst hga; simp [H.hut, H.ne_aj]
    · by_cases hgj : g = j
      · simp [hgj, Ne.symm H.ne_aj]
      · by_cases hbu : base g = some u
        · simp [hga, hgj, hbu]
        · have hbt : base g ≠ some t := fun h => hga (H.eq_a hg h)
          simp [hga, hgj, hbu, hbt]
  rw [this]; exact filter_eq_single hgd H.hj

theorem hold_topSwap_other (H : TopSwapHyp v agents goods base u t a j) {i : A} (hiu : i ≠ u) (hit : i ≠ t) :
    hold goods (topSwap base u t a j) i = hold goods base i := by
  unfold hold topSwap
  apply List.filter_congr
  intro g _
  by_cases hga : g = a
  · subst hga; simp [H.base_a, Ne.symm hiu, Ne.symm hit]
  · by_cases hgj : g = j
    · subst hgj; simp [hga, H.hjn, Ne.symm hit]
    · by_cases hbu : base g = some u
      · simp [hga, hgj, hbu, Ne.symm hiu]
      · simp [hga, hgj, hbu]

theorem topSwap_valid (hgd : goods.Nodup) (hb : Valid v agents goods base)
    (H : TopSwapHyp v agents goods base u t a j) : Valid v agents goods (topSwap base u t a j) := by
  have hU := hold_topSwap_u hgd H
  have hT := hold_topSwap_t hgd H
  have hO := fun {i : A} (h1 : i ≠ u) (h2 : i ≠ t) => hold_topSwap_other H h1 h2
  have hlen : (hold goods base u).length = 2 := H.hlp.2.1
  have hva : value v u (hold goods base u) < v u a := by rw [H.hat]; exact H.hlp.2.2.2.1
  -- a good held alone in `base` by an agent other than `u` and `t` is still held alone
  have halone : ∀ k ∈ agents, ∀ g, hold goods base k = [g] → ∃ k' ∈ agents, hold goods (topSwap base u t a j) k' = [g] := by
    intro k hk g hkg
    by_cases hku : k = u
    · subst hku; rw [hkg] at hlen; simp at hlen
    · by_cases hkt : k = t
      · subst hkt
        have : g = a := by rw [H.hta] at hkg; simpa using hkg.symm
        subst this; exact ⟨u, H.hu, hU⟩
      · exact ⟨k, hk, by rw [hO hku hkt]; exact hkg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- owners
    intro g hg k hk
    unfold topSwap at hk
    by_cases hga : g = a
    · simp [hga] at hk; subst hk; exact H.hu
    · by_cases hgj : g = j
      · simp [hgj, Ne.symm H.ne_aj] at hk; subst hk; exact H.ht
      · by_cases hbu : base g = some u
        · simp [hga, hgj, hbu] at hk
        · simp [hga, hgj, hbu] at hk; exact hb.owners g hg k hk
  · -- allowed
    intro i hi
    by_cases hiu : i = u
    · subst hiu; rw [hU]
      exact Or.inl ⟨by simp, fun g hg => by
        simp at hg; subst hg; have := H.hlp.2.2.2.1; omega⟩
    · by_cases hit : i = t
      · subst hit; rw [hT]
        exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; exact H.hj0⟩
      · rw [hO hiu hit]; exact hb.allowed i hi
  · -- (V1)
    intro i hi g hg hlt
    by_cases hiu : i = u
    · subst hiu; rw [hU, value_singleton, H.hat] at hlt
      have := le_topV v i goods hg; omega
    · by_cases hit : i = t
      · subst hit; rw [hT, value_singleton] at hlt
        by_cases hga : g = a
        · subst hga; exact ⟨u, H.hu, hU⟩
        · have h1 := H.hjust g hg hga hlt
          have h2 : value v i (hold goods base i) < v i g := by rw [H.hta, value_singleton]; exact h1
          obtain ⟨k, hk, hkg⟩ := hb.v1 i hi g hg h2
          exact halone k hk g hkg
      · rw [hO hiu hit] at hlt
        obtain ⟨k, hk, hkg⟩ := hb.v1 i hi g hg hlt
        exact halone k hk g hkg
  · -- (V2)
    intro i hi k hk hik h hh
    by_cases hku : k = u
    · subst hku; rw [hU] at hh ⊢; simp at hh; subst hh; simp
    · by_cases hkt : k = t
      · subst hkt; rw [hT] at hh ⊢; simp at hh; subst hh; simp
      · rw [hO hku hkt] at hh ⊢
        by_cases hiu : i = u
        · subst hiu; rw [hU, value_singleton]
          have := hb.v2 i hi k hk hik h hh
          omega
        · by_cases hit : i = t
          · subst hit; rw [hT, value_singleton]
            by_cases h3 : 3 ≤ (hold goods base k).length
            · exact H.htrip k hk hku hkt h3 h hh
            · have hl1 : ((hold goods base k).erase h).length ≤ 1 := by
                rw [List.length_erase_of_mem hh]; omega
              match he : (hold goods base k).erase h, hl1 with
              | [], _ => simp
              | [g'], _ =>
                have hg'm : g' ∈ hold goods base k := List.mem_of_mem_erase (by rw [he]; simp)
                rw [value_singleton]
                refine Nat.le_of_not_lt fun hlt => ?_
                have hg'g := (mem_hold.mp hg'm).1
                have hbk := (mem_hold.mp hg'm).2
                have hg'a : g' ≠ a := fun e => by
                  rw [e, H.base_a] at hbk; exact hkt (Option.some.inj hbk).symm
                have h1 := H.hjust g' hg'g hg'a hlt
                have h2 : value v i (hold goods base i) < v i g' := by rw [H.hta, value_singleton]; exact h1
                obtain ⟨k', _, hk'g⟩ := hb.v1 i hi g' hg'g h2
                have hk'k : k' = k := by
                  have : g' ∈ hold goods base k' := by rw [hk'g]; simp
                  rw [(mem_hold.mp this).2] at hbk; exact Option.some.inj hbk
                subst hk'k
                have := List.length_erase_of_mem hh
                rw [he, hk'g] at this; simp at this
          · rw [hO hiu hit]; exact hb.v2 i hi k hk hik h hh

theorem topSwap_numLP (H : TopSwapHyp v agents goods base u t a j) (hgd : goods.Nodup) :
    numLP v agents goods (topSwap base u t a j) < numLP v agents goods base := by
  classical
  have hU := hold_topSwap_u hgd H
  have hT := hold_topSwap_t hgd H
  unfold numLP
  apply sum_map_lt
  · intro i _
    by_cases hiu : i = u
    · subst hiu
      have : ¬ IsLowerPair v i goods (hold goods (topSwap base i t a j) i) := by
        rw [hU]; intro h; have := h.2.1; simp at this
      simp [this]
    · by_cases hit : i = t
      · subst hit
        have : ¬ IsLowerPair v i goods (hold goods (topSwap base u i a j) i) := by
          rw [hT]; intro h; have := h.2.1; simp at this
        simp [this]
      · rw [hold_topSwap_other H hiu hit]; exact Nat.le_refl _
  · refine ⟨u, H.hu, ?_⟩
    have : ¬ IsLowerPair v u goods (hold goods (topSwap base u t a j) u) := by
      rw [hU]; intro h; have := h.2.1; simp at this
    simp [this, H.hlp]

theorem topSwap_potentialR (hag : agents.Nodup) (hgd : goods.Nodup) (H : TopSwapHyp v agents goods base u t a j) :
    potentialR v agents goods base ≤ potentialR v agents goods (topSwap base u t a j) := by
  have hU := hold_topSwap_u hgd H
  have hT := hold_topSwap_t hgd H
  let F := fun i => levelR v i goods (hold goods base i)
  let Gf := fun i => levelR v i goods (hold goods (topSwap base u t a j) i)
  -- u rises by one, t drops by at most one
  have hFu : F u = 3 := levelR_lowerPair H.hlp
  have hGu : Gf u = 4 := by
    show levelR v u goods (hold goods (topSwap base u t a j) u) = 4
    rw [hU, levelR_single u a H.ha, level_single]
    have : ((relevant v u goods).filter (fun g' => decide (v u a < v u g'))).length = 0 := by
      have h0 := filter_len_le (l := relevant v u goods) (p := fun g' => decide (v u a < v u g'))
        (q := fun _ => false) (fun g hg hp => by
          have := le_topV v u goods (List.mem_filter.mp hg).1
          have := H.hat
          simp only [decide_eq_true_eq] at hp; omega)
      have h1 : ((relevant v u goods).filter (fun _ => false)).length = 0 := by simp
      omega
    omega
  have hFt : F t ≤ Gf t + 1 := by
    show levelR v t goods (hold goods base t) ≤ levelR v t goods (hold goods (topSwap base u t a j) t) + 1
    rw [H.hta, hT, levelR_single t a H.ha, levelR_single t j H.hj, level_single, level_single]
    have := filter_len_le_succ (l := relevant v t goods) (hgd.filter _) (p := fun g' => decide (v t j < v t g'))
      (q := fun g' => decide (v t a < v t g')) (a := a) (fun g hg hp => by
        simp only [decide_eq_true_eq] at hp ⊢
        by_cases hga : g = a
        · exact Or.inl hga
        · exact Or.inr (H.hjust g (List.mem_filter.mp hg).1 hga hp))
    omega
  have hpt : ∀ i ∈ agents, F i + (if i = u then 1 else 0) ≤ Gf i + (if i = t then 1 else 0) := by
    intro i _
    by_cases hiu : i = u
    · subst hiu; simp [H.hut, hFu, hGu]
    · by_cases hit : i = t
      · subst hit; simp [hiu]; exact hFt
      · simp [hiu, hit]
        show levelR v i goods (hold goods base i) ≤ levelR v i goods (hold goods (topSwap base u t a j) i)
        rw [hold_topSwap_other H hiu hit]
        exact Nat.le_refl _
  have h1 := sum_map_le hpt
  rw [sum_map_ind hag H.hu, sum_map_ind hag H.ht] at h1
  show (agents.map F).sum ≤ (agents.map Gf).sum
  omega

/-- **Lemma 27 (the top swap)** (`k4/de4.md` §10.4): the swapped state is valid, has at least the robust level sum
and one lower-pair holder fewer. -/
theorem top_swap (hag : agents.Nodup) (hgd : goods.Nodup) (hb : Valid v agents goods base)
    (H : TopSwapHyp v agents goods base u t a j) :
    Valid v agents goods (topSwap base u t a j) ∧
      potentialR v agents goods base ≤ potentialR v agents goods (topSwap base u t a j) ∧
      numLP v agents goods (topSwap base u t a j) < numLP v agents goods base :=
  ⟨topSwap_valid hgd hb H, topSwap_potentialR hag hgd H, topSwap_numLP H hgd⟩

/-- **Lemma 27 at a maximum**: a maximum of the lower-pair order admits no top swap. With Lemma R the swapped state
gives a (V3)-valid state of larger robust level sum, or of the same one with fewer lower-pair holders. -/
theorem not_maxLP_of_top_swap (hag : agents.Nodup) (hgd : goods.Nodup) (hmax : IsMaximumLP v agents goods base)
    (H : TopSwapHyp v agents goods base u t a j) : False := by
  obtain ⟨hZ, hP, hN⟩ := top_swap hag hgd hmax.1.1 H
  obtain ⟨Z', hZ', hP', hN'⟩ := exists_validV3_numLP hgd _ _ (Nat.le_refl _) hZ
  rcases Nat.lt_or_eq_of_le (Nat.le_trans hP hP') with hlt | heq
  · exact hmax.2 Z' hZ' (Or.inl hlt)
  · exact hmax.2 Z' hZ' (Or.inr (Or.inl ⟨heq, by omega⟩))

end topswap

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.numLP_le
#print axioms EFX.DE4.lex_lt
#print axioms EFX.DE4.measureLP_le
#print axioms EFX.DE4.measureLP_lt_of_better
#print axioms EFX.DE4.exists_maximumLP_of_valid
#print axioms EFX.DE4.exists_maximumLP
#print axioms EFX.DE4.exists_validV3_numLP
#print axioms EFX.DE4.potentialR_le_of_maxLP
#print axioms EFX.DE4.filter_len_le
#print axioms EFX.DE4.filter_len_le_succ
#print axioms EFX.DE4.sum_map_ind_zero
#print axioms EFX.DE4.sum_map_ind
#print axioms EFX.DE4.levelR_single
#print axioms EFX.DE4.levelR_lowerPair
#print axioms EFX.DE4.TopSwapHyp.base_a
#print axioms EFX.DE4.TopSwapHyp.eq_a
#print axioms EFX.DE4.TopSwapHyp.ne_aj
#print axioms EFX.DE4.hold_topSwap_u
#print axioms EFX.DE4.hold_topSwap_t
#print axioms EFX.DE4.hold_topSwap_other
#print axioms EFX.DE4.topSwap_valid
#print axioms EFX.DE4.topSwap_numLP
#print axioms EFX.DE4.topSwap_potentialR
#print axioms EFX.DE4.top_swap
#print axioms EFX.DE4.not_maxLP_of_top_swap
