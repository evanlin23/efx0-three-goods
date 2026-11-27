import EFX.DE4Three

/-!
# Lemma 18 at a maximum: clean F₂-clash cycles (`k4/de4.md` §10.1, Lemma 18 and Theorem 19; ledger K4.DE4V3R.LEAN)

**Results.**
- `levelR_lt_of_danger`: an agent that does not hold a single good strictly rises in robust level when it takes a
  danger set (an allowed set of two or more goods outside its holding, worth more); `not_two_lowerPairs`.
- `no_clean_clashCycle` (**Lemma 18 at a maximum**): at a maximum of the robust order with (H), no F₂-clash cycle has
  pairwise disjoint labels. The trade along it (frozen givers hand their good, free givers the arc's set, releasing
  their other goods) is valid; if the robust level sum rises, Lemma R contradicts maximality; if not, every agent of
  the cycle is a free holder of one good, and `no_f1_clashCycle` applies.
- `HX` (**(X) fails at maxima**, a hypothesis, never an axiom: every F₂-clash cycle at a maximum is clean),
  `hc2_of_hx` (**Theorem 19 at maxima**), `hx_of_hc3'` (HC3′ implies HX, so HX is weaker), and
  `target4_of_HX_HLL`: **HX and Claim T′ in case (L) imply TARGET₄**.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section strict
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
/-- Two disjoint lower pairs do not exist. -/
theorem not_two_lowerPairs {i : A} {S T : List G} (hS : IsLowerPair v i goods S) (hT : IsLowerPair v i goods T)
    (hSg : ∀ g ∈ S, g ∈ goods) (hTg : ∀ g ∈ T, g ∈ goods) (hdis : ∀ g ∈ T, g ∉ S) : False := by
  obtain ⟨s, t, hst⟩ := pair_of_length hT.2.1
  have ht : s ∈ T := by rw [hst]; simp
  obtain ⟨a, b, hab⟩ := pair_of_length hS.2.1
  have ha : a ∈ S := by rw [hab]; simp
  have hsr : s ∈ relevant v i goods := mem_relevant.mpr ⟨hTg s ht, hT.2.2.1 s ht⟩
  have har : a ∈ relevant v i goods := mem_relevant.mpr ⟨hSg a ha, hS.2.2.1 a ha⟩
  have haT : a ∉ T := fun h => hdis a h ha
  have h1 := hS.2.2.2.2.1 a ha s hsr (hdis s ht)
  have h2 := hT.2.2.2.2.1 s ht a har haT
  omega

omit [DecidableEq A] in
/-- **Strict rise for danger sets.** An agent whose allowed holding `Y` is not a single good strictly rises in robust
level when it takes an allowed set `D` of two or more goods outside `Y`, worth more. -/
theorem levelR_lt_of_danger (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {i : A} (hi : i ∈ agents)
    {Y D : List G} (hY : Allowed v i goods Y) (hYnd : Y.Nodup) (hYg : ∀ g ∈ Y, g ∈ goods)
    (hD : Allowed v i goods D) (hDnd : D.Nodup) (hDg : ∀ g ∈ D, g ∈ goods) (hdis : ∀ g ∈ D, g ∉ Y)
    (hD2 : 2 ≤ D.length) (hlt : value v i Y < value v i D) (hns : ¬ ∃ y, Y = [y]) :
    levelR v i goods Y < levelR v i goods D := by
  have hDl := level_le_levelR v i goods D
  have hD3 := three_le_level_multi v i goods hD2
  have hDcompl : value v i D ≤ value v i (goods.filter (fun g => decide (g ∉ Y))) :=
    value_le_of_subset v i hDnd (hgd.filter _) (fun g hg =>
      List.mem_filter.mpr ⟨hDg g hg, decide_eq_true (hdis g hg)⟩)
  have hDpos : ∀ g ∈ D, 0 < v i g := allowed_pos hD
  rcases hY with ⟨hl1, _⟩ | hup | hlp
  · -- Y is empty
    match hYe : Y, hl1 with
    | [], _ =>
      have : levelR v i goods [] = 0 := by
        unfold levelR
        have : ¬ (IsUpper v i goods [] ∧ IsRobust v i goods []) := fun h => by
          have := h.1.2.1; simp [value] at this
        simp only [this, ↓reduceIte]; rfl
      omega
    | [y], _ => exact absurd ⟨y, rfl⟩ hns
  · -- Y is an upper set; it is not robust, D is the complementary pair and robust
    by_cases hrob : IsRobust v i goods Y
    · unfold IsRobust at hrob; omega
    have hY5 : levelR v i goods Y = 5 := by
      unfold levelR
      simp only [show ¬ (IsUpper v i goods Y ∧ IsRobust v i goods Y) from fun h => hrob h.2, ↓reduceIte]
      rw [level_multi v i goods (two_le_of_upper hup hYg)]
      simp [hup.2.1]
    have hDup : IsUpper v i goods D := isUpper_of_gt_top v hD (Nat.lt_trans hup.2.1 hlt) hDg
    -- counting: Y and D fill the at most four relevant goods
    have hYD : (Y ++ D).Nodup := List.nodup_append.mpr ⟨hYnd, hDnd, fun a ha b hb e => by
      subst e; exact hdis a hb ha⟩
    have hYDr : ∀ g ∈ Y ++ D, g ∈ relevant v i goods := by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact mem_relevant.mpr ⟨hYg g h, hup.1 g h⟩
      · exact mem_relevant.mpr ⟨hDg g h, hDpos g h⟩
    have hY2 := two_le_of_upper hup hYg
    have hR4 := (hc i hi).2.1
    have hlen := List.Nodup.length_le_of_subset hYD hYDr
    simp only [List.length_append] at hlen
    have hall := subset_of_length_le hYD hYDr (by simp only [List.length_append]; omega)
    -- the goods outside D worth anything to i lie in Y
    have hcD : value v i (goods.filter (fun g => decide (g ∉ D))) ≤ value v i Y := by
      rw [← value_filter_pos (v := v) i (goods.filter (fun g => decide (g ∉ D)))]
      refine value_le_of_subset v i ((hgd.filter _).filter _) hYnd fun g hg => ?_
      have h1 := List.mem_filter.mp hg
      have h2 := List.mem_filter.mp h1.1
      have hgr : g ∈ relevant v i goods := mem_relevant.mpr ⟨h2.1, of_decide_eq_true h1.2⟩
      rcases List.mem_append.mp (hall g hgr) with h | h
      · exact h
      · exact absurd h (of_decide_eq_true h2.2)
    have hDrob : IsRobust v i goods D := by unfold IsRobust; omega
    have hD6 : levelR v i goods D = 6 := by unfold levelR; simp [hDup, hDrob]
    omega
  · -- Y is the lower pair: D is an upper set (two disjoint lower pairs do not exist)
    have hY3 : levelR v i goods Y = 3 := by
      unfold levelR
      have : ¬ (IsUpper v i goods Y ∧ IsRobust v i goods Y) := fun h => by
        have := h.1.2.1; have := hlp.2.2.2.1; omega
      simp only [this, ↓reduceIte]
      rw [level_multi v i goods (by have := hlp.2.1; omega)]
      have := hlp.2.2.2.1
      simp only [show ¬ topV v i goods < value v i Y by omega, ↓reduceIte]
    rcases hD with ⟨hl1, _⟩ | hDup | hDlp
    · omega
    · have hl := level_multi v i goods hD2
      have := hDup.2.1
      simp only [show topV v i goods < value v i D from this, ↓reduceIte] at hl
      omega
    · exact absurd (not_two_lowerPairs hlp hDlp hYg hDg hdis) id

end strict

section clean

variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] in
theorem eq_of_sum_eq {l : List A} {f g : A → Nat} (hle : ∀ i ∈ l, f i ≤ g i)
    (heq : (l.map f).sum = (l.map g).sum) : ∀ i ∈ l, f i = g i := by
  intro i hi
  refine Nat.le_antisymm (hle i hi) (Nat.le_of_not_lt fun hlt => ?_)
  have := sum_map_lt hle ⟨i, hi, hlt⟩
  omega

theorem two_le_of_danger {base : G → Option A} {i : A} {D : List G} (hdan : IsDanger v goods base i D) :
    2 ≤ D.length := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := value_le_of_length_le_one' (v := v) i (by omega : D.length ≤ 1) (c := value v i (hold goods base i))
    (fun g hg => (hdan.2.1 g hg).2.2)
  have := hdan.2.2.1
  omega

/-- **Lemma 18 at a top state, for F₂-clash cycles** (`TopR`: a maximum of the robust order or of the lower-pair
order). With (H), on an F₂-clash cycle with pairwise disjoint labels every free agent holds one good. Trade along it:
each agent of the cycle takes the wanted good of a frozen predecessor, or the arc's set from a free one, and the free
givers' other goods become leftover. The trade is valid and no robust level drops. If the robust level sum rises,
Lemma R contradicts maximality. Otherwise no agent of the cycle rose, so every taker held one good and none is frozen. -/
theorem clean_cycle_one_good (hgd : goods.Nodup) (hc : R1Core4 v agents goods) (hs : Strict v agents goods)
    {base : G → Option A} (hmax : TopR v agents goods base) (hH : CondH v agents goods base)
    {x : A → A} {d : A → G → Bool} {C : List A} (hC : ClashCycle v agents goods base x d C)
    (hclean : ∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
      ∀ g ∈ goods, base g = none → d o g = true → d o' g = false) :
    ∀ o ∈ C, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y] := by
  classical
  obtain ⟨hCnd, hCa, hCc, ⟨c, w₀, hcl, hw₀, hcw⟩, harcs, _⟩ := hC
  have hb : Valid v agents goods base := hmax.1.1
  have hU := hH.2
  obtain ⟨hspec, hinj, hcyc, hdef⟩ := cycNext_spec hCnd hCc hcl hw₀ hcw
  -- the free givers release the goods their successor does not take
  let rel : G → Prop := fun g => ∃ o, base g = some o ∧ o ∈ C ∧ ¬ Frozen v agents goods base o ∧ d o g = false
  let base₁ : G → Option A := fun g => if rel g then none else base g
  have hb1 : ∀ g j, base₁ g = some j ↔ base g = some j ∧ ¬ rel g := by
    intro g j
    simp only [base₁]
    by_cases hr : rel g
    · simp [hr]
    · simp [hr]
  have hb1n : ∀ g, base g = none → base₁ g = none := by
    intro g h
    simp only [base₁]
    split
    · rfl
    · exact h
  -- the labels
  let lab : G → Option A := fun g => if base g = none then
    C.find? (fun o => decide (¬ Frozen v agents goods base o ∧ d o g = true)) else none
  have hlabs : ∀ g o, lab g = some o → base g = none ∧ o ∈ C ∧ ¬ Frozen v agents goods base o ∧ d o g = true := by
    intro g o h
    by_cases hg : base g = none
    · simp only [lab, hg, ↓reduceIte] at h
      have h1 := List.find?_some h
      simp only [decide_eq_true_eq] at h1
      exact ⟨hg, List.mem_of_find?_eq_some h, h1⟩
    · simp [lab, hg] at h
  have hlabof : ∀ g ∈ goods, base g = none → ∀ o ∈ C, ¬ Frozen v agents goods base o → d o g = true →
      lab g = some o := by
    intro g hg hn o hoC hnf hd
    have hp : ∀ o' ∈ C, ¬ Frozen v agents goods base o' → d o' g = true → o' = o := by
      intro o' ho'C hnf' hd'
      refine Classical.byContradiction fun hne' => ?_
      have := hclean o hoC o' ho'C (fun e => hne' e.symm) hnf hnf' g hg hn hd
      rw [hd'] at this; exact absurd this (by simp)
    simp only [lab, hn, ↓reduceIte]
    cases hf : C.find? (fun o => decide (¬ Frozen v agents goods base o ∧ d o g = true)) with
    | none =>
      have := List.find?_eq_none.mp hf o hoC
      simp only [decide_eq_true_eq] at this
      exact absurd ⟨hnf, hd⟩ this
    | some a =>
      have h1 := List.find?_some hf
      simp only [decide_eq_true_eq] at h1
      rw [hp a (List.mem_of_find?_eq_some hf) h1.1 h1.2]
  have hlab1 : ∀ g j, lab g = some j → base₁ g = none ∧ cycNext C c w₀ j ≠ none := fun g j h =>
    ⟨hb1n g (hlabs g j h).1, hdef j (hlabs g j h).2.1⟩
  -- what each giver hands on
  have htakF : ∀ j, Frozen v agents goods base j → taken goods base₁ lab j = hold goods base j := by
    intro j hj
    unfold taken hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    constructor
    · rintro (h | h)
      · exact ((hb1 g j).mp h).1
      · exact absurd hj (hlabs g j h).2.2.1
    · intro h
      refine Or.inl ((hb1 g j).mpr ⟨h, ?_⟩)
      rintro ⟨o, ho, _, hnf, _⟩
      rw [h] at ho; cases ho; exact hnf hj
  have htakO : ∀ o ∈ C, ¬ Frozen v agents goods base o → taken goods base₁ lab o = goods.filter (d o) := by
    intro o hoC hnf
    have harc := (harcs o hoC hnf).1
    unfold taken
    apply List.filter_congr
    intro g hg
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · obtain ⟨h1, h2⟩ := (hb1 g o).mp h
        refine Classical.byContradiction fun hd => h2 ⟨o, h1, hoC, hnf, ?_⟩
        simpa using hd
      · exact (hlabs g o h).2.2.2
    · intro hd
      rcases harc.2.2.2.1 g hg hd with h | h
      · refine Or.inl ((hb1 g o).mpr ⟨h, ?_⟩)
        rintro ⟨o', ho', _, _, hdf⟩
        rw [h] at ho'; cases ho'; rw [hd] at hdf; exact absurd hdf (by simp)
      · exact Or.inr (hlabof g hg h o hoC hnf hd)
  -- the trade
  have hrecv : ∀ {p w}, cycNext C c w₀ p = some w →
      hold goods (rotateL base₁ (cycNext C c w₀) lab) w = taken goods base₁ lab p :=
    fun h => rotateL_hold_recv hlab1 hinj hcyc h
  have hoff : ∀ i, i ∉ C → hold goods (rotateL base₁ (cycNext C c w₀) lab) i = hold goods base i := by
    intro i hiC
    have hσi : cycNext C c w₀ i = none := by
      cases h : cycNext C c w₀ i with
      | none => rfl
      | some w => exact absurd (hspec i w h).1 hiC
    unfold hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    rw [rotateL_eq_some hlab1]
    constructor
    · rintro (⟨c', _, e⟩ | ⟨_, h2, _⟩)
      · exact absurd (hspec c' i e).2.1 hiC
      · exact ((hb1 g i).mp h2).1
    · intro h2
      refine Or.inr ⟨?_, (hb1 g i).mpr ⟨h2, ?_⟩, hσi⟩
      · cases hl : lab g with
        | none => rfl
        | some o => rw [(hlabs g o hl).1] at h2; exact absurd h2 (by simp)
      · rintro ⟨o, ho, hoC, _, _⟩
        rw [h2] at ho; cases ho; exact hiC hoC
  -- the danger set of a free giver's arc is an allowed holding of its taker, of at most three goods
  have hdanger : ∀ o ∈ C, ¬ Frozen v agents goods base o →
      Allowed v (x o) goods (goods.filter (d o)) ∧
        value v (x o) (hold goods base (x o)) < value v (x o) (goods.filter (d o)) ∧
        (goods.filter (d o)).length ≤ 3 := by
    intro o hoC hnf
    have harc := (harcs o hoC hnf).1
    have hdan := harc.2.2.1
    have hm := allowed_of_minimal hgd hs hc harc.1 rfl (fun g hg => (List.mem_filter.mp hg).1)
      (fun g hg => mem_goods_of_mem_hold hg) (fun g hg => (hdan.2.1 g hg).2.2)
      (fun g hg hgY => (hdan.2.1 g hg).2.1 (mem_hold.mp hgY).2) (nodup_hold hgd base _) (hb.allowed _ harc.1)
      hdan.2.2.1 hdan.2.2.2
    refine ⟨hm.1, hm.2.1, ?_⟩
    rcases hm.2.2.2 with h | ⟨_, _, _, h⟩ <;> omega
  have hgive : ∀ p w, cycNext C c w₀ p = some w → p ∈ C ∧ w ∈ C ∧ w ∈ agents ∧
      Allowed v w goods (taken goods base₁ lab p) ∧
      value v w (hold goods base w) < value v w (taken goods base₁ lab p) := by
    intro p w h
    obtain ⟨hpC, hwC, hR⟩ := hspec p w h
    refine ⟨hpC, hwC, hCa w hwC, ?_⟩
    rcases hR with ⟨hfp, hW⟩ | ⟨hnf, rfl⟩
    · obtain ⟨_, y, hyg, hy, hlt⟩ := hW
      rw [htakF p hfp, hy]
      refine ⟨Or.inl ⟨by simp, ?_⟩, by rw [value_singleton]; exact hlt⟩
      intro g hg
      simp at hg; subst hg; omega
    · rw [htakO p hpC hnf]
      exact ⟨(hdanger p hpC hnf).1, (hdanger p hpC hnf).2.1⟩
  have hval : ∀ i, value v i (hold goods base i) ≤ value v i (hold goods (rotateL base₁ (cycNext C c w₀) lab) i) := by
    intro i
    by_cases hiC : i ∈ C
    · obtain ⟨p, hp⟩ := (hcyc i).mpr (hdef i hiC)
      rw [hrecv hp]; exact Nat.le_of_lt (hgive p i hp).2.2.2.2
    · rw [hoff i hiC]; exact Nat.le_refl _
  have hvalid : Valid v agents goods (rotateL base₁ (cycNext C c w₀) lab) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- owners
      intro g hg j hj
      rcases (rotateL_eq_some hlab1).mp hj with ⟨c', _, e⟩ | ⟨_, h1, _⟩
      · exact (hgive c' j e).2.2.1
      · exact hb.owners g hg _ ((hb1 g j).mp h1).1
    · -- allowed
      intro i hi
      by_cases hiC : i ∈ C
      · obtain ⟨p, hp⟩ := (hcyc i).mpr (hdef i hiC)
        rw [hrecv hp]; exact (hgive p i hp).2.2.2.1
      · rw [hoff i hiC]; exact hb.allowed i hi
    · -- (V1)
      intro i hi g hg hlt
      obtain ⟨j, hj, hjg⟩ := hb.v1 i hi g hg (Nat.lt_of_le_of_lt (hval i) hlt)
      by_cases hjC : j ∈ C
      · have hjf : Frozen v agents goods base j := ⟨g, hjg, i, hi, Nat.lt_of_le_of_lt (hval i) hlt⟩
        cases hs' : cycNext C c w₀ j with
        | none => exact absurd hs' (hdef j hjC)
        | some w =>
          refine ⟨w, (hgive j w hs').2.2.1, ?_⟩
          rw [hrecv hs', htakF j hjf, hjg]
      · exact ⟨j, hj, by rw [hoff j hjC]; exact hjg⟩
    · -- (V2)
      intro i hi j hj hij hh hhm
      by_cases hjC : j ∈ C
      · obtain ⟨p, hp⟩ := (hcyc j).mpr (hdef j hjC)
        obtain ⟨hpC, _, _, _, _⟩ := hgive p j hp
        rw [hrecv hp] at hhm ⊢
        by_cases hpf : Frozen v agents goods base p
        · rw [htakF p hpf] at hhm ⊢
          obtain ⟨y, hy, _⟩ := hpf
          rw [hy] at hhm ⊢
          simp at hhm; subst hhm; simp [value]
        · rw [htakO p hpC hpf] at hhm ⊢
          have harc := (harcs p hpC hpf).1
          by_cases h3 : 3 ≤ (goods.filter (d p)).length
          · by_cases hip : i = p
            · -- the giver: a threat would be a free self-upgrade of the giver (against (H))
              subst hip
              refine Nat.le_of_not_lt fun hlt => ?_
              have hiC := hpC
              obtain ⟨p', hp'⟩ := (hcyc i).mpr (hdef i hiC)
              rw [hrecv hp'] at hlt
              obtain ⟨hp'C, _, _, hZall, hZgain⟩ := hgive p' i hp'
              have hpi : p' ≠ i := by
                intro e
                subst e
                rcases (hspec p' p' hp').2.2 with ⟨⟨y, hy, _⟩, _, y', _, hy', hlt'⟩ | ⟨_, e⟩
                · rw [hy'] at hlt'; simp [value] at hlt'
                · exact (harcs _ hpC hpf).1.2.1 e.symm
              let q₀ : G → Bool := fun g => d i g && g != hh
              have hq₀ : (goods.filter (d i)).erase hh = goods.filter q₀ := filter_erase_eq hgd (d i) hh
              rw [hq₀] at hlt
              obtain ⟨q', hq', hval', hmin'⟩ := shrink v i hgd _ _ q₀ (Nat.le_refl _) hlt
              have hq'd : ∀ g, q' g = true → d i g = true := by
                intro g hg
                have := hq' g hg
                simp only [q₀, Bool.and_eq_true] at this
                exact this.1
              have hq'h : ∀ g, q' g = true → g ≠ hh := by
                intro g hg
                have := hq' g hg
                simp only [q₀, Bool.and_eq_true, bne_iff_ne] at this
                exact this.2
              have hsrc : ∀ g ∈ goods, q' g = true → base g = some i ∨ base g = none := fun g hg hq =>
                harc.2.2.2.1 g hg (hq'd g hq)
              have hdisZ : ∀ g ∈ goods.filter q', g ∉ taken goods base₁ lab p' := by
                intro g hg hgZ
                have hgg := (List.mem_filter.mp hg).1
                have hdi := hq'd g (List.mem_filter.mp hg).2
                have hZ' := (List.mem_filter.mp hgZ).2
                rw [decide_eq_true_eq] at hZ'
                rcases hsrc g hgg (List.mem_filter.mp hg).2 with hbi | hbn
                · rcases hZ' with h1 | h1
                  · rw [((hb1 g p').mp h1).1] at hbi; exact hpi (Option.some.inj hbi)
                  · rw [(hlabs g p' h1).1] at hbi; exact absurd hbi (by simp)
                · rcases hZ' with h1 | h1
                  · rw [((hb1 g p').mp h1).1] at hbn; exact absurd hbn (by simp)
                  · obtain ⟨_, hp'C', hp'nf, hdp⟩ := hlabs g p' h1
                    have := hclean i hpC p' hp'C' (Ne.symm hpi) hpf hp'nf g hgg hbn hdi
                    rw [hdp] at this; exact absurd this (by simp)
              have hle : ∀ g ∈ goods.filter q', v i g ≤ value v i (taken goods base₁ lab p') := by
                intro g hg
                have hgg := (List.mem_filter.mp hg).1
                refine Nat.le_trans ?_ (Nat.le_of_lt hZgain)
                rcases hsrc g hgg (List.mem_filter.mp hg).2 with hbi | hbn
                · exact le_value_of_mem v i (mem_hold.mpr ⟨hgg, hbi⟩)
                · exact leftover_le hb hi hgg hbn
              have hm := allowed_of_minimal hgd hs hc hi rfl (fun g hg => (List.mem_filter.mp hg).1)
                (fun g hg => (List.mem_filter.mp hg).1) hle hdisZ (hgd.filter _) hZall hval' hmin'
              have hlen3 := (hdanger i hpC hpf).2.2
              have hlenN : (goods.filter q').length ≤ 2 := by
                have hsub : ∀ g ∈ goods.filter q', g ∈ (goods.filter (d i)).erase hh := by
                  intro g hg
                  rw [List.Nodup.mem_erase_iff (hgd.filter _)]
                  exact ⟨hq'h g (List.mem_filter.mp hg).2, List.mem_filter.mpr ⟨(List.mem_filter.mp hg).1,
                    hq'd g (List.mem_filter.mp hg).2⟩⟩
                have := List.Nodup.length_le_of_subset (hgd.filter q') hsub
                rw [List.length_erase_of_mem hhm] at this
                omega
              exact hU i hi (free_of_not_frozen hb hpf) q' hsrc hm.1 hlenN (Nat.lt_trans hZgain hval')
            · exact Nat.le_trans ((harcs p hpC hpf).2 i hi hip hh hhm) (hval i)
          · -- a pair or less: removing a good leaves at most one good, unwanted
            have hl1 : ((goods.filter (d p)).erase hh).length ≤ 1 := by
              rw [List.length_erase_of_mem hhm]; omega
            refine Nat.le_trans (value_le_of_length_le_one' (v := v) i hl1 (c := value v i (hold goods base i))
              fun g hg => ?_) (hval i)
            have hgm := List.mem_of_mem_erase hg
            have hgg := (List.mem_filter.mp hgm).1
            exact unwanted_of_free hb hpf hi hgg (harc.2.2.2.1 g hgg (List.mem_filter.mp hgm).2)
      · rw [hoff j hjC] at hhm ⊢
        exact Nat.le_trans (hb.v2 i hi j hj hij hh hhm) (hval i)
  -- no robust level drops
  have hlev : ∀ i ∈ agents, levelR v i goods (hold goods base i) ≤
      levelR v i goods (hold goods (rotateL base₁ (cycNext C c w₀) lab) i) := by
    intro i hi
    by_cases hiC : i ∈ C
    · obtain ⟨p, hp⟩ := (hcyc i).mpr (hdef i hiC)
      obtain ⟨_, _, _, hall, hgain⟩ := hgive p i hp
      rw [hrecv hp]
      exact levelR_mono v hgd (hb.allowed i hi) hall (hold_nodup hgd base i) (hgd.filter _)
        (fun g hg => (mem_hold.mp hg).1) (fun g hg => (List.mem_filter.mp hg).1) hgain
    · rw [hoff i hiC]; exact Nat.le_refl _
  have hpot := sum_map_le hlev
  rcases Nat.lt_or_eq_of_le hpot with hlt | heq
  · exfalso
    have := hmax.2 _ hvalid
    unfold potentialR at this
    omega
  · have heqC := eq_of_sum_eq hlev heq
    -- no agent of the cycle is frozen: its successor would rise
    have hfree : ∀ o ∈ C, ¬ Frozen v agents goods base o := by
      intro o hoC hfo
      cases hw : cycNext C c w₀ o with
      | none => exact hdef o hoC hw
      | some w =>
        obtain ⟨_, hwC, hwa, _, _⟩ := hgive o w hw
        rcases (hspec o w hw).2.2 with ⟨_, hW⟩ | ⟨hnf, _⟩
        · obtain ⟨_, y, hyg, hy, hlt⟩ := hW
          have hZw : hold goods (rotateL base₁ (cycNext C c w₀) lab) w = [y] := by
            rw [hrecv hw, htakF o hfo, hy]
          have hyY : y ∉ hold goods base w := fun hm => by have := le_value_of_mem v w hm; omega
          have hlt' := levelR_lt_of_want hgd hc hwa (hb.allowed w hwa) hyg hyY hlt
          rw [← hZw] at hlt'
          have := heqC w hwa
          omega
        · exact hnf hfo
    -- every agent of the cycle holds one good: a taker of a danger set holding anything else would rise
    have hone : ∀ o ∈ C, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y] := by
      intro o hoC _
      obtain ⟨p, hp⟩ := (hcyc o).mpr (hdef o hoC)
      obtain ⟨hpC, _, hoa, hZall, _⟩ := hgive p o hp
      have hpf := hfree p hpC
      refine Classical.byContradiction fun hns => ?_
      have harc := (harcs p hpC hpf).1
      have hxo : o = x p := by
        rcases (hspec p o hp).2.2 with ⟨hfp, _⟩ | ⟨_, e⟩
        · exact absurd hfp hpf
        · exact e
      have hdan := harc.2.2.1
      rw [← hxo] at hdan
      rw [htakO p hpC hpf] at hZall
      have hlt' := levelR_lt_of_danger hgd hc hoa (hb.allowed o hoa) (hold_nodup hgd base o)
        (fun g hg => (mem_hold.mp hg).1) hZall (hgd.filter _) (fun g hg => (List.mem_filter.mp hg).1)
        (fun g hg hgY => (hdan.2.1 g hg).2.1 (mem_hold.mp hgY).2) (two_le_of_danger hdan) hdan.2.2.1 hns
      have := heqC o hoa
      rw [hrecv hp, htakO p hpC hpf] at this
      omega
    exact hone

/-- **Lemma 18 at a maximum, for F₂-clash cycles.** At a maximum of the robust order with (H), no F₂-clash cycle has
pairwise disjoint labels: by `clean_cycle_one_good` its free agents hold one good, and `no_f1_clashCycle` applies. -/
theorem no_clean_clashCycle (hgd : goods.Nodup) (hc : R1Core4 v agents goods) (hs : Strict v agents goods)
    {base : G → Option A} (hmax : IsMaximumR v agents goods base) (hH : CondH v agents goods base)
    {x : A → A} {d : A → G → Bool} {C : List A} (hC : ClashCycle v agents goods base x d C)
    (hclean : ∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
      ∀ g ∈ goods, base g = none → d o g = true → d o' g = false) : False :=
  no_f1_clashCycle hgd hc hs hmax hH hC (clean_cycle_one_good hgd hc hs (topR_of_maxR hgd hmax) hH hC hclean)

end clean

/-- **(X) fails at maxima** (a hypothesis, never an axiom; the open half of Theorem 19 of `k4/de4.md` §10.1): at a
maximum of the robust order in which everyone holds a good, (H) holds and some agent does not hold an upper set, every
F₂-clash cycle is clean: the labels of its free agents are pairwise disjoint. -/
def HX (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ClashCycle v agents goods base x d C →
        ∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
          ∀ g ∈ goods, base g = none → d o g = true → d o' g = false

/-- **Theorem 19 at maxima**: with Lemma 18 (`no_clean_clashCycle`), `HX` implies `HC2`. -/
theorem hc2_of_hx (h : HX A G) : HC2 A G := by
  intro v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  exact no_clean_clashCycle hgd hc hs hmax hH hC (h v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC)

/-- `HC3'` implies `HX`: if the free agents on an F₂-clash cycle hold one good (Lemma 25(a) excludes robust holders),
its labels are pairwise disjoint by definition. -/
theorem hx_of_hc3' (h : HC3' A G) : HX A G := by
  intro v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC o ho o' ho' hoo' hnf hnf' g hg hn hd
  have h3 := hc3_of_hc3' h v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  exact hC.2.2.2.2.2 o ho o' ho' hoo' hnf hnf' (h3 o ho hnf) g hg hn hd

/-- **TARGET₄ from (X) failing at maxima (`HX`) and Claim T′ in case (L) (`HLL`)** (machine-checked: Lemmas 7, 8,
17, 18, R, V, 4 at a maximum; Proposition 24; Theorem A′; the existence of maxima; Lemma 3). -/
theorem target4_of_HX_HLL (I : Inst) (hn : 0 < I.n) (hx : HX (Fin I.n) (Fin I.m)) (hl : HLL (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_HC2 I hn (hc2_of_hx hx) (hl_of_hll hl) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.not_two_lowerPairs
#print axioms EFX.DE4.levelR_lt_of_danger
#print axioms EFX.DE4.eq_of_sum_eq
#print axioms EFX.DE4.two_le_of_danger
#print axioms EFX.DE4.clean_cycle_one_good
#print axioms EFX.DE4.no_clean_clashCycle
#print axioms EFX.DE4.hc2_of_hx
#print axioms EFX.DE4.hx_of_hc3'
#print axioms EFX.DE4.target4_of_HX_HLL
