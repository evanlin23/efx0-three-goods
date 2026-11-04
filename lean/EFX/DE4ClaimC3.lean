import EFX.DE4ClaimC2
import EFX.DE4Repair

/-!
# Conjecture C₃ at maxima implies Conjecture C₂ at maxima (`k4/de4.md` §10.3; ledger K4.DE4V3R.C3, K4.DE4V3R.LEAN)

A cycle of the pointer relation whose free agents all hold one good is traded as in Corollary 10: every agent of the
cycle takes its predecessor's whole holding with its label. In the robust order the trade is valid, every agent's
value weakly rises and the first agent's strictly, nothing is released, and so it keeps (V3) (Lemma V). With Lemma R
it contradicts maximality. Hence an F₂-clash cycle at a maximum passes through a free agent holding two or more goods,
and Conjecture C₃ (no such cycle does) excludes F₂-clash cycles at maxima altogether.

**Results.**
- `lemmaV` (**Lemma V**, `k4/de4.md` §9): from a (V3)-valid state, a state in which no listed agent's value drops and
  every good held before is still held satisfies (V3).
- `cycle_trade`: the trade along a cycle of the pointer relation whose free agents hold one good, with tight arcs and
  pairwise disjoint labels (a generalization of the trade of Corollary 10).
- `no_f1_clashCycle`: at a maximum of the robust order with (H), no F₂-clash cycle has all its free agents holding one
  good.
- `HC3` (**Conjecture C₃** for F₂-clash cycles, a hypothesis, never an axiom): at a maximum with (H) in which everyone
  holds a good and someone is not upper, no F₂-clash cycle passes through a free agent holding two or more goods.
- `hc2_of_hc3`, `target4_of_HC3`: `HC3` implies `HC2`, and with `HL` it implies **TARGET₄**.
- `robust_not_on_clashCycle` (**Lemma 25(a)**): a free robust upper holder lies on no F₂-clash cycle. Hence `HC3'`
  (free agents on F₂-clash cycles at maxima hold one good or a robust upper set: no lower-pair or non-robust upper
  holder lies on one, P1 and P2 of §10.3) implies `HC3` (`hc3_of_hc3'`), and `target4_of_HC3'`.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section lemmaV
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **Lemma V** (`k4/de4.md` §9): from a (V3)-valid state, a state in which no listed agent's value drops and every
good held before is still held satisfies (V3). (Its validity is not needed.) -/
theorem lemmaV (hgd : goods.Nodup) {base base' : G → Option A} (hv3 : ValidV3 v agents goods base)
    (hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i))
    (hheld : ∀ g ∈ goods, base g ≠ none → base' g ≠ none) : V3 v agents goods base' := by
  intro i hi hlp g hg hgS hgt hn
  have hgg : g ∈ goods := (mem_relevant.mp hg).1
  -- it suffices that `g` was held
  refine (hheld g hgg ?_) hn
  intro hn0
  by_cases hlp0 : IsLowerPair v i goods (hold goods base i)
  · by_cases hgY : g ∈ hold goods base i
    · rw [(mem_hold.mp hgY).2] at hn0; exact absurd hn0 (by simp)
    · exact hv3.2 i hi hlp0 g hg hgY hgt hn0
  · have hSnd := hold_nodup hgd base' i
    have hSg : ∀ s ∈ hold goods base' i, s ∈ goods := fun s hs => (mem_hold.mp hs).1
    have hle := hval i hi
    have hLP := hlp.2.2.2.1
    by_cases hw : value v i (hold goods base i) < v i g
    · obtain ⟨j, _, hj⟩ := hv3.1.v1 i hi g hgg hw
      have := (mem_hold.mp (by rw [hj]; simp : g ∈ hold goods base j)).2
      rw [hn0] at this; exact absurd this (by simp)
    · -- `Y_i` is worth at least `v(g)` and less than the top, and is not the lower pair: it is one good
      have hge : v i g ≤ value v i (hold goods base i) := Nat.le_of_not_lt hw
      rcases hv3.1.allowed i hi with ⟨hl1, hpos⟩ | hup | hlp'
      · match hY : hold goods base i, hl1 with
        | [], _ => rw [hY] at hge; simp [value] at hge; have := (mem_relevant.mp hg).2; omega
        | [s], _ =>
          rw [hY, value_singleton] at hge
          have hs := (mem_hold.mp (by rw [hY]; simp : s ∈ hold goods base i))
          by_cases hsg : s = g
          · subst hsg; rw [hs.2] at hn0; exact absurd hn0 (by simp)
          · have hsr : s ∈ relevant v i goods := mem_relevant.mpr ⟨hs.1, by have := (mem_relevant.mp hg).2; omega⟩
            have hsS : s ∉ hold goods base' i := by
              intro hsZ
              have := hlp.2.2.2.2.1 s hsZ g hg hgS
              omega
            obtain ⟨s1, s2, hS⟩ := pair_of_length hlp.2.1
            have h12 : s1 ≠ s2 := by rw [hS] at hSnd; simp at hSnd; exact hSnd
            have hs1 : v i s1 < v i g := hlp.2.2.2.2.1 s1 (by rw [hS]; simp) g hg hgS
            have hs2 : v i s2 < v i g := hlp.2.2.2.2.1 s2 (by rw [hS]; simp) g hg hgS
            have hst : v i s < topV v i goods := by
              have : value v i (hold goods base' i) = v i s1 + v i s2 := by rw [hS]; simp [value]
              have := hlp.2.2.2.1
              rw [hY, value_singleton] at hle
              omega
            obtain ⟨t, htg, htv⟩ := exists_topV v i goods (by omega)
            have ht : t ∈ relevant v i goods := mem_relevant.mpr ⟨htg, by omega⟩
            have hr1 : s1 ∈ relevant v i goods :=
              mem_relevant.mpr ⟨hSg s1 (by rw [hS]; simp), hlp.2.2.1 s1 (by rw [hS]; simp)⟩
            have hr2 : s2 ∈ relevant v i goods :=
              mem_relevant.mpr ⟨hSg s2 (by rw [hS]; simp), hlp.2.2.1 s2 (by rw [hS]; simp)⟩
            exact not_five hlp.1 (a := s1) (b := s2) (c := g) (d := s) (e := t)
              (nodup5 h12 (ne_of_val_lt v i hs1) (ne_of_val_lt v i (by omega)) (ne_of_val_lt v i (by omega))
                (ne_of_val_lt v i hs2) (ne_of_val_lt v i (by omega)) (ne_of_val_lt v i (by omega)) (Ne.symm hsg)
                (ne_of_val_lt v i (by omega)) (ne_of_val_lt v i (by omega)))
              (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption)
      · have := hup.2.1; omega
      · exact absurd hlp' hlp0

end lemmaV

section trade
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **The trade along a pointer cycle of one-good free agents** (Corollary 10's trade, for any such cycle). Under (H),
let `C` be a cycle of the pointer relation of `x` in which every free agent holds one good and has a tight arc
`(x o, d o)`, the labels of its free agents being pairwise disjoint. Trading along `C` gives a valid state in which no
value drops, the first agent's value rises, the agents off `C` keep their holdings, and every held good stays held. -/
theorem cycle_trade (hgd : goods.Nodup) (hc : R1Core4 v agents goods) (hs : Strict v agents goods)
    {base : G → Option A} (hb : Valid v agents goods base)
    (hU : ∀ x ∈ agents, (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) →
        ∀ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) →
          Allowed v x goods (goods.filter p) → (goods.filter p).length ≤ 2 →
          ¬ value v x (hold goods base x) < value v x (goods.filter p))
    {x : A → A} {d : A → G → Bool} {C : List A} (hCnd : C.Nodup) (hCa : ∀ j ∈ C, j ∈ agents)
    (hCc : IsChain (PtrRel v agents goods base x) C) {c w₀ : A} (hcl : C.getLast? = some c)
    (hw₀ : C.head? = some w₀) (hcw : PtrRel v agents goods base x c w₀)
    (harcs : ∀ o ∈ C, ¬ Frozen v agents goods base o →
      ArcInto v agents goods base o (x o) (d o) ∧ Tight v agents goods base o (d o))
    (hone : ∀ o ∈ C, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y])
    (hdisj : ∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
      ∀ g ∈ goods, base g = none → d o g = true → d o' g = false) :
    ∃ base', Valid v agents goods base' ∧
      (∀ i, value v i (hold goods base i) ≤ value v i (hold goods base' i)) ∧
      (∀ i ∈ C, value v i (hold goods base i) < value v i (hold goods base' i)) ∧
      (∀ i, i ∉ C → hold goods base' i = hold goods base i) ∧
      (∀ g ∈ goods, base g ≠ none → base' g ≠ none) := by
  classical
  obtain ⟨hspec, hinj, hcyc, hdef⟩ := cycNext_spec hCnd hCc hcl hw₀ hcw
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
      have := hdisj o hoC o' ho'C (fun e => hne' e.symm) hnf hnf' g hg hn hd
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
  -- what each agent of the cycle hands on
  have htakF : ∀ j, Frozen v agents goods base j → taken goods base lab j = hold goods base j := by
    intro j hj
    unfold taken hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd hj (hlabs g j h).2.2.1
    · exact Or.inl
  have htakO : ∀ o ∈ C, ¬ Frozen v agents goods base o → taken goods base lab o = goods.filter (d o) := by
    intro o hoC hnf
    have harc := (harcs o hoC hnf).1
    obtain ⟨y, hy⟩ := hone o hoC hnf
    obtain ⟨g₁, hg₁, hd₁, hb₁⟩ := harc.2.2.2.2
    have hy₁ : g₁ = y := by
      have : g₁ ∈ hold goods base o := mem_hold.mpr ⟨hg₁, hb₁⟩
      rw [hy] at this; simpa using this
    unfold taken
    apply List.filter_congr
    intro g hg
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · have : g ∈ hold goods base o := mem_hold.mpr ⟨hg, h⟩
        rw [hy] at this
        have hgy : g = y := by simpa using this
        rw [hgy, ← hy₁]; exact hd₁
      · exact (hlabs g o h).2.2.2
    · intro hd
      rcases harc.2.2.2.1 g hg hd with h | h
      · exact Or.inl h
      · exact Or.inr (hlabof g hg h o hoC hnf hd)
  -- the danger set of an arc is an allowed holding of its blocker, at most three goods
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
  have hgive : ∀ j w, cycNext C c w₀ j = some w → j ∈ agents ∧ w ∈ agents ∧
      Allowed v w goods (taken goods base lab j) ∧
      value v w (hold goods base w) < value v w (taken goods base lab j) := by
    intro j w h
    obtain ⟨hjC, hwC, hRjw⟩ := hspec j w h
    refine ⟨hCa j hjC, hCa w hwC, ?_⟩
    rcases hRjw with ⟨hfj, hW⟩ | ⟨hnf, rfl⟩
    · obtain ⟨_, y, hyg, hy, hlt⟩ := hW
      rw [htakF j hfj, hy]
      refine ⟨Or.inl ⟨by simp, ?_⟩, by rw [value_singleton]; exact hlt⟩
      intro g hg
      simp at hg; subst hg; omega
    · rw [htakO j hjC hnf]
      exact ⟨(hdanger j hjC hnf).1, (hdanger j hjC hnf).2.1⟩
  have hlab : ∀ g j, lab g = some j → base g = none ∧ cycNext C c w₀ j ≠ none := fun g j h =>
    ⟨(hlabs g j h).1, hdef j (hlabs g j h).2.1⟩
  have hfrozen : ∀ j, (∃ i ∈ agents, ∃ y, hold goods base j = [y] ∧ value v i (hold goods base i) < v i y) →
      ∀ g, lab g ≠ some j := by
    rintro j ⟨i, hi, y, hy, hlt⟩ g hl
    exact (hlabs g j hl).2.2.1 ⟨y, hy, i, hi, hlt⟩
  have hge := rotateL_value_ge (v := v) (agents := agents) hlab hgive hinj hcyc
  have hbig : ∀ j w, cycNext C c w₀ j = some w → 3 ≤ (taken goods base lab j).length → ∀ i ∈ agents, i ≠ w →
      ∀ hh ∈ taken goods base lab j, value v i ((taken goods base lab j).erase hh) ≤
        value v i (hold goods (rotateL base (cycNext C c w₀) lab) i) := by
    intro j w h h3 i hi hiw hh hhm
    obtain ⟨hjC, hwC, hRjw⟩ := hspec j w h
    rcases hRjw with ⟨hfj, _⟩ | ⟨hnf, rfl⟩
    · obtain ⟨y, hy, _⟩ := hfj
      rw [htakF j ⟨y, hy, by assumption⟩, hy] at h3
      simp at h3
    have hjo : j ∈ C ∧ ¬ Frozen v agents goods base j := ⟨hjC, hnf⟩
    rw [htakO j hjC hnf] at hhm ⊢
    by_cases hij : i = j
    · subst hij
      refine Nat.le_of_not_lt fun hlt => ?_
      -- `i` receives from its predecessor `p` on the cycle
      obtain ⟨p, hp⟩ := (hcyc i).mpr (hdef i hjC)
      have hZ := rotateL_hold_recv (goods := goods) (base := base) hlab hinj hcyc hp
      rw [hZ] at hlt
      obtain ⟨hpa, _, hZall, hZgain⟩ := hgive p i hp
      have hpi : p ≠ i := by
        intro e
        subst e
        rcases (hspec p p hp).2.2 with ⟨⟨y, hy, _⟩, _, y', _, hy', hlt'⟩ | ⟨_, e⟩
        · rw [hy'] at hlt'; simp [value] at hlt'
        · exact (harcs p hjo.1 hjo.2).1.2.1 e.symm
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
        (harcs i hjo.1 hjo.2).1.2.2.2.1 g hg (hq'd g hq)
      have hdisZ : ∀ g ∈ goods.filter q', g ∉ taken goods base lab p := by
        intro g hg hgZ
        have hgg := (List.mem_filter.mp hg).1
        have hdi := hq'd g (List.mem_filter.mp hg).2
        have hZ' := (List.mem_filter.mp hgZ).2
        rw [decide_eq_true_eq] at hZ'
        rcases hsrc g hgg (List.mem_filter.mp hg).2 with hbi | hbn
        · rcases hZ' with h1 | h1
          · rw [hbi] at h1; exact hpi (Option.some.inj h1).symm
          · rw [(hlabs g p h1).1] at hbi; exact absurd hbi (by simp)
        · rcases hZ' with h1 | h1
          · rw [hbn] at h1; exact absurd h1 (by simp)
          · obtain ⟨_, hpC, hpnf, hdp⟩ := hlabs g p h1
            have := hdisj i hjo.1 p hpC (Ne.symm hpi) hjo.2 hpnf g hgg hbn hdi
            rw [hdp] at this; exact absurd this (by simp)
      have hle : ∀ g ∈ goods.filter q', v i g ≤ value v i (taken goods base lab p) := by
        intro g hg
        have hgg := (List.mem_filter.mp hg).1
        refine Nat.le_trans ?_ (Nat.le_of_lt hZgain)
        rcases hsrc g hgg (List.mem_filter.mp hg).2 with hbi | hbn
        · exact le_value_of_mem v i (mem_hold.mpr ⟨hgg, hbi⟩)
        · exact leftover_le hb hi hgg hbn
      have hm := allowed_of_minimal hgd hs hc hi rfl (fun g hg => (List.mem_filter.mp hg).1)
        (fun g hg => (List.mem_filter.mp hg).1) hle hdisZ (hgd.filter _) hZall hval' hmin'
      -- at most two goods: the arc's set has at most three
      have hlen3 := (hdanger i hjo.1 hjo.2).2.2
      have hlenN : (goods.filter q').length ≤ 2 := by
        have hsub : ∀ g ∈ goods.filter q', g ∈ (goods.filter (d i)).erase hh := by
          intro g hg
          rw [List.Nodup.mem_erase_iff (hgd.filter _)]
          exact ⟨hq'h g (List.mem_filter.mp hg).2, List.mem_filter.mpr ⟨(List.mem_filter.mp hg).1,
            hq'd g (List.mem_filter.mp hg).2⟩⟩
        have := List.Nodup.length_le_of_subset (hgd.filter q') hsub
        rw [List.length_erase_of_mem hhm] at this
        omega
      exact hU i hi (free_of_not_frozen hb hjo.2) q' hsrc hm.1 hlenN (Nat.lt_trans hZgain hval')
    · exact Nat.le_trans ((harcs j hjo.1 hjo.2).2 i hi hij hh hhm) (hge i)
  have hsome : ∃ j w, cycNext C c w₀ j = some w := by
    have hw₀C : w₀ ∈ C := List.mem_of_mem_head? hw₀
    cases h : cycNext C c w₀ w₀ with
    | none => exact absurd h (hdef w₀ hw₀C)
    | some w => exact ⟨w₀, w, h⟩
  have hval := (rotateL_valid_better hb hlab hgive hinj hcyc hfrozen hbig hsome).1
  refine ⟨_, hval, hge, ?_, ?_, ?_⟩
  · -- every agent of the cycle receives from its predecessor, a holding worth more
    intro i hiC
    obtain ⟨p, hp⟩ := (hcyc i).mpr (hdef i hiC)
    rw [rotateL_hold_recv hlab hinj hcyc hp]
    exact (hgive p i hp).2.2.2
  · -- agents off the cycle keep their holdings
    intro i hiC
    have hσi : cycNext C c w₀ i = none := by
      cases h : cycNext C c w₀ i with
      | none => rfl
      | some w => exact absurd (hspec i w h).1 hiC
    unfold hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    rw [rotateL_eq_some hlab]
    constructor
    · rintro (⟨c', _, e⟩ | ⟨_, h2, _⟩)
      · exact absurd (hspec c' i e).2.1 hiC
      · exact h2
    · intro h2
      refine Or.inr ⟨?_, h2, hσi⟩
      cases hl : lab g with
      | none => rfl
      | some o => rw [(hlabs g o hl).1] at h2; exact absurd h2 (by simp)
  · -- held goods stay held
    intro g _ hgn
    cases hbg : base g with
    | none => exact absurd hbg hgn
    | some j =>
      have hl : lab g = none := by
        cases hl : lab g with
        | none => rfl
        | some o => rw [(hlabs g o hl).1] at hbg; exact absurd hbg (by simp)
      unfold rotateL
      simp only [hl, hbg]
      cases cycNext C c w₀ j <;> simp


/-- At a maximum of the robust order with (H), no F₂-clash cycle has all its free agents holding one good: its trade
would raise the robust level sum (against Lemma R) or keep it with (V3) and Pareto-better values. -/
theorem no_f1_clashCycle (hgd : goods.Nodup) (hc : R1Core4 v agents goods) (hs : Strict v agents goods)
    {base : G → Option A} (hmax : IsMaximumR v agents goods base) (hH : CondH v agents goods base)
    {x : A → A} {d : A → G → Bool} {C : List A} (hC : ClashCycle v agents goods base x d C)
    (hone : ∀ o ∈ C, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y]) : False := by
  obtain ⟨hCnd, hCa, hCc, ⟨c, w₀, hcl, hw₀, hcw⟩, harcs, hdisj⟩ := hC
  have hb : Valid v agents goods base := hmax.1.1
  obtain ⟨base', hb', hge, hgain, hoff, hheld⟩ := cycle_trade hgd hc hs hb hH.2 hCnd hCa hCc hcl hw₀ hcw harcs hone
    (fun o ho o' ho' hoo' hnf hnf' g hg hn hd => hdisj o ho o' ho' hoo' hnf hnf' (hone o ho hnf) g hg hn hd)
  have hw₀C : w₀ ∈ C := List.mem_of_mem_head? hw₀
  -- no robust level drops
  have hlev : ∀ i ∈ agents, levelR v i goods (hold goods base i) ≤ levelR v i goods (hold goods base' i) := by
    intro i hi
    by_cases hiC : i ∈ C
    · exact levelR_mono v hgd (hmax.1.1.allowed i hi) (hb'.allowed i hi) (hold_nodup hgd base i)
        (hold_nodup hgd base' i) (fun g hg => (mem_hold.mp hg).1) (fun g hg => (mem_hold.mp hg).1) (hgain i hiC)
    · rw [hoff i hiC]; exact Nat.le_refl _
  have hpot : potentialR v agents goods base ≤ potentialR v agents goods base' := sum_map_le hlev
  rcases Nat.lt_or_eq_of_le hpot with hlt | heq
  · have := potentialR_le_of_max hgd hmax hb'
    omega
  · have hv3 : V3 v agents goods base' := lemmaV hgd hmax.1 (fun i _ => hge i) hheld
    exact hmax.2 base' ⟨hb', hv3⟩ (Or.inr ⟨heq, fun i _ => hge i, w₀, hCa w₀ hw₀C, hgain w₀ hw₀C⟩)

end trade

/-- **Conjecture C₃ for F₂-clash cycles at maxima** (a hypothesis, never an axiom): at a maximum of the robust order in
which everyone holds a good, (H) holds and some agent does not hold an upper set, every free agent on an F₂-clash
cycle holds one good. (Conjecture C₃ of `k4/de4.md` §10.3 says more: no cycle of the arc graph passes through a free
agent holding two or more goods.) -/
def HC3 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ClashCycle v agents goods base x d C →
        ∀ o ∈ C, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y]

/-- **Conjecture C₃ at maxima implies Conjecture C₂ at maxima.** -/
theorem hc2_of_hc3 (h3 : HC3 A G) : HC2 A G := by
  intro v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  exact no_f1_clashCycle hgd hc hs hmax hH hC (h3 v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC)

/-- **Conjecture C₃ at maxima and Claim T′ where (H) fails imply TARGET₄.** -/
theorem target4_of_HC3 (I : Inst) (hn : 0 < I.n) (h3 : HC3 (Fin I.n) (Fin I.m)) (hl : HL (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_HC2 I hn (hc2_of_hc3 h3) hl h4

section lemma25
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **Lemma 25(a)** (`k4/de4.md` §10.3), on F₂-clash cycles: a free agent holding a robust upper set lies on no
F₂-clash cycle. It wants no good (its holding is worth more than its top), and it has no danger set (the goods outside
its holding are worth at most the holding). -/
theorem robust_not_on_clashCycle {base : G → Option A} {x : A → A} {d : A → G → Bool} {C : List A}
    (hC : ClashCycle v agents goods base x d C) {o : A} (ho : o ∈ C)
    (hup : IsUpper v o goods (hold goods base o)) (hrob : IsRobust v o goods (hold goods base o)) : False := by
  obtain ⟨hCnd, _, hCc, ⟨c, w₀, hcl, hw₀, hcw⟩, harcs, _⟩ := hC
  obtain ⟨hspec, _, hcyc, hdef⟩ := cycNext_spec hCnd hCc hcl hw₀ hcw
  obtain ⟨p, hp⟩ := (hcyc o).mpr (hdef o ho)
  obtain ⟨hpC, _, hR⟩ := hspec p o hp
  rcases hR with ⟨_, _, y, hyg, _, hlt⟩ | ⟨hnf, e⟩
  · -- `o` would want a single good
    have := le_topV v o goods hyg
    have := hup.2.1
    omega
  · -- `o` would have a danger set outside its holding
    have hdan := (harcs p hpC hnf).1.2.2.1
    rw [← e] at hdan
    have hsub : (goods.filter (d p)).Sublist (goods.filter (fun g => decide (g ∉ hold goods base o))) := by
      apply filter_sublist_filter
      intro g hg hdg
      have := (hdan.2.1 g (List.mem_filter.mpr ⟨hg, hdg⟩)).2.1
      exact decide_eq_true fun hm => this (mem_hold.mp hm).2
    have h1 := value_sublist v o hsub
    have h2 := hdan.2.2.1
    unfold IsRobust at hrob
    omega

end lemma25

/-- **Conjecture C₃ for F₂-clash cycles, without robust holders** (a hypothesis, never an axiom): at a maximum of the
robust order in which everyone holds a good, (H) holds and some agent does not hold an upper set, every free agent on
an F₂-clash cycle holds one good or a robust upper set. Its content is P1 and P2 of `k4/de4.md` §10.3 on such cycles:
no free holder of its lower pair or of a non-robust upper set lies on one. -/
def HC3' (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ClashCycle v agents goods base x d C →
        ∀ o ∈ C, ¬ Frozen v agents goods base o →
          (∃ y, hold goods base o = [y]) ∨ (IsUpper v o goods (hold goods base o) ∧
            IsRobust v o goods (hold goods base o))

/-- With Lemma 25(a), `HC3'` implies `HC3`. -/
theorem hc3_of_hc3' (h : HC3' A G) : HC3 A G := by
  intro v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC o ho hnf
  rcases h v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC o ho hnf with h1 | ⟨hup, hrob⟩
  · exact h1
  · exact absurd (robust_not_on_clashCycle hC ho hup hrob) id

/-- **No lower-pair or non-robust upper holder on an F₂-clash cycle at a maximum (`HC3'`), and Claim T′ where (H)
fails (`HL`), imply TARGET₄.** -/
theorem target4_of_HC3' (I : Inst) (hn : 0 < I.n) (h3 : HC3' (Fin I.n) (Fin I.m)) (hl : HL (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_HC3 I hn (hc3_of_hc3' h3) hl h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.lemmaV
#print axioms EFX.DE4.cycle_trade
#print axioms EFX.DE4.no_f1_clashCycle
#print axioms EFX.DE4.hc2_of_hc3
#print axioms EFX.DE4.target4_of_HC3
#print axioms EFX.DE4.robust_not_on_clashCycle
#print axioms EFX.DE4.hc3_of_hc3'
#print axioms EFX.DE4.target4_of_HC3'
