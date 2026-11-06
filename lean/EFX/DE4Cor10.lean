import EFX.DE4Ring

/-!
# DE4: Corollary 10 when every free agent holds one good (`k4/de4.md` §7; ledger K4.DE4.LEAN)

**Results.**
- `exists_cycle_rel`: a relation in which every listed agent points to a listed agent has a cycle.
- `cycNext_spec`: the successor map of a cycle is injective and its givers are exactly its receivers.
- `cor10` (**Corollary 10**, the case F₂ = ∅): under (H), if every free agent holds exactly one good, DE's walk closes
  a cycle (frozen agents point to an agent wanting their good, free agents to the blocker of their Lemma 8 arc), and
  the trade along it gives a valid, better state.
- `ConjDE4H₂` (a hypothesis, never an axiom): Conjecture 11″ for the states of (H) where some free agent holds two or
  more goods; `conjDE4H_of_H₂` (with Corollary 10 it implies `ConjDE4H`) and `target4_of_conjDE4H₂` (it implies
  TARGET₄). The hypothesis is false (`attempts/k4-de4.md`), so this is not a route to TARGET₄; Corollary 10 itself is
  a statement about valid states and stands.

**Faithfulness.** The walk of `k4/de4.md` Theorem 9 starts at a fixed agent and follows first wanters; here any
cycle of the relation "a frozen agent points to an agent wanting its good, a free agent to the blocker of its Lemma 8
arc" is used, which is all the proof of Corollary 10 needs. The labels are the leftover goods of the Lemma 8 arcs of
the free agents on the cycle.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Cycles of a relation on the agents -/

section cycle
variable {agents : List A}

omit [DecidableEq A] in
theorem nodup_append_single {P : List A} {w : A} (hnd : P.Nodup) (hw : w ∉ P) : (P ++ [w]).Nodup :=
  List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hw ha⟩

/-- A relation in which every listed agent points to a listed agent has a cycle: a duplicate-free chain whose last
agent points to its first. -/
theorem exists_cycle_rel (R : A → A → Prop) (hR : ∀ a ∈ agents, ∃ b ∈ agents, R a b) :
    ∀ (k : Nat) (P : List A), agents.length - P.length ≤ k → P ≠ [] → P.Nodup → (∀ j ∈ P, j ∈ agents) →
      IsChain R P → ∃ C : List A, C.Nodup ∧ IsChain R C ∧ (∀ j ∈ C, j ∈ agents) ∧
        ∃ c w, C.getLast? = some c ∧ C.head? = some w ∧ R c w := by
  intro k
  induction k with
  | zero =>
    intro P hk hne hnd hP hc
    obtain ⟨c, hcl⟩ : ∃ c, P.getLast? = some c := by
      cases h : P.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some c => exact ⟨c, rfl⟩
    have hcP : c ∈ P := List.mem_of_getLast? hcl
    obtain ⟨w, hwa, hw⟩ := hR c (hP c hcP)
    by_cases hwP : w ∈ P
    · obtain ⟨pre, hpre⟩ := fromFirst_suffix w P
      refine ⟨fromFirst w P, hnd.sublist (fromFirst_sublist w P), ?_, fun j hj => hP j ?_, c, w, ?_,
        fromFirst_head w hwP, hw⟩
      · rw [hpre] at hc; exact isChain_right hc
      · rw [hpre]; exact List.mem_append_right _ hj
      · rw [fromFirst_getLast w hwP]; exact hcl
    · exfalso
      have := List.Nodup.length_le_of_subset (nodup_append_single hnd hwP) (fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · exact hP a h
        · simp at h; subst h; exact hwa)
      simp at this
      omega
  | succ k ih =>
    intro P hk hne hnd hP hc
    obtain ⟨c, hcl⟩ : ∃ c, P.getLast? = some c := by
      cases h : P.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some c => exact ⟨c, rfl⟩
    have hcP : c ∈ P := List.mem_of_getLast? hcl
    obtain ⟨w, hwa, hw⟩ := hR c (hP c hcP)
    by_cases hwP : w ∈ P
    · obtain ⟨pre, hpre⟩ := fromFirst_suffix w P
      refine ⟨fromFirst w P, hnd.sublist (fromFirst_sublist w P), ?_, fun j hj => hP j ?_, c, w, ?_,
        fromFirst_head w hwP, hw⟩
      · rw [hpre] at hc; exact isChain_right hc
      · rw [hpre]; exact List.mem_append_right _ hj
      · rw [fromFirst_getLast w hwP]; exact hcl
    · exact ih (P ++ [w]) (by simp; omega) (by simp) (nodup_append_single hnd hwP)
        (fun j hj => by
          rcases List.mem_append.mp hj with h | h
          · exact hP j h
          · simp at h; subst h; exact hwa)
        (isChain_append hcl hc hw)

/-- The successor map of a cycle: defined exactly on the cycle, along the relation, injective, and onto the
cycle. -/
theorem cycNext_spec {R : A → A → Prop} {C : List A} (hCnd : C.Nodup) (hCc : IsChain R C) {c w₀ : A}
    (hc : C.getLast? = some c) (hw₀ : C.head? = some w₀) (hcw : R c w₀) :
    (∀ j w, cycNext C c w₀ j = some w → j ∈ C ∧ w ∈ C ∧ R j w) ∧
    (∀ j j' w, cycNext C c w₀ j = some w → cycNext C c w₀ j' = some w → j = j') ∧
    (∀ j, (∃ j', cycNext C c w₀ j' = some j) ↔ cycNext C c w₀ j ≠ none) ∧
    (∀ j ∈ C, cycNext C c w₀ j ≠ none) := by
  obtain ⟨t, rfl⟩ : ∃ t, C = w₀ :: t := by
    cases C with
    | nil => simp at hw₀
    | cons a t => simp at hw₀; exact ⟨t, by rw [hw₀]⟩
  have hw₀t : w₀ ∉ t := (List.nodup_cons.mp hCnd).1
  have hcC : c ∈ w₀ :: t := List.mem_of_getLast? hc
  have hcnone : nextIn (w₀ :: t) c = none := nextIn_last hCnd hc
  have hne : ∀ {j}, j ∈ w₀ :: t → cycNext (w₀ :: t) c w₀ j ≠ none := by
    intro j hj
    unfold cycNext
    by_cases hjc : j = c
    · simp [hjc]
    · simp only [hjc, ↓reduceIte]
      have : (w₀ :: t).getLast? ≠ some j := by rw [hc]; exact fun e => hjc (Option.some.inj e).symm
      obtain ⟨u, hu⟩ := nextIn_some hCnd hj this
      rw [hu]; simp
  have spec : ∀ j w, cycNext (w₀ :: t) c w₀ j = some w → j ∈ w₀ :: t ∧ w ∈ w₀ :: t ∧ R j w := by
    intro j w h
    unfold cycNext at h
    by_cases hjc : j = c
    · simp only [hjc, ↓reduceIte, Option.some.injEq] at h
      subst hjc; subst h; exact ⟨hcC, by simp, hcw⟩
    · simp only [hjc, ↓reduceIte] at h
      obtain ⟨hR, hjC, hwt⟩ := nextIn_spec hCc h
      exact ⟨hjC, List.mem_of_mem_tail hwt, hR⟩
  refine ⟨spec, fun j j' w h1 h2 => ?_, fun j => ⟨fun ⟨j', hj'⟩ => hne (spec j' j hj').2.1, fun hj => ?_⟩,
    fun j hj => hne hj⟩
  · unfold cycNext at h1 h2
    by_cases hjc : j = c <;> by_cases hj'c : j' = c
    · rw [hjc, hj'c]
    · simp only [hjc, ↓reduceIte, Option.some.injEq] at h1
      simp only [hj'c, ↓reduceIte] at h2
      subst h1
      exact absurd (nextIn_mem_tail h2).2 hw₀t
    · simp only [hj'c, ↓reduceIte, Option.some.injEq] at h2
      simp only [hjc, ↓reduceIte] at h1
      subst h2
      exact absurd (nextIn_mem_tail h1).2 hw₀t
    · simp only [hjc, hj'c, ↓reduceIte] at h1 h2
      exact nextIn_inj hCnd h1 h2
  · have hjC : j ∈ w₀ :: t := by
      refine Classical.byContradiction fun hn => ?_
      apply hj
      unfold cycNext
      have hjc : j ≠ c := fun e => hn (e ▸ hcC)
      simp only [hjc, ↓reduceIte]
      exact nextIn_none_of_not_mem hn
    by_cases hjw : j = w₀
    · subst hjw; exact ⟨c, by simp [cycNext]⟩
    · have hjt : j ∈ (w₀ :: t).tail := by
        rcases List.mem_cons.mp hjC with e | hm
        · exact absurd e hjw
        · exact hm
      obtain ⟨j', hj'⟩ := exists_nextIn_of_mem_tail hCnd hjt
      have hj'c : j' ≠ c := fun e => by rw [e, hcnone] at hj'; exact absurd hj' (by simp)
      exact ⟨j', by simp [cycNext, hj'c, hj']⟩

end cycle

/-! ## Corollary 10 when every free agent holds one good -/

section cor10
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **Corollary 10** (the case F₂ = ∅). Under (H) (valid, not completable, the leftover goods alone threatening
nobody, no free self-upgrade), if every free agent holds exactly one good, there is a better valid state: DE's walk
closes a cycle, and the trade along it (each agent of the cycle takes the wanted good of a frozen predecessor, or
the danger set of its Lemma 8 arc into a free predecessor) is valid and better. -/
theorem cor10 (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods) (hs : Strict v agents goods)
    {base : G → Option A} (hb : Valid v agents goods base) (hnc : ¬ Completable v agents goods base)
    (hne : agents ≠ [])
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i))
    (hU : ∀ x ∈ agents, (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) →
        ∀ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) →
          Allowed v x goods (goods.filter p) → (goods.filter p).length ≤ 2 →
          ¬ value v x (hold goods base x) < value v x (goods.filter p))
    (hF : ∀ o ∈ agents, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y]) :
    ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base := by
  classical
  -- Lemma 8 for the free agents
  let os := agents.filter (fun o => decide (¬ Frozen v agents goods base o))
  have hos : ∀ o ∈ os, o ∈ agents ∧ ¬ Frozen v agents goods base o ∧ ∃ y, hold goods base o = [y] := by
    intro o ho
    have h1 := List.mem_filter.mp ho
    have hnf : ¬ Frozen v agents goods base o := of_decide_eq_true h1.2
    exact ⟨h1.1, hnf, hF o h1.1 hnf⟩
  have hmemos : ∀ o ∈ agents, ¬ Frozen v agents goods base o → o ∈ os := fun o ho hnf =>
    List.mem_filter.mpr ⟨ho, decide_eq_true hnf⟩
  obtain ⟨x, d, harcs, hdisj⟩ := lemma8 hb hgd hnc hJ os (hag.filter _) hos
  -- the walk's relation and its cycle
  let R : A → A → Prop := fun a b => (Frozen v agents goods base a ∧ WantsGood v agents goods base a b) ∨
    (¬ Frozen v agents goods base a ∧ b = x a)
  have hR : ∀ a ∈ agents, ∃ b ∈ agents, R a b := by
    intro a ha
    by_cases hfa : Frozen v agents goods base a
    · obtain ⟨w, hw⟩ := wantsGood_of_frozen hfa
      exact ⟨w, hw.1, Or.inl ⟨hfa, hw⟩⟩
    · exact ⟨x a, (harcs a (hmemos a ha hfa)).1.1, Or.inr ⟨hfa, rfl⟩⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a, a ∈ agents := by
    cases agents with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, List.mem_cons_self⟩
  obtain ⟨C, hCnd, hCc, hCa, c, w₀, hcl, hw₀, hcw⟩ :=
    exists_cycle_rel R hR agents.length [a₀] (by simp) (by simp) (by simp) (by simpa using ha₀) trivial
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
      have := hdisj o (hmemos o (hCa o hoC) hnf) o' (hmemos o' (hCa o' ho'C) hnf') (fun e => hne' e.symm) g hg hn hd
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
    have harc := (harcs o (hmemos o (hCa o hoC) hnf)).1
    obtain ⟨y, hy⟩ := hF o (hCa o hoC) hnf
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
    have harc := (harcs o (hmemos o (hCa o hoC) hnf)).1
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
    have hjo : j ∈ os := hmemos j (hCa j hjC) hnf
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
        · exact (harcs p hjo).1.2.1 e.symm
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
        (harcs i hjo).1.2.2.2.1 g hg (hq'd g hq)
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
            have := hdisj i hjo p (hmemos p (hCa p hpC) hpnf) (Ne.symm hpi) g hgg hbn hdi
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
      have hlen3 := (hdanger i hjC (hos i hjo).2.1).2.2
      have hlenN : (goods.filter q').length ≤ 2 := by
        have hsub : ∀ g ∈ goods.filter q', g ∈ (goods.filter (d i)).erase hh := by
          intro g hg
          rw [List.Nodup.mem_erase_iff (hgd.filter _)]
          exact ⟨hq'h g (List.mem_filter.mp hg).2, List.mem_filter.mpr ⟨(List.mem_filter.mp hg).1,
            hq'd g (List.mem_filter.mp hg).2⟩⟩
        have := List.Nodup.length_le_of_subset (hgd.filter q') hsub
        rw [List.length_erase_of_mem hhm] at this
        omega
      exact hU i hi (free_of_not_frozen hb (hos i hjo).2.1) q' hsrc hm.1 hlenN (Nat.lt_trans hZgain hval')
    · exact Nat.le_trans ((harcs j hjo).2 i hi hij hh hhm) (hge i)
  have hsome : ∃ j w, cycNext C c w₀ j = some w := by
    have hw₀C : w₀ ∈ C := List.mem_of_mem_head? hw₀
    cases h : cycNext C c w₀ w₀ with
    | none => exact absurd h (hdef w₀ hw₀C)
    | some w => exact ⟨w₀, w, h⟩
  exact ⟨_, rotateL_valid_better hb hlab hgive hinj hcyc hfrozen hbig hsome⟩

end cor10

/-! ## The frame: the remaining case is a free agent holding two or more goods -/

/-- **Conjecture 11″ where Corollary 10 does not apply** (a hypothesis, never an axiom): every non-completable valid
state satisfying (H) in which some free agent holds two or more goods has a better valid state. **False**: the
counterexample of `attempts/k4-de4.md` is such a state with no better valid state. -/
def ConjDE4H₂ (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, Valid v agents goods base → ¬ Completable v agents goods base →
      (∀ i ∈ agents, hold goods base i ≠ []) →
      (∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) →
      (∀ x ∈ agents, (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) →
        ∀ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) →
          Allowed v x goods (goods.filter p) → (goods.filter p).length ≤ 2 →
          ¬ value v x (hold goods base x) < value v x (goods.filter p)) →
      (∃ o ∈ agents, ¬ Frozen v agents goods base o ∧ 2 ≤ (hold goods base o).length) →
      ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base

/-- With Corollary 10, the case where some free agent holds two or more goods implies Conjecture 11″. -/
theorem conjDE4H_of_H₂ (h : ConjDE4H₂ A G) : ConjDE4H A G := by
  intro v agents goods hne hag hgd hc hs base hb hnc hE hJ hU
  by_cases hF : ∀ o ∈ agents, ¬ Frozen v agents goods base o → ∃ y, hold goods base o = [y]
  · exact cor10 hag hgd hc hs hb hnc hne hJ hU hF
  · refine h v agents goods hne hag hgd hc hs base hb hnc hE hJ hU ?_
    refine Classical.byContradiction fun hno => hF fun o ho hnf => ?_
    have hlen : ¬ 2 ≤ (hold goods base o).length := fun h2 => hno ⟨o, ho, hnf, h2⟩
    have hE' := hE o ho
    generalize hold goods base o = l at hlen hE' ⊢
    rcases l with _ | ⟨y, _ | ⟨y', t⟩⟩
    · exact absurd rfl hE'
    · exact ⟨y, rfl⟩
    · simp at hlen

/-- **Conjecture 11″ for free agents holding two or more goods implies TARGET₄** (machine-checked: Lemmas 2, 4, 4′,
Corollary 5(b), Lemmas 7(a), 7(b), 8, Theorem 9's trade, Corollary 10, the existence of maxima and Lemma 3). -/
theorem target4_of_conjDE4H₂ (I : Inst) (hn : 0 < I.n) (h : ConjDE4H₂ (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjDE4H I hn (conjDE4H_of_H₂ h) h4

end DE4
end EFX

#print axioms EFX.DE4.exists_cycle_rel
#print axioms EFX.DE4.cycNext_spec
#print axioms EFX.DE4.cor10
#print axioms EFX.DE4.conjDE4H_of_H₂
#print axioms EFX.DE4.target4_of_conjDE4H₂
