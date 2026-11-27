import EFX.DE4ClaimT

/-!
# Claim T′ from Conjecture C₂ and the case (L) (`k4/de4.md` §10.1–§10.2; ledger K4.DE4V3R.T23, K4.DE4V3R.LEAN)

This file machine-checks the cycle frame of `k4/de4.md`: **Lemma 17** (a total pointer map) and **Proposition 24**
(its cycles are F₂-clash cycles). With them, Claim T′ (`ClaimTMax`), and hence TARGET₄, follows from two
hypotheses that no longer mention completability:
- `HC2` (**Conjecture C₂** at maxima): no maximum of the robust order that satisfies (H) and is not all-upper has an
  F₂-clash cycle;
- `HL` (the case where (H) fails, that is (L) and the moves of "(H) at a maximum"): Claim T′ for maxima that do not
  satisfy (H).

**Definitions.**
- `CondH`: (H) of §7, without "everyone holds a good" (which follows at a non-completable state, Corollary 5(b)):
  the leftover goods alone threaten nobody, and no free agent has a self-upgrade of at most two goods (Lemma 4′).
- `PtrRel x`: the pointer relation of a map `x`: a frozen agent points to an agent wanting its good, a free agent `o`
  to `x o`.
- `ClashCycle x d C`: `C` is a cycle of `PtrRel x` in which every free agent `o` has a tight arc `(x o, d o)` into it,
  and the label (leftover goods of `d o`) of every free agent holding one good avoids the labels of all other free
  agents of `C`. Tight arcs are the minimal arcs of `k4/de4.md` §10.2 (under (H) the two notions agree; only
  tightness is used).

**Results.**
- `pointer_map` (**Lemma 17**): at a valid, non-completable state with (H), there are `x` and `d` giving every free
  agent a tight arc, with the labels of the free agents holding one good pairwise disjoint and avoided by the labels
  of the other free agents.
- `exists_clashCycle` (**Proposition 24**): such a state has an F₂-clash cycle.
- `claimTMax_of_HC2`: `HC2` and `HL` imply Claim T′; `target4_of_HC2`: they imply **TARGET₄**.

`HC2` and `HL` are hypotheses, never axioms. `HC2` is Conjecture C₂ (EVIDENCE only, `k4/de4.md` §10.2) restricted to
maxima, plus the extra premise "not all-upper"; `HL` is partly proved on paper (`k4/de4.md` §10.1, "(H) at a
maximum", Lemma 17′, Lemma 20(c)) and open in the case (L).
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- (H) of `k4/de4.md` §7 (without "everyone holds a good"): the leftover goods alone threaten nobody, and no free
agent has an allowed self-upgrade of at most two goods made of its own goods and leftover goods. -/
def CondH (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  (∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) ∧
  (∀ x ∈ agents, (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) →
    ∀ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) →
      Allowed v x goods (goods.filter p) → (goods.filter p).length ≤ 2 →
      ¬ value v x (hold goods base x) < value v x (goods.filter p))

/-- The pointer relation of a map `x`: a frozen agent points to an agent wanting its good, a free agent `o` to
`x o`. -/
def PtrRel (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (x : A → A) (a b : A) :
    Prop :=
  (Frozen v agents goods base a ∧ WantsGood v agents goods base a b) ∨ (¬ Frozen v agents goods base a ∧ b = x a)

/-- An **F₂-clash cycle** (`k4/de4.md` §10.2): a cycle `C` of the pointer relation of `x` in which every free agent
`o` has a tight arc `(x o, d o)` into it, and the label of every free agent holding one good avoids the labels of the
other free agents of `C`. -/
def ClashCycle (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (x : A → A)
    (d : A → G → Bool) (C : List A) : Prop :=
  C.Nodup ∧ (∀ j ∈ C, j ∈ agents) ∧ IsChain (PtrRel v agents goods base x) C ∧
    (∃ c w, C.getLast? = some c ∧ C.head? = some w ∧ PtrRel v agents goods base x c w) ∧
    (∀ o ∈ C, ¬ Frozen v agents goods base o →
      ArcInto v agents goods base o (x o) (d o) ∧ Tight v agents goods base o (d o)) ∧
    ∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
      (∃ y, hold goods base o = [y]) → ∀ g ∈ goods, base g = none → d o g = true → d o' g = false

/-- **Conjecture C₂ at maxima** (a hypothesis, never an axiom): no maximum of the robust order in which everyone holds
a good, (H) holds and some agent does not hold an upper set has an F₂-clash cycle. -/
def HC2 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ¬ ClashCycle v agents goods base x d C

/-- **Claim T′ where (H) fails** (a hypothesis, never an axiom): a non-completable maximum of the robust order that
does not satisfy (H) has every agent holding an upper set. -/
def HL (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ Completable v agents goods base → ¬ CondH v agents goods base →
      ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

section pointer
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **Lemma 17** (a total pointer map). At a valid, non-completable state in which the leftover goods alone threaten
nobody, there are `x` and `d` such that every free agent `o` has a tight arc `(x o, d o)` into it, the labels of the
free agents holding one good are pairwise disjoint, and the label of every other free agent avoids them. -/
theorem pointer_map {base : G → Option A} (hb : Valid v agents goods base) (hag : agents.Nodup)
    (hgd : goods.Nodup) (hnc : ¬ Completable v agents goods base)
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) :
    ∃ (x : A → A) (d : A → G → Bool),
      (∀ o ∈ agents, ¬ Frozen v agents goods base o →
        ArcInto v agents goods base o (x o) (d o) ∧ Tight v agents goods base o (d o)) ∧
      ∀ o ∈ agents, ∀ o' ∈ agents, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
        (∃ y, hold goods base o = [y]) → ∀ g ∈ goods, base g = none → d o g = true → d o' g = false := by
  classical
  -- F₁: the free agents holding one good, with the arcs of Lemma 8
  let os := agents.filter (fun o => decide (¬ Frozen v agents goods base o ∧ ∃ y, hold goods base o = [y]))
  have hos : ∀ o ∈ os, o ∈ agents ∧ ¬ Frozen v agents goods base o ∧ ∃ y, hold goods base o = [y] := by
    intro o ho
    have h1 := List.mem_filter.mp ho
    have h2 := of_decide_eq_true h1.2
    exact ⟨h1.1, h2.1, h2.2⟩
  have hmemos : ∀ o ∈ agents, ¬ Frozen v agents goods base o → (∃ y, hold goods base o = [y]) → o ∈ os :=
    fun o ho hnf hy => List.mem_filter.mpr ⟨ho, decide_eq_true ⟨hnf, hy⟩⟩
  obtain ⟨x', d', harcs, hdisj⟩ := lemma8 hb hgd hnc hJ os (hag.filter _) hos
  -- every other free agent: a shortest arc whose label avoids the labels of F₁
  let Q : A → A × (G → Bool) → Prop := fun o p => ArcInto v agents goods base o p.1 p.2 ∧
    ∀ g ∈ goods, p.2 g = true → base g = none → ∀ r ∈ os, d' r g = false
  have hQ : ∀ o, ∃ p : A × (G → Bool), o ∈ agents → ¬ Frozen v agents goods base o → o ∉ os →
      Q o p ∧ Tight v agents goods base o p.2 := by
    intro o
    by_cases hpre : o ∈ agents ∧ ¬ Frozen v agents goods base o ∧ o ∉ os
    · obtain ⟨ho, hof, hor⟩ := hpre
      obtain ⟨x₀, d₀, harc, hav⟩ := exists_arc_avoiding hb hgd hnc hJ
        (fun r hr => (hos r hr).2.2) x' d' harcs hdisj ho hof hor
      obtain ⟨⟨x₁, d₁⟩, hP, hmin⟩ := exists_min_len (fun p : A × (G → Bool) => (goods.filter p.2).length) (Q o) _
        ⟨(x₀, d₀), ⟨harc, hav⟩, Nat.le_refl _⟩
      refine ⟨(x₁, d₁), fun _ _ _ => ⟨hP, ?_⟩⟩
      exact tight_of_min hb hgd hJ hof (fun g => ∀ r ∈ os, d' r g = false) hP.1 hP.2
        (fun x₂ d₂ h2 hav2 => hmin (x₂, d₂) ⟨h2, hav2⟩)
    · exact ⟨(o, fun _ => false), fun ho hof hor => absurd ⟨ho, hof, hor⟩ hpre⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hQ
  refine ⟨fun o => if o ∈ os then x' o else (f o).1, fun o => if o ∈ os then d' o else (f o).2, ?_, ?_⟩
  · intro o ho hof
    by_cases hor : o ∈ os
    · simp only [hor, ↓reduceIte]; exact harcs o hor
    · simp only [hor, ↓reduceIte]
      have h := hf o ho hof hor
      exact ⟨h.1.1, h.2⟩
  · intro o ho o' ho' hoo' hof hof' hy g hg hn hd
    have hor : o ∈ os := hmemos o ho hof hy
    simp only [hor, ↓reduceIte] at hd
    by_cases hor' : o' ∈ os
    · simp only [hor', ↓reduceIte]
      exact hdisj o hor o' hor' hoo' g hg hn hd
    · simp only [hor', ↓reduceIte]
      cases h2 : (f o').2 g with
      | false => rfl
      | true =>
        have := (hf o' ho' hof' hor').1.2 g hg h2 hn o hor
        rw [hd] at this; exact absurd this (by simp)

/-- **Proposition 24**: a valid, non-completable state of a nonempty list of agents in which the leftover goods alone
threaten nobody has an F₂-clash cycle (a cycle of the pointer map of Lemma 17). -/
theorem exists_clashCycle {base : G → Option A} (hb : Valid v agents goods base) (hag : agents.Nodup)
    (hgd : goods.Nodup) (hnc : ¬ Completable v agents goods base) (hne : agents ≠ [])
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) :
    ∃ (x : A → A) (d : A → G → Bool) (C : List A), ClashCycle v agents goods base x d C := by
  obtain ⟨x, d, harcs, hdisj⟩ := pointer_map hb hag hgd hnc hJ
  have hR : ∀ a ∈ agents, ∃ b ∈ agents, PtrRel v agents goods base x a b := by
    intro a ha
    by_cases hfa : Frozen v agents goods base a
    · obtain ⟨w, hw⟩ := wantsGood_of_frozen hfa
      exact ⟨w, hw.1, Or.inl ⟨hfa, hw⟩⟩
    · exact ⟨x a, (harcs a ha hfa).1.1, Or.inr ⟨hfa, rfl⟩⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a, a ∈ agents := by
    cases agents with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, List.mem_cons_self⟩
  obtain ⟨C, hCnd, hCc, hCa, c, w₀, hcl, hw₀, hcw⟩ :=
    exists_cycle_rel (PtrRel v agents goods base x) hR agents.length [a₀] (by simp) (by simp) (by simp)
      (by simpa using ha₀) trivial
  exact ⟨x, d, C, hCnd, hCa, hCc, ⟨c, w₀, hcl, hw₀, hcw⟩, fun o ho hof => harcs o (hCa o ho) hof,
    fun o ho o' ho' hoo' hof hof' hy g hg hn hd => hdisj o (hCa o ho) o' (hCa o' ho') hoo' hof hof' hy g hg hn hd⟩

end pointer

/-- **Conjecture C₂ at maxima and Claim T′ where (H) fails imply Claim T′.** At a non-completable maximum with (H),
everyone holds a good (Corollary 5(b)) and Proposition 24 gives an F₂-clash cycle, which `HC2` excludes unless every
agent holds an upper set. -/
theorem claimTMax_of_HC2 (h2 : HC2 A G) (hl : HL A G) : ClaimTMax A G := by
  intro v agents goods hne hag hgd hc hs base hmax hnc
  by_cases hH : CondH v agents goods base
  · refine Classical.byContradiction fun hnu => ?_
    have hb : Valid v agents goods base := hmax.1.1
    have hE : ∀ i ∈ agents, hold goods base i ≠ [] := fun i hi he => hnc (completable_of_empty hb hi he hH.1)
    obtain ⟨x, d, C, hC⟩ := exists_clashCycle hb hag hgd hnc hne hH.1
    exact h2 v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  · exact hl v agents goods hne hag hgd hc hs base hmax hnc hH

/-- **Conjecture C₂ at maxima and Claim T′ where (H) fails imply TARGET₄** (machine-checked: Lemmas 7, 8, 17,
Proposition 24, Corollary 5(b), Theorem A′, the existence of maxima and Lemma 3). -/
theorem target4_of_HC2 (I : Inst) (hn : 0 < I.n) (h2 : HC2 (Fin I.n) (Fin I.m)) (hl : HL (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_claimTMax I hn (claimTMax_of_HC2 h2 hl) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.pointer_map
#print axioms EFX.DE4.exists_clashCycle
#print axioms EFX.DE4.claimTMax_of_HC2
#print axioms EFX.DE4.target4_of_HC2
