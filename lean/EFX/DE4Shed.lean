import EFX.DE4Lemma18

/-!
# Shed-completability: the robust frame with a weaker finishing rule (`k4/de4.md` §10.5; ledger K4.DE4V3R.SHED)

Every tie-break of the robust order fails (`k4/de4/refute_lp.py`): the largest robust level sum can be reached by a
single non-completable state. In all known such states the completion only needs some holders of an upper set that
contains their top to keep the top alone (and release the rest). A state is *shed-completable* if, after such
sheddings, it has an EFX₀ completion. That still gives an EFX₀ allocation, and it is all a frame needs: every lemma of
the robust frame uses only non-completability, which non-shed-completability implies.

**Results.**
- `ShedCompletable`, `shed_of_completable`, `exists_efx0_of_shed`.
- `ConjShed` (**Conjecture K4.DE4V3R.SHED**, a hypothesis, never an axiom: every maximum of the robust order is
  shed-completable) and `target4_of_conjShed`.
- `ClaimTMaxShed`, `conjShed_of_claimTMaxShed` (Theorem A′).
- `HC2Shed`, `HLShed`, `claimTMaxShed_of_HC2Shed` (Corollary 5(b), Proposition 24).
- `HXShed` (at a maximum of the robust order that is not shed-completable, with (H), every F₂-clash cycle is clean),
  `hc2shed_of_hxshed` (Lemma 18).
- `HLLShed` (Claim T′ in case (L) there), `hlshed_of_hllshed` (Lemma 4 at a maximum).
- `target4_of_HXShed_HLLShed`: **HXShed and HLLShed imply TARGET₄.** The two refuting instances of the robust order and
  of the lower-pair order are shed-completable, so neither refutes these hypotheses.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `base` is shed-completable: some holders of an upper set containing their top keep the top alone (every other
agent keeps its holding), and the result has an EFX₀ completion. -/
def ShedCompletable (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ∃ base' : G → Option A, (∀ g j, base' g = some j → base g = some j) ∧
    (∀ i ∈ agents, hold goods base' i = hold goods base i ∨
      (IsUpper v i goods (hold goods base i) ∧ ∃ a, hold goods base' i = [a] ∧ v i a = topV v i goods)) ∧
    Completable v agents goods base'

section shed
variable {v : A → G → Nat} {agents : List A} {goods : List G}

theorem shed_of_completable {base : G → Option A} (h : Completable v agents goods base) :
    ShedCompletable v agents goods base :=
  ⟨base, fun _ _ e => e, fun _ _ => Or.inl rfl, h⟩

theorem exists_efx0_of_shed {base : G → Option A} (h : ShedCompletable v agents goods base) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨_, -, -, X, hX, -, hE⟩ := h
  exact ⟨X, hX, hE⟩

end shed

/-- **Conjecture K4.DE4V3R.SHED** (a hypothesis, never an axiom): every maximum of the robust order is
shed-completable. -/
def ConjShed (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ShedCompletable v agents goods base

/-- **Conjecture K4.DE4V3R.SHED implies TARGET₄** (with K4.CORE and K4.TIE, as in Lemma 3). -/
theorem target4_of_conjShed (I : Inst) (hn : 0 < I.n) (h : ConjShed (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _)
    (fun w agents _ hag hgd _ hcore _ hs _ => by
      obtain ⟨base, hmax⟩ := exists_maximumR (v := w) hag hgd
      exact exists_efx0_of_shed (h w agents _ (fun he => by have := hcore.1; rw [he] at this; simp at this) hag hgd
        (fun i hi => ⟨(hcore.2.1 i hi).1, (hcore.2.1 i hi).2, hcore.2.2.1 i hi⟩) hs base hmax)) h4

/-- **Claim T′ for shed-completability** (a hypothesis, never an axiom): a maximum of the robust order that is not
shed-completable has every agent holding an upper set. -/
def ClaimTMaxShed (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ ShedCompletable v agents goods base →
      ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- With Theorem A′, `ClaimTMaxShed` gives `ConjShed`. -/
theorem conjShed_of_claimTMaxShed (hT : ClaimTMaxShed A G) : ConjShed A G := by
  intro v agents goods hne hag hgd hc hs base hmax
  refine Classical.byContradiction fun hns => ?_
  have hup := hT v agents goods hne hag hgd hc hs base hmax hns
  have hnc : ¬ Completable v agents goods base := fun h => hns (shed_of_completable h)
  obtain ⟨b', hv', hb'⟩ := thmAllUpper v agents goods hne hag hgd hc hs base hmax.1 hup hnc
  exact hmax.2 b' hv' hb'

theorem target4_of_claimTMaxShed (I : Inst) (hn : 0 < I.n) (h : ClaimTMaxShed (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjShed I hn (conjShed_of_claimTMaxShed h) h4

/-- **Conjecture C₂ at maxima that are not shed-completable** (a hypothesis, never an axiom). -/
def HC2Shed (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ ShedCompletable v agents goods base →
      (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ¬ ClashCycle v agents goods base x d C

/-- **Claim T′ where (H) fails, for shed-completability** (a hypothesis, never an axiom). -/
def HLShed (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ ShedCompletable v agents goods base → ¬ CondH v agents goods base →
      ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

theorem claimTMaxShed_of_HC2Shed (h2 : HC2Shed A G) (hl : HLShed A G) : ClaimTMaxShed A G := by
  intro v agents goods hne hag hgd hc hs base hmax hns
  have hnc : ¬ Completable v agents goods base := fun h => hns (shed_of_completable h)
  by_cases hH : CondH v agents goods base
  · refine Classical.byContradiction fun hnu => ?_
    have hb : Valid v agents goods base := hmax.1.1
    have hE : ∀ i ∈ agents, hold goods base i ≠ [] := fun i hi he => hnc (completable_of_empty hb hi he hH.1)
    obtain ⟨x, d, C, hC⟩ := exists_clashCycle hb hag hgd hnc hne hH.1
    exact h2 v agents goods hne hag hgd hc hs base hmax hns hE hH hnu x d C hC
  · exact hl v agents goods hne hag hgd hc hs base hmax hns hH

/-- **(X) fails at maxima that are not shed-completable** (a hypothesis, never an axiom): at a maximum of the robust
order that is not shed-completable, in which everyone holds a good, (H) holds and some agent does not hold an upper set,
every F₂-clash cycle is clean. -/
def HXShed (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ ShedCompletable v agents goods base →
      (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ClashCycle v agents goods base x d C →
        ∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
          ∀ g ∈ goods, base g = none → d o g = true → d o' g = false

/-- With Lemma 18 (`no_clean_clashCycle`), `HXShed` implies `HC2Shed`. -/
theorem hc2shed_of_hxshed (h : HXShed A G) : HC2Shed A G := by
  intro v agents goods hne hag hgd hc hs base hmax hns hE hH hnu x d C hC
  exact no_clean_clashCycle hgd hc hs hmax hH hC (h v agents goods hne hag hgd hc hs base hmax hns hE hH hnu x d C hC)

/-- **Claim T′ in case (L), for shed-completability** (a hypothesis, never an axiom). -/
def HLLShed (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ ShedCompletable v agents goods base →
      (∃ x ∈ agents, FreeSelfUp v agents goods base x) → ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- With Lemma 4 at a maximum, `HLLShed` implies `HLShed`. -/
theorem hlshed_of_hllshed (h : HLLShed A G) : HLShed A G := by
  intro v agents goods hne hag hgd hc hs base hmax hns hH
  refine h v agents goods hne hag hgd hc hs base hmax hns ?_
  by_cases hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)
  · exact Classical.byContradiction fun hno =>
      hH ⟨hJ, fun x hx hfree p hp hN h2 hgain => hno ⟨x, hx, hfree, p, hp, hN, h2, hgain⟩⟩
  · obtain ⟨i, hi, hJi⟩ : ∃ i ∈ agents, value v i (hold goods base i) < value v i (leftover goods base) :=
      Classical.byContradiction fun hno => hJ fun i hi => Nat.le_of_not_lt fun hlt => hno ⟨i, hi, hlt⟩
    exact threat_at_max hgd hs hc (topR_of_maxR hgd hmax) hi hJi

/-- **TARGET₄ from (X) failing at maxima that are not shed-completable (`HXShed`) and Claim T′ in case (L) there
(`HLLShed`)** (machine-checked: Lemmas 7, 8, 17, 18, R, V, 4 at a maximum; Proposition 24; Theorem A′; the existence
of maxima; Lemma 3). -/
theorem target4_of_HXShed_HLLShed (I : Inst) (hn : 0 < I.n) (hx : HXShed (Fin I.n) (Fin I.m))
    (hl : HLLShed (Fin I.n) (Fin I.m)) (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_claimTMaxShed I hn (claimTMaxShed_of_HC2Shed (hc2shed_of_hxshed hx) (hlshed_of_hllshed hl)) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.shed_of_completable
#print axioms EFX.DE4.exists_efx0_of_shed
#print axioms EFX.DE4.target4_of_conjShed
#print axioms EFX.DE4.conjShed_of_claimTMaxShed
#print axioms EFX.DE4.target4_of_claimTMaxShed
#print axioms EFX.DE4.claimTMaxShed_of_HC2Shed
#print axioms EFX.DE4.hc2shed_of_hxshed
#print axioms EFX.DE4.hlshed_of_hllshed
#print axioms EFX.DE4.target4_of_HXShed_HLLShed
