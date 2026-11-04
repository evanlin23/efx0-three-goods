import EFX.DE4Lemma18
import EFX.DE4LowerPair

/-!
# The frame for the lower-pair order (`k4/de4.md` §10.4; ledger K4.DE4V3R.LP, K4.DE4V3R.LEANLP)

The lemmas of §10 that contradict maximality through a larger robust level sum need only a *top state* (`TopR`:
(V3)-valid, with the largest robust level sum among valid states), and a maximum of the lower-pair order is one
(`topR_of_maxLP`, by Lemma R). Theorem A′ carries over because a state value-Pareto-better than an all-upper state holds
no lower pair. Lemma 18 carries over except where its trade keeps the level sum, which happens only on cycles of free
agents holding one good (`clean_cycle_one_good`); the hypothesis `HXLP` excludes those (flat) cycles too.

**Results.**
- `topR_of_maxLP`: a maximum of the lower-pair order is a top state.
- `ConjLP` (**Conjecture K4.DE4V3R.LP**, a hypothesis, never an axiom) and `target4_of_conjLP`: it implies TARGET₄.
- `numLP_eq_zero_of_upper`, `thmAllUpperLP` (**Theorem A′ in the lower-pair order**).
- `ClaimTMaxLP`, `conjLP_of_claimTMaxLP`, `target4_of_claimTMaxLP`.
- `HC2LP`, `HLLP` (hypotheses at maxima of the lower-pair order), `claimTMaxLP_of_HC2LP`, `target4_of_HC2LP`.
- `HXLP`: at a maximum of the lower-pair order with (H), every F₂-clash cycle is clean and has a free agent holding
  something other than one good; `hc2lp_of_hxlp` (Lemma 18).
- `HLLLP` (Claim T′ in case (L) at maxima of the lower-pair order), `hllp_of_hlllp` (Lemma 4 at a maximum).
- `target4_of_HXLP_HLLLP`: **HXLP and HLLLP imply TARGET₄**.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

theorem topR_of_maxLP {v : A → G → Nat} {agents : List A} {goods : List G} (hgd : goods.Nodup)
    {base : G → Option A} (hmax : IsMaximumLP v agents goods base) : TopR v agents goods base :=
  ⟨hmax.1, fun _ hb' => potentialR_le_of_maxLP hgd hmax hb'⟩

/-- **Conjecture K4.DE4V3R.LP** (a hypothesis, never an axiom): every maximum of the lower-pair order is completable. -/
def ConjLP (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumLP v agents goods base → Completable v agents goods base

theorem exists_efx0_of_conjLP (h : ConjLP A G) (v : A → G → Nat) {agents : List A} {goods : List G}
    (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨base, hmax⟩ := exists_maximumLP (v := v) hag hgd
  obtain ⟨X, hX, -, hE⟩ := h v agents goods hne hag hgd hc hs base hmax
  exact ⟨X, hX, hE⟩

/-- **Conjecture K4.DE4V3R.LP implies TARGET₄** (with K4.CORE and K4.TIE, as in Lemma 3). -/
theorem target4_of_conjLP (I : Inst) (hn : 0 < I.n) (h : ConjLP (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _)
    (fun w agents _ hag hgd _ hcore _ hs _ =>
      exists_efx0_of_conjLP h w (fun he => by have := hcore.1; rw [he] at this; simp at this) hag hgd
        (fun i hi => ⟨(hcore.2.1 i hi).1, (hcore.2.1 i hi).2, hcore.2.2.1 i hi⟩) hs) h4

section allUpper
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq G] in
/-- No agent holding something worth more than its top holds its lower pair: then no lower-pair holders. -/
theorem numLP_eq_zero_of_upper {base : G → Option A}
    (h : ∀ i ∈ agents, topV v i goods < value v i (hold goods base i)) : numLP v agents goods base = 0 := by
  classical
  unfold numLP
  have : (agents.map (fun i => if IsLowerPair v i goods (hold goods base i) then 1 else 0)).sum ≤
      (agents.map (fun _ => (0 : Nat))).sum := by
    apply sum_map_le
    intro i hi
    have hn : ¬ IsLowerPair v i goods (hold goods base i) := fun hlp => by
      have := hlp.2.2.2.1; have := h i hi; omega
    simp [hn]
  have h0 : ∀ l : List A, (l.map (fun _ => (0 : Nat))).sum = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]
  have := h0 agents
  omega

/-- **Theorem A′ in the lower-pair order**: a non-completable (V3)-valid state in which every agent holds an upper set
has a better (V3)-valid state. A value-Pareto-better state of an all-upper state is all-upper, so Theorem A′'s state is
better in the lower-pair order too. -/
theorem thmAllUpperLP (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) {base : G → Option A} (hv3 : ValidV3 v agents goods base)
    (hup : ∀ i ∈ agents, IsUpper v i goods (hold goods base i)) (hnc : ¬ Completable v agents goods base) :
    ∃ base', ValidV3 v agents goods base' ∧ BetterLP v agents goods base' base := by
  obtain ⟨b', hv', hb'⟩ := thmAllUpper v agents goods hne hag hgd hc hs base hv3 hup hnc
  refine ⟨b', hv', ?_⟩
  rcases hb' with hlt | ⟨heq, hle, hlt⟩
  · exact Or.inl hlt
  · have h0 : numLP v agents goods base = 0 := numLP_eq_zero_of_upper fun i hi => (hup i hi).2.1
    have h0' : numLP v agents goods b' = 0 := numLP_eq_zero_of_upper fun i hi =>
      Nat.lt_of_lt_of_le (hup i hi).2.1 (hle i hi)
    exact Or.inr (Or.inr ⟨heq, by omega, hle, hlt⟩)

end allUpper

/-- **Claim T′ in the lower-pair order** (a hypothesis, never an axiom): every non-completable maximum of the
lower-pair order has every agent holding an upper set. -/
def ClaimTMaxLP (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumLP v agents goods base → ¬ Completable v agents goods base →
      ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- Claim T′ and Theorem A′ give Conjecture K4.DE4V3R.LP. -/
theorem conjLP_of_claimTMaxLP (hT : ClaimTMaxLP A G) : ConjLP A G := by
  intro v agents goods hne hag hgd hc hs base hmax
  refine Classical.byContradiction fun hnc => ?_
  have hup := hT v agents goods hne hag hgd hc hs base hmax hnc
  obtain ⟨b', hv', hb'⟩ := thmAllUpperLP hne hag hgd hc hs hmax.1 hup hnc
  exact hmax.2 b' hv' hb'

theorem target4_of_claimTMaxLP (I : Inst) (hn : 0 < I.n) (h : ClaimTMaxLP (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjLP I hn (conjLP_of_claimTMaxLP h) h4

/-- **Conjecture C₂ at maxima of the lower-pair order** (a hypothesis, never an axiom). -/
def HC2LP (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumLP v agents goods base → (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ¬ ClashCycle v agents goods base x d C

/-- **Claim T′ where (H) fails, in the lower-pair order** (a hypothesis, never an axiom). -/
def HLLP (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumLP v agents goods base → ¬ Completable v agents goods base → ¬ CondH v agents goods base →
      ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- `HC2LP` and `HLLP` give Claim T′ in the lower-pair order (Corollary 5(b) and Proposition 24, machine-checked). -/
theorem claimTMaxLP_of_HC2LP (h2 : HC2LP A G) (hl : HLLP A G) : ClaimTMaxLP A G := by
  intro v agents goods hne hag hgd hc hs base hmax hnc
  by_cases hH : CondH v agents goods base
  · refine Classical.byContradiction fun hnu => ?_
    have hb : Valid v agents goods base := hmax.1.1
    have hE : ∀ i ∈ agents, hold goods base i ≠ [] := fun i hi he => hnc (completable_of_empty hb hi he hH.1)
    obtain ⟨x, d, C, hC⟩ := exists_clashCycle hb hag hgd hnc hne hH.1
    exact h2 v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  · exact hl v agents goods hne hag hgd hc hs base hmax hnc hH

/-- **`HC2LP` and `HLLP` imply TARGET₄.** -/
theorem target4_of_HC2LP (I : Inst) (hn : 0 < I.n) (h2 : HC2LP (Fin I.n) (Fin I.m)) (hl : HLLP (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_claimTMaxLP I hn (claimTMaxLP_of_HC2LP h2 hl) h4

/-- **(X) fails at maxima of the lower-pair order** (a hypothesis, never an axiom): at such a maximum in which everyone
holds a good, (H) holds and some agent does not hold an upper set, every F₂-clash cycle is clean (its free agents'
labels are pairwise disjoint) and not flat (some free agent on it holds something other than one good). -/
def HXLP (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumLP v agents goods base → (∀ i ∈ agents, hold goods base i ≠ []) → CondH v agents goods base →
      ¬ (∀ i ∈ agents, IsUpper v i goods (hold goods base i)) →
      ∀ (x : A → A) (d : A → G → Bool) (C : List A), ClashCycle v agents goods base x d C →
        (∀ o ∈ C, ∀ o' ∈ C, o ≠ o' → ¬ Frozen v agents goods base o → ¬ Frozen v agents goods base o' →
          ∀ g ∈ goods, base g = none → d o g = true → d o' g = false) ∧
        ∃ o ∈ C, ¬ Frozen v agents goods base o ∧ ¬ ∃ y, hold goods base o = [y]

/-- **Theorem 19 at maxima of the lower-pair order**: with Lemma 18 (`clean_cycle_one_good`), `HXLP` implies
`HC2LP`. -/
theorem hc2lp_of_hxlp (h : HXLP A G) : HC2LP A G := by
  intro v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  obtain ⟨hclean, o, hoC, hnf, hno⟩ := h v agents goods hne hag hgd hc hs base hmax hE hH hnu x d C hC
  exact hno (clean_cycle_one_good hgd hc hs (topR_of_maxLP hgd hmax) hH hC hclean o hoC hnf)

/-- **Claim T′ in case (L), in the lower-pair order** (a hypothesis, never an axiom): a non-completable maximum of the
lower-pair order in which some free agent has a self-upgrade of at most two goods has every agent holding an upper
set. -/
def HLLLP (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumLP v agents goods base → ¬ Completable v agents goods base →
      (∃ x ∈ agents, FreeSelfUp v agents goods base x) → ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- With Lemma 4 at a maximum (`threat_at_max`, at any top state), `HLLLP` implies `HLLP`. -/
theorem hllp_of_hlllp (h : HLLLP A G) : HLLP A G := by
  intro v agents goods hne hag hgd hc hs base hmax hnc hH
  refine h v agents goods hne hag hgd hc hs base hmax hnc ?_
  by_cases hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)
  · exact Classical.byContradiction fun hno =>
      hH ⟨hJ, fun x hx hfree p hp hN h2 hgain => hno ⟨x, hx, hfree, p, hp, hN, h2, hgain⟩⟩
  · obtain ⟨i, hi, hJi⟩ : ∃ i ∈ agents, value v i (hold goods base i) < value v i (leftover goods base) :=
      Classical.byContradiction fun hno => hJ fun i hi => Nat.le_of_not_lt fun hlt => hno ⟨i, hi, hlt⟩
    exact threat_at_max hgd hs hc (topR_of_maxLP hgd hmax) hi hJi

/-- **TARGET₄ from (X) failing at maxima of the lower-pair order (`HXLP`) and Claim T′ in case (L) there (`HLLLP`)**
(machine-checked: Lemmas 7, 8, 17, 18, R (counting lower pairs), 4 at a maximum; Proposition 24; Theorem A′; the
existence of maxima of the lower-pair order; Lemma 3). -/
theorem target4_of_HXLP_HLLLP (I : Inst) (hn : 0 < I.n) (hx : HXLP (Fin I.n) (Fin I.m))
    (hl : HLLLP (Fin I.n) (Fin I.m)) (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_HC2LP I hn (hc2lp_of_hxlp hx) (hllp_of_hlllp hl) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.topR_of_maxLP
#print axioms EFX.DE4.exists_efx0_of_conjLP
#print axioms EFX.DE4.target4_of_conjLP
#print axioms EFX.DE4.numLP_eq_zero_of_upper
#print axioms EFX.DE4.thmAllUpperLP
#print axioms EFX.DE4.conjLP_of_claimTMaxLP
#print axioms EFX.DE4.target4_of_claimTMaxLP
#print axioms EFX.DE4.claimTMaxLP_of_HC2LP
#print axioms EFX.DE4.target4_of_HC2LP
#print axioms EFX.DE4.hc2lp_of_hxlp
#print axioms EFX.DE4.hllp_of_hlllp
#print axioms EFX.DE4.target4_of_HXLP_HLLLP
