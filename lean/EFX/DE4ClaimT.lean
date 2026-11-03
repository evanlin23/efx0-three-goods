import EFX.DE4RobustA

/-!
# Claim T′: the maxima version of Claim T (`k4/de4.md` §10.1; ledger K4.DE4V3R.T, K4.DE4V3R.LEAN)

`ClaimTMax` (**Claim T′**, a hypothesis, never an axiom): every non-completable maximum of the robust order (largest
robust level sum, then no (V3)-valid value-Pareto-better state) has every agent holding an upper set. It is weaker
than `ClaimT`, which speaks of every (V3)-valid state of the largest level sum, and it is all the frame needs: a proof
of Claim T′ may also use value-Pareto improvements that keep (V3) as contradictions.

**Results.**
- `potentialR_top_of_max`: a maximum has the largest robust level sum among (V3)-valid states.
- `claimTMax_of_claimT`: Claim T implies Claim T′.
- `conjRob_of_claimTMax`: Claim T′ and Theorem A′ imply Conjecture K4.DE4V3R.
- `target4_of_claimTMax`: **Claim T′ implies TARGET₄**.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

/-- **Claim T′** (a hypothesis, never an axiom): a non-completable maximum of the robust order has every agent holding
an upper set. -/
def ClaimTMax (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ Completable v agents goods base →
      ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- A maximum of the robust order has the largest robust level sum among the (V3)-valid states. -/
theorem potentialR_top_of_max {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}
    (hmax : IsMaximumR v agents goods base) :
    ∀ base', ValidV3 v agents goods base' → potentialR v agents goods base' ≤ potentialR v agents goods base :=
  fun base' hv' => Nat.le_of_not_lt fun hlt => hmax.2 base' hv' (Or.inl hlt)

/-- Claim T implies Claim T′. -/
theorem claimTMax_of_claimT (h : ClaimT A G) : ClaimTMax A G := by
  intro v agents goods hne hag hgd hc hs base hmax hnc
  exact h v agents goods hne hag hgd hc hs base hmax.1 (potentialR_top_of_max hmax) hnc

/-- **Claim T′ and Theorem A′ imply Conjecture K4.DE4V3R**: a non-completable maximum would have every agent holding
an upper set, and Theorem A′ would then give a better (V3)-valid state. -/
theorem conjRob_of_claimTMax (hT : ClaimTMax A G) (hA : ThmAllUpper A G) : ConjRob A G := by
  intro v agents goods hne hag hgd hc hs base hmax
  refine Classical.byContradiction fun hnc => ?_
  have hup := hT v agents goods hne hag hgd hc hs base hmax hnc
  obtain ⟨b', hv', hb'⟩ := hA v agents goods hne hag hgd hc hs base hmax.1 hup hnc
  exact hmax.2 b' hv' hb'

/-- **Claim T′ implies TARGET₄** (Theorem A′ and the frame of `DE4Robust.lean` are machine-checked): if every
non-completable maximum of the robust order has every agent holding an upper set, every instance in which each agent
positively values at most four goods has an EFX₀ allocation. -/
theorem target4_of_claimTMax (I : Inst) (hn : 0 < I.n) (h : ClaimTMax (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjRob I hn (conjRob_of_claimTMax h thmAllUpper) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.potentialR_top_of_max
#print axioms EFX.DE4.claimTMax_of_claimT
#print axioms EFX.DE4.conjRob_of_claimTMax
#print axioms EFX.DE4.target4_of_claimTMax
