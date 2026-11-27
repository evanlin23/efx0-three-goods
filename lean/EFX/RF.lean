import EFX.OCVariants
import EFX.SDE

/-!
# The receiver-first frame: Conjecture RF ⟹ OC₁^∃max ⟹ TARGET₄ (`k4/sdc.md` §31 end)

**Conjecture RF** (K4.SDC.RF, receiver first). In every strict connected `k = 4` core, at every maximum-matching
serial-dictatorship start `Y` where OC₁ fails:
- `Y` has exactly one *receiver* `u`, an agent whose pick no other agent prefers to its own (TTC's R2; `Receiver`);
- some order with `u` first gives a maximum matching;
- every order with `u` first that gives a maximum matching satisfies OC₁.

`ConjRF` is a `Prop`, not an axiom (with any move relation: `ConjRFWith`). It implies OC₁^∃max
(`conjOC1exmaxWith_of_conjRFWith`): MAXSD gives a maximum-matching order; either OC₁ holds there, or RF's receiver-first
order is a maximum-matching order where it does. With `EFX.OC1Max.target4_of_conjOC1exmax` this gives TARGET₄
(`target4_of_conjRF`). Only the second and third parts of RF are used.
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `u` is a **receiver** at `Y`: a listed agent whose pick no other listed agent prefers to its own. -/
def Receiver (v : A → G → Nat) (agents : List A) (Y : A → Option G) (u : A) : Prop :=
  u ∈ agents ∧ ∀ i ∈ agents, i ≠ u → ¬ Wants v Y i u

/-- **OC₁ at the order `ord`** for the move relation `Move`: the picks have a one-absorber completion, or one move
reaches a state that has one. -/
def OC1With (Move : MoveRel A G) (v : A → G → Nat) (agents : List A) (goods : List G) (ord : List A) : Prop :=
  OneAbsorber v agents goods (pickBase v goods ord) ∨
    ∃ B', Move v agents goods (pickBase v goods ord) B' ∧ OneAbsorber v agents goods B'

/-- **Conjecture RF for a move relation `Move`.** -/
def ConjRFWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      IsMaximum v agents goods (sdPick v ord goods) → ¬ OC1With Move v agents goods ord →
      ∃ u, (Receiver v agents (sdPick v ord goods) u ∧ ∀ u', Receiver v agents (sdPick v ord goods) u' → u' = u) ∧
        (∃ ord' : List A, ord'.Perm agents ∧ ord'.head? = some u ∧ IsMaximum v agents goods (sdPick v ord' goods)) ∧
        ∀ ord' : List A, ord'.Perm agents → ord'.head? = some u → IsMaximum v agents goods (sdPick v ord' goods) →
          OC1With Move v agents goods ord'

/-- **Conjecture RF** (K4.SDC.RF): `ConjRFWith` for the moves of `k4/sdc.md` §29 (an addition, a chain or a ring). -/
def ConjRF (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjRFWith A G (fun v agents goods => OneMove v agents goods)

/-- **RF ⟹ OC₁^∃max.** A maximum-matching order exists (MAXSD); either it satisfies OC₁, or RF's receiver-first
order is a maximum-matching order that does. -/
theorem conjOC1exmaxWith_of_conjRFWith {Move : MoveRel A G} (h : ConjRFWith A G Move) :
    ConjOC1exmaxWith A G Move := by
  intro agents goods v hag hgd hc hconn hs
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd (strictVals_of_strict hs)
  by_cases hoc : OC1With Move v agents goods ord
  · exact ⟨ord, hperm, hmax, hoc⟩
  · obtain ⟨u, -, ⟨ord', hperm', hhead, hmax'⟩, hall⟩ := h agents goods v hag hgd hc hconn hs ord hperm hmax hoc
    exact ⟨ord', hperm', hmax', hall ord' hperm' hhead hmax'⟩

/-- **RF ⟹ OC₁^∃max** for the moves of `k4/sdc.md` §29. -/
theorem conjOC1exmax_of_conjRF (h : ConjRF A G) : ConjOC1exmax A G :=
  conjOC1exmaxWith_of_conjRFWith h

/-- **Conjecture RF ⟹ TARGET₄** (through OC₁^∃max). -/
theorem target4_of_conjRF (I : Inst) (hn : 0 < I.n) (h : ConjRF (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1exmax I hn (conjOC1exmax_of_conjRF h) hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.conjOC1exmaxWith_of_conjRFWith
#print axioms EFX.OC1Max.conjOC1exmax_of_conjRF
#print axioms EFX.OC1Max.target4_of_conjRF
