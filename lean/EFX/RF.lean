import EFX.OCVariants
import EFX.SDE

/-!
# The receiver-first frame: Conjecture RF ⟹ OC₁^∃max ⟹ TARGET₄ (`k4/sdc.md` §31 end)

**Conjecture RF** (K4.SDC.RF, receiver first, as amended after K4.SDC.R2.N5). In every strict connected `k = 4`
core, at every maximum-matching serial-dictatorship start `Y` where OC₁ fails, for every *receiver* `u` of `Y` (an
agent whose pick no other agent prefers to its own; `Receiver`):
- some order with `u` first gives a maximum matching;
- every order with `u` first that gives a maximum matching satisfies OC₁.

The first version asked for exactly one receiver; at `n = 5` there can be two (K4.SDC.R2.N5), so the uniqueness was
dropped. `ConjRF` is a `Prop`, not an axiom (with any move relation: `ConjRFWith`).

- Every start has a receiver: the last agent of the order, since a wanter of a pick comes after its holder
  (`exists_receiver`). So RF implies its weakest form **RF∃** (`ConjRFsome`: for *some* receiver), which is all the
  frame uses (`conjRFsomeWith_of_conjRFWith`).
- RF∃ implies OC₁^∃max (`conjOC1exmaxWith_of_conjRFsomeWith`): MAXSD gives a maximum-matching order; either OC₁
  holds there, or the receiver-first order of RF∃ is a maximum-matching order where it does.
- With `EFX.OC1Max.target4_of_conjOC1exmax`, both give TARGET₄ (`target4_of_conjRF`, `target4_of_conjRFsome`).
- `Receiver` counts a pickless agent vacuously, so `ConjRF` also asks RF of pickless receivers. `EFX/RFPick.lean`
  drops them: by Lemma REC-∃ a failing start has a receiver that holds a pick, so RF for pick-holding receivers
  (`ConjRFpick`) already implies RF∃ (`target4_of_conjRFpick`).
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

/-- What RF asks of a receiver `u`: some order with `u` first gives a maximum matching, and every such order
satisfies OC₁. -/
def ReceiverFirst (Move : MoveRel A G) (v : A → G → Nat) (agents : List A) (goods : List G) (u : A) : Prop :=
  (∃ ord' : List A, ord'.Perm agents ∧ ord'.head? = some u ∧ IsMaximum v agents goods (sdPick v ord' goods)) ∧
    ∀ ord' : List A, ord'.Perm agents → ord'.head? = some u → IsMaximum v agents goods (sdPick v ord' goods) →
      OC1With Move v agents goods ord'

/-- **Conjecture RF for a move relation `Move`** (amended form): at every maximum-matching start where OC₁ fails,
every receiver satisfies `ReceiverFirst`. -/
def ConjRFWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      IsMaximum v agents goods (sdPick v ord goods) → ¬ OC1With Move v agents goods ord →
      ∀ u, Receiver v agents (sdPick v ord goods) u → ReceiverFirst Move v agents goods u

/-- **RF∃ for a move relation `Move`**: at every maximum-matching start where OC₁ fails, *some* receiver satisfies
`ReceiverFirst`. -/
def ConjRFsomeWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      IsMaximum v agents goods (sdPick v ord goods) → ¬ OC1With Move v agents goods ord →
      ∃ u, Receiver v agents (sdPick v ord goods) u ∧ ReceiverFirst Move v agents goods u

/-- **Conjecture RF** (K4.SDC.RF): `ConjRFWith` for the moves of `k4/sdc.md` §29 (an addition, a chain or a ring). -/
def ConjRF (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjRFWith A G (fun v agents goods => OneMove v agents goods)

/-- **RF∃** for the moves of `k4/sdc.md` §29. -/
def ConjRFsome (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjRFsomeWith A G (fun v agents goods => OneMove v agents goods)

omit [DecidableEq A] in
/-- Nothing comes after the last element of a list without repetitions. -/
theorem not_before_getLast : ∀ {l : List A} (hne : l ≠ []), l.Nodup → ∀ a, ¬ Before l (l.getLast hne) a
  | [], hne, _, _, _ => absurd rfl hne
  | [_], _, _, _, h => by simp [Before] at h
  | x :: y :: t, _, hnd, a, h => by
    rw [List.getLast_cons (List.cons_ne_nil y t)] at h
    rcases h with ⟨hx, -⟩ | h
    · exact (List.nodup_cons.mp hnd).1 (by rw [← hx]; exact List.getLast_mem _)
    · exact not_before_getLast (List.cons_ne_nil y t) (List.nodup_cons.mp hnd).2 a h

/-- **Every start has a receiver**: the last agent of the order, since a wanter of a pick comes after its holder. -/
theorem exists_receiver {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A} (hσ : σ.Perm agents)
    (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ []) : ∃ u, Receiver v agents (sdPick v σ goods) u := by
  have hσne : σ ≠ [] := by
    rintro rfl; exact hne (List.Perm.eq_nil hσ.symm)
  have hu : σ.getLast hσne ∈ agents := hσ.mem_iff.mp (List.getLast_mem hσne)
  exact ⟨σ.getLast hσne, hu, fun i hi hiu hw =>
    not_before_getLast hσne (hσ.nodup_iff.mpr hag) i (before_of_wants hσ hag hgd hi hu hiu hw)⟩

/-- **RF ⟹ RF∃**: a core has at least two agents, so the failing start has a receiver. -/
theorem conjRFsomeWith_of_conjRFWith {Move : MoveRel A G} (h : ConjRFWith A G Move) : ConjRFsomeWith A G Move := by
  intro agents goods v hag hgd hc hconn hs ord hperm hmax hoc
  have hne : agents ≠ [] := by
    intro he; have := hc.1; rw [he] at this; simp at this
  obtain ⟨u, hu⟩ := exists_receiver (v := v) (goods := goods) hperm hag hgd hne
  exact ⟨u, hu, h agents goods v hag hgd hc hconn hs ord hperm hmax hoc u hu⟩

/-- **RF∃ ⟹ OC₁^∃max.** A maximum-matching order exists (MAXSD); either it satisfies OC₁, or RF∃'s receiver-first
order is a maximum-matching order that does. -/
theorem conjOC1exmaxWith_of_conjRFsomeWith {Move : MoveRel A G} (h : ConjRFsomeWith A G Move) :
    ConjOC1exmaxWith A G Move := by
  intro agents goods v hag hgd hc hconn hs
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd (strictVals_of_strict hs)
  by_cases hoc : OC1With Move v agents goods ord
  · exact ⟨ord, hperm, hmax, hoc⟩
  · obtain ⟨u, -, ⟨ord', hperm', hhead, hmax'⟩, hall⟩ := h agents goods v hag hgd hc hconn hs ord hperm hmax hoc
    exact ⟨ord', hperm', hmax', hall ord' hperm' hhead hmax'⟩

/-- **RF ⟹ OC₁^∃max**, for any move relation. -/
theorem conjOC1exmaxWith_of_conjRFWith {Move : MoveRel A G} (h : ConjRFWith A G Move) :
    ConjOC1exmaxWith A G Move :=
  conjOC1exmaxWith_of_conjRFsomeWith (conjRFsomeWith_of_conjRFWith h)

/-- **RF ⟹ OC₁^∃max** for the moves of `k4/sdc.md` §29. -/
theorem conjOC1exmax_of_conjRF (h : ConjRF A G) : ConjOC1exmax A G :=
  conjOC1exmaxWith_of_conjRFWith h

/-- **RF∃ ⟹ OC₁^∃max** for the moves of `k4/sdc.md` §29. -/
theorem conjOC1exmax_of_conjRFsome (h : ConjRFsome A G) : ConjOC1exmax A G :=
  conjOC1exmaxWith_of_conjRFsomeWith h

/-- **Conjecture RF ⟹ TARGET₄** (through OC₁^∃max). -/
theorem target4_of_conjRF (I : Inst) (hn : 0 < I.n) (h : ConjRF (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1exmax I hn (conjOC1exmax_of_conjRF h) hk

/-- **RF∃ ⟹ TARGET₄** (through OC₁^∃max). -/
theorem target4_of_conjRFsome (I : Inst) (hn : 0 < I.n) (h : ConjRFsome (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1exmax I hn (conjOC1exmax_of_conjRFsome h) hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.exists_receiver
#print axioms EFX.OC1Max.conjRFsomeWith_of_conjRFWith
#print axioms EFX.OC1Max.conjOC1exmaxWith_of_conjRFsomeWith
#print axioms EFX.OC1Max.conjOC1exmaxWith_of_conjRFWith
#print axioms EFX.OC1Max.conjOC1exmax_of_conjRF
#print axioms EFX.OC1Max.conjOC1exmax_of_conjRFsome
#print axioms EFX.OC1Max.target4_of_conjRF
#print axioms EFX.OC1Max.target4_of_conjRFsome
