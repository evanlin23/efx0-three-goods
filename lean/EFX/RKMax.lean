import EFX.RF

/-!
# The rank-maximal frame: Conjecture RKMAX ⟹ OC₁^∃max ⟹ TARGET₄ (`k4/sdc.md` §31 end)

**Conjecture RKMAX** (K4.SDC.RKMAX, rank-maximal start). For picks `Y`, agent `i`'s *rank* is
`1 + #{g ∈ R_i : v_i(g) > v_i(Y_i)}` (`pickRank`), and the *rank signature* of `Y` is
`σ = (#rank 1, #rank 2, #rank 3, #rank 4)` (`rankSig`), compared lexicographically (`LexLt`). RKMAX: in every strict
connected `k = 4` core, every maximum-matching serial-dictatorship order whose picks have a lexicographically maximal
signature among the maximum-matching orders satisfies OC₁ (`ConjRKMAX`, a `Prop`, not an axiom; any move relation:
`ConjRKMAXWith`).

**The frame** (`target4_of_conjRKMAX`): RKMAX implies OC₁^∃max (`conjOC1exmaxWith_of_conjRKMAXWith`), hence TARGET₄.
The orders are finitely many and some gives a maximum matching (MAXSD), so a lexicographically maximal one exists
(`exists_lexMax`: four nested argmaxes over the bounded counts).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- Strict lexicographic order on four counts. -/
def LexLt (s t : Nat × Nat × Nat × Nat) : Prop :=
  s.1 < t.1 ∨ (s.1 = t.1 ∧ (s.2.1 < t.2.1 ∨ (s.2.1 = t.2.1 ∧
    (s.2.2.1 < t.2.2.1 ∨ (s.2.2.1 = t.2.2.1 ∧ s.2.2.2 < t.2.2.2)))))

/-- **A lexicographic argmax**: over a nonempty set on which the four counts are bounded, some element has a
lexicographically maximal signature. -/
theorem exists_lexMax {α : Type} (P : α → Prop) (f : α → Nat × Nat × Nat × Nat) (B : Nat)
    (hB : ∀ a, P a → (f a).1 ≤ B ∧ (f a).2.1 ≤ B ∧ (f a).2.2.1 ≤ B ∧ (f a).2.2.2 ≤ B) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → ¬ LexLt (f a) (f b) := by
  obtain ⟨a₁, h₁, m₁⟩ := exists_max_of_bdd P (fun a => (f a).1) B (fun a ha => (hB a ha).1) h
  let P₂ : α → Prop := fun b => P b ∧ (f b).1 = (f a₁).1
  obtain ⟨a₂, h₂, m₂⟩ := exists_max_of_bdd P₂ (fun a => (f a).2.1) B (fun a ha => (hB a ha.1).2.1) ⟨a₁, h₁, rfl⟩
  let P₃ : α → Prop := fun b => P₂ b ∧ (f b).2.1 = (f a₂).2.1
  obtain ⟨a₃, h₃, m₃⟩ := exists_max_of_bdd P₃ (fun a => (f a).2.2.1) B (fun a ha => (hB a ha.1.1).2.2.1)
    ⟨a₂, h₂, rfl⟩
  let P₄ : α → Prop := fun b => P₃ b ∧ (f b).2.2.1 = (f a₃).2.2.1
  obtain ⟨a₄, h₄, m₄⟩ := exists_max_of_bdd P₄ (fun a => (f a).2.2.2) B (fun a ha => (hB a ha.1.1.1).2.2.2)
    ⟨a₃, h₃, rfl⟩
  obtain ⟨⟨⟨hP, e₁⟩, e₂⟩, e₃⟩ := h₄
  refine ⟨a₄, hP, fun b hb hlt => ?_⟩
  have k₁ : (f b).1 ≤ (f a₁).1 := m₁ b hb
  rcases hlt with hlt | ⟨q₁, hlt | ⟨q₂, hlt | ⟨q₃, hlt⟩⟩⟩
  · omega
  · have k₂ : (f b).2.1 ≤ (f a₂).2.1 := m₂ b ⟨hb, by omega⟩
    omega
  · have k₃ : (f b).2.2.1 ≤ (f a₃).2.2.1 := m₃ b ⟨⟨hb, by omega⟩, by omega⟩
    omega
  · have k₄ : (f b).2.2.2 ≤ (f a₄).2.2.2 := m₄ b ⟨⟨⟨hb, by omega⟩, by omega⟩, by omega⟩
    omega

/-- Agent `i`'s **rank** at the picks `Y`: one more than the number of its relevant goods it values above its pick. -/
def pickRank (v : A → G → Nat) (goods : List G) (Y : A → Option G) (i : A) : Nat :=
  1 + ((relevant v i goods).filter (fun g => decide (mval v Y i < v i g))).length

/-- The number of agents of rank `r`. -/
def rankCount (v : A → G → Nat) (agents : List A) (goods : List G) (Y : A → Option G) (r : Nat) : Nat :=
  (agents.filter (fun i => decide (pickRank v goods Y i = r))).length

/-- The **rank signature** `(#rank 1, #rank 2, #rank 3, #rank 4)`. -/
def rankSig (v : A → G → Nat) (agents : List A) (goods : List G) (Y : A → Option G) : Nat × Nat × Nat × Nat :=
  (rankCount v agents goods Y 1, rankCount v agents goods Y 2, rankCount v agents goods Y 3,
    rankCount v agents goods Y 4)

/-- **Conjecture RKMAX for a move relation `Move`.** -/
def ConjRKMAXWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      IsMaximum v agents goods (sdPick v ord goods) →
      (∀ ord' : List A, ord'.Perm agents → IsMaximum v agents goods (sdPick v ord' goods) →
        ¬ LexLt (rankSig v agents goods (sdPick v ord goods)) (rankSig v agents goods (sdPick v ord' goods))) →
      OC1With Move v agents goods ord

/-- **Conjecture RKMAX** (K4.SDC.RKMAX): `ConjRKMAXWith` for the moves of `k4/sdc.md` §29. -/
def ConjRKMAX (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjRKMAXWith A G (fun v agents goods => OneMove v agents goods)

/-- **RKMAX ⟹ OC₁^∃max.** A maximum-matching order exists (MAXSD), so a rank-maximal one does, and RKMAX applies to
it. -/
theorem conjOC1exmaxWith_of_conjRKMAXWith {Move : MoveRel A G} (h : ConjRKMAXWith A G Move) :
    ConjOC1exmaxWith A G Move := by
  intro agents goods v hag hgd hc hconn hs
  obtain ⟨ord₀, hperm₀, hmax₀⟩ := exists_order_maximum hag hgd (strictVals_of_strict hs)
  obtain ⟨ord, ⟨hperm, hmax⟩, hlex⟩ := exists_lexMax
    (fun ord : List A => ord.Perm agents ∧ IsMaximum v agents goods (sdPick v ord goods))
    (fun ord => rankSig v agents goods (sdPick v ord goods)) agents.length
    (fun _ _ => ⟨List.length_filter_le _ _, List.length_filter_le _ _, List.length_filter_le _ _,
      List.length_filter_le _ _⟩)
    ⟨ord₀, hperm₀, hmax₀⟩
  exact ⟨ord, hperm, hmax,
    h agents goods v hag hgd hc hconn hs ord hperm hmax fun ord' hperm' hmax' => hlex ord' ⟨hperm', hmax'⟩⟩

/-- **RKMAX ⟹ OC₁^∃max** for the moves of `k4/sdc.md` §29. -/
theorem conjOC1exmax_of_conjRKMAX (h : ConjRKMAX A G) : ConjOC1exmax A G :=
  conjOC1exmaxWith_of_conjRKMAXWith h

/-- **Conjecture RKMAX ⟹ TARGET₄** (through OC₁^∃max). -/
theorem target4_of_conjRKMAX (I : Inst) (hn : 0 < I.n) (h : ConjRKMAX (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1exmax I hn (conjOC1exmax_of_conjRKMAX h) hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.exists_lexMax
#print axioms EFX.OC1Max.conjOC1exmaxWith_of_conjRKMAXWith
#print axioms EFX.OC1Max.conjOC1exmax_of_conjRKMAX
#print axioms EFX.OC1Max.target4_of_conjRKMAX
