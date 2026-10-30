import EFX.K4Ties
import EFX.MinimalThreats

/-!
# A strict five-relevant obstruction to the two-good bundle shape

Two agents share four goods and each has one private good. The instance has an EFX₀
allocation, but every EFX₀ allocation gives each agent exactly three goods. Thus the
shape with at most one bundle larger than two does not extend to five relevant goods.
The finite check below evaluates all 64 owner maps in the kernel.
-/

set_option autoImplicit false

namespace EFX
namespace SparseShape

/-- Four common goods and one private good per agent, initially with unit values. -/
def unitValues (i : Fin 2) (g : Fin 6) : Nat :=
  if g.val < 4 ∨ g.val = 4 + i.val then 1 else 0

/-- Existing verified tie-breaking makes all positive subset sums distinct.
The value rows are `[96,80,72,68,66,0]` and `[96,80,72,68,0,65]`. -/
abbrev five : Inst := ⟨2, 6, tieBreak unitValues (List.finRange 6)⟩

def size (X : five.Alloc) (i : Fin 2) : Nat :=
  finSum 6 (fun g => if X g = i then 1 else 0)

def mk6 (a b c d e f : Fin 2) (g : Fin 6) : Fin 2 :=
  match g.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

theorem mk6_eq (X : five.Alloc) : mk6 (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) = X := by
  funext g
  match g with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨k + 6, h⟩ => exact absurd h (by omega)

theorem five_relevant : ∀ i, numRelevant five i = 5 := by decide

theorem five_strict : Strict five.v (List.finRange 2) (List.finRange 6) :=
  strict_tieBreak unitValues (List.finRange 6) (List.nodup_finRange 6)

theorem five_balanced : ∀ i : Fin 2, ∀ g : Fin 6,
    2 * five.v i g < value five.v i (List.finRange 6) := by decide

theorem five_private : ∀ i : Fin 2,
    (privateGoods five.v (List.finRange 2) i (List.finRange 6)).length = 1 ∧
    value five.v i (privateGoods five.v (List.finRange 2) i (List.finRange 6)) <
      value five.v i (sharedGoods five.v (List.finRange 2) i (List.finRange 6)) := by decide

theorem five_no_junk : ∀ g : Fin 6, ∃ i : Fin 2, 0 < five.v i g := by decide

theorem five_connected : Connected five.v (List.finRange 2) (List.finRange 6) := by
  intro S h i hi j hj
  have hpos : ∀ a : Fin 2, 0 < five.v a 0 := by decide
  exact h 0 (by decide) i hi j hj (hpos i) (hpos j)

theorem check_sizes : ∀ a b c d e f : Fin 2,
    five.EFX0 (mk6 a b c d e f) → ∀ i : Fin 2, size (mk6 a b c d e f) i = 3 := by
  unfold Inst.EFX0
  decide +kernel

/-- Every EFX₀ allocation has two bundles of three goods. -/
theorem five_sizes (X : five.Alloc) (h : five.EFX0 X) : ∀ i, size X i = 3 := by
  have hc := check_sizes (X 0) (X 1) (X 2) (X 3) (X 4) (X 5)
  rw [mk6_eq] at hc
  exact hc h

/-- This obstruction concerns shape only: an EFX₀ witness exists. -/
theorem five_exists : ∃ X : five.Alloc, five.EFX0 X :=
  ⟨mk6 0 0 1 1 0 1, by unfold Inst.EFX0; decide⟩

/-- No EFX₀ allocation has at most one bundle larger than two goods. -/
theorem five_not_d2 : ¬ ∃ X : five.Alloc, five.EFX0 X ∧
    ∀ i j : Fin 2, 2 < size X i → 2 < size X j → i = j := by
  rintro ⟨X, hE, hshape⟩
  have hs := five_sizes X hE
  have h01 := hshape 0 1 (by rw [hs]; decide) (by rw [hs]; decide)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- Two individually safe additions can be jointly threatening: neither added good is a
singleton need at threshold 3, but the pair of value-2 goods becomes a proper subset. -/
def jointValues (_ : Unit) (g : Fin 3) : Nat := if g.val < 2 then 2 else 0

theorem individually_safe_jointly_unsafe :
    Threats.Safe jointValues () 3 [0, 1] ∧
    Threats.Safe jointValues () 3 [0, 2] ∧
    ¬ Threats.Safe jointValues () 3 [0, 1, 2] ∧
    (∀ g : Fin 3, jointValues () g ≤ 3) ∧
    Threats.Minimal jointValues () 3 [0, 1] := by
  unfold Threats.Safe Threats.Minimal
  decide

end SparseShape
end EFX

#print axioms EFX.SparseShape.five_relevant
#print axioms EFX.SparseShape.five_strict
#print axioms EFX.SparseShape.five_balanced
#print axioms EFX.SparseShape.five_private
#print axioms EFX.SparseShape.five_no_junk
#print axioms EFX.SparseShape.five_connected
#print axioms EFX.SparseShape.five_sizes
#print axioms EFX.SparseShape.five_exists
#print axioms EFX.SparseShape.five_not_d2
#print axioms EFX.SparseShape.individually_safe_jointly_unsafe
