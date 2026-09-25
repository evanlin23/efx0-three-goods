import EFX.LB4R

/-!
# LB₄ʳ is not vacuous: two runs that succeed (from the independent audit of PR #35)

Two certified k = 4 cores on which the relational LB₄ʳ of `EFX/LB4R.lean` succeeds, checked by `decide`: witnesses
that `Succeeds`, `UpRun`, `RotStep` and `Output` can all be satisfied (not a ledger item).
- **W1** (`k4_certs_2`: two 4-good agents, each with two private goods): Phase 1 in index order, policy "no
  upgrades", no rotation, and an owner holding four goods. It gives a `SoundCompletion` directly (`W1.sound_direct`)
  and through `sound_of_succeeds` (`W1.sound_pr`).
- **W2**: Phase 1 freezes agent 0 and no output exists before a rotation. One `RotStep` along the chain [0, 1] with
  O = {0} satisfies every conjunct (`rotate`, `RotChecks`, and ω = 1 with the signed caps); then `Succeeds` holds with
  the rotated one-good agent owning three goods.
-/

set_option autoImplicit false

namespace EFX
namespace LB4R
namespace Examples

open LB4

/-- All sublists of a list. -/
def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (subs l).map (a :: ·) ++ subs l

theorem mem_subs {α : Type} {S l : List α} (h : S.Sublist l) : S ∈ subs l := by
  induction h with
  | slnil => simp [subs]
  | cons a _ ih => simp [subs, ih]
  | cons_cons a _ ih => simp only [subs, List.mem_append, List.mem_map]; exact Or.inl ⟨_, ih, rfl⟩

/-- `Strict` from a finite check over the sublists of `goods`. -/
theorem strict_of {A G : Type} [DecidableEq A] [DecidableEq G] {v : A → G → Nat} {agents : List A}
    {goods : List G}
    (h : ∀ i ∈ agents, ∀ S ∈ subs goods, ∀ T ∈ subs goods, (∀ g ∈ S, g ∉ T) →
      value v i S = value v i T → value v i S = 0) : Strict v agents goods :=
  fun i hi S T hS hT hd he => h i hi S (mem_subs hS) T (mem_subs hT) hd he

theorem frozen_iff' {A G : Type} [DecidableEq A] [DecidableEq G] {agents : List A} {goods : List G}
    {base : G → Option A} {N : A → G → Prop} {j : A} :
    Frozen agents goods base N j ↔ ∃ y ∈ goods, baseOf goods base j = [y] ∧ NA agents N y := by
  constructor
  · rintro ⟨y, hy, hn⟩
    exact ⟨y, (mem_baseOf.mp (by rw [hy]; simp : y ∈ baseOf goods base j)).1, hy, hn⟩
  · rintro ⟨y, -, hy, hn⟩; exact ⟨y, hy, hn⟩

namespace W1

/-- Agent 0: goods 0, 1 (private), 4, 5; agent 1: goods 2, 3 (private), 4, 5. -/
def v : Fin 2 → Fin 6 → Nat := fun i g => [[3, 2, 0, 0, 4, 8], [0, 0, 2, 4, 8, 7]][i.val]![g.val]!
abbrev ag : List (Fin 2) := List.finRange 2
abbrev gd : List (Fin 6) := List.finRange 6

theorem core : IsCore4 v ag gd := by
  unfold IsCore4 privateGoods sharedGoods; decide

theorem strict : Strict v ag gd := strict_of (by decide +kernel)

/-- Phase 1 (index order): agent 0 picks 5, agent 1 (lost 5) picks 4; junk 0, 1, 2, 3. -/
def st : LState (Fin 2) (Fin 6) :=
  { base := fun g => [none, none, none, none, some 1, some 0][g.val]!
    pick := fun i => [some 5, some 4][i.val]!
    marked := fun _ => False }

instance : DecidablePred st.marked := fun _ => isFalse id

theorem phase1_eq : phase1State v ag gd [] = st := by
  unfold phase1State st
  dsimp only
  congr 1 <;> funext x <;> revert x <;> decide

/-- The owner 0 gets its base 5 and junk 0, 1, 2; agent 1's slot gets 3. -/
def X : Fin 6 → Fin 2 := fun g => [0, 0, 0, 1, 1, 0][g.val]!

theorem noNeeds : ∀ i g, ¬ ownerNeeds v gd X (needsOf v gd st) (some 0) i g := by
  unfold ownerNeeds needsOf; decide

theorem noNeedsN : ∀ i g, ¬ needsOf v gd st i g := by
  unfold needsOf; decide

theorem notFrozenX : ∀ j, ¬ Frozen ag gd st.base (ownerNeeds v gd X (needsOf v gd st) (some 0)) j :=
  fun _ ⟨_, _, ⟨i, _, h⟩⟩ => noNeeds i _ h

theorem notFrozenN : ∀ j, ¬ Frozen ag gd st.base (needsOf v gd st) j :=
  fun _ ⟨_, _, ⟨i, _, h⟩⟩ => noNeedsN i _ h

theorem omega_eq : omega v ag gd st = 2 := by
  unfold omega capSum cap
  simp only [notFrozenN, ite_false]
  decide

theorem output : Output v ag gd st (some 0) X := by
  refine ⟨⟨fun g _ => List.mem_finRange _, ?_, fun w hw => ?_, fun j _ _ hF => absurd hF (notFrozenX j), ?_⟩,
    ?_, fun _ => ?_⟩
  · have : ∀ g : Fin 6, ∀ i : Fin 2, st.base g = some i → X g = i := by decide
    exact fun g _ i h => this g i h
  · cases hw; exact ⟨List.mem_finRange _, notFrozenX 0⟩
  · have : ∀ j : Fin 2, some 0 ≠ some j →
        (junkOf gd st.base X j).length + (baseOf gd st.base j).length ≤ 2 := by decide
    exact fun j _ hjo _ => this j hjo
  · unfold OC; decide
  · rw [omega_eq]; decide

/-- **W1: LB₄ʳ succeeds** (index order, policy "no upgrades", no rotation). -/
theorem succeeds : Succeeds v ag gd [] := by
  refine ⟨.none, st, st, some 0, X, ?_, RotReach.refl 3 st, output⟩
  rw [phase1_eq]
  exact UpRun.done _ fun k g h => by obtain ⟨-, -, y, -, -, -, -, -, -, -, -, h⟩ := h

/-- The owner's bundle has four goods; both agents have four relevant goods. -/
theorem shape : (bundle gd X 0).length = 4 ∧ (relevant v 0 gd).length = 4 ∧ (relevant v 1 gd).length = 4 := by
  decide

/-- **C₄∃'s conclusion holds for W1**, proved directly (not through `sound_of_succeeds`): a sound completion. -/
theorem sound_direct : SoundCompletion v ag gd st.base (needsOf v gd st) (some 0) X := by
  refine ⟨fun i _ _ => ⟨fun g hg hb hlt => ?_, fun g hN => ?_⟩,
    ⟨fun g _ ⟨i, _, h⟩ => noNeeds i g h, fun _ _ g _ ⟨i, _, h⟩ => noNeeds i g h⟩, output.1, output.2.1⟩
  · exfalso
    have : ∀ i : Fin 2, ∀ g : Fin 6, st.base g ≠ some i → ¬ value v i (baseOf gd st.base i) < v i g := by decide
    exact this i g hb hlt
  · exact absurd hN (noNeedsN i g)

/-- And through `sound_of_succeeds`. -/
theorem sound_pr : ∃ (base : Fin 6 → Option (Fin 2)) (N : Fin 2 → Fin 6 → Prop) (o : Option (Fin 2))
    (X : Fin 6 → Fin 2), SoundCompletion v ag gd base N o X :=
  sound_of_succeeds (List.nodup_finRange 2) (List.nodup_finRange 6) succeeds

end W1

namespace W2

def v : Fin 2 → Fin 4 → Nat := fun i g => [[6, 4, 8, 5], [6, 3, 10, 2]][i.val]![g.val]!
abbrev ag : List (Fin 2) := List.finRange 2
abbrev gd : List (Fin 4) := List.finRange 4

theorem core : IsCore4 v ag gd := by
  unfold IsCore4 privateGoods sharedGoods; decide

theorem strict : Strict v ag gd := strict_of (by decide +kernel)

/-- Phase 1: agent 0 picks 2, agent 1 (lost 2) picks 0; junk 1, 3. -/
def st0 : LState (Fin 2) (Fin 4) :=
  { base := fun g => [some 1, none, some 0, none][g.val]!
    pick := fun i => [some 2, some 0][i.val]!
    marked := fun _ => False }

instance : DecidablePred st0.marked := fun _ => isFalse id

theorem phase1_eq : phase1State v ag gd [] = st0 := by
  unfold phase1State st0
  dsimp only
  congr 1 <;> funext x <;> revert x <;> decide

/-- After the rotation: agent 0 holds {0} (marked), agent 1 holds 2. -/
def st1 : LState (Fin 2) (Fin 4) :=
  { base := fun g => [some 0, none, some 1, none][g.val]!
    pick := fun i => [none, some 2][i.val]!
    marked := fun x => x = 0 }

instance : DecidablePred st1.marked := fun x => inferInstanceAs (Decidable (x = 0))

theorem rotate_eq : rotate st0 [0, 1] [0] = st1 := by
  unfold rotate st1
  congr 1
  · funext x; revert x; decide
  · funext x; revert x; decide
  · funext x; apply propext; revert x; decide

theorem frozenAt0 : FrozenAt v ag gd st0 0 := by
  refine ⟨id, 2, by decide, 1, List.mem_finRange _, ?_⟩
  unfold needsOf; decide

theorem notFrozenAt1 : ¬ FrozenAt v ag gd st0 1 := by
  rintro ⟨-, h⟩
  rw [frozen_iff'] at h
  revert h
  unfold NA needsOf; decide

theorem rotChecks : RotChecks v ag gd st1 := by
  refine ⟨⟨?_, ?_⟩, ?_, by decide⟩
  · unfold NA needsOf; decide
  · unfold NA needsOf; decide
  · unfold NA needsOf; decide

/-- A rotation along the chain [0, 1] with O = {0}: every conjunct of `RotStep`. -/
theorem rotStep : RotStep v ag gd st0 st1 := by
  refine ⟨[0, 1], 0, 1, [0], by decide, by decide, by decide, rfl, rfl, ?_, notFrozenAt1, by decide, by decide,
    by decide, rotate_eq.symm, rotChecks⟩
  intro i a b ha hb
  match i, ha, hb with
  | 0, ha, hb =>
    cases ha; cases hb
    exact ⟨frozenAt0, 2, rfl, by unfold needsOf; decide⟩
  | i + 1, _, hb => simp at hb

/-- Agent 0 (the rotated agent) owns 0, 1, 3; agent 1 holds its base 2. -/
def X : Fin 4 → Fin 2 := fun g => [0, 0, 1, 0][g.val]!

theorem noNeeds : ∀ i g, ¬ ownerNeeds v gd X (needsOf v gd st1) (some 0) i g := by
  unfold ownerNeeds needsOf; decide

theorem notFrozenX : ∀ j, ¬ Frozen ag gd st1.base (ownerNeeds v gd X (needsOf v gd st1) (some 0)) j :=
  fun _ ⟨_, _, ⟨i, _, h⟩⟩ => noNeeds i _ h

theorem frozen1 : Frozen ag gd st1.base (needsOf v gd st1) 1 := by
  rw [frozen_iff']; unfold NA needsOf; decide

theorem notFrozen0 : ¬ Frozen ag gd st1.base (needsOf v gd st1) 0 := by
  rw [frozen_iff']; unfold NA needsOf; decide

/-- ω = |J| − S = 2 − (1 + 0) = 1 with the text's signed caps (the rotated agent has a slot). -/
theorem omega_eq : omega v ag gd st1 = 1 := by
  unfold omega capSum
  have h0 : cap ag gd st1.base (needsOf v gd st1) 0 = 1 := by
    unfold cap; rw [ite_eq_right_of_eq_false _ _ (eq_false notFrozen0)]; decide
  have h1 : cap ag gd st1.base (needsOf v gd st1) 1 = 0 := by
    unfold cap; rw [ite_eq_left_of_eq_true _ _ (eq_true frozen1)]
  have hl : ag = [0, 1] := by decide
  rw [hl] at h0 h1 ⊢; simp only [List.map_cons, List.map_nil, h0, h1]
  decide

theorem output : Output v ag gd st1 (some 0) X := by
  refine ⟨⟨fun g _ => List.mem_finRange _, ?_, fun w hw => ?_, fun j _ _ hF => absurd hF (notFrozenX j), ?_⟩,
    ?_, fun _ => ?_⟩
  · have : ∀ g : Fin 4, ∀ i : Fin 2, st1.base g = some i → X g = i := by decide
    exact fun g _ i h => this g i h
  · cases hw; exact ⟨List.mem_finRange _, notFrozenX 0⟩
  · have : ∀ j : Fin 2, some 0 ≠ some j →
        (junkOf gd st1.base X j).length + (baseOf gd st1.base j).length ≤ 2 := by decide
    exact fun j _ hjo _ => this j hjo
  · unfold OC; decide
  · rw [omega_eq]; decide

/-- **W2: LB₄ʳ succeeds with one rotation.** -/
theorem succeeds : Succeeds v ag gd [] := by
  refine ⟨.none, st0, st1, some 0, X, ?_, RotReach.step 2 st0 st1 st1 rotStep (RotReach.refl 2 st1), output⟩
  rw [phase1_eq]
  exact UpRun.done _ fun k g h => by obtain ⟨-, -, y, -, -, -, -, -, -, -, -, h⟩ := h

/-- The rotated agent's base has one good and its bundle three; both agents have four relevant goods. -/
theorem shape : (bundle gd X 0).length = 3 ∧ (baseOf gd st1.base 0).length = 1 ∧
    (relevant v 0 gd).length = 4 ∧ (relevant v 1 gd).length = 4 := by decide

/-- Through `sound_of_succeeds`: a sound completion. -/
theorem sound_pr : ∃ (base : Fin 4 → Option (Fin 2)) (N : Fin 2 → Fin 4 → Prop) (o : Option (Fin 2))
    (X : Fin 4 → Fin 2), SoundCompletion v ag gd base N o X :=
  sound_of_succeeds (List.nodup_finRange 2) (List.nodup_finRange 4) succeeds

end W2

end Examples
end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.Examples.W1.core
#print axioms EFX.LB4R.Examples.W1.strict
#print axioms EFX.LB4R.Examples.W1.succeeds
#print axioms EFX.LB4R.Examples.W1.sound_direct
#print axioms EFX.LB4R.Examples.W1.sound_pr
#print axioms EFX.LB4R.Examples.W2.core
#print axioms EFX.LB4R.Examples.W2.strict
#print axioms EFX.LB4R.Examples.W2.rotStep
#print axioms EFX.LB4R.Examples.W2.succeeds
#print axioms EFX.LB4R.Examples.W2.sound_pr
