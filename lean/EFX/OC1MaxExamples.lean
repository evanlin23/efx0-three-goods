import EFX.OC1Max

/-!
# Examples for `EFX.OC1Max` (non-vacuity, by evaluation)

On the strict MC2-class core of `k4/sdc.md` §31 on which OC fails (n = 5, m = 9; sets
[[0,3,6,8],[1,4,7,6],[2,5,8,7],[0,1,2],[0,1,2]], values [[10,6,5,7] for agents 0–2, [4,3,2], [2,4,3]]):
- `not_maximum_MC2`: the failing start, the index order with picks (0, 1, 2, –, –), is **not** a maximum-matching
  start (a matching of all five agents exists), so Conjecture OC₁^max does not ask about it;
- `maximum_ordM`, `oneAbsorber_ordM`: the order 3, 4, 0, 1, 2 picks a maximum matching, and its picks have a
  one-absorber EFX₀ completion (agent 0 absorbs goods 3, 4, 5), the first case of OC₁^max;
- `addition_ex`, `chain_ex`, `ring_ex`: each kind of move of `EFX.OC1Max.OneMove` occurs, at the index order's picks.

All facts are checked by `decide` (kernel evaluation of the definitions); the core and strictness conditions of
the instance are not re-checked here (they are in `k4/sdc/oc_mc2_cex_verify.py`).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max
namespace Ex

/-- The MC2-class core of `k4/sdc.md` §31 on which OC fails (n = 5, m = 9). -/
def vMC2 : Fin 5 → Fin 9 → Nat := fun i g =>
  match i.val, g.val with
  | 0, 0 => 10 | 0, 3 => 6 | 0, 6 => 5 | 0, 8 => 7
  | 1, 1 => 10 | 1, 4 => 6 | 1, 7 => 5 | 1, 6 => 7
  | 2, 2 => 10 | 2, 5 => 6 | 2, 8 => 5 | 2, 7 => 7
  | 3, 0 => 4 | 3, 1 => 3 | 3, 2 => 2
  | 4, 0 => 2 | 4, 1 => 4 | 4, 2 => 3
  | _, _ => 0

/-- The index order's picks: agents 0, 1, 2 take goods 0, 1, 2; agents 3 and 4 find nothing. -/
theorem picks_MC2 : ∀ i : Fin 5, sdPick vMC2 (List.finRange 5) (List.finRange 9) i =
    if i.val < 3 then some ⟨i.val, by omega⟩ else none := by decide

theorem card_picks_MC2 : card (List.finRange 5) (sdPick vMC2 (List.finRange 5) (List.finRange 9)) = 3 := by decide

/-- A matching of all five agents. -/
def μ5 : Fin 5 → Option (Fin 9) := fun i =>
  match i.val with
  | 0 => some 8 | 1 => some 4 | 2 => some 2 | 3 => some 0 | _ => some 1

theorem isMatching_μ5 : IsMatching vMC2 (List.finRange 5) (List.finRange 9) μ5 :=
  ⟨by decide, by decide⟩

theorem card_μ5 : card (List.finRange 5) μ5 = 5 := by decide

/-- **The failing start of OC on the MC2 core is not a maximum-matching start**, so OC₁^max does not see it. -/
theorem not_maximum_MC2 : ¬ IsMaximum vMC2 (List.finRange 5) (List.finRange 9)
    (sdPick vMC2 (List.finRange 5) (List.finRange 9)) := fun h => by
  have := h.2 μ5 isMatching_μ5
  rw [card_μ5, card_picks_MC2] at this
  omega

/-- A maximum-matching order on the MC2 core: agents 3 and 4 first. -/
def ordM : List (Fin 5) := [3, 4, 0, 1, 2]

theorem ordM_perm : ordM.Perm (List.finRange 5) := by decide

/-- Its picks match every agent (goods 8, 6, 2, 0, 1), so they form a maximum matching. -/
theorem maximum_ordM : IsMaximum vMC2 (List.finRange 5) (List.finRange 9) (sdPick vMC2 ordM (List.finRange 9)) := by
  refine ⟨isMatching_sdPick ordM_perm (List.nodup_finRange 9), fun μ' _ => ?_⟩
  have h5 : card (List.finRange 5) (sdPick vMC2 ordM (List.finRange 9)) = 5 := by decide
  rw [h5]
  have := List.countP_le_length (p := fun i => (μ' i).isSome) (l := List.finRange 5)
  simpa [card] using this

/-- The completion: agent 0 absorbs the junk goods 3, 4, 5; agent 2 takes the junk good 7. -/
def XM : Fin 9 → Fin 5 := fun g =>
  match g.val with
  | 0 => 3 | 1 => 4 | 2 => 2 | 6 => 1 | 7 => 2 | _ => 0

/-- **Non-vacuity**: at this maximum-matching start the picks have a one-absorber EFX₀ completion (the first case
of OC₁^max), checked by evaluation. -/
theorem oneAbsorber_ordM : OneAbsorber vMC2 (List.finRange 5) (List.finRange 9) (pickBase vMC2 (List.finRange 9) ordM) :=
  ⟨XM, by unfold IsAllocation; decide, by unfold EFX0L; decide, by decide, 0, by decide⟩

/-! ### The moves are satisfiable (at the index order's picks of the MC2 core) -/

/-- The index order's picks as bases. -/
abbrev B0 : Fin 5 → List (Fin 9) := pickBase vMC2 (List.finRange 9) (List.finRange 5)

/-- An addition: agent 0 adds the junk good 3. -/
theorem addition_ex : IsAddition vMC2 (List.finRange 5) (List.finRange 9) B0
    (fun i => if i = 0 then B0 i ++ [3] else B0 i) :=
  ⟨0, [3], by decide, by simp, by simp, by decide, by simp, fun y hy => by simp [hy]⟩

/-- A chain: agent 0 trades its top for the junk goods 3, 8 (13 > 10), and agent 3 takes good 0. -/
theorem chain_ex : IsChain vMC2 (List.finRange 5) (List.finRange 9) B0
    (fun i => if i = 0 then [3, 8] else if i = 3 then [0] else B0 i) :=
  ⟨0, [3], fun i => if i = 0 then [3, 8] else [], by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A ring 0 → 1 → 2 → 0: each agent takes its predecessor's top, worthless to it, with two junk goods (13 > 10). -/
theorem ring_ex : IsRing vMC2 (List.finRange 5) (List.finRange 9) B0
    (fun i => if i = 0 then [2, 3, 8] else if i = 1 then [0, 4, 6] else if i = 2 then [1, 5, 7] else B0 i) :=
  ⟨0, [1, 2], fun i => if i = 0 then [3, 8] else if i = 1 then [4, 6] else if i = 2 then [5, 7] else [],
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Ex
end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.Ex.picks_MC2
#print axioms EFX.OC1Max.Ex.card_picks_MC2
#print axioms EFX.OC1Max.Ex.isMatching_μ5
#print axioms EFX.OC1Max.Ex.not_maximum_MC2
#print axioms EFX.OC1Max.Ex.ordM_perm
#print axioms EFX.OC1Max.Ex.maximum_ordM
#print axioms EFX.OC1Max.Ex.oneAbsorber_ordM
#print axioms EFX.OC1Max.Ex.addition_ex
#print axioms EFX.OC1Max.Ex.chain_ex
#print axioms EFX.OC1Max.Ex.ring_ex
