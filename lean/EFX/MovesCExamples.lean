import EFX.MovesC
import EFX.C4minExamples

/-!
# (T3⁺) is wider than R_T4: the n = 5 instance (`results/k4_rt4/n5b_FAILURES.md`; ledger K4.DL2.RT4, K4.DL2.RC.LEAN)

The smallest failure of DL_RT4 (ledger K4.DL2.RT4, REFUTED; `rt4-n5m9-chain`), found by compute/k4-rt4-n5b and merged with
PR #86: core pos 3206, idx 364, m = 9, of `results/k4_certs_5_n4_4.json.gz`, profile 108,86,1,108,27, the first row of
`results/k4_rt4/n5b_FAILURES.md`; the key of P is one of the failures of K4.DL13.KEY, and a (T3⁺) move repairs it
(ledger K4.DL2.RC). Five agents, nine goods,
- agent 0 on goods {0, 2, 4, 7} with values (6, 3, 5, 7); agent 1 on {1, 4, 7, 8}: (4, 2, 8, 7);
- agent 2 on {3, 6, 8}: (2, 4, 3); agents 3 and 4 on {5, 6, 7, 8}: (4, 8, 1, 6) and (2, 7, 8, 4);
- P = ({7}, {8}, {3}, {5}, {6}) (agents 0, 1, 4 frozen, NA = {6, 7, 8}) and its nearest better state
  P′ = ({0}, {8}, {3}, {6}, {7}): agent 0 (x) gives up 7 for {0}, agent 4 (the frozen intermediary, W = {4}) moves from
  6 to 7, agent 3 (z) moves from 5 to 6 and becomes frozen.

Checked here by `decide`: the instance is a k = 4 core (`core`; `IsCore4` only); P and P′ are pre-allocations of 𝒫
with three frozen agents each (`inP_P`, `inP_P'`, `nFrozen_P`, `nFrozen_P'`); the move P → P′ is a (T3⁺) move
(`moveT3plus_PP'`, with x = 0, z = 3, W = {4}, Y = ∅) and no move of R_T4: not a (T1) move (`not_moveT1_PP'`: agent 0
changes and is frozen in P, so it would be the re-based agent, which is free), not a (T2) move (`not_moveT2_PP'`:
agent 0 changes and is frozen in P, so it is outside the rotated set, which keeps every other base), not a (T3) move
(`not_moveT3_PP'`: agent 0 would be x, and then z would hold 7 in P′, but agent 4 does, which is frozen in P), not a
(T4) move (`not_moveT4_PP'`: agent 0 changes and is free in P′). `Ex5.wider` collects these facts and `Ex5.rc_not_rt4`
restates them: P → P′ is in R_C and outside R_T4.

Not checked in Lean (compute/k4-rt4-n5b's claims, from `k4/dlrt4.c` and its Python reference, and the certificate):
that the profile is strict and the core connected (`Strict`, `Connected`); that P and P′ have the fewest frozen
agents; def(P) = 1 and def(P′) = −1; and that no (T1), (T2), (T3) or (T4) move from P lowers the deficit. Values are
stored for the nine goods, with 0 for the goods outside an agent's set.
-/

set_option autoImplicit false

namespace EFX
namespace C4min
namespace Ex5

open LB4

/-- The values `v i g`, agent by agent, for goods 0–8. -/
def tbl : List (List Nat) :=
  [[6, 0, 3, 0, 5, 0, 0, 7, 0],
   [0, 4, 0, 0, 2, 0, 0, 8, 7],
   [0, 0, 0, 2, 0, 0, 4, 0, 3],
   [0, 0, 0, 0, 0, 4, 8, 1, 6],
   [0, 0, 0, 0, 0, 2, 7, 8, 4]]

def v : Fin 5 → Fin 9 → Nat := fun i g => (tbl.getD i.val []).getD g.val 0
abbrev ag : List (Fin 5) := List.finRange 5
abbrev gd : List (Fin 9) := List.finRange 9

/-- P = ({7}, {8}, {3}, {5}, {6}). -/
def P : Fin 9 → Option (Fin 5) := fun g =>
  [none, none, none, some 2, none, some 3, some 4, some 0, some 1].getD g.val none

/-- P′ = ({0}, {8}, {3}, {6}, {7}). -/
def P' : Fin 9 → Option (Fin 5) := fun g =>
  [some 0, none, none, some 2, none, none, some 3, some 4, some 1].getD g.val none

/-- The instance is a k = 4 core (`IsCore4`: five agents, three or four relevant goods each, strictly balanced, enough
private goods, every good relevant to someone). -/
theorem core : IsCore4 v ag gd := by unfold IsCore4 privateGoods sharedGoods; decide

theorem inP_P : InP v ag gd P := InP.fold ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem inP_P' : InP v ag gd P' := InP.fold ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem nFrozen_P : nFrozen v ag gd P = 3 := by rw [nFrozen_eq]; decide

theorem nFrozen_P' : nFrozen v ag gd P' = 3 := by rw [nFrozen_eq]; decide

theorem frozen_P (j : Fin 5) : Frozen ag gd P (vbNeeds v gd P) j ↔ frozenB v ag gd P j = true := frozen_iff_frozenB

theorem frozen_P' (j : Fin 5) : Frozen ag gd P' (vbNeeds v gd P') j ↔ frozenB v ag gd P' j = true :=
  frozen_iff_frozenB

/-- `W = {4}`: agent 4 is the only changed agent frozen in P and in P′. -/
theorem changedFrozen_iff (w : Fin 5) : ChangedFrozen v ag gd P P' w ↔ w = 4 := by
  unfold ChangedFrozen
  rw [frozen_P, frozen_P']
  revert w
  decide

/-- **P → P′ is a (T3⁺) move**: x = 0, z = 3 (needing good 6 in P), W = {4}, Y = ∅. -/
theorem moveT3plus_PP' : MoveT3plus v ag gd P P' := by
  refine ⟨0, by decide, 3, by decide, (frozen_P 0).mpr (by decide), fun h => absurd ((frozen_P' 0).mp h) (by decide),
    fun h => absurd ((frozen_P 3).mp h) (by decide), (frozen_P' 3).mpr (by decide), ⟨6, by decide, by decide⟩, [],
    by decide, by simp, fun i hi hi0 hi3 _ hne => ?_, fun B => ?_, by unfold NA; decide⟩
  · rw [frozen_P, frozen_P']
    revert i hi hi0 hi3 hne
    decide
  · simp only [changedFrozen_iff, exists_eq_left]
    rw [show baseOf gd P' 3 = [6] by decide, show baseOf gd P' 4 = [7] by decide,
      show baseOf gd P 0 = [7] by decide, show baseOf gd P 4 = [6] by decide]
    exact Or.comm

/-- **P → P′ is not a (T3) move**: agent 0 changes and is frozen in P, so it is the frozen agent `x` of the swap (good 7);
then `z` holds {7} in P′, so `z` is agent 4, which is frozen in P. -/
theorem not_moveT3_PP' : ¬ MoveT3 v ag gd P P' := by
  rintro ⟨x, -, z, -, g, hbx, -, hzf, -, hbz', H, -, hHp, hsame, -⟩
  have h0F : Frozen ag gd P (vbNeeds v gd P) 0 := (frozen_P 0).mpr (by decide)
  have hx : x = 0 := Classical.byContradiction fun hx0 => by
    have hz0 : (0 : Fin 5) ≠ z := fun e => hzf (e ▸ h0F)
    have hH0 : (0 : Fin 5) ∉ H := fun hm => (hHp 0 hm).2.2.2.1 h0F
    exact absurd (hsame 0 (by decide) (fun e => hx0 e.symm) hz0 hH0) (by decide)
  subst hx
  have hg : g = 7 := (List.cons.inj ((show baseOf gd P 0 = [7] by decide).symm.trans hbx)).1.symm
  subst hg
  have hz : ∀ z : Fin 5, baseOf gd P' z = [7] → frozenB v ag gd P z = true := by decide
  exact hzf ((frozen_P z).mpr (hz z hbz'))

/-- **P → P′ is not a (T1) move**: agent 0 changes and is frozen in P, so it would be the re-based agent, which is
free in P. -/
theorem not_moveT1_PP' : ¬ MoveT1 v ag gd P P' := by
  rintro ⟨y, -, hyf, -, -, hsame, -⟩
  have h0F : Frozen ag gd P (vbNeeds v gd P) 0 := (frozen_P 0).mpr (by decide)
  exact absurd (hsame 0 (by decide) fun e => hyf (e ▸ h0F)) (by decide)

/-- **P → P′ is not a (T2) move**: agent 0 changes and is frozen in P, so it is outside the rotated set, whose agents
are free in P, and keeps its base. -/
theorem not_moveT2_PP' : ¬ MoveT2 v ag gd P P' := by
  rintro ⟨Y, -, -, hYf, -, hsame, -⟩
  have h0F : Frozen ag gd P (vbNeeds v gd P) 0 := (frozen_P 0).mpr (by decide)
  exact absurd (hsame 0 (by decide) fun hm => (hYf 0 hm).2 h0F) (by decide)

/-- **P → P′ is not a (T4) move**: agent 0 changes and is free in P′. -/
theorem not_moveT4_PP' : ¬ MoveT4 v ag gd P P' := by
  rintro ⟨h, -⟩
  exact absurd ((frozen_P' 0).mp (h 0 (by decide) (by decide)).2) (by decide)

/-- **(T3⁺) is strictly wider than (T3) and (T4)**, on the n = 5 instance (a k = 4 core): P → P′ is a (T3⁺) move,
between two pre-allocations of 𝒫 with three frozen agents, and not a (T1), (T2), (T3) or (T4) move. -/
theorem wider : IsCore4 v ag gd ∧ InP v ag gd P ∧ InP v ag gd P' ∧ nFrozen v ag gd P = 3 ∧ nFrozen v ag gd P' = 3 ∧
    MoveT3plus v ag gd P P' ∧ ¬ MoveT1 v ag gd P P' ∧ ¬ MoveT2 v ag gd P P' ∧ ¬ MoveT3 v ag gd P P' ∧
    ¬ MoveT4 v ag gd P P' :=
  ⟨core, inP_P, inP_P', nFrozen_P, nFrozen_P', moveT3plus_PP', not_moveT1_PP', not_moveT2_PP', not_moveT3_PP',
    not_moveT4_PP'⟩

/-- **P → P′ is in R_C and outside R_T4**: R_C is strictly wider than R_T4 on this core. -/
theorem rc_not_rt4 : RC v ag gd P P' ∧ ¬ RT4 v ag gd P P' :=
  ⟨Or.inr (Or.inr (Or.inl moveT3plus_PP')), fun h => by
    rcases h with h | h | h | h
    · exact not_moveT1_PP' h
    · exact not_moveT2_PP' h
    · exact not_moveT3_PP' h
    · exact not_moveT4_PP' h⟩

end Ex5
end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.Ex5.core
#print axioms EFX.C4min.Ex5.inP_P
#print axioms EFX.C4min.Ex5.inP_P'
#print axioms EFX.C4min.Ex5.nFrozen_P
#print axioms EFX.C4min.Ex5.nFrozen_P'
#print axioms EFX.C4min.Ex5.frozen_P
#print axioms EFX.C4min.Ex5.frozen_P'
#print axioms EFX.C4min.Ex5.changedFrozen_iff
#print axioms EFX.C4min.Ex5.moveT3plus_PP'
#print axioms EFX.C4min.Ex5.not_moveT1_PP'
#print axioms EFX.C4min.Ex5.not_moveT2_PP'
#print axioms EFX.C4min.Ex5.not_moveT3_PP'
#print axioms EFX.C4min.Ex5.not_moveT4_PP'
#print axioms EFX.C4min.Ex5.wider
#print axioms EFX.C4min.Ex5.rc_not_rt4
