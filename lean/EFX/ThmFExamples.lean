import EFX.ThmF
import EFX.C4minExamples

/-!
# Theorem F is not vacuous (`k4/c4min.md` §3.6)

A concrete instance, checked by `decide` (cited in K4.C4MIN.F.LEAN):
- **ExF** (three agents, five goods, a strict k = 4 core): agents 0 and 1 are frozen (holding goods 0 and 3), agent 2 is
  free (holding goods 2 and 4), and good 1 is the pool. This is a frozen-robust configuration (`ExF.cfg`, `ExF.frobust`) at
  the fewest frozen agents: every pre-allocation of 𝒫 has at least two frozen agents (`ExF.hmin`, all 1,024 base maps
  checked). Its pre-allocation has `ω = 1` (`ExF.omega_cfg`), so an owner is needed, and Theorem F applies with frozen
  agents (`ExF.c4min`).
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

namespace ExF

/-- The 4^5 = 1,024 base maps on five goods and three agents, as tables. -/
def opts : List (Option (Fin 3)) := [none, some 0, some 1, some 2]

def ofTable (t : List (Option (Fin 3))) : Fin 5 → Option (Fin 3) := fun g => t.getD g.val none

def tables : List (List (Option (Fin 3))) :=
  opts.flatMap fun a => opts.flatMap fun b => opts.flatMap fun c => opts.flatMap fun d =>
    opts.map fun e => [a, b, c, d, e]

theorem mem_opts (o : Option (Fin 3)) : o ∈ opts := by
  match o with
  | none => simp [opts]
  | some ⟨0, _⟩ => simp [opts]
  | some ⟨1, _⟩ => simp [opts]
  | some ⟨2, _⟩ => simp [opts]

theorem table_of (b : Fin 5 → Option (Fin 3)) : ∃ t ∈ tables, b = ofTable t :=
  ⟨[b 0, b 1, b 2, b 3, b 4], by simp [tables, mem_opts],
    funext fun g => match g with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
      | ⟨4, _⟩ => rfl⟩

/-- A strict k = 4 core with three agents and five goods. -/
def v : Fin 3 → Fin 5 → Nat := fun i g =>
  [[12, 0, 0, 16, 7], [13, 6, 0, 14, 4], [15, 0, 11, 8, 0]][i.val]![g.val]!
abbrev ag : List (Fin 3) := List.finRange 3
abbrev gd : List (Fin 5) := List.finRange 5

/-- Agents 0 and 1 are frozen. -/
def fr : Fin 3 → Bool := fun i => decide (i.val ≤ 1)

/-- Agent 0 holds good 0, agent 1 holds good 3, agent 2 holds {2, 4}; good 1 is the pool. Agent 0 needs good 3 (its
top), agent 2 needs good 0. -/
def hold : Fin 5 → Option (Fin 3) := fun g => [some 0, none, some 2, some 1, some 2][g.val]!

theorem core : IsCore4 v ag gd := by unfold IsCore4 privateGoods sharedGoods; decide

theorem strict : Strict v ag gd := LB4R.Examples.strict_of (by decide +kernel)

theorem cfg : IsCfg v ag gd fr hold := by
  have key : ∀ x : Fin 3, fr x = true →
      baseOf gd hold x = [if x.val = 0 then 0 else 3] ∧ 0 < v x (if x.val = 0 then 0 else 3) := by
    unfold hold fr; decide
  exact ⟨by unfold hold; decide, fun x _ hx => ⟨_, key x hx⟩, by unfold hold fr; decide,
    by unfold hold fr frG; decide⟩

theorem frobust : FRobust v ag gd fr hold := by unfold FRobust outN frG hold fr; decide

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 100000 in
/-- **Fewest frozen agents**: every pre-allocation of 𝒫 has at least two frozen agents (all 1,024 base maps checked). -/
theorem hmin : ∀ base, InP v ag gd base → ag.countP fr ≤ nFrozen v ag gd base := by
  intro b' hb'
  obtain ⟨t, ht, rfl⟩ := table_of b'
  have hc := hb'.unfold
  clear hb'
  rw [nFrozen_eq]
  revert hc
  revert t
  decide +kernel

/-- `ω = 1`: an owner is needed. -/
theorem omega_cfg : omegaP v ag gd (apaBase v hold) = 1 := by
  unfold omegaP; rw [capSum_eq]; unfold apaBase hold; decide

/-- **Theorem F applies with frozen agents**: on this k = 4 core some pre-allocation of 𝒫 with the fewest frozen agents
(two) has `def(P) ≤ 0` and is completable. -/
theorem c4min : IsCore4 v ag gd ∧ Strict v ag gd ∧ (∃ x ∈ ag, fr x = true) ∧ omegaP v ag gd (apaBase v hold) = 1 ∧
    ∃ base, MinFrozen v ag gd base ∧ RemovalOnly v ag gd base ∧ Completable v ag gd base :=
  ⟨core, strict, ⟨0, by simp, rfl⟩, omega_cfg,
    theoremF (List.nodup_finRange 3) (List.nodup_finRange 5) core cfg frobust hmin⟩

end ExF

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.ExF.cfg
#print axioms EFX.C4min.ExF.frobust
#print axioms EFX.C4min.ExF.hmin
#print axioms EFX.C4min.ExF.c4min
