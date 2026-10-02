import EFX.DL13Moves
import EFX.C4minExamples

/-!
# Lemma 12 is not vacuous (`k4/dl13.md` §2.2)

The smallest failure of DL₁₃ (`k4/dl13.md` §2.2; `results/k4_dl13/n4_FAILURES.md`, core m = 6, idx 5 of
`results/k4_certs_4_n4_1.json.gz`), checked by `decide` (cited in K4.DL13.ROT.LEAN):
- **ExRot** (four agents, six goods, a strict k = 4 core, `ExRot.core`, `ExRot.strict`): agent 0 values goods
  0, 2, 4, 5 at 2, 3, 4, 8; agent 1 values goods 1, 3, 5 at 2, 4, 3; agents 2 and 3 value goods 3, 4, 5 at 3, 4, 2.
  `P = ({4}, {1}, {3}, {5})` (goods 0 and 2 junk) is min-frozen (`ExRot.minFrozen`: every pre-allocation of 𝒫 has at
  least three frozen agents; all 640 base maps that give each good to nobody or to an agent valuing it are checked, and
  the others are not in 𝒫) with `ω = 1` (`ExRot.omega_b`). Its only free agent, 1, has the optimal bundle `{0, 1}` of a
  best owner (`ExRot.optimal`: `Val*(P) = 2`, so `def(P) = 1`). Exchanging the goods of the frozen agents 0 and 3 is a
  Pareto reassignment (`ExRot.pareto`, `π = (0 3)`) and a (T4) move (`ExRot.moveT4`), after which `{0, 1, 2}` is safe for
  agent 1 (`ExRot.safe'`), so **Lemma 12's strict case applies: `def(P′) < def(P)`** (`ExRot.lemma12_example`, by
  `lemma12_lt`).
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

namespace ExRot

/-- The profile of `k4/dl13.md` §2.2 (four agents, six goods). -/
def v : Fin 4 → Fin 6 → Nat := fun i g =>
  [[2, 0, 3, 0, 4, 8], [0, 2, 0, 4, 0, 3], [0, 0, 0, 3, 4, 2], [0, 0, 0, 3, 4, 2]][i.val]![g.val]!
abbrev ag : List (Fin 4) := List.finRange 4
abbrev gd : List (Fin 6) := List.finRange 6

/-- `P = ({4}, {1}, {3}, {5})`: goods 0 and 2 are junk. -/
def b : Fin 6 → Option (Fin 4) := fun g => [none, some 1, none, some 2, some 0, some 3][g.val]!

/-- `P′ = ({5}, {1}, {3}, {4})`: agents 0 and 3 exchange their goods. -/
def b' : Fin 6 → Option (Fin 4) := fun g => [none, some 1, none, some 2, some 3, some 0][g.val]!

/-- `π` exchanges agents 0 and 3. -/
def π : Fin 4 → Fin 4 := fun i => [3, 1, 2, 0][i.val]!

theorem core : IsCore4 v ag gd := by unfold IsCore4 privateGoods sharedGoods; decide

theorem strict : Strict v ag gd := LB4R.Examples.strict_of (by decide +kernel)

/-! ## The base maps that may lie in 𝒫 -/

/-- The owners a good may have in 𝒫: nobody, or an agent that values it. -/
def optsOf (g : Fin 6) : List (Option (Fin 4)) :=
  none :: (List.finRange 4).filterMap fun i => if 0 < v i g then some (some i) else none

def ofTable (t : List (Option (Fin 4))) : Fin 6 → Option (Fin 4) := fun g => t.getD g.val none

/-- The 2 · 2 · 2 · 4 · 4 · 5 = 640 base maps giving each good to nobody or to an agent valuing it. -/
def tables : List (List (Option (Fin 4))) :=
  (optsOf 0).flatMap fun a => (optsOf 1).flatMap fun c => (optsOf 2).flatMap fun d =>
    (optsOf 3).flatMap fun e => (optsOf 4).flatMap fun f => (optsOf 5).map fun k => [a, c, d, e, f, k]

theorem mem_optsOf (g : Fin 6) (o : Option (Fin 4)) (h : ∀ i, o = some i → 0 < v i g) : o ∈ optsOf g := by
  cases o with
  | none => simp [optsOf]
  | some i =>
    have hi := h i rfl
    revert hi; revert i; revert g; decide

/-- Every base map whose base goods are valued by their owners is the base map of a table. -/
theorem table_of (b₀ : Fin 6 → Option (Fin 4)) (hrel : ∀ g ∈ gd, ∀ i, b₀ g = some i → 0 < v i g) :
    ∃ t ∈ tables, b₀ = ofTable t := by
  have hm : ∀ g : Fin 6, b₀ g ∈ optsOf g := fun g => mem_optsOf g _ (hrel g (List.mem_finRange g))
  refine ⟨[b₀ 0, b₀ 1, b₀ 2, b₀ 3, b₀ 4, b₀ 5], ?_, funext fun g => match g with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl⟩
  simp only [tables, List.mem_flatMap, List.mem_map]
  exact ⟨_, hm 0, _, hm 1, _, hm 2, _, hm 3, _, hm 4, _, hm 5, rfl⟩

/-! ## `P` is min-frozen, with `ω = 1` -/

theorem inP : InP v ag gd b := InP.fold ⟨by unfold b; decide, by unfold b; decide, by unfold b; decide,
  by unfold b; decide, by unfold b; decide⟩

theorem nFrozen_b : nFrozen v ag gd b = 3 := by rw [nFrozen_eq]; decide

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 100000 in
/-- **Fewest frozen agents**: every pre-allocation of 𝒫 has at least three frozen agents (640 base maps checked). -/
theorem minFrozen : MinFrozen v ag gd b := by
  refine ⟨inP, fun b₀ hb₀ => ?_⟩
  obtain ⟨t, ht, rfl⟩ := table_of b₀ hb₀.rel
  have hc := hb₀.unfold
  clear hb₀
  rw [nFrozen_b, nFrozen_eq]
  revert hc
  revert t
  decide +kernel

/-- `ω = 1`. -/
theorem omega_b : omegaP v ag gd b = 1 := by unfold omegaP; rw [capSum_eq]; decide

/-! ## The best owner: agent 1 with `{0, 1}` -/

/-- Agent 1 is free, and it is the only free agent. -/
theorem free1 : ¬ Frozen ag gd b (vbNeeds v gd b) 1 := by rw [frozen_iff_frozenB]; decide

theorem free_eq : ∀ o ∈ ag, ¬ Frozen ag gd b (vbNeeds v gd b) o → o = 1 := by
  simp only [frozen_iff_frozenB]; decide

/-- Every frozen agent's good is needed by an agent other than 1. -/
theorem needed_by_other : ∀ x ∈ ag, frozenB v ag gd b x = true →
    ∃ g ∈ baseOf gd b x, ∃ i ∈ ag, i ≠ 1 ∧ vbNeeds v gd b i g := by decide

open Classical in
/-- So `u_1(Z) = 0` for every `Z`. -/
theorem uCount_zero (Z : Fin 6 → Bool) : uCount v ag gd b 1 Z = 0 := by
  unfold uCount
  refine List.countP_eq_zero.mpr fun x hx hc => ?_
  obtain ⟨hF, hnot⟩ := of_decide_eq_true hc
  obtain ⟨g, hg, i, hi, hi1, hN⟩ := needed_by_other x hx (frozen_iff_frozenB.mp hF)
  exact (hnot g hg).2 i hi hi1 hN

def ofB (t : List Bool) : Fin 6 → Bool := fun g => t.getD g.val false

theorem bundle_len_tab : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    IsBundle gd b 1 (ofB [c0, c1, c2, c3, c4, c5]) → SafeFor v ag gd b 1 (ofB [c0, c1, c2, c3, c4, c5]) →
      (gd.filter (ofB [c0, c1, c2, c3, c4, c5])).length ≤ 2 := by
  intro c0 c1 c2 c3 c4 c5
  unfold IsBundle SafeFor
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;> decide

/-- A safe bundle of agent 1 in `P` has at most two goods (`{0, 1, 2}` threatens agent 0 holding good 4). -/
theorem bundle_len (Z : Fin 6 → Bool) (hZ : IsBundle gd b 1 Z) (hS : SafeFor v ag gd b 1 Z) :
    (gd.filter Z).length ≤ 2 := by
  have e : Z = ofB [Z 0, Z 1, Z 2, Z 3, Z 4, Z 5] := funext fun g => match g with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
  rw [e] at hZ hS ⊢
  exact bundle_len_tab _ _ _ _ _ _ hZ hS

/-- Agent 1's bundle `{0, 1}`. -/
def X : Fin 6 → Bool := fun g => decide (g.val ≤ 1)

/-- **`{0, 1}` is an optimal bundle of a best owner** (`Val*(P) = 2`). -/
theorem optimal : OptimalBest v ag gd b 1 X := by
  refine ⟨by decide, free1, by unfold IsBundle X b; decide, by unfold SafeFor X; decide, ?_⟩
  intro o' ho' hoF' Z hZ hS
  obtain rfl := free_eq o' ho' hoF'
  rw [uCount_zero, uCount_zero]
  have := bundle_len Z hZ hS
  have hX : (gd.filter X).length = 2 := by decide
  omega

/-! ## The frozen rotation -/

/-- **Exchanging the goods of agents 0 and 3 is a Pareto reassignment.** -/
theorem pareto : ParetoReassign v ag gd b b' π := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp only [frozen_iff_frozenB]) <;> decide

/-- It is a (T4) move (`moveT4_of_paretoReassign`). -/
theorem moveT4 : MoveT4 v ag gd b b' :=
  moveT4_of_paretoReassign (List.nodup_finRange 4) (List.nodup_finRange 6) minFrozen pareto

/-- After the exchange, `{0, 1} ∪ {2}` is safe for agent 1 (agent 0 holds good 5, worth 8 to it). -/
theorem safe' : SafeFor v ag gd b' 1 (fun g => X g || decide (g = 2)) := by unfold SafeFor X; decide

/-- **Lemma 12's strict case on the smallest failure of DL₁₃**: the frozen rotation lowers the deficit
(`lemma12_lt`, with `c = 2`). -/
theorem lemma12_example : DeficitLT v ag gd b' b :=
  lemma12_lt (List.nodup_finRange 4) (List.nodup_finRange 6) minFrozen (by rw [omega_b]; decide) pareto optimal
    (Or.inr ⟨2, List.mem_finRange 2, by decide, by decide, safe'⟩)

end ExRot

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.ExRot.core
#print axioms EFX.C4min.ExRot.strict
#print axioms EFX.C4min.ExRot.minFrozen
#print axioms EFX.C4min.ExRot.omega_b
#print axioms EFX.C4min.ExRot.optimal
#print axioms EFX.C4min.ExRot.pareto
#print axioms EFX.C4min.ExRot.moveT4
#print axioms EFX.C4min.ExRot.lemma12_example
