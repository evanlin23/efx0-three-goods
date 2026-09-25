import EFX.K3Theorem
import EFX.LB4RExamples

/-!
# C₄ᵐⁱⁿ's definitions are not vacuous (`k4/c4x.md` §1, §5)

Concrete instances, checked by `decide` (not a ledger item of its own; cited in K4.C4MIN.FRAME):
- **Ex3** (three agents with the same three goods, values 4, 3, 2; a strict k = 3 core, hence a strict k = 4 core):
  the pre-allocation "agent `i` holds good `i`" is in 𝒫, has two frozen agents, and **has the fewest frozen agents**
  (`Ex3.minFrozen`: every pre-allocation of 𝒫 has at least two, checked over all 64 base maps); it is Pareto-maximal
  (`Ex3.paretoMax`, over all base maps), so Theorem K3's hypotheses hold (`Ex3.k3_hyps`); it is removal-only completable
  without owner (`ω = −1`) and completable (`Ex3.completable`). So C₄ᵐⁱⁿ's conclusion holds on it (`Ex3.c4min`).
- **ExOmega** (from the independent audit of PR #47; a k = 3 core on a 3-cycle of agents): a Pareto-maximal
  pre-allocation (all 4,096 base maps checked) with `ω = 1`, so Theorem K3's owner branch is reached: a terminal is a
  removal-only owner (`ExOmega.k3_owner`, from `EFX.C4min.theoremK3_owner`).
- **ExW** (the core W1 of `EFX/LB4RExamples.lean`: two 4-good agents, strict): the pre-allocation {5} | {4} (Phase 1's
  picks) is in 𝒫 with no frozen agent (so it has the fewest), `ω = 2`, and it is removal-only completable **with an owner**:
  owner 1, the junk good 0 kept out of the owner's bundle (`ExW.removalOnly`). So C₄ᵐⁱⁿ's conclusion (both forms) holds on
  a k = 4 core with 4-good agents (`ExW.c4min`); the owner's bundle `{4} ∪ (J ∖ {0})` has four goods.

Tools: `frozenB` (a Boolean test for `Frozen` with the value-based needs; `nFrozen_eq`), `InP.unfold` (the fields of `InP`
with `NA` unfolded, decidable on finite instances), and the list of all base maps on three goods (`Tab3.tables`).
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

section generic

variable {A G : Type} [DecidableEq A] [DecidableEq G]
variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}

/-- A Boolean test for "frozen" with the value-based needs. -/
def frozenB (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (j : A) : Bool :=
  match baseOf goods base j with
  | [y] => agents.any (fun i => decide (vbNeeds v goods base i y))
  | _ => false

theorem frozen_iff_frozenB {j : A} :
    Frozen agents goods base (vbNeeds v goods base) j ↔ frozenB v agents goods base j = true := by
  unfold Frozen frozenB NA
  constructor
  · rintro ⟨y, hy, i, hi, hN⟩
    rw [hy]; exact List.any_eq_true.mpr ⟨i, hi, decide_eq_true hN⟩
  · intro h
    split at h
    · rename_i y hy
      obtain ⟨i, hi, hN⟩ := List.any_eq_true.mp h
      exact ⟨y, hy, i, hi, of_decide_eq_true hN⟩
    · cases h

theorem nFrozen_eq : nFrozen v agents goods base = agents.countP (frozenB v agents goods base) := by
  unfold nFrozen numFrozen
  apply List.countP_congr
  intro j _
  simp only [decide_eq_true_eq]
  exact frozen_iff_frozenB

theorem capSum_eq : capSum agents goods base (vbNeeds v goods base) =
    (agents.map (fun j => if frozenB v agents goods base j then (0 : Int) else
      2 - ((baseOf goods base j).length : Int))).sum := by
  unfold capSum
  congr 1
  apply List.map_congr_left
  intro j _
  unfold cap
  by_cases hF : Frozen agents goods base (vbNeeds v goods base) j
  · simp [hF, frozen_iff_frozenB.mp hF]
  · have : frozenB v agents goods base j = false := by
      cases h : frozenB v agents goods base j
      · rfl
      · exact absurd (frozen_iff_frozenB.mpr h) hF
    simp [hF, this]

theorem otherSlots_eq (w : A) : otherSlots agents goods base (vbNeeds v goods base) w =
    (agents.map (fun j => if j = w ∨ frozenB v agents goods base j = true then 0 else
      2 - (baseOf goods base j).length)).sum := by
  unfold otherSlots
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [frozen_iff_frozenB]

omit [DecidableEq G] in
/-- The fields of `InP`, with `NA` unfolded (decidable on finite instances). -/
theorem InP.unfold (h : InP v agents goods base) :
    (∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) ∧ (∀ g ∈ goods, ∀ i, base g = some i → 0 < v i g) ∧
    (∀ i, (baseOf goods base i).length ≤ 2) ∧
    (∀ g ∈ LB4.junk goods base, ¬ ∃ i ∈ agents, vbNeeds v goods base i g) ∧
    (∀ i, 2 ≤ (baseOf goods base i).length → ∀ g ∈ baseOf goods base i, ¬ ∃ i' ∈ agents, vbNeeds v goods base i' g) :=
  ⟨h.mem, h.rel, h.two, h.valid.v1, h.valid.v2⟩

omit [DecidableEq G] in
theorem InP.fold (h : (∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) ∧
    (∀ g ∈ goods, ∀ i, base g = some i → 0 < v i g) ∧ (∀ i, (baseOf goods base i).length ≤ 2) ∧
    (∀ g ∈ LB4.junk goods base, ¬ ∃ i ∈ agents, vbNeeds v goods base i g) ∧
    (∀ i, 2 ≤ (baseOf goods base i).length → ∀ g ∈ baseOf goods base i, ¬ ∃ i' ∈ agents, vbNeeds v goods base i' g)) :
    InP v agents goods base :=
  ⟨h.1, h.2.1, h.2.2.1, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩

end generic

/-! ## All base maps on three goods -/

namespace Tab3

def opts : List (Option (Fin 3)) := [none, some 0, some 1, some 2]

/-- The base map of a table `[B(0), B(1), B(2)]`. -/
def ofTable (t : List (Option (Fin 3))) : Fin 3 → Option (Fin 3) := fun g => t.getD g.val none

def tables : List (List (Option (Fin 3))) :=
  opts.flatMap fun a => opts.flatMap fun b => opts.map fun c => [a, b, c]

theorem mem_opts (o : Option (Fin 3)) : o ∈ opts := by
  match o with
  | none => simp [opts]
  | some ⟨0, _⟩ => simp [opts]
  | some ⟨1, _⟩ => simp [opts]
  | some ⟨2, _⟩ => simp [opts]

/-- Every base map on three goods and three agents is the base map of a table. -/
theorem table_of (b : Fin 3 → Option (Fin 3)) : ∃ t ∈ tables, b = ofTable t :=
  ⟨[b 0, b 1, b 2], by simp [tables, mem_opts],
    funext fun g => match g with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl⟩

end Tab3

/-! ## Ex3: three agents with the same three goods -/

namespace Ex3

open Tab3

/-- Every agent values goods 0, 1, 2 at 4, 3, 2. -/
def v : Fin 3 → Fin 3 → Nat := fun _ g => [4, 3, 2][g.val]!
abbrev ag : List (Fin 3) := List.finRange 3
abbrev gd : List (Fin 3) := List.finRange 3

/-- Agent `i` holds good `i`. -/
def b : Fin 3 → Option (Fin 3) := fun g => some g

theorem core3 : IsCore v ag gd := by unfold IsCore privateGoods; decide

theorem core : IsCore4 v ag gd := isCore4_of_isCore v core3

theorem strict : Strict v ag gd := LB4R.Examples.strict_of (by decide +kernel)

theorem inP : InP v ag gd b := InP.fold (by unfold b; decide)

/-- Agents 0 and 1 are frozen (agent 1 needs good 0, agent 2 needs goods 0 and 1); agent 2 is free. -/
theorem frozen_iff : ∀ j, Frozen ag gd b (vbNeeds v gd b) j ↔ j.val ≤ 1 := fun j => by
  rw [frozen_iff_frozenB]; revert j; decide

theorem nFrozen_b : nFrozen v ag gd b = 2 := by rw [nFrozen_eq]; decide

/-- **Fewest frozen agents**: every pre-allocation of 𝒫 has at least two frozen agents (all 64 base maps checked). -/
theorem minFrozen : MinFrozen v ag gd b := by
  refine ⟨inP, fun b' hb' => ?_⟩
  obtain ⟨t, ht, rfl⟩ := table_of b'
  have hc := hb'.unfold
  clear hb'
  rw [nFrozen_eq, nFrozen_eq]
  revert hc
  revert t
  decide +kernel

set_option synthInstance.maxSize 512 in
/-- **Pareto-maximal** (all 64 base maps checked), so Theorem K3 applies to it. -/
theorem paretoMax : ParetoMax v ag gd b := by
  refine ⟨inP, fun b' hb' hd => ?_⟩
  obtain ⟨t, ht, rfl⟩ := table_of b'
  have hc := hb'.unfold
  clear hb'
  unfold Dominates at hd
  revert hd hc
  revert t
  decide +kernel

/-- Theorem K3's hypotheses hold for `b`: Pareto-maximal, three goods per agent, balanced, `m ≤ 2n`. -/
theorem k3_hyps : ParetoMax v ag gd b ∧ Three v ag gd ∧ gd.length ≤ 2 * ag.length :=
  ⟨paretoMax, ⟨core3.2.1, core3.2.2.1⟩, by decide⟩

/-- `ω = |J| − S = 0 − 1 = −1`. -/
theorem omega_b : omegaP v ag gd b = -1 := by unfold omegaP; rw [capSum_eq]; decide

/-- Removal-only completable without owner (`ω ≤ 0`). -/
theorem removalOnly : RemovalOnly v ag gd b := by
  have := omega_b
  exact Or.inl ⟨by omega, by omega⟩

theorem completable : Completable v ag gd b :=
  completable_of_removalOnly (List.nodup_finRange 3) (List.nodup_finRange 3) (by decide) inP removalOnly

/-- **C₄ᵐⁱⁿ's conclusion holds on Ex3** (a strict k = 4 core): a pre-allocation with the fewest frozen agents (two) is
completable, even removal-only; it is also Pareto-maximal, and `ω = −1` (so no owner is needed). -/
theorem c4min : IsCore4 v ag gd ∧ Strict v ag gd ∧ ∃ base, MinFrozen v ag gd base ∧ Completable v ag gd base ∧
    RemovalOnly v ag gd base ∧ nFrozen v ag gd base = 2 ∧ ParetoMax v ag gd base ∧ omegaP v ag gd base = -1 :=
  ⟨core, strict, b, minFrozen, completable, removalOnly, nFrozen_b, paretoMax, omega_b⟩

end Ex3

/-! ## ExOmega: Theorem K3's owner branch is reached (from the independent audit of PR #47) -/

namespace ExOmega

/-- The 64 × 64 base maps on six goods and three agents, as tables. -/
def opts : List (Option (Fin 3)) := [none, some 0, some 1, some 2]

def ofTable (t : List (Option (Fin 3))) : Fin 6 → Option (Fin 3) := fun g => t.getD g.val none

def tables : List (List (Option (Fin 3))) :=
  opts.flatMap fun a => opts.flatMap fun b => opts.flatMap fun c => opts.flatMap fun d => opts.flatMap fun e =>
    opts.map fun f => [a, b, c, d, e, f]

theorem mem_opts (o : Option (Fin 3)) : o ∈ opts := by
  match o with
  | none => simp [opts]
  | some ⟨0, _⟩ => simp [opts]
  | some ⟨1, _⟩ => simp [opts]
  | some ⟨2, _⟩ => simp [opts]

theorem table_of (b : Fin 6 → Option (Fin 3)) : ∃ t ∈ tables, b = ofTable t :=
  ⟨[b 0, b 1, b 2, b 3, b 4, b 5], by simp [tables, mem_opts],
    funext fun g => match g with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
      | ⟨4, _⟩ => rfl
      | ⟨5, _⟩ => rfl⟩

/-- A k = 3 core on a 3-cycle of agents (goods 0, 2, 4 shared; 1, 3, 5 private). -/
def v : Fin 3 → Fin 6 → Nat := fun i g => [[6, 2, 7, 0, 0, 0], [0, 0, 6, 5, 3, 0], [5, 0, 0, 0, 7, 3]][i.val]![g.val]!
abbrev ag : List (Fin 3) := List.finRange 3
abbrev gd : List (Fin 6) := List.finRange 6

/-- Agent 0 holds 2, agent 1 holds 3, agent 2 holds {0, 4}; goods 1 and 5 are junk. -/
def b : Fin 6 → Option (Fin 3) := fun g => [some 2, none, some 0, some 1, some 2, none][g.val]!

theorem core3 : IsCore v ag gd := by unfold IsCore privateGoods; decide

theorem inP : InP v ag gd b := InP.fold ⟨by unfold b; decide, by unfold b; decide, by unfold b; decide,
  by unfold b; decide, by unfold b; decide⟩

/-- `ω = 1`: an owner is needed. -/
theorem omega_b : omegaP v ag gd b = 1 := by unfold omegaP; rw [capSum_eq]; decide

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 100000 in
/-- **Pareto-maximal** (all 4,096 base maps checked). -/
theorem paretoMax : ParetoMax v ag gd b := by
  refine ⟨inP, fun b' hb' hd => ?_⟩
  obtain ⟨t, ht, rfl⟩ := table_of b'
  have hc := hb'.unfold
  clear hb'
  unfold Dominates at hd
  revert hd hc
  revert t
  decide +kernel

/-- **Theorem K3's owner branch is reached**: `ω = 1`, so `theoremK3_owner` gives a terminal owner whose labels fit the
other agents' slots and whose bundle threatens nobody. -/
theorem k3_owner : ∃ t, Terminal v ag gd b t ∧ Unthreatened v ag gd b t (labelC v ag gd b t) ∧
    ((LB4.junk gd b).filter (labelC v ag gd b t)).length ≤ otherSlots ag gd b (vbNeeds v gd b) t := by
  rcases theoremK3_owner (List.nodup_finRange 3) (List.nodup_finRange 6) paretoMax ⟨core3.2.1, core3.2.2.1⟩
    (sigma_nonneg core3) with h | h
  · rw [omega_b] at h; exact absurd h (by decide)
  · exact h

end ExOmega

/-! ## ExW: the core W1 of `EFX/LB4RExamples.lean` -/

namespace ExW

open LB4R.Examples.W1 in
/-- The values of W1: agent 0 values goods 0, 1 (private), 4, 5; agent 1 goods 2, 3 (private), 4, 5. -/
abbrev v := LB4R.Examples.W1.v
abbrev ag : List (Fin 2) := List.finRange 2
abbrev gd : List (Fin 6) := List.finRange 6

/-- Phase 1's picks: agent 0 holds 5, agent 1 holds 4; goods 0–3 are junk. -/
def b : Fin 6 → Option (Fin 2) := fun g => [none, none, none, none, some 1, some 0][g.val]!

theorem inP : InP v ag gd b := InP.fold ⟨by unfold b; decide, by unfold b; decide, by unfold b; decide,
  by unfold b; decide, by unfold b; decide⟩

theorem noFrozen : ∀ j, ¬ Frozen ag gd b (vbNeeds v gd b) j := fun j h => by
  rw [frozen_iff_frozenB] at h; revert j; decide

theorem nFrozen_b : nFrozen v ag gd b = 0 := by rw [nFrozen_eq]; decide

/-- No frozen agent, so the fewest. -/
theorem minFrozen : MinFrozen v ag gd b := ⟨inP, fun _ _ => by rw [nFrozen_b]; exact Nat.zero_le _⟩

/-- `ω = |J| − S = 4 − 2 = 2`: an owner is needed. -/
theorem omega_b : omegaP v ag gd b = 2 := by unfold omegaP; rw [capSum_eq]; decide

/-- The junk good 0 is kept out of the owner's bundle. -/
def C : Fin 6 → Bool := fun g => g.val = 0

/-- The owner 1's bundle `{4} ∪ {1, 2, 3}` threatens nobody holding its base alone. -/
theorem unthreatened : Unthreatened v ag gd b 1 C := by
  unfold Unthreatened ownerBundle b C; decide

/-- **Removal-only completable with owner 1** (`def(P) ≤ 0`). -/
theorem removalOnly : RemovalOnly v ag gd b := by
  refine removalOnly_of_owner (by rw [omega_b]; decide) (by decide) (noFrozen 1) C unthreatened ?_
  rw [otherSlots_eq]; unfold b C; decide

theorem completable : Completable v ag gd b :=
  completable_of_removalOnly (List.nodup_finRange 2) (List.nodup_finRange 6) (by decide) inP removalOnly

/-- The owner's bundle has four goods: only the junk good 0 goes to agent 0's slot. -/
theorem ownerBundle_length : (ownerBundle gd b 1 C).length = 4 := by unfold ownerBundle b C; decide

/-- **C₄ᵐⁱⁿ's conclusion holds on W1** (a strict k = 4 core whose two agents have four goods): a pre-allocation with the
fewest frozen agents is completable, removal-only with an owner. -/
theorem c4min : IsCore4 v ag gd ∧ Strict v ag gd ∧ (∃ i ∈ ag, (relevant v i gd).length = 4) ∧
    ∃ base, MinFrozen v ag gd base ∧ Completable v ag gd base ∧ RemovalOnly v ag gd base ∧
      0 < omegaP v ag gd base :=
  ⟨LB4R.Examples.W1.core, LB4R.Examples.W1.strict, ⟨0, by decide, by decide⟩, b, minFrozen, completable,
    removalOnly, by rw [omega_b]; decide⟩

end ExW

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.nFrozen_eq
#print axioms EFX.C4min.Ex3.minFrozen
#print axioms EFX.C4min.Ex3.paretoMax
#print axioms EFX.C4min.Ex3.k3_hyps
#print axioms EFX.C4min.Ex3.c4min
#print axioms EFX.C4min.ExOmega.paretoMax
#print axioms EFX.C4min.ExOmega.k3_owner
#print axioms EFX.C4min.ExW.removalOnly
#print axioms EFX.C4min.ExW.c4min
