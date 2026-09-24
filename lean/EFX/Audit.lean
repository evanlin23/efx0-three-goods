import EFX.Target
import EFX.CorollaryD

/-
# Adversarial audit: an independently written statement of TARGET and D

This file is written by the red team (workstream `formal/audit`). Its definitions below were
written from the informal statements alone, BEFORE reading `EFX/Model.lean`, `EFX/Target.lean`
or `EFX/CorollaryD.lean` (git history records this: the definitions were committed first).
They deliberately use a different representation from the project's model:

* an allocation is a function `Fin n → List (Fin m)` (bundles are lists, not sets or
  predicates), required to partition the goods: every bundle is duplicate-free and every good
  lies in exactly one bundle;
* the value of a bundle is computed by a hand-written recursive sum `Audit.lsum`;
* `X_j ∖ {g}` is `List.erase`;
* "positively values at most / exactly 3 goods" counts the goods of `List.finRange m` with
  positive value;
* "balanced" (each good is worth at most the sum of the agent's other two) is stated as
  `2 * v i g ≤ v i (all goods)`, which is equivalent when the agent has exactly 3 relevant goods.

Values are natural numbers (core Lean has no reals); the reduction from nonnegative real values
to natural numbers is lemma L12 (`proofs/real_values.md`), which this file does not formalize.

Informal statements audited (verbatim from the audit brief):

TARGET: every additive fair-division instance (n ≥ 1 agents, m goods, values v_i(g) ≥ 0) in
which each agent positively values at most 3 goods has a complete EFX₀ allocation, i.e. for all
agents i ≠ j and every good g in X_j (including goods i values at 0), v_i(X_i) ≥ v_i(X_j ∖ {g}).

D: every instance in which every agent positively values exactly 3 goods and is balanced (each
good worth at most the sum of the agent's other two) has an EFX₀ allocation in which at most one
bundle has more than two goods.
-/

namespace Audit

/-- The value of a list of goods under the valuation `f`: a hand-written recursive sum. -/
def lsum {m : Nat} (f : Fin m → Nat) : List (Fin m) → Nat
  | [] => 0
  | g :: gs => f g + lsum f gs

/-- `X : Fin n → List (Fin m)` is a complete allocation: each bundle has no repeated good, every
good lies in some bundle, and no good lies in two different bundles. -/
def IsPartition {n m : Nat} (X : Fin n → List (Fin m)) : Prop :=
  (∀ i, (X i).Nodup) ∧ (∀ g : Fin m, ∃ i, g ∈ X i) ∧
    (∀ (i j : Fin n) (g : Fin m), g ∈ X i → g ∈ X j → i = j)

/-- EFX₀: no agent `i` envies another agent's bundle after the removal of ANY single good of it,
including goods that `i` values at zero. -/
def IsEFX0 {n m : Nat} (v : Fin n → Fin m → Nat) (X : Fin n → List (Fin m)) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ g, g ∈ X j → lsum (v i) ((X j).erase g) ≤ lsum (v i) (X i)

/-- The goods agent `i` values positively ("relevant goods"), as a list. -/
def relevant {n m : Nat} (v : Fin n → Fin m → Nat) (i : Fin n) : List (Fin m) :=
  (List.finRange m).filter (fun g => decide (0 < v i g))

/-- Agent `i`'s value for the set of all goods. -/
def total {n m : Nat} (v : Fin n → Fin m → Nat) (i : Fin n) : Nat :=
  lsum (v i) (List.finRange m)

/-- Balanced: no good is worth more than the rest of the agent's goods together. With exactly
three relevant goods `a, b, c` this says `v a ≤ v b + v c` (and symmetrically). -/
def Balanced {n m : Nat} (v : Fin n → Fin m → Nat) : Prop :=
  ∀ i g, 2 * v i g ≤ total v i

/-- TARGET, stated independently: with at least one agent and at most three relevant goods per
agent, a complete EFX₀ allocation exists. -/
def TargetStmt : Prop :=
  ∀ (n m : Nat) (v : Fin n → Fin m → Nat), 0 < n →
    (∀ i, (relevant v i).length ≤ 3) →
    ∃ X : Fin n → List (Fin m), IsPartition X ∧ IsEFX0 v X

/-- D, stated independently: with at least one agent, exactly three relevant goods per agent and
balanced valuations, a complete EFX₀ allocation exists in which at most one bundle has more than
two goods (goods counted with no regard to value, zero-valued goods included). -/
def DStmt : Prop :=
  ∀ (n m : Nat) (v : Fin n → Fin m → Nat), 0 < n →
    (∀ i, (relevant v i).length = 3) → Balanced v →
    ∃ X : Fin n → List (Fin m), IsPartition X ∧ IsEFX0 v X ∧
      ∀ j k, 2 < (X j).length → 2 < (X k).length → j = k

/-! ## Bridge: the project's theorems imply the independent statements

Everything below was written after reading `EFX/Model.lean`. The bridge uses only the statements of
`EFX.target` and `EFX.LB.corollaryD` and the definitions `EFX.finSum`, `EFX.Inst`,
`EFX.Inst.bundleVal`, `EFX.Inst.EFX0`, `EFX.numRelevant`; all other lemmas are proved here. -/

section Bridge

variable {m : Nat}

theorem lsum_append (f : Fin m → Nat) (l l' : List (Fin m)) :
    lsum f (l ++ l') = lsum f l + lsum f l' := by
  induction l with
  | nil => simp [lsum]
  | cons g gs ih => simp only [List.cons_append, lsum, ih]; omega

theorem lsum_congr {f f' : Fin m → Nat} {l : List (Fin m)} (h : ∀ g ∈ l, f g = f' g) :
    lsum f l = lsum f' l := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [lsum, h g (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The project's `finSum` is the hand-written list sum over `List.finRange`. -/
theorem finSum_eq_lsum : ∀ (k : Nat) (f : Fin k → Nat), EFX.finSum k f = lsum f (List.finRange k)
  | 0, _ => rfl
  | k + 1, f => by
    rw [EFX.finSum, List.finRange_succ_last, lsum_append, finSum_eq_lsum k]
    have hmap : ∀ l : List (Fin k), lsum f (l.map Fin.castSucc) = lsum (fun i => f i.castSucc) l := by
      intro l; induction l with
      | nil => rfl
      | cons g gs ih => simp only [List.map_cons, lsum, ih]
    rw [hmap]; simp [lsum]

theorem lsum_filter (f : Fin m → Nat) (p : Fin m → Bool) (l : List (Fin m)) :
    lsum f (l.filter p) = lsum (fun g => if p g then f g else 0) l := by
  induction l with
  | nil => rfl
  | cons g gs ih => by_cases hp : p g <;> simp [hp, lsum, ih]

theorem length_eq_lsum (p : Fin m → Bool) (l : List (Fin m)) :
    (l.filter p).length = lsum (fun g => if p g then 1 else 0) l := by
  induction l with
  | nil => rfl
  | cons g gs ih => by_cases hp : p g <;> simp [hp, lsum, ih]; omega

theorem lsum_erase (f : Fin m → Nat) {g : Fin m} :
    ∀ {l : List (Fin m)}, g ∈ l → lsum f l = f g + lsum f (l.erase g)
  | [], h => absurd h (List.not_mem_nil)
  | x :: xs, h => by
    by_cases hx : x = g
    · subst hx; simp [lsum]
    · have hg : g ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      have he : (x :: xs).erase g = x :: xs.erase g := by simp [hx]
      rw [he, lsum, lsum, lsum_erase f hg]; omega

variable {n : Nat}

/-- The bundles of an owner map, as lists. -/
def bundles (X : Fin m → Fin n) (j : Fin n) : List (Fin m) :=
  (List.finRange m).filter (fun g => decide (X g = j))

theorem mem_bundles {X : Fin m → Fin n} {j : Fin n} {g : Fin m} : g ∈ bundles X j ↔ X g = j := by
  simp [bundles, List.mem_finRange]

theorem bundles_partition (X : Fin m → Fin n) : IsPartition (bundles X) :=
  ⟨fun _ => (List.nodup_finRange m).sublist List.filter_sublist,
   fun g => ⟨X g, mem_bundles.mpr rfl⟩,
   fun _ _ _ hi hj => (mem_bundles.mp hi).symm.trans (mem_bundles.mp hj)⟩

theorem bundleVal_none (v : Fin n → Fin m → Nat) (X : Fin m → Fin n) (i j : Fin n) :
    EFX.Inst.bundleVal ⟨n, m, v⟩ X i j none = lsum (v i) (bundles X j) := by
  rw [EFX.Inst.bundleVal, finSum_eq_lsum, bundles, lsum_filter]
  exact lsum_congr (fun g _ => by simp)

theorem bundleVal_some (v : Fin n → Fin m → Nat) (X : Fin m → Fin n) (i j : Fin n) (g : Fin m) :
    EFX.Inst.bundleVal ⟨n, m, v⟩ X i j (some g) = lsum (v i) ((bundles X j).erase g) := by
  rw [EFX.Inst.bundleVal, finSum_eq_lsum, bundles,
    List.Nodup.erase_eq_filter ((List.nodup_finRange m).sublist List.filter_sublist),
    List.filter_filter, lsum_filter]
  refine lsum_congr (fun x _ => ?_)
  by_cases h2 : x = g
  · subst h2; simp
  · have h3 : g ≠ x := Ne.symm h2
    by_cases h1 : X x = j <;> simp [h1, h2, h3]

/-- An owner map that is EFX₀ in the project's sense gives a list allocation that is EFX₀ in the
sense of this file. -/
theorem isEFX0_bundles (v : Fin n → Fin m → Nat) (X : Fin m → Fin n)
    (hX : EFX.Inst.EFX0 ⟨n, m, v⟩ X) : IsEFX0 v (bundles X) := by
  intro i j hij g hg
  have := hX i j hij g (mem_bundles.mp hg)
  rwa [bundleVal_some, bundleVal_none] at this

theorem numRelevant_eq (v : Fin n → Fin m → Nat) (i : Fin n) :
    EFX.numRelevant ⟨n, m, v⟩ i = (relevant v i).length := by
  rw [EFX.numRelevant, finSum_eq_lsum, relevant, length_eq_lsum]
  exact lsum_congr (fun g _ => by simp)

theorem length_bundles (X : Fin m → Fin n) (j : Fin n) :
    (bundles X j).length = EFX.finSum m (fun g => if X g = j then 1 else 0) := by
  rw [finSum_eq_lsum, bundles, length_eq_lsum]
  exact lsum_congr (fun g _ => by simp)

end Bridge

/-- **AUD-T**: the independently written TARGET follows from `EFX.target`. -/
theorem target_audit : TargetStmt := by
  intro n m v hn hrel
  obtain ⟨X, hX⟩ := EFX.target ⟨n, m, v⟩ hn (fun i => (numRelevant_eq v i).symm ▸ hrel i)
  exact ⟨bundles X, bundles_partition X, isEFX0_bundles v X hX⟩

/-- **AUD-D**: the independently written D follows from `EFX.LB.corollaryD`. -/
theorem corollaryD_audit : DStmt := by
  intro n m v hn hrel hbal
  obtain ⟨X, hX, o, ho⟩ := EFX.LB.corollaryD ⟨n, m, v⟩ hn
    (fun i => (numRelevant_eq v i).symm ▸ hrel i)
    (fun i g => (finSum_eq_lsum m (v i)).symm ▸ hbal i g)
  refine ⟨bundles X, bundles_partition X, isEFX0_bundles v X hX, fun j k hj hk => ?_⟩
  have hj' : j = o := Classical.byContradiction fun h => by
    have := ho j h; rw [← length_bundles] at this; omega
  have hk' : k = o := Classical.byContradiction fun h => by
    have := ho k h; rw [← length_bundles] at this; omega
  exact hj'.trans hk'.symm

end Audit

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms Audit.target_audit
#print axioms Audit.corollaryD_audit
