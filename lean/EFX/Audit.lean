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

/-! ## Non-vacuity

The definitions above are not trivially satisfied, and the hypotheses of both statements are
satisfiable. All concrete facts are checked by `decide` (kernel evaluation; no `native_decide`). -/

section NonVacuity

/-- Standard EFX (only goods the envious agent values positively may be removed), for contrast. -/
def IsEFX {n m : Nat} (v : Fin n → Fin m → Nat) (X : Fin n → List (Fin m)) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ g, g ∈ X j → 0 < v i g → lsum (v i) ((X j).erase g) ≤ lsum (v i) (X i)

/-- `total` counts only relevant goods. -/
theorem total_eq_relevant {n m : Nat} (v : Fin n → Fin m → Nat) (i : Fin n) :
    total v i = lsum (v i) (relevant v i) := by
  rw [total, relevant, lsum_filter]
  exact lsum_congr (fun g _ => by by_cases h : 0 < v i g <;> simp [h]; omega)

/-- `Balanced` at an agent with relevant goods `a, b, c` is exactly "each good is worth at most the
sum of the other two", as in the informal statement of D. -/
theorem balanced_iff_pairwise {n m : Nat} (v : Fin n → Fin m → Nat) (i : Fin n) {a b c : Fin m}
    (h : relevant v i = [a, b, c]) :
    (∀ g, 2 * v i g ≤ total v i) ↔
      (v i a ≤ v i b + v i c ∧ v i b ≤ v i a + v i c ∧ v i c ≤ v i a + v i b) := by
  have ht : total v i = v i a + v i b + v i c := by
    rw [total_eq_relevant, h]; simp only [lsum]; omega
  constructor
  · intro hb; have := hb a; have := hb b; have := hb c; omega
  · intro ⟨h1, h2, h3⟩ g
    by_cases hg : 0 < v i g
    · have hm : g ∈ relevant v i := by simp [relevant, List.mem_finRange, hg]
      rw [h] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> omega
    · omega

/-- With no agents, no allocation of a good exists: the hypothesis `0 < n` is needed. -/
theorem no_partition_without_agents : ¬ ∃ X : Fin 0 → List (Fin 1), IsPartition X :=
  fun ⟨_, _, hcov, _⟩ => (hcov 0).elim fun i _ => i.elim0

/-- Instance 1 (two agents, three goods). Agent 0 values every good 1; agent 1 values goods
0, 1, 2 at 2, 1, 0. Every agent has at most three relevant goods. -/
def v1 : Fin 2 → Fin 3 → Nat := fun i g => ([[1, 1, 1], [2, 1, 0]].getD i.val []).getD g.val 0

/-- Agent 0 gets goods 0 and 2 (good 2 is worth 0 to agent 1), agent 1 gets good 1. -/
def X1bad : Fin 2 → List (Fin 3) := fun i => if i = 0 then [0, 2] else [1]

/-- Agent 0 gets goods 1 and 2, agent 1 gets good 0. -/
def X1good : Fin 2 → List (Fin 3) := fun i => if i = 0 then [1, 2] else [0]

theorem v1_target_hyp : ∀ i, (relevant v1 i).length ≤ 3 := by decide
theorem X1bad_partition : IsPartition X1bad := by unfold IsPartition; decide
/-- `X1bad` is EFX ... -/
theorem X1bad_EFX : IsEFX v1 X1bad := by unfold IsEFX; decide
/-- ... but not EFX₀: agent 1 envies `{0, 2} ∖ {2} = {0}` (value 2 > 1), and good 2 is worth 0 to
agent 1. So `IsEFX0` really quantifies over zero-valued goods. -/
theorem X1bad_not_EFX0 : ¬ IsEFX0 v1 X1bad := by unfold IsEFX0; decide
theorem X1good_partition : IsPartition X1good := by unfold IsPartition; decide
theorem X1good_EFX0 : IsEFX0 v1 X1good := by unfold IsEFX0; decide

/-- Two agents, two goods, all values 1: giving both goods to agent 0 is not EFX₀ (nor EFX). -/
theorem all_to_one_not_EFX0 :
    ¬ IsEFX0 (fun (_ : Fin 2) (_ : Fin 2) => 1) (fun i => if i = 0 then [0, 1] else []) := by
  unfold IsEFX0; decide

/-- Lists that are not partitions: a missing good, a good in two bundles, a repeated good. -/
theorem not_partitions :
    ¬ IsPartition (fun (_ : Fin 1) => ([] : List (Fin 1))) ∧
    ¬ IsPartition (fun (_ : Fin 2) => ([0] : List (Fin 1))) ∧
    ¬ IsPartition (fun (_ : Fin 1) => ([0, 0] : List (Fin 1))) := by
  unfold IsPartition; decide

/-- Instance 2 (two agents, six goods): both agents value goods 0, 1, 2 at 1 and goods 3, 4, 5 at 0
(goods nobody values). It satisfies the hypotheses of D. -/
def v2 : Fin 2 → Fin 6 → Nat := fun _ g => if g.val < 3 then 1 else 0

theorem v2_D_hyp : (∀ i, (relevant v2 i).length = 3) ∧ Balanced v2 := by
  unfold Balanced total; decide

/-- At most one bundle of `X` has more than two goods. -/
def AtMostOneBig {n m : Nat} (X : Fin n → List (Fin m)) : Prop :=
  ∀ j k, 2 < (X j).length → 2 < (X k).length → j = k

/-- An allocation meeting D's conclusion for instance 2: bundles `{0, 1}` and `{2, 3, 4, 5}`. -/
def X2good : Fin 2 → List (Fin 6) := fun i => if i = 0 then [0, 1] else [2, 3, 4, 5]

/-- An allocation of instance 2 with two bundles of three goods. -/
def X2bad : Fin 2 → List (Fin 6) := fun i => if i = 0 then [0, 1, 3] else [2, 4, 5]

theorem v2_D_witness : IsPartition X2good ∧ IsEFX0 v2 X2good ∧ AtMostOneBig X2good := by
  unfold IsPartition IsEFX0 AtMostOneBig; decide

/-- `X2bad` violates both parts of D's conclusion: two bundles have three goods, and agent 1
envies `{0, 1, 3} ∖ {3}` (good 3 is worth 0 to agent 1). -/
theorem v2_D_violation : IsPartition X2bad ∧ ¬ IsEFX0 v2 X2bad ∧ ¬ AtMostOneBig X2bad := by
  unfold IsPartition IsEFX0 AtMostOneBig; decide

/-- An unbalanced agent (values 3, 1, 1) fails `Balanced`, and an agent with four relevant goods
fails TARGET's hypothesis: both hypotheses have content. -/
theorem hyps_not_trivial :
    ¬ Balanced (fun (_ : Fin 1) (g : Fin 3) => if g = 0 then 3 else 1) ∧
    ¬ (∀ i, (relevant (fun (_ : Fin 1) (_ : Fin 4) => 1) i).length ≤ 3) := by
  unfold Balanced total; decide

end NonVacuity

end Audit

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms Audit.target_audit
#print axioms Audit.corollaryD_audit
#print axioms Audit.balanced_iff_pairwise
#print axioms Audit.no_partition_without_agents
#print axioms Audit.v1_target_hyp
#print axioms Audit.X1bad_partition
#print axioms Audit.X1bad_EFX
#print axioms Audit.X1bad_not_EFX0
#print axioms Audit.X1good_partition
#print axioms Audit.X1good_EFX0
#print axioms Audit.all_to_one_not_EFX0
#print axioms Audit.not_partitions
#print axioms Audit.v2_D_hyp
#print axioms Audit.v2_D_witness
#print axioms Audit.v2_D_violation
#print axioms Audit.hyps_not_trivial
