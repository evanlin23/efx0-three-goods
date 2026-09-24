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

end Audit
