import EFX.DE4Cor10

/-!
# DE4: Conjecture DE4 is false (`attempts/k4-de4.md`; ledger K4.DE4)

A strict R1-core with four agents and seven goods (core 131 of `results/k4_certs_4_n4_2.json.gz`, profile A of
`k4/de4/refute_de4.py`): agents 0–3 value the goods {0:3, 2:8, 4:2, 6:4}, {1:3, 3:2, 5:8, 6:4}, {2:4, 3:2, 6:3},
{4:2, 5:4, 6:3}. The state ({0, 4}, {1, 3}, {2}, {5}), with good 6 left over, is a maximum (`maximum`: valid, and no
valid state is better) with no EFX₀ completion (`not_completable`).

**Results.**
- `not_conjDE4`: Conjecture DE4 (`EFX.DE4.ConjDE4`) is false.
- `not_conjDE4Imp`, `not_conjDE4H`, `not_conjDE4H₂`: so are the improvement form and both forms of Conjecture 11″
  used as hypotheses in `DE4.lean`, `DE4Upgrade.lean` and `DE4Cor10.lean`.

**Method.** Every check is a kernel computation (`decide +kernel`, no `native_decide`). Strictness quantifies over
all sublists of the goods (`mem_subs`). Maximality: a valid state's holdings are allowed, so they lie in the finite
lists `allowedL i`, and the state is determined by its holdings (`recon_eq`); `check` runs through all 10 · 10 · 7 · 7
combinations of allowed holdings.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 100000

open EFX EFX.DE4

namespace EFX.DE4.Refute
def v : Fin 4 → Fin 7 → Nat
  | 0, 0 => 3 | 0, 2 => 8 | 0, 4 => 2 | 0, 6 => 4
  | 1, 1 => 3 | 1, 3 => 2 | 1, 5 => 8 | 1, 6 => 4
  | 2, 2 => 4 | 2, 3 => 2 | 2, 6 => 3
  | 3, 4 => 2 | 3, 5 => 4 | 3, 6 => 3
  | _, _ => 0
def agents : List (Fin 4) := [0, 1, 2, 3]
def goods : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]
def base : Fin 7 → Option (Fin 4)
  | 0 => some 0 | 4 => some 0 | 1 => some 1 | 3 => some 1 | 2 => some 2 | 5 => some 3 | _ => none

theorem core : R1Core4 v agents goods := by unfold R1Core4; decide

theorem mem_agents : ∀ j : Fin 4, j ∈ agents := by decide
theorem mem_goods : ∀ g : Fin 7, g ∈ goods := by decide

instance (i : Fin 4) (S : List (Fin 7)) : Decidable (Allowed v i goods S) := by
  unfold Allowed IsUpper IsLowerPair; infer_instance

instance (b : Fin 7 → Option (Fin 4)) : Decidable (Valid v agents goods b) :=
  decidable_of_iff ((∀ g ∈ goods, ∀ j ∈ agents, b g = some j → j ∈ agents) ∧
      (∀ i ∈ agents, Allowed v i goods (hold goods b i)) ∧
      (∀ i ∈ agents, ∀ g ∈ goods, value v i (hold goods b i) < v i g → ∃ j ∈ agents, hold goods b j = [g]) ∧
      (∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → ∀ h ∈ hold goods b j,
        value v i ((hold goods b j).erase h) ≤ value v i (hold goods b i))) (by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨fun g hg j hj => h1 g hg j (mem_agents j) hj, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨fun g hg j _ hj => h1 g hg j hj, h2, h3, h4⟩)

theorem valid_base : Valid v agents goods base := by decide

theorem not_completable : ¬ Completable v agents goods base := by
  rintro ⟨X, hall, hext, hefx⟩
  have h0 : X 0 = 0 := hext 0 (by decide) 0 rfl
  have h1 : X 1 = 1 := hext 1 (by decide) 1 rfl
  have h2 : X 2 = 2 := hext 2 (by decide) 2 rfl
  have h3 : X 3 = 1 := hext 3 (by decide) 1 rfl
  have h4 : X 4 = 0 := hext 4 (by decide) 0 rfl
  have h5 : X 5 = 3 := hext 5 (by decide) 3 rfl
  have hX : X = fun g => if g = 6 then X 6 else (match base g with | some j => j | none => 0) := by
    funext g
    match g with
    | 0 => simp [h0, base] | 1 => simp [h1, base] | 2 => simp [h2, base] | 3 => simp [h3, base]
    | 4 => simp [h4, base] | 5 => simp [h5, base] | 6 => simp
  clear hall
  generalize X 6 = x6 at hX
  subst hX
  clear hext h0 h1 h2 h3 h4 h5
  revert hefx
  match x6 with
  | 0 => unfold EFX0L bundle; decide
  | 1 => unfold EFX0L bundle; decide
  | 2 => unfold EFX0L bundle; decide
  | 3 => unfold EFX0L bundle; decide

def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => subs l ++ (subs l).map (a :: ·)

theorem mem_subs {α : Type} : ∀ {S l : List α}, S.Sublist l → S ∈ subs l := by
  intro S l h
  induction h with
  | slnil => simp [subs]
  | cons a _ ih => simp only [subs, List.mem_append]; exact Or.inl ih
  | cons_cons a _ ih => simp only [subs, List.mem_append, List.mem_map]; exact Or.inr ⟨_, ih, rfl⟩

theorem strictB : ∀ i ∈ agents, ∀ S ∈ subs goods, ∀ T ∈ subs goods, (∀ g ∈ S, g ∉ T) →
    value v i S = value v i T → value v i S = 0 := by decide +kernel

theorem strict : Strict v agents goods := fun i hi S T hS hT hd he =>
  strictB i hi S (mem_subs hS) T (mem_subs hT) hd he

instance (b : Fin 7 → Option (Fin 4)) : Decidable (Better v agents goods b base) := by
  unfold Better; infer_instance

def allowedL (i : Fin 4) : List (List (Fin 7)) := (subs goods).filter (fun S => decide (Allowed v i goods S))

def recon (H : Fin 4 → List (Fin 7)) : Fin 7 → Option (Fin 4) :=
  fun g => agents.find? (fun i => decide (g ∈ H i))

def pick (H0 H1 H2 H3 : List (Fin 7)) : Fin 4 → List (Fin 7)
  | 0 => H0 | 1 => H1 | 2 => H2 | _ => H3

theorem check : ∀ H0 ∈ allowedL 0, ∀ H1 ∈ allowedL 1, ∀ H2 ∈ allowedL 2, ∀ H3 ∈ allowedL 3,
    ¬ Better v agents goods (recon (pick H0 H1 H2 H3)) base ∨
      ¬ Valid v agents goods (recon (pick H0 H1 H2 H3)) := by decide +kernel

theorem recon_eq (b : Fin 7 → Option (Fin 4)) : recon (fun i => hold goods b i) = b := by
  funext g
  have key : ∀ j, g ∈ hold goods b j ↔ b g = some j := fun j => by
    rw [mem_hold]; exact ⟨fun h => h.2, fun h => ⟨mem_goods g, h⟩⟩
  unfold recon
  cases hbg : b g with
  | none =>
    rw [List.find?_eq_none]
    intro j _ hj
    rw [decide_eq_true_eq, key, hbg] at hj
    exact absurd hj (by simp)
  | some i =>
    simp only [key, hbg, Option.some.injEq, agents]
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl

theorem hold_pick (b : Fin 7 → Option (Fin 4)) :
    (fun i => hold goods b i) = pick (hold goods b 0) (hold goods b 1) (hold goods b 2) (hold goods b 3) := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

theorem maximum : IsMaximum v agents goods base := by
  refine ⟨valid_base, fun b hb hbet => ?_⟩
  have hmem : ∀ i, hold goods b i ∈ allowedL i := fun i =>
    List.mem_filter.mpr ⟨mem_subs List.filter_sublist, decide_eq_true (hb.allowed i (mem_agents i))⟩
  have hr : recon (pick (hold goods b 0) (hold goods b 1) (hold goods b 2) (hold goods b 3)) = b := by
    rw [← hold_pick, recon_eq]
  rcases check _ (hmem 0) _ (hmem 1) _ (hmem 2) _ (hmem 3) with h | h <;> rw [hr] at h
  · exact h hbet
  · exact h hb

/-- **Conjecture DE4 is false**: four agents, seven goods (`attempts/k4-de4.md`). -/
theorem not_conjDE4 : ¬ ConjDE4 (Fin 4) (Fin 7) := fun h =>
  not_completable (h v agents goods (by decide) (by decide) (by decide) core strict base maximum)

theorem not_conjDE4Imp : ¬ ConjDE4Imp (Fin 4) (Fin 7) := fun h => not_conjDE4 (conjDE4_of_imp h)
theorem not_conjDE4H : ¬ ConjDE4H (Fin 4) (Fin 7) := fun h => not_conjDE4Imp (conjDE4Imp_of_H h)
theorem not_conjDE4H₂ : ¬ ConjDE4H₂ (Fin 4) (Fin 7) := fun h => not_conjDE4H (conjDE4H_of_H₂ h)
end EFX.DE4.Refute

#print axioms EFX.DE4.Refute.core
#print axioms EFX.DE4.Refute.strict
#print axioms EFX.DE4.Refute.valid_base
#print axioms EFX.DE4.Refute.not_completable
#print axioms EFX.DE4.Refute.maximum
#print axioms EFX.DE4.Refute.check
#print axioms EFX.DE4.Refute.not_conjDE4
#print axioms EFX.DE4.Refute.not_conjDE4Imp
#print axioms EFX.DE4.Refute.not_conjDE4H
#print axioms EFX.DE4.Refute.not_conjDE4H₂
