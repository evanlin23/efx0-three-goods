import EFX.OCVariants
import EFX.DE4Refute

/-!
# OC₁^max is false at k = 4 (`k4/sdc.md` §31; ledger K4.SDC.OC1MAX)

**Instance 1** of `k4/sdc.md` §31 (found by the ordinal CEGAR of `compute/k4-oc1max-cert`, replayed by
`k4/sdc/oc1max_cex_verify.py`): four agents and seven goods, agents 0–3 valuing
{1:10, 5:7, 2:4, 0:2}, {1:10, 6:8, 5:4, 2:3}, {6:7, 5:6, 4:5, 3:3}, {6:4, 3:3, 4:2}. It is a strict connected k = 4 core
(`core`, `connected`, `strict`). The order 0, 3, 2, 1 gives the picks 1, 2, 5, 6 (`pickBase_eq`): every agent picks,
so they form a maximum matching (`maximum`) and a perfect start (`perfect`). The junk is {0, 3, 4}.

**Results.**
- `no_completion_picks`, `no_completion_move`: neither the picks nor any state one improving move reaches (an
  addition, a chain or a ring, `EFX.OC1Max.OneMove`) has an EFX₀ completion, not even a free one (any number of
  absorbers).
- **`not_conjOC1max`: Conjecture OC₁^max (`EFX.OC1Max.ConjOC1max`) is false**, and **`not_conjOC1perf`: so is OC₁
  at perfect starts (`EFX.OC1Max.ConjOC1perf`)**. The implications `target4_of_conjOC1max` and
  `target4_of_conjOC1perf` stand; OC₂^max, OC_k^max and the ∃-order form (`EFX/OCVariants.lean`) are not affected.

**Method.**
- `move_local` (general, any instance): after one move every agent either keeps its base, or strictly gains with a
  new base, without repetitions, inside its old base, one other agent's base and the junk.
- So a completion `X` of the picks or of a one-move state passes the test `crit X`: every agent keeps its pick
  under `X`, or some agent `j` makes the goods of `B i ∪ B j ∪ J` that `X` gives to `i` worth more to `i` than its
  pick (`crit_of_local`).
- No allocation passing the test is EFX₀ (`no_efx0_of_crit`). This is a kernel computation (`decide +kernel`, no
  `native_decide`) over all 4⁷ allocations, in 16 chunks fixed by the owners of goods 0 and 1 (`chunkab`); an
  allocation is recovered from its list of owners (`ofList_map`, `mem_allLists`). Strictness is checked over all
  sublists of the goods, as in `EFX/DE4Refute.lean` (`EFX.DE4.Refute.mem_subs`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace EFX
namespace OC1Max

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## After one move (any instance) -/

section afterMove
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem value_append_eq (i : A) (S T : List G) : value v i (S ++ T) = value v i S + value v i T := by
  simp [value]

omit [DecidableEq A] in
/-- The value of a list without repetitions is at most that of any list containing its goods. -/
theorem value_le_of_nodup_sub (i : A) : ∀ {L M : List G}, L.Nodup → (∀ g ∈ L, g ∈ M) →
    value v i L ≤ value v i M
  | [], _, _, _ => by simp
  | a :: t, M, hnd, hsub => by
    obtain ⟨hat, htn⟩ := List.nodup_cons.mp hnd
    have haM : a ∈ M := hsub a List.mem_cons_self
    have hM : value v i M = v i a + value v i (M.erase a) := by
      have := ((List.perm_cons_erase haM).map (v i)).sum_nat
      simpa [value] using this
    have ih := value_le_of_nodup_sub i htn fun g hg => by
      have hne : g ≠ a := fun e => hat (e ▸ hg)
      exact (List.mem_erase_of_ne hne).mpr (hsub g (List.mem_cons_of_mem _ hg))
    rw [value_cons, hM]; omega

omit [DecidableEq A] in
theorem nodup_append_junk {B : A → List G} {j : A} (hj : j ∈ agents) {H : List G} (hBj : (B j).Nodup)
    (hH : H.Nodup) (hHJ : ∀ g ∈ H, g ∈ junkOf agents goods B) : (B j ++ H).Nodup :=
  List.nodup_append.mpr ⟨hBj, hH, fun _ ha b hb e => (mem_junkOf.mp (hHJ b hb)).2 j hj (e ▸ ha)⟩

omit [DecidableEq A] [DecidableEq G] in
theorem exists_pair_of_mem {l₁ l₂ : List A} (hlen : l₂.length ≤ l₁.length) {i : A} (hi : i ∈ l₂) :
    ∃ p ∈ l₁.zip l₂, p.2 = i := by
  rw [← List.map_snd_zip hlen] at hi
  exact List.mem_map.mp hi

/-- **After one move** (`OneMove`), with bases without repetitions: every listed agent keeps its base, or it
strictly gains and its new base, without repetitions, lies inside its old base, the base of one listed agent `j`
and the junk. -/
theorem move_local {B B' : A → List G} (hB : ∀ k ∈ agents, (B k).Nodup) (h : OneMove v agents goods B B') :
    ∀ i ∈ agents, B' i = B i ∨ ∃ j ∈ agents, (B' i).Nodup ∧
      (∀ g ∈ B' i, g ∈ B i ∨ g ∈ B j ∨ g ∈ junkOf agents goods B) ∧ value v i (B i) < value v i (B' i) := by
  intro i hi
  rcases h with ⟨x, H, hx, hHne, hHnd, hHJ, hB'x, hB'y⟩ | ⟨x₀, xs, H, hxs, hnd, hag, hH, -, hH0, hHJ, hgain0,
    hpairs, hB'0, hB'p, hB'o⟩ | ⟨w₀, ws, H, -, -, hag, hH, -, hp, hB'o⟩
  · -- an addition
    by_cases hix : i = x
    · subst hix
      refine Or.inr ⟨i, hx, ?_, fun g hg => ?_, ?_⟩
      · rw [hB'x]; exact nodup_append_junk hx (hB i hx) hHnd fun g hg => (hHJ g hg).1
      · rw [hB'x] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inl hg
        · exact Or.inr (Or.inr (hHJ g hg).1)
      · rw [hB'x, value_append_eq]
        obtain ⟨h0, t, rfl⟩ := List.exists_cons_of_ne_nil hHne
        have := (hHJ h0 List.mem_cons_self).2
        rw [value_cons]; omega
    · exact Or.inl (hB'y i hix)
  · -- a chain
    by_cases hm : i ∈ x₀ :: xs
    · rcases List.mem_cons.mp hm with rfl | hixs
      · refine Or.inr ⟨(i :: xs).getLast (List.cons_ne_nil _ _),
          hag _ (List.getLast_mem (List.cons_ne_nil _ _)), ?_, fun g hg => ?_, ?_⟩
        · rw [hB'0]; exact (hH i hm).1
        · rw [hB'0] at hg
          rcases hH0 g hg with h1 | h1
          · exact Or.inr (Or.inr h1)
          · exact Or.inr (Or.inl h1)
        · rw [hB'0]; exact hgain0
      · obtain ⟨p, hp, rfl⟩ := exists_pair_of_mem (l₁ := x₀ :: xs) (by simp) hixs
        have hp1 : p.1 ∈ x₀ :: xs := (List.of_mem_zip hp).1
        refine Or.inr ⟨p.1, hag _ hp1, ?_, fun g hg => ?_, ?_⟩
        · rw [hB'p p hp]
          exact nodup_append_junk (hag _ hp1) (hB _ (hag _ hp1)) (hH _ hm).1 (hHJ _ hixs)
        · rw [hB'p p hp] at hg
          rcases List.mem_append.mp hg with hg | hg
          · exact Or.inr (Or.inl hg)
          · exact Or.inr (Or.inr (hHJ _ hixs g hg))
        · rw [hB'p p hp]; exact (hpairs p hp).2
    · exact Or.inl (hB'o i hm)
  · -- a ring
    by_cases hm : i ∈ w₀ :: ws
    · have hm' : i ∈ ws ++ [w₀] := by
        rcases List.mem_cons.mp hm with rfl | h
        · simp
        · exact List.mem_append_left _ h
      obtain ⟨p, hpm, rfl⟩ := exists_pair_of_mem (l₁ := w₀ :: ws) (by simp) hm'
      have hp1 : p.1 ∈ w₀ :: ws := (List.of_mem_zip hpm).1
      obtain ⟨-, hgain, hB'⟩ := hp p hpm
      refine Or.inr ⟨p.1, hag _ hp1, ?_, fun g hg => ?_, ?_⟩
      · rw [hB']
        exact nodup_append_junk (hag _ hp1) (hB _ (hag _ hp1)) (hH _ hm).1 fun g hg => ((hH _ hm).2 g hg).1
      · rw [hB'] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inr (Or.inl hg)
        · exact Or.inr (Or.inr ((hH _ hm).2 g hg).1)
      · rw [hB']; exact hgain
    · exact Or.inl (hB'o i hm)

end afterMove

/-! ## Instance 1 -/

namespace Cex1

def v : Fin 4 → Fin 7 → Nat
  | 0, 0 => 2 | 0, 1 => 10 | 0, 2 => 4 | 0, 5 => 7
  | 1, 1 => 10 | 1, 2 => 3 | 1, 5 => 4 | 1, 6 => 8
  | 2, 3 => 3 | 2, 4 => 5 | 2, 5 => 6 | 2, 6 => 7
  | 3, 3 => 3 | 3, 4 => 2 | 3, 6 => 4
  | _, _ => 0
def agents : List (Fin 4) := [0, 1, 2, 3]
def goods : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]
/-- The order 0, 3, 2, 1. -/
def ord : List (Fin 4) := [0, 3, 2, 1]
/-- Its picks. -/
def B : Fin 4 → List (Fin 7)
  | 0 => [1] | 1 => [2] | 2 => [5] | _ => [6]
/-- The junk at the picks. -/
def J : List (Fin 7) := [0, 3, 4]

theorem mem_agents : ∀ i : Fin 4, i ∈ agents := by decide
theorem mem_goods : ∀ g : Fin 7, g ∈ goods := by decide

theorem pickBase_eq : pickBase v goods ord = B := funext (by decide)
theorem junk_eq : junkOf agents goods B = J := by decide
theorem ord_perm : ord.Perm agents := by decide

theorem core : IsCore4 v agents goods := by unfold IsCore4; decide

theorem connected : Connected v agents goods := by
  intro S hS i hi j hj
  have h01 : S 0 = S 1 := hS 1 (by decide) 0 (by decide) 1 (by decide) (by decide) (by decide)
  have h12 : S 1 = S 2 := hS 5 (by decide) 1 (by decide) 2 (by decide) (by decide) (by decide)
  have h23 : S 2 = S 3 := hS 3 (by decide) 2 (by decide) 3 (by decide) (by decide) (by decide)
  have key : ∀ k : Fin 4, S k = S 0 := fun k => by
    match k with
    | 0 => rfl
    | 1 => exact h01.symm
    | 2 => exact (h01.trans h12).symm
    | 3 => exact (h01.trans (h12.trans h23)).symm
  rw [key i, key j]

theorem strictB : ∀ i ∈ agents, ∀ S ∈ DE4.Refute.subs goods, ∀ T ∈ DE4.Refute.subs goods, (∀ g ∈ S, g ∉ T) →
    value v i S = value v i T → value v i S = 0 := by decide +kernel

theorem strict : Strict v agents goods := fun i hi S T hS hT hd he =>
  strictB i hi S (DE4.Refute.mem_subs hS) T (DE4.Refute.mem_subs hT) hd he

theorem relevant_le : ∀ i ∈ agents, (relevant v i goods).length ≤ 4 := by decide

theorem card_picks : card agents (sdPick v ord goods) = 4 := by decide

/-- Every agent picks, so the picks form a maximum matching. -/
theorem maximum : IsMaximum v agents goods (sdPick v ord goods) := by
  refine ⟨isMatching_sdPick ord_perm (by decide), fun μ' _ => ?_⟩
  rw [card_picks]
  have := List.countP_le_length (p := fun i => (μ' i).isSome) (l := agents)
  simpa [card, agents] using this

/-- Every agent picks, so the picks form a perfect start. -/
theorem perfect : PerfectStart v agents goods (sdPick v ord goods) := by unfold PerfectStart; decide

/-! ### The test and the kernel computation -/

/-- All lists of owners of length `k`. -/
def allLists : Nat → List (List (Fin 4))
  | 0 => [[]]
  | k + 1 => (allLists k).flatMap (fun l => [0, 1, 2, 3].map (· :: l))

theorem mem_allLists : ∀ l : List (Fin 4), l ∈ allLists l.length
  | [] => by simp [allLists]
  | a :: l => by
    simp only [List.length_cons, allLists, List.mem_flatMap, List.mem_map]
    exact ⟨l, mem_allLists l, a, by revert a; decide, rfl⟩

/-- The allocation with a given list of owners. -/
def ofList (l : List (Fin 4)) : Fin 7 → Fin 4 := fun g => l.getD g.val 0

theorem ofList_map (X : Fin 7 → Fin 4) : ofList (goods.map X) = X := by
  funext g
  match g with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl

/-- Agent `i` keeps its pick under `X`. -/
def stay (X : Fin 7 → Fin 4) (i : Fin 4) : Bool := (B i).all (fun g => X g == i)

/-- Some agent `j` makes the goods of `B i ∪ B j ∪ J` that `X` gives to `i` worth more to `i` than its pick. -/
def moveOK (X : Fin 7 → Fin 4) (i : Fin 4) : Bool :=
  agents.any (fun j => decide (value v i (B i) <
    value v i (goods.filter (fun g => decide ((g ∈ B i ∨ g ∈ B j ∨ g ∈ J) ∧ X g = i)))))

/-- The test: every agent keeps its pick or can have moved. -/
def crit (X : Fin 7 → Fin 4) : Bool := agents.all (fun i => stay X i || moveOK X i)

theorem chunk00 : ∀ l ∈ allLists 5, crit (ofList (0 :: 0 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (0 :: 0 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk01 : ∀ l ∈ allLists 5, crit (ofList (0 :: 1 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (0 :: 1 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk02 : ∀ l ∈ allLists 5, crit (ofList (0 :: 2 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (0 :: 2 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk03 : ∀ l ∈ allLists 5, crit (ofList (0 :: 3 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (0 :: 3 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk10 : ∀ l ∈ allLists 5, crit (ofList (1 :: 0 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (1 :: 0 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk11 : ∀ l ∈ allLists 5, crit (ofList (1 :: 1 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (1 :: 1 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk12 : ∀ l ∈ allLists 5, crit (ofList (1 :: 2 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (1 :: 2 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk13 : ∀ l ∈ allLists 5, crit (ofList (1 :: 3 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (1 :: 3 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk20 : ∀ l ∈ allLists 5, crit (ofList (2 :: 0 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (2 :: 0 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk21 : ∀ l ∈ allLists 5, crit (ofList (2 :: 1 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (2 :: 1 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk22 : ∀ l ∈ allLists 5, crit (ofList (2 :: 2 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (2 :: 2 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk23 : ∀ l ∈ allLists 5, crit (ofList (2 :: 3 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (2 :: 3 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk30 : ∀ l ∈ allLists 5, crit (ofList (3 :: 0 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (3 :: 0 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk31 : ∀ l ∈ allLists 5, crit (ofList (3 :: 1 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (3 :: 1 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk32 : ∀ l ∈ allLists 5, crit (ofList (3 :: 2 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (3 :: 2 :: l)) := by
  unfold EFX0L bundle; decide +kernel

theorem chunk33 : ∀ l ∈ allLists 5, crit (ofList (3 :: 3 :: l)) = true →
    ¬ EFX0L v agents goods (ofList (3 :: 3 :: l)) := by
  unfold EFX0L bundle; decide +kernel
theorem chunk : ∀ a b : Fin 4, ∀ l ∈ allLists 5, crit (ofList (a :: b :: l)) = true →
    ¬ EFX0L v agents goods (ofList (a :: b :: l)) := by
  intro a b
  match a, b with
  | 0, 0 => exact chunk00
  | 0, 1 => exact chunk01
  | 0, 2 => exact chunk02
  | 0, 3 => exact chunk03
  | 1, 0 => exact chunk10
  | 1, 1 => exact chunk11
  | 1, 2 => exact chunk12
  | 1, 3 => exact chunk13
  | 2, 0 => exact chunk20
  | 2, 1 => exact chunk21
  | 2, 2 => exact chunk22
  | 2, 3 => exact chunk23
  | 3, 0 => exact chunk30
  | 3, 1 => exact chunk31
  | 3, 2 => exact chunk32
  | 3, 3 => exact chunk33

/-- **No allocation passing the test is EFX₀** (kernel computation over all 4⁷ allocations). -/
theorem no_efx0_of_crit (X : Fin 7 → Fin 4) (hc : crit X = true) : ¬ EFX0L v agents goods X := by
  rw [← ofList_map X] at hc ⊢
  have hl : goods.map X = X 0 :: X 1 :: [X 2, X 3, X 4, X 5, X 6] := rfl
  rw [hl] at hc ⊢
  exact chunk (X 0) (X 1) _ (mem_allLists _) hc

/-- **A completion of bases that satisfy `move_local`'s conclusion passes the test.** -/
theorem crit_of_local {B' : Fin 4 → List (Fin 7)}
    (hloc : ∀ i ∈ agents, B' i = B i ∨ ∃ j ∈ agents, (B' i).Nodup ∧
      (∀ g ∈ B' i, g ∈ B i ∨ g ∈ B j ∨ g ∈ junkOf agents goods B) ∧ value v i (B i) < value v i (B' i))
    (X : Fin 7 → Fin 4) (hX : ∀ i ∈ agents, ∀ g ∈ B' i, X g = i) : crit X = true := by
  refine List.all_eq_true.mpr fun i hi => ?_
  rcases hloc i hi with h | ⟨j, hj, hnd, hmem, hgain⟩
  · have : stay X i = true := List.all_eq_true.mpr fun g hg => by
      rw [← h] at hg; simp [hX i hi g hg]
    simp [this]
  · have : moveOK X i = true := List.any_eq_true.mpr ⟨j, hj, decide_eq_true (Nat.lt_of_lt_of_le hgain
      (value_le_of_nodup_sub i hnd fun g hg => List.mem_filter.mpr ⟨mem_goods g, decide_eq_true
        ⟨by rw [← junk_eq]; exact hmem g hg, hX i hi g hg⟩⟩))⟩
    simp [this]

/-- **The picks have no EFX₀ completion**, not even a free one. -/
theorem no_completion_picks : ¬ ∃ X : Fin 7 → Fin 4, EFX0L v agents goods X ∧
    ∀ i ∈ agents, ∀ g ∈ pickBase v goods ord i, X g = i := by
  rintro ⟨X, hE, hX⟩
  rw [pickBase_eq] at hX
  exact no_efx0_of_crit X (crit_of_local (fun i _ => Or.inl rfl) X hX) hE

/-- **No state one improving move reaches has an EFX₀ completion**, not even a free one. -/
theorem no_completion_move {B' : Fin 4 → List (Fin 7)} (hm : OneMove v agents goods (pickBase v goods ord) B') :
    ¬ ∃ X : Fin 7 → Fin 4, EFX0L v agents goods X ∧ ∀ i ∈ agents, ∀ g ∈ B' i, X g = i := by
  rintro ⟨X, hE, hX⟩
  rw [pickBase_eq] at hm
  have hloc := move_local (fun k _ => by revert k; decide) hm
  exact no_efx0_of_crit X (crit_of_local hloc X hX) hE

theorem not_oneAbsorber_picks : ¬ OneAbsorber v agents goods (pickBase v goods ord) := fun ⟨X, _, hE, hX, _⟩ =>
  no_completion_picks ⟨X, hE, hX⟩

theorem not_oneAbsorber_move {B' : Fin 4 → List (Fin 7)} (hm : OneMove v agents goods (pickBase v goods ord) B') :
    ¬ OneAbsorber v agents goods B' := fun ⟨X, _, hE, hX, _⟩ => no_completion_move hm ⟨X, hE, hX⟩

end Cex1

/-- **Conjecture OC₁^max is false** (ledger K4.SDC.OC1MAX): instance 1 of `k4/sdc.md` §31 with the order 0, 3, 2, 1. -/
theorem not_conjOC1max : ¬ ConjOC1max (Fin 4) (Fin 7) := fun h => by
  rcases h Cex1.agents Cex1.goods Cex1.v (by decide) (by decide) Cex1.core Cex1.connected Cex1.strict Cex1.ord
    Cex1.ord_perm Cex1.maximum with h0 | ⟨B', hm, hB'⟩
  · exact Cex1.not_oneAbsorber_picks h0
  · exact Cex1.not_oneAbsorber_move hm hB'

/-- **OC₁ at perfect starts is false**: the same start is perfect. -/
theorem not_conjOC1perf : ¬ ConjOC1perf (Fin 4) (Fin 7) := fun h => by
  rcases h Cex1.agents Cex1.goods Cex1.v (by decide) (by decide) (by decide) Cex1.relevant_le Cex1.strict Cex1.ord
    Cex1.ord_perm Cex1.perfect with h0 | ⟨B', hm, hB'⟩
  · exact Cex1.not_oneAbsorber_picks h0
  · exact Cex1.not_oneAbsorber_move hm hB'

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.value_le_of_nodup_sub
#print axioms EFX.OC1Max.move_local
#print axioms EFX.OC1Max.Cex1.core
#print axioms EFX.OC1Max.Cex1.connected
#print axioms EFX.OC1Max.Cex1.strict
#print axioms EFX.OC1Max.Cex1.maximum
#print axioms EFX.OC1Max.Cex1.perfect
#print axioms EFX.OC1Max.Cex1.no_efx0_of_crit
#print axioms EFX.OC1Max.Cex1.crit_of_local
#print axioms EFX.OC1Max.Cex1.no_completion_picks
#print axioms EFX.OC1Max.Cex1.no_completion_move
#print axioms EFX.OC1Max.not_conjOC1max
#print axioms EFX.OC1Max.not_conjOC1perf
