import EFX.T6
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
- `EFX.OC1Max.move_local` (`EFX/OC1MaxMoves.lean`, any instance): after one move every agent either keeps its
  base, or strictly gains with a new base, without repetitions, inside one agent's base and the junk.
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

/-- **A completion of bases that satisfy (a weak form of) `move_local`'s conclusion passes the test.** -/
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
  refine no_efx0_of_crit X (crit_of_local (fun i hi => (hloc i hi).imp id fun ⟨j, hj, hnd, hmem, hgain⟩ =>
    ⟨j, hj, hnd, fun g hg => (hmem g hg).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)), hgain⟩)
    X hX) hE

theorem not_oneAbsorber_picks : ¬ OneAbsorber v agents goods (pickBase v goods ord) := fun ⟨X, _, hE, hX, _⟩ =>
  no_completion_picks ⟨X, hE, hX⟩

theorem not_oneAbsorber_move {B' : Fin 4 → List (Fin 7)} (hm : OneMove v agents goods (pickBase v goods ord) B') :
    ¬ OneAbsorber v agents goods B' := fun ⟨X, _, hE, hX, _⟩ => no_completion_move hm ⟨X, hE, hX⟩

/-! ### A second, structural refutation: Lemma T6's certificate -/

/-- The picks. -/
def y : Fin 4 → Fin 7
  | 0 => 1 | 1 => 2 | 2 => 5 | _ => 6

theorem B_eq_y : ∀ k ∈ agents, B k = [y k] := by decide

theorem validState_B : ValidState agents goods B := ⟨by decide, by decide⟩

/-- `X` value-dominates the picks. -/
def dom (X : Fin 7 → Fin 4) : Bool :=
  agents.all (fun i => decide (value v i (B i) ≤ value v i (bundle goods X i)))

/-- Lemma T6's certificate at `X`: some agent holds three other agents' picks, or two, each worth so little that
with all of its junk it does not beat its pick. -/
def cert (X : Fin 7 → Fin 4) : Bool :=
  agents.any (fun i => decide (3 ≤ (foreignPicks agents y X i).length ∨
    (2 ≤ (foreignPicks agents y X i).length ∧ ∀ k ∈ foreignPicks agents y X i,
      v i (y k) + value v i (relevant v i J) ≤ value v i (B i))))

theorem certChunk00 : ∀ l ∈ allLists 5, dom (ofList (0 :: 0 :: l)) = true →
    EFX0L v agents goods (ofList (0 :: 0 :: l)) → cert (ofList (0 :: 0 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk01 : ∀ l ∈ allLists 5, dom (ofList (0 :: 1 :: l)) = true →
    EFX0L v agents goods (ofList (0 :: 1 :: l)) → cert (ofList (0 :: 1 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk02 : ∀ l ∈ allLists 5, dom (ofList (0 :: 2 :: l)) = true →
    EFX0L v agents goods (ofList (0 :: 2 :: l)) → cert (ofList (0 :: 2 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk03 : ∀ l ∈ allLists 5, dom (ofList (0 :: 3 :: l)) = true →
    EFX0L v agents goods (ofList (0 :: 3 :: l)) → cert (ofList (0 :: 3 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk10 : ∀ l ∈ allLists 5, dom (ofList (1 :: 0 :: l)) = true →
    EFX0L v agents goods (ofList (1 :: 0 :: l)) → cert (ofList (1 :: 0 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk11 : ∀ l ∈ allLists 5, dom (ofList (1 :: 1 :: l)) = true →
    EFX0L v agents goods (ofList (1 :: 1 :: l)) → cert (ofList (1 :: 1 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk12 : ∀ l ∈ allLists 5, dom (ofList (1 :: 2 :: l)) = true →
    EFX0L v agents goods (ofList (1 :: 2 :: l)) → cert (ofList (1 :: 2 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk13 : ∀ l ∈ allLists 5, dom (ofList (1 :: 3 :: l)) = true →
    EFX0L v agents goods (ofList (1 :: 3 :: l)) → cert (ofList (1 :: 3 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk20 : ∀ l ∈ allLists 5, dom (ofList (2 :: 0 :: l)) = true →
    EFX0L v agents goods (ofList (2 :: 0 :: l)) → cert (ofList (2 :: 0 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk21 : ∀ l ∈ allLists 5, dom (ofList (2 :: 1 :: l)) = true →
    EFX0L v agents goods (ofList (2 :: 1 :: l)) → cert (ofList (2 :: 1 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk22 : ∀ l ∈ allLists 5, dom (ofList (2 :: 2 :: l)) = true →
    EFX0L v agents goods (ofList (2 :: 2 :: l)) → cert (ofList (2 :: 2 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk23 : ∀ l ∈ allLists 5, dom (ofList (2 :: 3 :: l)) = true →
    EFX0L v agents goods (ofList (2 :: 3 :: l)) → cert (ofList (2 :: 3 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk30 : ∀ l ∈ allLists 5, dom (ofList (3 :: 0 :: l)) = true →
    EFX0L v agents goods (ofList (3 :: 0 :: l)) → cert (ofList (3 :: 0 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk31 : ∀ l ∈ allLists 5, dom (ofList (3 :: 1 :: l)) = true →
    EFX0L v agents goods (ofList (3 :: 1 :: l)) → cert (ofList (3 :: 1 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk32 : ∀ l ∈ allLists 5, dom (ofList (3 :: 2 :: l)) = true →
    EFX0L v agents goods (ofList (3 :: 2 :: l)) → cert (ofList (3 :: 2 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel

theorem certChunk33 : ∀ l ∈ allLists 5, dom (ofList (3 :: 3 :: l)) = true →
    EFX0L v agents goods (ofList (3 :: 3 :: l)) → cert (ofList (3 :: 3 :: l)) = true := by
  unfold EFX0L bundle; decide +kernel
theorem certChunk : ∀ a b : Fin 4, ∀ l ∈ allLists 5, dom (ofList (a :: b :: l)) = true →
    EFX0L v agents goods (ofList (a :: b :: l)) → cert (ofList (a :: b :: l)) = true := by
  intro a b
  match a, b with
  | 0, 0 => exact certChunk00
  | 0, 1 => exact certChunk01
  | 0, 2 => exact certChunk02
  | 0, 3 => exact certChunk03
  | 1, 0 => exact certChunk10
  | 1, 1 => exact certChunk11
  | 1, 2 => exact certChunk12
  | 1, 3 => exact certChunk13
  | 2, 0 => exact certChunk20
  | 2, 1 => exact certChunk21
  | 2, 2 => exact certChunk22
  | 2, 3 => exact certChunk23
  | 3, 0 => exact certChunk30
  | 3, 1 => exact certChunk31
  | 3, 2 => exact certChunk32
  | 3, 3 => exact certChunk33

/-- **Every EFX₀ allocation that value-dominates the picks satisfies T6's certificate** (kernel computation over
all 4⁷ allocations; only 144 dominate the picks, 6 of them EFX₀, and agent 0 holds the picks 2 and 5 in each). -/
theorem cert_all (X : Fin 7 → Fin 4) (hE : EFX0L v agents goods X)
    (hdom : ∀ i ∈ agents, value v i (B i) ≤ value v i (bundle goods X i)) :
    ∃ i ∈ agents, 3 ≤ (foreignPicks agents y X i).length ∨
      (2 ≤ (foreignPicks agents y X i).length ∧ ∀ k ∈ foreignPicks agents y X i,
        v i (y k) + value v i (relevant v i (junkOf agents goods B)) ≤ value v i (B i)) := by
  have hd : dom X = true := List.all_eq_true.mpr fun i hi => decide_eq_true (hdom i hi)
  rw [← ofList_map X] at hd hE
  have hl : goods.map X = X 0 :: X 1 :: [X 2, X 3, X 4, X 5, X 6] := rfl
  rw [hl] at hd hE
  have hc := certChunk (X 0) (X 1) _ (mem_allLists _) hd hE
  rw [← hl, ofList_map] at hc
  obtain ⟨i, hi, h⟩ := List.any_eq_true.mp hc
  rw [junk_eq]
  exact ⟨i, hi, of_decide_eq_true h⟩

/-- **No state one move reaches has an EFX₀ completion**, by Lemma T6 (`EFX.OC1Max.no_completion_of_cert`). -/
theorem no_completion_move_T6 {B' : Fin 4 → List (Fin 7)} (hm : OneMove v agents goods (pickBase v goods ord) B') :
    ¬ ∃ X : Fin 7 → Fin 4, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∀ i ∈ agents, ∀ g ∈ B' i, X g = i := by
  rw [pickBase_eq] at hm
  exact no_completion_of_cert (by decide) validState_B B_eq_y (fun X _ hE hdom => cert_all X hE hdom) hm

/-- **The picks have no EFX₀ completion**, by the same certificate: a completion of the picks gives every pick to
its holder, so nobody holds another agent's pick. -/
theorem no_completion_picks_T6 : ¬ ∃ X : Fin 7 → Fin 4, EFX0L v agents goods X ∧
    ∀ i ∈ agents, ∀ g ∈ pickBase v goods ord i, X g = i := by
  rintro ⟨X, hE, hX⟩
  rw [pickBase_eq] at hX
  have hdom : ∀ i ∈ agents, value v i (B i) ≤ value v i (bundle goods X i) := fun i hi =>
    value_le_of_nodup_sub i (by revert i; decide) fun g hg => mem_bundle.mpr ⟨mem_goods g, hX i hi g hg⟩
  obtain ⟨i, hi, h⟩ := cert_all X hE hdom
  have h0 : foreignPicks agents y X i = [] := List.eq_nil_iff_forall_not_mem.mpr fun k hk => by
    obtain ⟨hka, hki, hXk⟩ := mem_foreignPicks.mp hk
    rw [hX k hka (y k) (by rw [B_eq_y k hka]; simp)] at hXk
    exact hki hXk
  rw [h0] at h
  simp at h

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

/-- **OC₁^max is false, by Lemma T6** (the structural certificate of `k4/ttc.md` §14.2). -/
theorem not_conjOC1max_T6 : ¬ ConjOC1max (Fin 4) (Fin 7) := fun h => by
  rcases h Cex1.agents Cex1.goods Cex1.v (by decide) (by decide) Cex1.core Cex1.connected Cex1.strict Cex1.ord
    Cex1.ord_perm Cex1.maximum with ⟨X, -, hE, hX, -⟩ | ⟨B', hm, X, hXa, hE, hX, -⟩
  · exact Cex1.no_completion_picks_T6 ⟨X, hE, hX⟩
  · exact Cex1.no_completion_move_T6 hm ⟨X, hXa, hE, hX⟩

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

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
#print axioms EFX.OC1Max.Cex1.cert_all
#print axioms EFX.OC1Max.Cex1.no_completion_move_T6
#print axioms EFX.OC1Max.Cex1.no_completion_picks_T6
#print axioms EFX.OC1Max.not_conjOC1max_T6
