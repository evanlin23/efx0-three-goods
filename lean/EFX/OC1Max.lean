import EFX.NOF
import EFX.K4Ties

/-!
# Maximum-matching orders and Conjecture OC₁^max (`k4/sdc.md` §28, §29, §31)

Serial dictatorship, matchings and the frame of Conjecture OC₁^max (ledger K4.SDC.OC1MAX), over explicit lists
of agents and goods (`EFX.Lists`), as in `EFX.NOF`.

- `sdPick v ord goods`: serial dictatorship in the order `ord`, each agent taking its favourite available good
  (`EFX.LB4R.fav`); `sdPick_eq_runState`: it is the pick of `EFX.NOF.runState (EFX.NOF.sdList v ord goods)`.
- `IsMatching`, `card`, `IsMaximum`, `ParetoImp`, `ParetoOpt`: matchings of the agent / relevant-good graph,
  their size, maximum matchings, Pareto improvements and Pareto optimality (values of single goods, an
  unmatched agent having value 0).
- **Lemma SDPO** (K4.SDC.SDPO): with strict values, the serial-dictatorship outcomes over all orders are exactly
  the Pareto-optimal matchings (`sdpo`; the two inclusions `paretoOpt_sdPick` and `exists_order_of_paretoOpt`).
  The proof of ⊇ puts first an agent holding its favourite good (`exists_holds_fav`), which exists because
  otherwise the pointer map "the holder of my favourite good" has a cycle (`exists_cycle`) and the trade along
  it is a Pareto improvement.
- **Lemma MAXSD** (K4.SDC.MAXSD): some order's picks form a maximum matching (`exists_order_maximum`), through a
  maximum matching of largest total value (`exists_maximum_paretoOpt`).
- **Lemma MAX** (`k4/sdc.md` §31, `k4/oc1_hall.md` §19): if a matching is maximum, no agent reachable from an
  unmatched agent by an alternating path values an unmatched good (`max_no_augment`, `picks_no_augment`).
- The moves of `k4/sdc.md` §29 (`IsAddition`, `IsChain`, `IsRing`, `OneMove`), the one-absorber completion
  (`OneAbsorber`) and **Conjecture OC₁^max** (`ConjOC1max`, a `Prop`); **`target4_of_conjOC1max`: OC₁^max ⟹
  TARGET₄**, through MAXSD, K4.CORE and K4.TIE (`EFX.target4_of_strict_cores`).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Serial dictatorship -/

/-- Serial dictatorship in the order `ord` on the available goods `G0`: the good `sdPick v ord G0 i` that agent `i`
picks (`none` if `i` is not in the order or finds no relevant good left at its turn). -/
def sdPick (v : A → G → Nat) : List A → List G → A → Option G
  | [], _, _ => none
  | x :: xs, G0, i => if i = x then fav v x G0 else sdPick v xs (takeOut G0 (fav v x G0)) i

section sd
variable (v : A → G → Nat)

@[simp] theorem sdPick_nil (G0 : List G) (i : A) : sdPick v [] G0 i = none := rfl

theorem sdPick_cons (x : A) (xs : List A) (G0 : List G) (i : A) :
    sdPick v (x :: xs) G0 i = if i = x then fav v x G0 else sdPick v xs (takeOut G0 (fav v x G0)) i := rfl

theorem sdPick_of_not_mem : ∀ {ord : List A} (G0 : List G) {i : A}, i ∉ ord → sdPick v ord G0 i = none
  | [], _, _, _ => rfl
  | x :: xs, G0, i, h => by
    have hix : i ≠ x := fun e => h (e ▸ List.mem_cons_self)
    rw [sdPick_cons, ite_eq_right hix]
    exact sdPick_of_not_mem _ fun hm => h (List.mem_cons_of_mem _ hm)

/-- `sdPick` is the pick of the state of `EFX.NOF.sdList`'s run (the serial dictatorship of `EFX.NOF`). -/
theorem sdPick_eq_runState : ∀ (ord : List A) (G0 : List G) (i : A),
    sdPick v ord G0 i = (NOF.runState (NOF.sdList v ord G0)).pick i
  | [], _, _ => by simp [sdPick, NOF.runState, NOF.sdList]
  | x :: xs, G0, i => by
    rw [sdPick_cons, sdPick_eq_runState xs]
    simp only [NOF.runState, NOF.sdList, List.find?_cons]
    by_cases h : i = x
    · subst h; simp
    · have : (x == i) = false := by simp [Ne.symm h]
      simp [h, this]

omit [DecidableEq A] in
theorem mem_takeOut {G0 : List G} {o : Option G} {g : G} (h : g ∈ takeOut G0 o) : g ∈ G0 := by
  cases o with
  | none => exact h
  | some y => exact List.mem_of_mem_erase h

omit [DecidableEq A] in
theorem nodup_takeOut {G0 : List G} (hG : G0.Nodup) (o : Option G) : (takeOut G0 o).Nodup := by
  cases o with
  | none => exact hG
  | some y => exact hG.erase y

/-- The picks are goods of `G0` their agents value, and no good is picked twice. -/
theorem sdPick_spec : ∀ (ord : List A) (G0 : List G), G0.Nodup →
    (∀ i g, sdPick v ord G0 i = some g → i ∈ ord ∧ g ∈ G0 ∧ 0 < v i g) ∧
    (∀ i j g, sdPick v ord G0 i = some g → sdPick v ord G0 j = some g → i = j)
  | [], _, _ => ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  | x :: xs, G0, hG => by
    obtain ⟨ih1, ih2⟩ := sdPick_spec xs (takeOut G0 (fav v x G0)) (nodup_takeOut hG _)
    have hout : ∀ g, fav v x G0 = some g → g ∉ takeOut G0 (fav v x G0) := fun g hg => by
      rw [hg]; exact List.Nodup.not_mem_erase hG
    refine ⟨fun i g h => ?_, fun i j g hi hj => ?_⟩
    · rw [sdPick_cons] at h
      by_cases hix : i = x
      · rw [ite_eq_left hix] at h
        obtain ⟨h1, h2, -⟩ := fav_some h
        exact ⟨hix ▸ List.mem_cons_self, h1, hix ▸ h2⟩
      · rw [ite_eq_right hix] at h
        obtain ⟨h1, h2, h3⟩ := ih1 i g h
        exact ⟨List.mem_cons_of_mem _ h1, mem_takeOut h2, h3⟩
    · rw [sdPick_cons] at hi hj
      by_cases hix : i = x <;> by_cases hjx : j = x
      · rw [hix, hjx]
      · rw [ite_eq_left hix] at hi; rw [ite_eq_right hjx] at hj
        exact absurd (ih1 j g hj).2.1 (hout g hi)
      · rw [ite_eq_right hix] at hi; rw [ite_eq_left hjx] at hj
        exact absurd (ih1 i g hi).2.1 (hout g hj)
      · rw [ite_eq_right hix] at hi; rw [ite_eq_right hjx] at hj
        exact ih2 i j g hi hj

end sd

/-! ## Matchings -/

/-- A matching of the agent / relevant-good graph: each listed agent gets at most one good of `goods` that it
values, no good goes to two agents, and agents outside the list get nothing. -/
structure IsMatching (v : A → G → Nat) (agents : List A) (goods : List G) (μ : A → Option G) : Prop where
  mem : ∀ i g, μ i = some g → i ∈ agents ∧ g ∈ goods ∧ 0 < v i g
  inj : ∀ i j g, μ i = some g → μ j = some g → i = j

/-- Agent `i`'s value for what it gets under `μ` (`0` if unmatched). -/
def mval (v : A → G → Nat) (μ : A → Option G) (i : A) : Nat :=
  match μ i with
  | none => 0
  | some g => v i g

/-- The size of a matching: the number of listed agents it matches. -/
def card (agents : List A) (μ : A → Option G) : Nat := agents.countP (fun i => (μ i).isSome)

/-- A maximum matching. -/
def IsMaximum (v : A → G → Nat) (agents : List A) (goods : List G) (μ : A → Option G) : Prop :=
  IsMatching v agents goods μ ∧ ∀ μ', IsMatching v agents goods μ' → card agents μ' ≤ card agents μ

/-- `μ'` is a Pareto improvement of `μ`: no listed agent is worse off, and one is better off. -/
def ParetoImp (v : A → G → Nat) (agents : List A) (μ' μ : A → Option G) : Prop :=
  (∀ i ∈ agents, mval v μ i ≤ mval v μ' i) ∧ ∃ i ∈ agents, mval v μ i < mval v μ' i

/-- A Pareto-optimal matching: no matching is a Pareto improvement of it. -/
def ParetoOpt (v : A → G → Nat) (agents : List A) (goods : List G) (μ : A → Option G) : Prop :=
  IsMatching v agents goods μ ∧ ∀ μ', IsMatching v agents goods μ' → ¬ ParetoImp v agents μ' μ

/-- Strict values on single goods: an agent values two different goods of `goods` differently, unless both are
worthless to it. -/
def StrictVals (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ i ∈ agents, ∀ g ∈ goods, ∀ h ∈ goods, 0 < v i g → v i g = v i h → g = h

section matchings
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
@[simp] theorem mval_none {μ : A → Option G} {i : A} (h : μ i = none) : mval v μ i = 0 := by
  simp [mval, h]

omit [DecidableEq A] [DecidableEq G] in
@[simp] theorem mval_some {μ : A → Option G} {i : A} {g : G} (h : μ i = some g) : mval v μ i = v i g := by
  simp [mval, h]

omit [DecidableEq A] [DecidableEq G] in
/-- Under a matching, an agent has positive value iff it is matched. -/
theorem mval_pos_iff {μ : A → Option G} (hμ : IsMatching v agents goods μ) (i : A) :
    0 < mval v μ i ↔ (μ i).isSome := by
  cases h : μ i with
  | none => simp [mval, h]
  | some g => simp [mval, h, (hμ.mem i g h).2.2]

omit [DecidableEq A] [DecidableEq G] in
/-- The empty matching. -/
theorem isMatching_empty : IsMatching v agents goods (fun _ => none) :=
  ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩

omit [DecidableEq A] [DecidableEq G] in
/-- A strict profile (`EFX.Strict`) has strict values on single goods. -/
theorem strictVals_of_strict (hs : Strict v agents goods) : StrictVals v agents goods := by
  intro i hi g hg h hh hpos heq
  refine Classical.byContradiction fun hne => ?_
  have := hs i hi [g] [h] (List.singleton_sublist.mpr hg) (List.singleton_sublist.mpr hh)
    (fun x hx hx' => by
      rw [List.mem_singleton] at hx hx'
      exact hne (hx.symm.trans hx'))
    (by simp [value, heq])
  simp [value] at this
  omega

/-- Serial dictatorship in any order of the agents gives a matching. -/
theorem isMatching_sdPick {ord : List A} (hperm : ord.Perm agents) (hgd : goods.Nodup) :
    IsMatching v agents goods (sdPick v ord goods) := by
  obtain ⟨h1, h2⟩ := sdPick_spec v ord goods hgd
  exact ⟨fun i g h => by
    obtain ⟨a, b, c⟩ := h1 i g h
    exact ⟨hperm.mem_iff.mp a, b, c⟩, h2⟩

end matchings

/-! ## Lemma SDPO (K4.SDC.SDPO) -/

/-- **A map of a finite set into itself has a cycle**: a nonempty part `C` of `S` that `f` maps into itself, and
on which `f` is injective. (If `f` is onto `S`, it is injective by counting; otherwise drop a point outside its
image and induct.) -/
theorem exists_cycle {α : Type} [DecidableEq α] (f : α → α) : ∀ (n : Nat) (S : List α), S.length = n → S.Nodup →
    S ≠ [] → (∀ x ∈ S, f x ∈ S) → ∃ C : List α, C ≠ [] ∧ (∀ x ∈ C, x ∈ S) ∧ (∀ x ∈ C, f x ∈ C) ∧
      ∀ x ∈ C, ∀ y ∈ C, f x = f y → x = y := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro S hn hS hne hf
  by_cases hsurj : ∀ y ∈ S, ∃ x ∈ S, f x = y
  · refine ⟨S, hne, fun x hx => hx, hf, fun x hx y hy hxy => ?_⟩
    refine Classical.byContradiction fun hxy' => ?_
    have hsub : S ⊆ (S.erase x).map f := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hsurj z hz
      by_cases hwx : w = x
      · subst hwx
        exact List.mem_map.mpr ⟨y, (List.mem_erase_of_ne (Ne.symm hxy')).mpr hy, hxy.symm⟩
      · exact List.mem_map.mpr ⟨w, (List.mem_erase_of_ne hwx).mpr hw, rfl⟩
    have h1 := hS.length_le_of_subset hsub
    rw [List.length_map, List.length_erase_of_mem hx] at h1
    have := List.length_pos_of_mem hx
    omega
  · obtain ⟨y, hy, hny⟩ : ∃ y ∈ S, ∀ x ∈ S, f x ≠ y := Classical.byContradiction fun h => hsurj fun y hy =>
      Classical.byContradiction fun h' => h ⟨y, hy, fun x hx hxy => h' ⟨x, hx, hxy⟩⟩
    have hf' : ∀ x ∈ S.erase y, f x ∈ S.erase y := fun x hx => by
      have hxS := List.mem_of_mem_erase hx
      exact (List.mem_erase_of_ne (hny x hxS)).mpr (hf x hxS)
    obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil S hne
    have hne' : S.erase y ≠ [] :=
      List.ne_nil_of_mem ((List.mem_erase_of_ne (hny x0 hx0)).mpr (hf x0 hx0))
    have hlt : (S.erase y).length < n := by
      rw [List.length_erase_of_mem hy]; have := List.length_pos_of_mem hy; omega
    obtain ⟨C, hC, hCS, hCf, hCi⟩ := ih _ hlt (S.erase y) rfl (hS.erase y) hne' hf'
    exact ⟨C, hC, fun x hx => List.mem_of_mem_erase (hCS x hx), hCf, hCi⟩

section sdpo
variable {v : A → G → Nat}

omit [DecidableEq A] [DecidableEq G] in
theorem mval_congr {μ ν : A → Option G} {i : A} (h : μ i = ν i) : mval v μ i = mval v ν i := by
  simp [mval, h]

/-- **Some agent holds its favourite good** (the step of SDPO's ⊇): in a Pareto-optimal matching under strict
values, some listed agent `a` gets exactly `fav v a goods` (its favourite relevant good, or nothing if it values
no good). Otherwise every agent's favourite exists, beats what it holds and is held; the map "the holder of my
favourite" has a cycle (`exists_cycle`), and giving every agent on it its favourite is a Pareto improvement. -/
theorem exists_holds_fav {agents : List A} {goods : List G} {μ : A → Option G} (hag : agents.Nodup)
    (hsv : StrictVals v agents goods) (hpo : ParetoOpt v agents goods μ) (hne : agents ≠ []) :
    ∃ a ∈ agents, fav v a goods = μ a := by
  refine Classical.byContradiction fun hno => ?_
  have hno' : ∀ a ∈ agents, fav v a goods ≠ μ a := fun a ha h => hno ⟨a, ha, h⟩
  obtain ⟨hμ, hopt⟩ := hpo
  -- every agent's favourite exists and beats what it holds
  have hfav : ∀ a ∈ agents, ∃ h, fav v a goods = some h ∧ mval v μ a < v a h := by
    intro a ha
    cases hf : fav v a goods with
    | none =>
      cases hm : μ a with
      | none => exact absurd (hf.trans hm.symm) (hno' a ha)
      | some g => exact absurd (hμ.mem a g hm).2.2 (fav_none hf g (hμ.mem a g hm).2.1)
    | some h =>
      refine ⟨h, rfl, ?_⟩
      obtain ⟨hh, hpos, hmax⟩ := fav_some hf
      cases hm : μ a with
      | none => rw [mval_none hm]; exact hpos
      | some g =>
        rw [mval_some hm]
        obtain ⟨-, hg, hgpos⟩ := hμ.mem a g hm
        have hle := hmax g hg hgpos
        have hgh : g ≠ h := fun e => hno' a ha (by rw [hf, hm, e])
        have : v a g ≠ v a h := fun e => hgh (hsv a ha g hg h hh hgpos e)
        omega
  -- every agent's favourite is held by someone
  have hheld : ∀ a ∈ agents, ∀ h, fav v a goods = some h → ∃ b, μ b = some h := by
    intro a ha h hf
    refine Classical.byContradiction fun hnh => ?_
    obtain ⟨h', hf', hlt⟩ := hfav a ha
    rw [hf] at hf'; cases hf'
    obtain ⟨hh, hpos, -⟩ := fav_some hf
    have hν : IsMatching v agents goods (fun x => if x = a then some h else μ x) := by
      refine ⟨fun x g hx => ?_, fun x y g hx hy => ?_⟩
      · by_cases hxa : x = a
        · rw [ite_eq_left hxa] at hx; cases hx; subst hxa; exact ⟨ha, hh, hpos⟩
        · rw [ite_eq_right hxa] at hx; exact hμ.mem x g hx
      · by_cases hxa : x = a <;> by_cases hya : y = a
        · rw [hxa, hya]
        · rw [ite_eq_left hxa] at hx; rw [ite_eq_right hya] at hy; cases hx; exact absurd ⟨y, hy⟩ hnh
        · rw [ite_eq_right hxa] at hx; rw [ite_eq_left hya] at hy; cases hy; exact absurd ⟨x, hx⟩ hnh
        · rw [ite_eq_right hxa] at hx; rw [ite_eq_right hya] at hy; exact hμ.inj x y g hx hy
    refine hopt _ hν ⟨fun x _ => ?_, a, ha, ?_⟩
    · by_cases hxa : x = a
      · rw [hxa, mval_some (μ := fun x => if x = a then some h else μ x) (i := a) (g := h) (by simp)]; omega
      · exact Nat.le_of_eq (mval_congr (by simp [hxa]))
    · rw [mval_some (μ := fun x => if x = a then some h else μ x) (i := a) (g := h) (by simp)]; exact hlt
  -- the pointer map: the holder of one's favourite
  let f : A → A := fun a => (agents.find? (fun b => μ b == fav v a goods)).getD a
  have hf : ∀ a ∈ agents, f a ∈ agents ∧ μ (f a) = fav v a goods := by
    intro a ha
    obtain ⟨h, hfa, -⟩ := hfav a ha
    obtain ⟨b, hb⟩ := hheld a ha h hfa
    have hbm : b ∈ agents := (hμ.mem b h hb).1
    cases hq : agents.find? (fun b => μ b == fav v a goods) with
    | none => exact absurd (List.find?_eq_none.mp hq b hbm) (by simp [hb, hfa])
    | some c =>
      have hc1 := List.mem_of_find?_eq_some hq
      have hc2 : μ c = fav v a goods := by simpa using List.find?_some hq
      have : f a = c := by simp only [f, hq, Option.getD_some]
      rw [this]
      exact ⟨hc1, hc2⟩
  obtain ⟨C, hC, hCS, hCf, hCi⟩ := exists_cycle f agents.length agents rfl hag hne (fun x hx => (hf x hx).1)
  -- the trade along the cycle
  have hν : IsMatching v agents goods (fun x => if x ∈ C then μ (f x) else μ x) := by
    refine ⟨fun x g hx => ?_, fun x y g hx hy => ?_⟩
    · by_cases hxC : x ∈ C
      · rw [ite_eq_left hxC, (hf x (hCS x hxC)).2] at hx
        obtain ⟨h1, h2, -⟩ := fav_some hx
        exact ⟨hCS x hxC, h1, h2⟩
      · rw [ite_eq_right hxC] at hx; exact hμ.mem x g hx
    · by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C
      · rw [ite_eq_left hxC] at hx; rw [ite_eq_left hyC] at hy
        exact hCi x hxC y hyC (hμ.inj _ _ g hx hy)
      · rw [ite_eq_left hxC] at hx; rw [ite_eq_right hyC] at hy
        exact absurd (hμ.inj _ _ g hx hy ▸ hCf x hxC) hyC
      · rw [ite_eq_right hxC] at hx; rw [ite_eq_left hyC] at hy
        exact absurd (hμ.inj _ _ g hy hx ▸ hCf y hyC) hxC
      · rw [ite_eq_right hxC] at hx; rw [ite_eq_right hyC] at hy
        exact hμ.inj x y g hx hy
  have hgain : ∀ x ∈ C, mval v μ x < mval v (fun x => if x ∈ C then μ (f x) else μ x) x := by
    intro x hxC
    obtain ⟨h, hfx, hlt⟩ := hfav x (hCS x hxC)
    rw [mval_some (μ := fun x => if x ∈ C then μ (f x) else μ x) (i := x)
      (by simp only [hxC, ite_true]; rw [(hf x (hCS x hxC)).2, hfx])]
    exact hlt
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil C hC
  refine hopt _ hν ⟨fun x _ => ?_, x0, hCS x0 hx0, hgain x0 hx0⟩
  by_cases hxC : x ∈ C
  · exact Nat.le_of_lt (hgain x hxC)
  · exact Nat.le_of_eq (mval_congr (by simp [hxC]))

end sdpo

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.sdPick_eq_runState
#print axioms EFX.OC1Max.sdPick_spec
#print axioms EFX.OC1Max.isMatching_sdPick
#print axioms EFX.OC1Max.strictVals_of_strict
#print axioms EFX.OC1Max.exists_cycle
#print axioms EFX.OC1Max.exists_holds_fav
