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
- OC₁^max is false (`EFX/OC1MaxCex.lean`, `EFX.OC1Max.not_conjOC1max`); the frame is parametrized by the move
  relation (`ConjOC1maxWith`), and `EFX/OCVariants.lean` applies it to the surviving variants.
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

/-- **SDPO, ⊇**: under strict values every Pareto-optimal matching is the outcome of serial dictatorship in some
order of the agents. Put first an agent holding its favourite (`exists_holds_fav`); the rest of the matching is
Pareto optimal among the other agents and goods; induct. -/
theorem exists_order_of_paretoOpt : ∀ (n : Nat) (agents : List A) (goods : List G) (μ : A → Option G),
    agents.length = n → agents.Nodup → goods.Nodup → StrictVals v agents goods → ParetoOpt v agents goods μ →
      ∃ ord : List A, ord.Perm agents ∧ ∀ i, sdPick v ord goods i = μ i := by
  intro n
  induction n with
  | zero =>
    intro agents goods μ hn _ _ _ hpo
    have : agents = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    refine ⟨[], List.Perm.refl _, fun i => ?_⟩
    cases hm : μ i with
    | none => rfl
    | some g => exact absurd (hpo.1.mem i g hm).1 (by simp)
  | succ n ih =>
    intro agents goods μ hn hag hgd hsv hpo
    have hne : agents ≠ [] := fun h => by rw [h] at hn; simp at hn
    obtain ⟨a, ha, hfa⟩ := exists_holds_fav hag hsv hpo hne
    obtain ⟨hμ, hopt⟩ := hpo
    have hmemE : ∀ x, x ∈ agents.erase a → x ≠ a := fun x hx e => List.Nodup.not_mem_erase hag (e ▸ hx)
    -- the sub-instance
    have hμ' : IsMatching v (agents.erase a) (takeOut goods (μ a)) (fun x => if x = a then none else μ x) := by
      refine ⟨fun x g hx => ?_, fun x y g hx hy => ?_⟩
      · by_cases hxa : x = a
        · rw [ite_eq_left hxa] at hx; cases hx
        · rw [ite_eq_right hxa] at hx
          obtain ⟨h1, h2, h3⟩ := hμ.mem x g hx
          refine ⟨(List.mem_erase_of_ne hxa).mpr h1, ?_, h3⟩
          cases hma : μ a with
          | none => exact h2
          | some g0 =>
            have : g ≠ g0 := fun e => hxa (hμ.inj x a g hx (e ▸ hma))
            exact (List.mem_erase_of_ne this).mpr h2
      · by_cases hxa : x = a
        · rw [ite_eq_left hxa] at hx; cases hx
        · by_cases hya : y = a
          · rw [ite_eq_left hya] at hy; cases hy
          · rw [ite_eq_right hxa] at hx; rw [ite_eq_right hya] at hy; exact hμ.inj x y g hx hy
    have hpo' : ParetoOpt v (agents.erase a) (takeOut goods (μ a)) (fun x => if x = a then none else μ x) := by
      refine ⟨hμ', fun ν hν himp => ?_⟩
      obtain ⟨hle, x0, hx0, hlt⟩ := himp
      have hν' : IsMatching v agents goods (fun x => if x = a then μ a else ν x) := by
        refine ⟨fun x g hx => ?_, fun x y g hx hy => ?_⟩
        · by_cases hxa : x = a
          · rw [ite_eq_left hxa] at hx; rw [hxa]; exact hμ.mem a g hx
          · rw [ite_eq_right hxa] at hx
            obtain ⟨h1, h2, h3⟩ := hν.mem x g hx
            exact ⟨List.mem_of_mem_erase h1, mem_takeOut h2, h3⟩
        · have hout : ∀ z, μ a = some g → ν z ≠ some g := fun z hma hz => by
            have := (hν.mem z g hz).2.1
            rw [hma] at this
            exact List.Nodup.not_mem_erase hgd this
          by_cases hxa : x = a <;> by_cases hya : y = a
          · rw [hxa, hya]
          · rw [ite_eq_left hxa] at hx; rw [ite_eq_right hya] at hy; exact absurd hy (hout y hx)
          · rw [ite_eq_right hxa] at hx; rw [ite_eq_left hya] at hy; exact absurd hx (hout x hy)
          · rw [ite_eq_right hxa] at hx; rw [ite_eq_right hya] at hy; exact hν.inj x y g hx hy
      refine hopt _ hν' ⟨fun x hx => ?_, x0, List.mem_of_mem_erase hx0, ?_⟩
      · by_cases hxa : x = a
        · exact Nat.le_of_eq (mval_congr (by simp [hxa]))
        · have := hle x ((List.mem_erase_of_ne hxa).mpr hx)
          rw [mval_congr (μ := fun x => if x = a then none else μ x) (ν := μ) (by simp [hxa])] at this
          rw [mval_congr (μ := fun x => if x = a then μ a else ν x) (ν := ν) (by simp [hxa])]
          exact this
      · have hxa := hmemE x0 hx0
        rw [mval_congr (μ := fun x => if x = a then none else μ x) (ν := μ) (by simp [hxa])] at hlt
        rw [mval_congr (μ := fun x => if x = a then μ a else ν x) (ν := ν) (by simp [hxa])]
        exact hlt
    have hsv' : StrictVals v (agents.erase a) (takeOut goods (μ a)) := fun i hi g hg h hh =>
      hsv i (List.mem_of_mem_erase hi) g (mem_takeOut hg) h (mem_takeOut hh)
    have hlen : (agents.erase a).length = n := by rw [List.length_erase_of_mem ha]; omega
    obtain ⟨ord, hord, hsd⟩ := ih (agents.erase a) (takeOut goods (μ a)) _ hlen (hag.erase a)
      (nodup_takeOut hgd _) hsv' hpo'
    refine ⟨a :: ord, (hord.cons a).trans (List.perm_cons_erase ha).symm, fun i => ?_⟩
    rw [sdPick_cons, hfa]
    by_cases hia : i = a
    · rw [ite_eq_left hia, hia]
    · rw [ite_eq_right hia, hsd i]; simp [hia]

/-- **SDPO, ⊆ (uniqueness)**: a matching of the agents of `ord` with goods of `G0` that gives every agent of `ord`
at least its serial-dictatorship value is the serial-dictatorship outcome itself (strict values). The first agent
already takes its favourite good, so it holds the same good; induct. -/
theorem eq_sdPick_of_le : ∀ (ord : List A) (G0 : List G) (ν : A → Option G), ord.Nodup → G0.Nodup →
    (∀ i ∈ ord, ∀ g ∈ G0, ∀ h ∈ G0, 0 < v i g → v i g = v i h → g = h) →
    (∀ i ∈ ord, ∀ g, ν i = some g → g ∈ G0 ∧ 0 < v i g) →
    (∀ i ∈ ord, ∀ j ∈ ord, ∀ g, ν i = some g → ν j = some g → i = j) →
    (∀ i ∈ ord, mval v (sdPick v ord G0) i ≤ mval v ν i) → ∀ i ∈ ord, ν i = sdPick v ord G0 i
  | [], _, _, _, _, _, _, _, _ => fun _ h => by simp at h
  | x :: xs, G0, ν, hord, hG, hsv, hmem, hinj, hdom => by
    have hxs : x ∉ xs := (List.nodup_cons.mp hord).1
    have hx : ν x = fav v x G0 := by
      cases hf : fav v x G0 with
      | none =>
        cases hν : ν x with
        | none => rfl
        | some g =>
          obtain ⟨h1, h2⟩ := hmem x List.mem_cons_self g hν
          exact absurd h2 (fav_none hf g h1)
      | some y =>
        obtain ⟨hy, hypos, hmax⟩ := fav_some hf
        have hle := hdom x List.mem_cons_self
        rw [mval_some (μ := sdPick v (x :: xs) G0) (g := y) (by rw [sdPick_cons, ite_eq_left rfl, hf])] at hle
        cases hν : ν x with
        | none => rw [mval_none hν] at hle; omega
        | some g =>
          rw [mval_some hν] at hle
          obtain ⟨h1, h2⟩ := hmem x List.mem_cons_self g hν
          have := hmax g h1 h2
          rw [hsv x List.mem_cons_self g h1 y hy h2 (by omega)]
    have hrest : ∀ i ∈ xs, ν i = sdPick v xs (takeOut G0 (fav v x G0)) i := by
      refine eq_sdPick_of_le xs _ ν (List.nodup_cons.mp hord).2 (nodup_takeOut hG _)
        (fun i hi g hg h hh => hsv i (List.mem_cons_of_mem _ hi) g (mem_takeOut hg) h (mem_takeOut hh))
        (fun i hi g hg => ?_) (fun i hi j hj => hinj i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj))
        (fun i hi => ?_)
      · obtain ⟨h1, h2⟩ := hmem i (List.mem_cons_of_mem _ hi) g hg
        refine ⟨?_, h2⟩
        cases hf : fav v x G0 with
        | none => exact h1
        | some y =>
          have hgy : g ≠ y := fun e => by
            have := hinj i (List.mem_cons_of_mem _ hi) x List.mem_cons_self g hg (by rw [hx, hf, e])
            exact hxs (this ▸ hi)
          exact (List.mem_erase_of_ne hgy).mpr h1
      · have hix : i ≠ x := fun e => hxs (e ▸ hi)
        have := hdom i (List.mem_cons_of_mem _ hi)
        rwa [mval_congr (μ := sdPick v (x :: xs) G0) (ν := sdPick v xs (takeOut G0 (fav v x G0)))
          (by rw [sdPick_cons, ite_eq_right hix])] at this
    intro i hi
    rw [sdPick_cons]
    by_cases hix : i = x
    · rw [ite_eq_left hix, hix, hx]
    · rw [ite_eq_right hix]
      exact hrest i ((List.mem_cons.mp hi).resolve_left hix)

/-- **SDPO, ⊆**: under strict values the outcome of serial dictatorship in any order is Pareto optimal. -/
theorem paretoOpt_sdPick {agents : List A} {goods : List G} {ord : List A} (hperm : ord.Perm agents)
    (hag : agents.Nodup) (hgd : goods.Nodup) (hsv : StrictVals v agents goods) :
    ParetoOpt v agents goods (sdPick v ord goods) := by
  refine ⟨isMatching_sdPick hperm hgd, fun ν hν ⟨hle, i, hi, hlt⟩ => ?_⟩
  have heq := eq_sdPick_of_le ord goods ν (hperm.nodup_iff.mpr hag) hgd
    (fun i hi => hsv i (hperm.mem_iff.mp hi))
    (fun i _ g hg => ⟨(hν.mem i g hg).2.1, (hν.mem i g hg).2.2⟩)
    (fun i _ j _ g => hν.inj i j g) (fun i hi => hle i (hperm.mem_iff.mp hi)) i (hperm.mem_iff.mpr hi)
  rw [mval_congr (μ := ν) (ν := sdPick v ord goods) heq] at hlt
  exact Nat.lt_irrefl _ hlt

/-- **Lemma SDPO** (K4.SDC.SDPO, `k4/sdc.md` §28): with strict values (and unmatched agents allowed), the
serial-dictatorship outcomes over all orders of the agents are exactly the Pareto-optimal matchings. -/
theorem sdpo {agents : List A} {goods : List G} (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) (μ : A → Option G) :
    (∃ ord : List A, ord.Perm agents ∧ sdPick v ord goods = μ) ↔ ParetoOpt v agents goods μ := by
  constructor
  · rintro ⟨ord, hperm, rfl⟩
    exact paretoOpt_sdPick hperm hag hgd hsv
  · intro hpo
    obtain ⟨ord, hperm, h⟩ := exists_order_of_paretoOpt agents.length agents goods μ rfl hag hgd hsv hpo
    exact ⟨ord, hperm, funext h⟩

end sdpo

/-! ## Lemma MAXSD (K4.SDC.MAXSD) -/

/-- A function bounded on a nonempty set has a maximum there. -/
theorem exists_max_of_bdd {α : Type} (P : α → Prop) (f : α → Nat) (B : Nat) (hB : ∀ a, P a → f a ≤ B)
    (h : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  have key : ∀ d, ∀ a, P a → B - f a = d → ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a ha hd
      by_cases hm : ∀ b, P b → f b ≤ f a
      · exact ⟨a, ha, hm⟩
      · obtain ⟨b, hb, hlt⟩ : ∃ b, P b ∧ f a < f b := Classical.byContradiction fun hno =>
          hm fun b hb => Nat.le_of_not_lt fun hl => hno ⟨b, hb, hl⟩
        exact ih _ (by have := hB b hb; omega) b hb rfl
  obtain ⟨a, ha⟩ := h
  exact key _ a ha rfl

theorem sum_map_le {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := sum_map_le (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

theorem sum_map_lt {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) →
    (∃ x ∈ l, f x < g x) → (l.map f).sum < (l.map g).sum
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | x :: l, h, ⟨y, hy, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    have hx := h x List.mem_cons_self
    have hl : ∀ z ∈ l, f z ≤ g z := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rcases List.mem_cons.mp hy with rfl | hy
    · have := sum_map_le hl; omega
    · have := sum_map_lt hl ⟨y, hy, hlt⟩; omega

theorem countP_lt_of {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
    (∃ x ∈ l, q x = true ∧ p x = false) → l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | x :: l, h, ⟨y, hy, hq, hp⟩ => by
    simp only [List.countP_cons]
    have hl : ∀ z ∈ l, p z = true → q z = true := fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hx := h x List.mem_cons_self
    rcases List.mem_cons.mp hy with rfl | hy
    · have := List.countP_mono_left hl; simp [hq, hp]; omega
    · have := countP_lt_of hl ⟨y, hy, hq, hp⟩
      cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega

section maxsd
variable {v : A → G → Nat}

/-- The total value of a matching. -/
def welfare (v : A → G → Nat) (agents : List A) (μ : A → Option G) : Nat := (agents.map (mval v μ)).sum

omit [DecidableEq A] [DecidableEq G] in
theorem welfare_le {agents : List A} {goods : List G} {μ : A → Option G} (hμ : IsMatching v agents goods μ) :
    welfare v agents μ ≤ (agents.map (fun i => value v i goods)).sum := by
  refine sum_map_le fun i _ => ?_
  cases h : μ i with
  | none => rw [mval_none h]; exact Nat.zero_le _
  | some g => rw [mval_some h]; exact le_value_of_mem v i (hμ.mem i g h).2.1

omit [DecidableEq A] [DecidableEq G] in
/-- A Pareto improvement of a matching keeps every matched agent matched. -/
theorem card_le_of_paretoImp {agents : List A} {goods : List G} {μ ν : A → Option G}
    (hμ : IsMatching v agents goods μ) (hν : IsMatching v agents goods ν) (h : ParetoImp v agents ν μ) :
    card agents μ ≤ card agents ν :=
  List.countP_mono_left fun i hi hs => by
    have h1 := (mval_pos_iff hμ i).mpr hs
    exact (mval_pos_iff hν i).mp (Nat.lt_of_lt_of_le h1 (h.1 i hi))

omit [DecidableEq A] [DecidableEq G] in
/-- **A maximum matching of largest total value is Pareto optimal**: a Pareto improvement keeps matched agents
matched, so it is again maximum, and it has larger total value. -/
theorem exists_maximum_paretoOpt (agents : List A) (goods : List G) :
    ∃ μ, IsMaximum v agents goods μ ∧ ParetoOpt v agents goods μ := by
  obtain ⟨μ0, hμ0, hmax0⟩ := exists_max_of_bdd (IsMatching v agents goods) (card agents) agents.length
    (fun _ _ => List.countP_le_length) ⟨_, isMatching_empty⟩
  obtain ⟨μ, ⟨hμ, hcard⟩, hbest⟩ := exists_max_of_bdd
    (fun μ => IsMatching v agents goods μ ∧ card agents μ = card agents μ0) (welfare v agents)
    ((agents.map (fun i => value v i goods)).sum) (fun _ h => welfare_le h.1) ⟨μ0, hμ0, rfl⟩
  refine ⟨μ, ⟨hμ, fun μ' hμ' => hcard ▸ hmax0 μ' hμ'⟩, hμ, fun ν hν himp => ?_⟩
  have h1 := card_le_of_paretoImp hμ hν himp
  have h2 := hmax0 ν hν
  have h3 := hbest ν ⟨hν, by omega⟩
  have h4 : welfare v agents μ < welfare v agents ν := sum_map_lt himp.1 himp.2
  omega

/-- **Lemma MAXSD** (K4.SDC.MAXSD, `k4/sdc.md` §31): with strict values, some serial-dictatorship order's picks
form a maximum matching (a maximum matching Pareto optimal among all matchings, by `exists_maximum_paretoOpt`, is
an SD outcome, by SDPO). -/
theorem exists_order_maximum {agents : List A} {goods : List G} (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) :
    ∃ ord : List A, ord.Perm agents ∧ IsMaximum v agents goods (sdPick v ord goods) := by
  obtain ⟨μ, hmax, hpo⟩ := exists_maximum_paretoOpt (v := v) agents goods
  obtain ⟨ord, hperm, rfl⟩ := (sdpo hag hgd hsv μ).mpr hpo
  exact ⟨ord, hperm, hmax⟩

end maxsd

/-! ## Lemma MAX -/

section lemmaMax
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- `b` is reachable from an unmatched agent by an alternating path of `μ`: an unmatched listed agent is reachable,
and if `a` is reachable and values the good `g` that `b` holds, `b` is reachable. -/
inductive AltReach (v : A → G → Nat) (agents : List A) (μ : A → Option G) : A → Prop
  | start {a : A} : a ∈ agents → μ a = none → AltReach v agents μ a
  | step {a b : A} {g : G} : AltReach v agents μ a → μ b = some g → 0 < v a g → AltReach v agents μ b

/-- An alternating path, listed from its end back to its start: `[x_k, …, x_0]` with `x_0` an unmatched listed
agent and each `x_{t−1}` valuing the good `x_t` holds. -/
def AltPath (v : A → G → Nat) (agents : List A) (μ : A → Option G) : List A → Prop
  | [] => False
  | [a] => a ∈ agents ∧ μ a = none
  | x :: y :: l => (∃ g, μ x = some g ∧ 0 < v y g) ∧ AltPath v agents μ (y :: l)

omit [DecidableEq A] [DecidableEq G] in
theorem altPath_suffix {μ : A → Option G} : ∀ (l₁ : List A) {b : A} {l₂ : List A},
    AltPath v agents μ (l₁ ++ b :: l₂) → AltPath v agents μ (b :: l₂)
  | [], _, _, h => h
  | x :: l₁, b, l₂, h => by
    apply altPath_suffix l₁
    cases hl : l₁ ++ b :: l₂ with
    | nil => simp at hl
    | cons y l => rw [List.cons_append, hl] at h; exact h.2

omit [DecidableEq A] [DecidableEq G] in
theorem altPath_congr {μ ν : A → Option G} : ∀ {p : List A}, (∀ x ∈ p, μ x = ν x) →
    AltPath v agents μ p → AltPath v agents ν p
  | [], _, h => h
  | [a], he, h => ⟨h.1, (he a List.mem_cons_self) ▸ h.2⟩
  | x :: y :: l, he, h => by
    obtain ⟨⟨g, hg, hpos⟩, hr⟩ := h
    exact ⟨⟨g, (he x List.mem_cons_self) ▸ hg, hpos⟩,
      altPath_congr (fun z hz => he z (List.mem_cons_of_mem _ hz)) hr⟩

omit [DecidableEq G] in
/-- A reachable agent is the end of an alternating path without repeated agents (cut the walk at the first
return). -/
theorem exists_altPath {μ : A → Option G} {b : A} (h : AltReach v agents μ b) :
    ∃ l, AltPath v agents μ (b :: l) ∧ (b :: l).Nodup := by
  induction h with
  | start ha hμ => exact ⟨[], ⟨ha, hμ⟩, by simp⟩
  | @step a b g _ hb hg ih =>
    obtain ⟨l, hp, hnd⟩ := ih
    by_cases hbm : b ∈ a :: l
    · obtain ⟨s, t, hst⟩ := List.append_of_mem hbm
      rw [hst] at hp hnd
      exact ⟨t, altPath_suffix s hp, hnd.sublist (List.sublist_append_right s (b :: t))⟩
    · exact ⟨a :: l, ⟨⟨g, hb, hg⟩, hp⟩, List.nodup_cons.mpr ⟨hbm, hnd⟩⟩

omit [DecidableEq A] [DecidableEq G] in
theorem card_congr {μ ν : A → Option G} (h : ∀ x ∈ agents, (μ x).isSome = (ν x).isSome) :
    card agents μ = card agents ν :=
  Nat.le_antisymm (List.countP_mono_left fun x hx hs => (h x hx) ▸ hs)
    (List.countP_mono_left fun x hx hs => (h x hx).symm ▸ hs)

omit [DecidableEq G] in
/-- **The augmenting path**: if the end `b` of an alternating path without repeats values a good `h` that no agent
holds, shifting the goods along the path (`b` takes `h`, each agent the good of the next) matches one more agent. -/
theorem augment : ∀ (l : List A) (b : A) (μ : A → Option G) (h : G), IsMatching v agents goods μ →
    AltPath v agents μ (b :: l) → (b :: l).Nodup → h ∈ goods → 0 < v b h → (∀ x, μ x ≠ some h) →
      ∃ μ', IsMatching v agents goods μ' ∧ card agents μ < card agents μ'
  | [], b, μ, h, hμ, hp, _, hh, hpos, hfree => by
    obtain ⟨hb, hbn⟩ := hp
    refine ⟨fun x => if x = b then some h else μ x, ⟨fun x g hx => ?_, fun x y g hx hy => ?_⟩, ?_⟩
    · by_cases hxb : x = b
      · rw [ite_eq_left hxb] at hx; cases hx; rw [hxb]; exact ⟨hb, hh, hpos⟩
      · rw [ite_eq_right hxb] at hx; exact hμ.mem x g hx
    · by_cases hxb : x = b <;> by_cases hyb : y = b
      · rw [hxb, hyb]
      · rw [ite_eq_left hxb] at hx; rw [ite_eq_right hyb] at hy; cases hx; exact absurd hy (hfree y)
      · rw [ite_eq_right hxb] at hx; rw [ite_eq_left hyb] at hy; cases hy; exact absurd hx (hfree x)
      · rw [ite_eq_right hxb] at hx; rw [ite_eq_right hyb] at hy; exact hμ.inj x y g hx hy
    · refine countP_lt_of (fun x _ hs => ?_) ⟨b, hb, by simp, by simp [hbn]⟩
      by_cases hxb : x = b
      · simp [hxb]
      · simpa [hxb] using hs
  | c :: l, b, μ, h, hμ, hp, hnd, hh, hpos, hfree => by
    obtain ⟨⟨g, hbg, hcg⟩, hp'⟩ := hp
    have hb : b ∈ agents := (hμ.mem b g hbg).1
    have hgh : g ≠ h := fun e => hfree b (e ▸ hbg)
    let μ₁ : A → Option G := fun x => if x = b then some h else μ x
    have hμ₁ : IsMatching v agents goods μ₁ := by
      refine ⟨fun x g' hx => ?_, fun x y g' hx hy => ?_⟩
      · by_cases hxb : x = b
        · simp only [μ₁, hxb, ite_true, Option.some.injEq] at hx; subst hx; rw [hxb]; exact ⟨hb, hh, hpos⟩
        · simp only [μ₁, hxb, ite_false] at hx; exact hμ.mem x g' hx
      · by_cases hxb : x = b <;> by_cases hyb : y = b
        · rw [hxb, hyb]
        · simp only [μ₁, hxb, hyb, ite_true, ite_false, Option.some.injEq] at hx hy; subst hx
          exact absurd hy (hfree y)
        · simp only [μ₁, hxb, hyb, ite_true, ite_false, Option.some.injEq] at hx hy; subst hy
          exact absurd hx (hfree x)
        · simp only [μ₁, hxb, hyb, ite_false] at hx hy; exact hμ.inj x y g' hx hy
    have hcard : card agents μ = card agents μ₁ := card_congr fun x _ => by
      by_cases hxb : x = b
      · simp [μ₁, hxb, hbg]
      · simp [μ₁, hxb]
    have hbl : b ∉ c :: l := (List.nodup_cons.mp hnd).1
    have hp₁ : AltPath v agents μ₁ (c :: l) := altPath_congr (fun x hx => by
      have : x ≠ b := fun e => hbl (e ▸ hx)
      simp [μ₁, this]) hp'
    have hfree₁ : ∀ x, μ₁ x ≠ some g := fun x hx => by
      by_cases hxb : x = b
      · simp only [μ₁, hxb, ite_true, Option.some.injEq] at hx; exact hgh hx.symm
      · simp only [μ₁, hxb, ite_false] at hx; exact hxb (hμ.inj x b g hx hbg)
    obtain ⟨μ', hμ', hlt⟩ := augment l c μ₁ g hμ₁ hp₁ (List.nodup_cons.mp hnd).2 (hμ.mem b g hbg).2.1 hcg hfree₁
    exact ⟨μ', hμ', hcard ▸ hlt⟩

omit [DecidableEq G] in
/-- **Lemma MAX** (`k4/sdc.md` §31, `k4/oc1_hall.md` §19): if `μ` is a maximum matching, no agent reachable from
an unmatched agent by an alternating path values a good that no agent holds (otherwise the path and that good
form an augmenting path, `augment`). -/
theorem max_no_augment {μ : A → Option G} (hmax : IsMaximum v agents goods μ) {b : A}
    (hb : AltReach v agents μ b) : ∀ h ∈ goods, (∀ x, μ x ≠ some h) → v b h = 0 := by
  intro h hh hfree
  refine Nat.eq_zero_of_not_pos fun hpos => ?_
  obtain ⟨l, hp, hnd⟩ := exists_altPath hb
  obtain ⟨μ', hμ', hlt⟩ := augment l b μ h hmax.1 hp hnd hh hpos hfree
  have := hmax.2 μ' hμ'
  omega

/-- **Lemma MAX at the picks**: if the picks of `ord` form a maximum matching, no agent reachable from a pickless
agent by an alternating path values an unpicked good. -/
theorem picks_no_augment {ord : List A} (hmax : IsMaximum v agents goods (sdPick v ord goods)) {b : A}
    (hb : AltReach v agents (sdPick v ord goods) b) :
    ∀ h ∈ goods, (∀ x, sdPick v ord goods x ≠ some h) → v b h = 0 :=
  max_no_augment hmax hb

end lemmaMax

/-! ## States, the moves of `k4/sdc.md` §29 and the one-absorber completion

A *state* gives each agent a *base*, a list of goods (`B : A → List G`); the *junk* is the goods of no listed
agent's base. At the picks of an order every base is the agent's pick (`pickBase`). The moves follow §29 and the
official move rule of the replays of §31 (`k4/sdc/oc1_core_cex_verify.py`): every mover strictly gains, a chain
never hands on an empty base, and the sets of junk goods have no size cap. -/

section moves
variable (v : A → G → Nat) (agents : List A) (goods : List G)

/-- The bases at the picks of `ord`: each agent's pick, or nothing. -/
def pickBase (ord : List A) (i : A) : List G := (sdPick v ord goods i).toList

/-- The junk of the state `B`: the goods in no listed agent's base. -/
def junkOf (B : A → List G) : List G :=
  goods.filter (fun g => agents.all (fun i => !((B i).contains g)))

/-- A **one-absorber completion** of the bases `B` (`k4/sdc.md` §29): a complete EFX₀ allocation that gives
every base good to its holder, in which at most one agent (the absorber `a`) receives two or more junk goods. -/
def OneAbsorber (B : A → List G) : Prop :=
  ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧ (∀ i ∈ agents, ∀ g ∈ B i, X g = i) ∧
    ∃ a : A, ∀ i ∈ agents, i ≠ a → ((junkOf agents goods B).filter (fun g => X g = i)).length ≤ 1

/-- An **addition** (the chain with t = 0): a listed agent `x` adds a nonempty set `H` of junk goods it values. -/
def IsAddition (B B' : A → List G) : Prop :=
  ∃ (x : A) (H : List G), x ∈ agents ∧ H ≠ [] ∧ H.Nodup ∧ (∀ g ∈ H, g ∈ junkOf agents goods B ∧ 0 < v x g) ∧
    B' x = B x ++ H ∧ ∀ y, y ≠ x → B' y = B y

/-- An **improving chain** `x₀, …, x_t` (t ≥ 1, distinct listed agents; `k4/sdc.md` §29) with pairwise disjoint
sets `H x` of goods that `x` values, `H x₀` inside the junk and the end's base `B x_t`, the others inside the junk:
`x₀` takes `H x₀`, worth more to it than its base; each `x_i` (i ≥ 1) takes `B x_{i−1} ∪ H x_i`, worth more to it
than its base, and `B x_{i−1}` is not empty; the rest of `B x_t` becomes junk; every other agent keeps its base.
The pairs `(x_{i−1}, x_i)` are `(x₀ :: xs).zip xs`. -/
def IsChain (B B' : A → List G) : Prop :=
  ∃ (x₀ : A) (xs : List A) (H : A → List G), xs ≠ [] ∧ (x₀ :: xs).Nodup ∧ (∀ x ∈ x₀ :: xs, x ∈ agents) ∧
    (∀ x ∈ x₀ :: xs, (H x).Nodup ∧ ∀ g ∈ H x, 0 < v x g) ∧
    (∀ x ∈ x₀ :: xs, ∀ y ∈ x₀ :: xs, x ≠ y → ∀ g ∈ H x, g ∉ H y) ∧
    (∀ g ∈ H x₀, g ∈ junkOf agents goods B ∨ g ∈ B ((x₀ :: xs).getLast (List.cons_ne_nil _ _))) ∧
    (∀ x ∈ xs, ∀ g ∈ H x, g ∈ junkOf agents goods B) ∧
    value v x₀ (B x₀) < value v x₀ (H x₀) ∧
    (∀ p ∈ (x₀ :: xs).zip xs, B p.1 ≠ [] ∧ value v p.2 (B p.2) < value v p.2 (B p.1 ++ H p.2)) ∧
    B' x₀ = H x₀ ∧ (∀ p ∈ (x₀ :: xs).zip xs, B' p.2 = B p.1 ++ H p.2) ∧ ∀ y, y ∉ x₀ :: xs → B' y = B y

/-- An **improving ring** `w₀ → w₁ → ⋯ → w_{r−1} → w₀` (r ≥ 2 distinct listed agents): each `w_i` takes its
predecessor's nonempty base plus a set `H w_i` of junk goods it values (pairwise disjoint), worth more to it than
its own base; every other agent keeps its base. The pairs (predecessor, agent) are `(w₀ :: ws).zip (ws ++ [w₀])`. -/
def IsRing (B B' : A → List G) : Prop :=
  ∃ (w₀ : A) (ws : List A) (H : A → List G), ws ≠ [] ∧ (w₀ :: ws).Nodup ∧ (∀ x ∈ w₀ :: ws, x ∈ agents) ∧
    (∀ x ∈ w₀ :: ws, (H x).Nodup ∧ ∀ g ∈ H x, g ∈ junkOf agents goods B ∧ 0 < v x g) ∧
    (∀ x ∈ w₀ :: ws, ∀ y ∈ w₀ :: ws, x ≠ y → ∀ g ∈ H x, g ∉ H y) ∧
    (∀ p ∈ (w₀ :: ws).zip (ws ++ [w₀]), B p.1 ≠ [] ∧
      value v p.2 (B p.2) < value v p.2 (B p.1 ++ H p.2) ∧ B' p.2 = B p.1 ++ H p.2) ∧
    ∀ y, y ∉ w₀ :: ws → B' y = B y

/-- **One improving move**: an addition, a chain or a ring. -/
def OneMove (B B' : A → List G) : Prop :=
  IsAddition v agents goods B B' ∨ IsChain v agents goods B B' ∨ IsRing v agents goods B B'

end moves

section junk
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] in
theorem mem_junkOf {B : A → List G} {g : G} :
    g ∈ junkOf agents goods B ↔ g ∈ goods ∧ ∀ i ∈ agents, g ∉ B i := by
  simp [junkOf, List.all_eq_true]

/-- The junk at the picks of an order of the agents is the set of unpicked goods. -/
theorem mem_junkOf_pickBase {ord : List A} (hperm : ord.Perm agents) {g : G} :
    g ∈ junkOf agents goods (pickBase v goods ord) ↔ g ∈ goods ∧ ∀ x, sdPick v ord goods x ≠ some g := by
  rw [mem_junkOf]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h i _ hi => ?_⟩
  · by_cases hxa : x ∈ agents
    · exact h x hxa (by simp [pickBase, hx])
    · rw [sdPick_of_not_mem v goods (fun hm => hxa (hperm.mem_iff.mp hm))] at hx; cases hx
  · cases hp : sdPick v ord goods i with
    | none => simp [pickBase, hp] at hi
    | some y =>
      simp only [pickBase, hp, Option.toList_some, List.mem_singleton] at hi
      exact h i (hi ▸ hp)

/-- **Lemma MAX in the state's terms**: if the picks of an order form a maximum matching, no agent reachable from a
pickless agent by an alternating path values a junk good of the picks. -/
theorem picks_no_junk {ord : List A} (hperm : ord.Perm agents) (hmax : IsMaximum v agents goods (sdPick v ord goods))
    {b : A} (hb : AltReach v agents (sdPick v ord goods) b) :
    ∀ h ∈ junkOf agents goods (pickBase v goods ord), v b h = 0 := fun h hh => by
  obtain ⟨h1, h2⟩ := (mem_junkOf_pickBase hperm).mp hh
  exact picks_no_augment hmax hb h h1 h2

end junk

/-- The type of a move relation: which states `B'` one move reaches from `B`, for the instance `v, agents, goods`. -/
abbrev MoveRel (A G : Type) : Type := (A → G → Nat) → List A → List G → (A → List G) → (A → List G) → Prop

/-- **OC₁^max for any move relation `Move`**: in every strict connected k = 4 core, for every order whose picks form
a maximum matching, the picks have a one-absorber completion, or some state one `Move` reaches from them has one. -/
def ConjOC1maxWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      IsMaximum v agents goods (sdPick v ord goods) →
      OneAbsorber v agents goods (pickBase v goods ord) ∨
        ∃ B', Move v agents goods (pickBase v goods ord) B' ∧ OneAbsorber v agents goods B'

/-- **Conjecture OC₁^max** (K4.SDC.OC1MAX, `k4/sdc.md` §31): in every strict connected k = 4 core, for every
serial-dictatorship order whose picks form a maximum matching, the picks have a one-absorber EFX₀ completion, or
one improving move (an addition, a chain or a ring, `OneMove`) gives bases that have one. A `Prop`, not an axiom.
It is **false** (`EFX.OC1Max.not_conjOC1max` in `EFX/OC1MaxCex.lean`); the implication `target4_of_conjOC1max`
stands, and the variants that survive are in `EFX/OCVariants.lean`. -/
def ConjOC1max (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjOC1maxWith A G (fun v agents goods => OneMove v agents goods)

/-- **OC₁^max (any move relation) gives EFX₀ allocations of every connected strict k = 4 core**: by MAXSD some
order's picks form a maximum matching, and either completion is an EFX₀ allocation. -/
theorem core_efx0_of_conjOC1maxWith {Move : MoveRel A G} (h : ConjOC1maxWith A G Move) {v : A → G → Nat}
    {agents : List A} {goods : List G} (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods)
    (hconn : Connected v agents goods) (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd (strictVals_of_strict hs)
  rcases h agents goods v hag hgd hc hconn hs ord hperm hmax with ⟨X, hX, hE, -⟩ | ⟨_, -, X, hX, hE, -⟩
  · exact ⟨X, hX, hE⟩
  · exact ⟨X, hX, hE⟩

/-- **OC₁^max (any move relation) ⟹ TARGET₄ over lists**: every instance with at most four relevant goods per agent
has a complete EFX₀ allocation (K4.CORE with K4.TIE, `EFX.core_reduction4_strict`). -/
theorem exists_efx0_of_conjOC1maxWith {Move : MoveRel A G} (h : ConjOC1maxWith A G Move) (v : A → G → Nat)
    (agents : List A) (goods : List G) (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X :=
  core_reduction4_strict agents.length
    (fun _ _ _ hag' hgd' _ hc hconn hs _ => core_efx0_of_conjOC1maxWith h hag' hgd' hc hconn hs) v agents goods
    hne hag hgd (Nat.le_refl _) h4

/-- **OC₁^max (any move relation) ⟹ TARGET₄** in the model's terms. -/
theorem target4_of_conjOC1maxWith (I : Inst) (hn : 0 < I.n) {Move : MoveRel (Fin I.n) (Fin I.m)}
    (h : ConjOC1maxWith (Fin I.n) (Fin I.m) Move) (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _)
    (fun _ _ _ hag hgd _ hc hconn hs _ => core_efx0_of_conjOC1maxWith h hag hgd hc hconn hs) hk

/-- **Conjecture OC₁^max ⟹ TARGET₄** (K4.SDC.OC1MAX.LEAN): if OC₁^max holds, every instance in which every agent
positively values at most four goods has a complete EFX₀ allocation. -/
theorem target4_of_conjOC1max (I : Inst) (hn : 0 < I.n) (h : ConjOC1max (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1maxWith I hn h hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.sdPick_eq_runState
#print axioms EFX.OC1Max.sdPick_spec
#print axioms EFX.OC1Max.isMatching_sdPick
#print axioms EFX.OC1Max.strictVals_of_strict
#print axioms EFX.OC1Max.exists_cycle
#print axioms EFX.OC1Max.exists_holds_fav
#print axioms EFX.OC1Max.exists_order_of_paretoOpt
#print axioms EFX.OC1Max.eq_sdPick_of_le
#print axioms EFX.OC1Max.paretoOpt_sdPick
#print axioms EFX.OC1Max.sdpo
#print axioms EFX.OC1Max.exists_max_of_bdd
#print axioms EFX.OC1Max.card_le_of_paretoImp
#print axioms EFX.OC1Max.exists_maximum_paretoOpt
#print axioms EFX.OC1Max.exists_order_maximum
#print axioms EFX.OC1Max.exists_altPath
#print axioms EFX.OC1Max.augment
#print axioms EFX.OC1Max.max_no_augment
#print axioms EFX.OC1Max.picks_no_augment
#print axioms EFX.OC1Max.mem_junkOf_pickBase
#print axioms EFX.OC1Max.picks_no_junk
#print axioms EFX.OC1Max.core_efx0_of_conjOC1maxWith
#print axioms EFX.OC1Max.exists_efx0_of_conjOC1maxWith
#print axioms EFX.OC1Max.target4_of_conjOC1maxWith
#print axioms EFX.OC1Max.target4_of_conjOC1max
