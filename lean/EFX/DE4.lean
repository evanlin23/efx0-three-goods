import EFX.K4Ties

/-!
# DE4: Draft and Exchange for four relevant goods, the frame (`k4/de4.md` §1–§2; ledger K4.DE4.LEAN)

The definitions of `k4/de4.md` §1 over lists, and the reduction of TARGET₄ to Conjecture DE4 (`k4/de4.md` Lemma 3)
and to its improvement form. Both conjectures are hypotheses of the theorems here, never axioms; neither is proved.

**Definitions** (agents `agents`, goods `goods`, values `v`; a state is a map `base : G → Option A`, `none` for a
leftover good).
- `hold goods base i` (**Y_i**): the goods of `goods` that `base` gives to `i`.
- `topV v i goods` (**v_i(a_i)**): the largest value of a good of `goods` to `i`.
- `IsUpper` (**upper set**): goods of `R_i` worth more than `i`'s top, every set obtained by removing one good worth
  at most the top (so every proper nonempty subset is worth at most the top, values being additive).
- `IsLowerPair` (**lower pair**): for a 4-good agent, two relevant goods each worth less than every other relevant
  good (the paper's `{c, d}`), worth less than the top and more than every other relevant good that is not worth the
  top (`v(b) < v(c) + v(d) < v(a)`).
- `Allowed` (**holding**): nothing or one relevant good, an upper set, or the lower pair.
- `level` (**ℓ**): `0` for nothing; `4 − r` for one good with `r` relevant goods worth more (`a, b, c, d ↦ 4, 3, 2, 1`
  on a strict profile); for two or more goods, `5` if worth more than the top (an upper set), else `3` (the lower
  pair).
- `Valid` (**valid state**): holdings go to listed agents and are allowed; (V1) every good some listed agent wants
  (worth more to it than its holding) is the whole holding of some listed agent; (V2) no holding threatens another
  listed agent: `v_i(Y_j ∖ h) ≤ v_i(Y_i)` for every `h ∈ Y_j`.
- `Completable`: some allocation of all goods to listed agents extends `base` and is EFX₀ (`EFX0L`).
- `potential` (**Φ**, the level sum), `Better` (**the order of §1**: Φ larger, or Φ equal and the values
  value-Pareto-better), `IsMaximum` (a valid state with no better valid state).
- `R1Core4`: every listed agent values 3 or 4 goods and is strictly balanced (`2 v_i(g) < v_i(goods)` for every
  good; with `Strict`, this is `v(a) < v(R ∖ a)`).
- `ConjDE4` (**Conjecture DE4**): on every strict R1-core with at most four relevant goods per agent, every maximum
  is completable. `ConjDE4Imp` (**the improvement form**): every valid state that is not completable has a better
  valid state.

**Results.**
- `draft_valid` (**Lemma 2**): the draft (agents in list order each take their most valuable relevant good not yet
  taken, or nothing) is a valid state.
- `exists_maximum`: every instance has a maximum (descent from the draft along `Better`, which raises the measure
  `Φ · (V + 1) + Σ_i v_i(Y_i)` with `V = Σ_i v_i(goods)`).
- `conjDE4_of_imp`: the improvement form implies Conjecture DE4.
- `exists_efx0_of_conjDE4`, `target4_of_conjDE4` (**Lemma 3**): Conjecture DE4 implies an EFX₀ allocation on every
  strict R1-core with at most four relevant goods, hence (with K4.CORE and K4.TIE, `EFX.target4_of_strict_cores`)
  TARGET₄: every instance in which each agent positively values at most four goods has an EFX₀ allocation.
  `target4_of_conjDE4Imp`: the same from the improvement form.

**Faithfulness** (paper / Lean / why they agree). The paper's holdings are subsets of `R_i`; here a holding is the
list of goods `base` assigns to `i`, and `Allowed` requires its goods to be relevant (for an upper set or the lower
pair this follows from the value conditions). "Minimal set worth more than the top" is stated through the sets
obtained by removing one good, which are the maximal proper subsets. On a strict profile the top is unique, so
"relevant goods not worth the top" is `R_i ∖ {a, c, d} = {b}`, and `level` gives one good the rank level of §1.
Validity is (V1) and (V2) of §1 verbatim (with `θ_i(B) = max_h v_i(B ∖ h)` unfolded). The paper's maxima are valid
states of largest Φ that no valid state of the same Φ value-Pareto-dominates; `IsMaximum` is exactly a valid state with
no `Better` valid state. Completions give every leftover good to some agent; `Completable` asks for an EFX₀ allocation
of all goods extending the state.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## States and holdings -/

/-- `Y_i`: the goods of `goods` that `base` gives to `i`. -/
def hold (goods : List G) (base : G → Option A) (i : A) : List G :=
  goods.filter (fun g => decide (base g = some i))

/-- `v_i(a_i)`: the largest value to `i` of a good of `goods` (`0` if there is none). -/
def topV (v : A → G → Nat) (i : A) (goods : List G) : Nat :=
  (goods.map (v i)).foldr max 0

/-- An upper set of `i`: relevant goods worth more than the top, and removing any one good leaves at most the top. -/
def IsUpper (v : A → G → Nat) (i : A) (goods : List G) (S : List G) : Prop :=
  (∀ g ∈ S, 0 < v i g) ∧ topV v i goods < value v i S ∧ ∀ g ∈ S, value v i (S.erase g) ≤ topV v i goods

/-- The lower pair `{c, d}` of a 4-good agent with `v(b) < v(c) + v(d) < v(a)`. -/
def IsLowerPair (v : A → G → Nat) (i : A) (goods : List G) (S : List G) : Prop :=
  (relevant v i goods).length = 4 ∧ S.length = 2 ∧ (∀ g ∈ S, 0 < v i g) ∧
    value v i S < topV v i goods ∧
    (∀ g ∈ S, ∀ g' ∈ relevant v i goods, g' ∉ S → v i g < v i g') ∧
    (∀ g' ∈ relevant v i goods, g' ∉ S → v i g' < topV v i goods → v i g' < value v i S)

/-- The holdings of `k4/de4.md` §1: nothing or one relevant good, an upper set, or the lower pair. -/
def Allowed (v : A → G → Nat) (i : A) (goods : List G) (S : List G) : Prop :=
  (S.length ≤ 1 ∧ ∀ g ∈ S, 0 < v i g) ∨ IsUpper v i goods S ∨ IsLowerPair v i goods S

/-- The level `ℓ` of a holding: `0` for nothing, `4 − r` for one good with `r` relevant goods worth more, and for
two or more goods `5` if worth more than the top (an upper set), else `3` (the lower pair). -/
def level (v : A → G → Nat) (i : A) (goods : List G) : List G → Nat
  | [] => 0
  | [g] => 4 - ((relevant v i goods).filter (fun g' => decide (v i g < v i g'))).length
  | S@(_ :: _ :: _) => if topV v i goods < value v i S then 5 else 3

/-- A valid state (`k4/de4.md` §1). -/
structure Valid (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop where
  /-- holdings go to listed agents -/
  owners : ∀ g ∈ goods, ∀ j, base g = some j → j ∈ agents
  /-- every holding is allowed -/
  allowed : ∀ i ∈ agents, Allowed v i goods (hold goods base i)
  /-- (V1): a good some listed agent wants is the whole holding of some listed agent -/
  v1 : ∀ i ∈ agents, ∀ g ∈ goods, value v i (hold goods base i) < v i g →
    ∃ j ∈ agents, hold goods base j = [g]
  /-- (V2): no holding threatens another listed agent -/
  v2 : ∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → ∀ h ∈ hold goods base j,
    value v i ((hold goods base j).erase h) ≤ value v i (hold goods base i)

/-- The state has an EFX₀ completion: an allocation of all goods to listed agents that extends it. -/
def Completable (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ∃ X : G → A, IsAllocation agents goods X ∧ (∀ g ∈ goods, ∀ j, base g = some j → X g = j) ∧
    EFX0L v agents goods X

/-- `Φ`, the level sum. -/
def potential (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  (agents.map (fun i => level v i goods (hold goods base i))).sum

/-- The sum of the listed agents' values for their holdings. -/
def totalValue (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  (agents.map (fun i => value v i (hold goods base i))).sum

/-- The order of `k4/de4.md` §1: `base'` is better than `base` if its level sum is larger, or equal with the values
value-Pareto-better. -/
def Better (v : A → G → Nat) (agents : List A) (goods : List G) (base' base : G → Option A) : Prop :=
  potential v agents goods base < potential v agents goods base' ∨
    (potential v agents goods base = potential v agents goods base' ∧
      (∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i)) ∧
      ∃ i ∈ agents, value v i (hold goods base i) < value v i (hold goods base' i))

/-- A maximum: a valid state that no valid state is better than. -/
def IsMaximum (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  Valid v agents goods base ∧ ∀ base', Valid v agents goods base' → ¬ Better v agents goods base' base

/-- An R1-core with at most four relevant goods per agent: every listed agent values 3 or 4 goods and is strictly
balanced. -/
def R1Core4 (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ (relevant v i goods).length ≤ 4 ∧
    ∀ g ∈ goods, 2 * v i g < value v i goods

/-- **Conjecture DE4** (`k4/de4.md` §2): on every strict R1-core with at most four relevant goods per agent, every
maximum is completable. A hypothesis, never an axiom. -/
def ConjDE4 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximum v agents goods base → Completable v agents goods base

/-- **The improvement form** (`k4/de4.md` §2): on every strict R1-core with at most four relevant goods per agent,
every valid state that is not completable has a better valid state. A hypothesis, never an axiom. -/
def ConjDE4Imp (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, Valid v agents goods base → ¬ Completable v agents goods base →
      ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base

/-! ## Basic facts -/

section basics
variable (v : A → G → Nat)

omit [DecidableEq G] in
theorem mem_hold {goods : List G} {base : G → Option A} {i : A} {g : G} :
    g ∈ hold goods base i ↔ g ∈ goods ∧ base g = some i := by
  simp [hold]

omit [DecidableEq G] in
theorem value_hold_le (goods : List G) (base : G → Option A) (i : A) :
    value v i (hold goods base i) ≤ value v i goods :=
  value_sublist v i (List.filter_sublist)

omit [DecidableEq A] [DecidableEq G] in
theorem level_le_five (i : A) (goods : List G) : ∀ S : List G, level v i goods S ≤ 5
  | [] => by simp [level]
  | [_] => by simp only [level]; omega
  | _ :: _ :: _ => by simp only [level]; split <;> omega

omit [DecidableEq A] in
theorem sum_map_le {l : List A} {f g : A → Nat} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    omega

omit [DecidableEq A] in
theorem sum_map_lt {l : List A} {f g : A → Nat} (h : ∀ i ∈ l, f i ≤ g i) (hs : ∃ i ∈ l, f i < g i) :
    (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => obtain ⟨_, hi, _⟩ := hs; simp at hi
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨i, hi, hlt⟩ := hs
    have ha := h a (by simp)
    have hle := sum_map_le (l := l) (fun j hj => h j (List.mem_cons_of_mem _ hj))
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · have := ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) ⟨i, hi, hlt⟩
      omega

omit [DecidableEq A] in
theorem sum_map_le_mul {l : List A} {f : A → Nat} {c : Nat} (h : ∀ i ∈ l, f i ≤ c) :
    (l.map f).sum ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    have := h a (by simp)
    have := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    omega

omit [DecidableEq G] in
theorem length_le_one_of_eq {l : List G} (hl : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, a = b) : l.length ≤ 1 := by
  match l, hl, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hl, h =>
    have hab : a = b := h a (by simp) b (by simp)
    exact absurd (hab ▸ List.mem_cons_self) (List.nodup_cons.mp hl).1

omit [DecidableEq G] in
theorem eq_singleton_of_length_le_one {l : List G} {g : G} (hl : l.length ≤ 1) (hg : g ∈ l) : l = [g] := by
  match l, hl, hg with
  | [a], _, hg => simp at hg; simp [hg]
  | [], _, hg => simp at hg

end basics

/-! ## The descent measure -/

section descent
variable (v : A → G → Nat) (agents : List A) (goods : List G)

/-- `V = Σ_i v_i(goods)`, a bound for the total value of the holdings. -/
def bigV : Nat := (agents.map (fun i => value v i goods)).sum

/-- The measure `Φ · (V + 1) + Σ_i v_i(Y_i)`, which every `Better` state raises. -/
def measure (base : G → Option A) : Nat :=
  potential v agents goods base * (bigV v agents goods + 1) + totalValue v agents goods base

omit [DecidableEq G] in
theorem totalValue_le (base : G → Option A) : totalValue v agents goods base ≤ bigV v agents goods :=
  sum_map_le (fun i _ => value_hold_le v goods base i)

omit [DecidableEq G] in
theorem potential_le (base : G → Option A) : potential v agents goods base ≤ 5 * agents.length :=
  sum_map_le_mul (fun i _ => level_le_five v i goods _)

omit [DecidableEq G] in
theorem measure_le (base : G → Option A) :
    measure v agents goods base ≤ 5 * agents.length * (bigV v agents goods + 1) + bigV v agents goods := by
  have h1 := Nat.mul_le_mul_right (bigV v agents goods + 1) (potential_le v agents goods base)
  have h2 := totalValue_le v agents goods base
  unfold measure
  omega

omit [DecidableEq G] in
theorem measure_lt_of_better {base base' : G → Option A} (h : Better v agents goods base' base) :
    measure v agents goods base < measure v agents goods base' := by
  unfold measure
  have hT := totalValue_le v agents goods base
  rcases h with hP | ⟨hP, hle, hlt⟩
  · have h1 := Nat.mul_le_mul_right (bigV v agents goods + 1) hP
    rw [Nat.succ_mul] at h1
    omega
  · have : totalValue v agents goods base < totalValue v agents goods base' := sum_map_lt hle hlt
    rw [hP]
    omega

/-- From any valid state, descent along `Better` reaches a maximum. -/
theorem exists_maximum_of_valid {base : G → Option A} (hb : Valid v agents goods base) :
    ∃ m, IsMaximum v agents goods m := by
  let M := 5 * agents.length * (bigV v agents goods + 1) + bigV v agents goods
  suffices key : ∀ k, ∀ b, Valid v agents goods b → M - measure v agents goods b ≤ k →
      ∃ m, IsMaximum v agents goods m from key _ base hb (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro b hb hk
    refine ⟨b, hb, fun b' hb' hbet => ?_⟩
    have := measure_lt_of_better v agents goods hbet
    have := measure_le v agents goods b'
    omega
  | succ k ih =>
    intro b hb hk
    by_cases hmax : ∀ b', Valid v agents goods b' → ¬ Better v agents goods b' b
    · exact ⟨b, hb, hmax⟩
    · obtain ⟨b', hb'⟩ := Classical.not_forall.mp hmax
      have hv' : Valid v agents goods b' := Classical.byContradiction fun hn => hb' fun h => absurd h hn
      have hbet : Better v agents goods b' b := Classical.byContradiction fun hn => hb' fun _ => hn
      have := measure_lt_of_better v agents goods hbet
      have := measure_le v agents goods b'
      exact ih b' hv' (by omega)

end descent

/-! ## The draft (Lemma 2) -/

section draft
variable (v : A → G → Nat) (goods : List G)

/-- The goods `i` may take: in `goods`, relevant to `i`, not yet taken. -/
def candidates (i : A) (base : G → Option A) : List G :=
  goods.filter (fun g => decide (base g = none ∧ 0 < v i g))

/-- `i`'s pick: its most valuable candidate. -/
def pickD (i : A) (base : G → Option A) : Option G := favorite (v i) (candidates v goods i base)

/-- One draft step: `i` takes its pick, if any. -/
def step (i : A) (base : G → Option A) : G → Option A :=
  match pickD v goods i base with
  | none => base
  | some p => fun g => if g = p then some i else base g

/-- The draft from a partial state: the agents of the list, in order, each take their pick. -/
def draftAux : List A → (G → Option A) → (G → Option A)
  | [], base => base
  | i :: rest, base => draftAux rest (step v goods i base)

/-- **The draft** (`k4/de4.md` Lemma 2): agents in list order each take their most valuable relevant good not yet
taken, or nothing. -/
def draft (agents : List A) : G → Option A := draftAux v goods agents (fun _ => none)

omit [DecidableEq A] [DecidableEq G] in
theorem pickD_spec {i : A} {base : G → Option A} {p : G} (h : pickD v goods i base = some p) :
    p ∈ goods ∧ base p = none ∧ 0 < v i p ∧
      ∀ g ∈ goods, base g = none → 0 < v i g → v i g ≤ v i p := by
  obtain ⟨hp, hmax⟩ := favorite_spec (v i) h
  simp only [candidates, List.mem_filter, decide_eq_true_eq] at hp
  refine ⟨hp.1, hp.2.1, hp.2.2, fun g hg hb hpos => hmax g ?_⟩
  simp [candidates, hg, hb, hpos]

omit [DecidableEq A] in
theorem step_of_some {i : A} {base : G → Option A} {g : G} {j : A} (h : base g = some j) :
    step v goods i base g = some j := by
  unfold step
  cases hp : pickD v goods i base with
  | none => exact h
  | some p =>
    have := (pickD_spec v goods hp).2.1
    have hgp : g ≠ p := fun e => by rw [e] at h; rw [h] at this; exact absurd this (by simp)
    simp [hgp, h]

omit [DecidableEq A] in
theorem step_eq {i : A} {base : G → Option A} {g : G} {j : A} (h : step v goods i base g = some j) :
    base g = some j ∨ (j = i ∧ pickD v goods i base = some g) := by
  unfold step at h
  cases hp : pickD v goods i base with
  | none => rw [hp] at h; exact Or.inl h
  | some p =>
    rw [hp] at h
    by_cases hgp : g = p
    · subst hgp
      simp only [ite_true, Option.some.injEq] at h
      exact Or.inr ⟨h.symm, rfl⟩
    · simp only [hgp, ite_false] at h
      exact Or.inl h

omit [DecidableEq A] in
theorem step_pick {i : A} {base : G → Option A} {p : G} (h : pickD v goods i base = some p) :
    step v goods i base p = some i := by
  unfold step
  rw [h]
  simp

omit [DecidableEq A] in
theorem aux_of_some : ∀ (L : List A) {base : G → Option A} {g : G} {j : A}, base g = some j →
    draftAux v goods L base g = some j
  | [], _, _, _, h => h
  | _ :: rest, _, _, _, h => aux_of_some rest (step_of_some v goods h)

omit [DecidableEq A] in
theorem aux_eq : ∀ (L : List A) {base : G → Option A} {g : G} {j : A}, draftAux v goods L base g = some j →
    base g = some j ∨ (j ∈ L ∧ g ∈ goods ∧ 0 < v j g)
  | [], _, _, _, h => Or.inl h
  | i :: rest, base, g, j, h => by
    rcases aux_eq rest h with h1 | ⟨hj, hg, hpos⟩
    · rcases step_eq v goods h1 with h2 | ⟨rfl, hp⟩
      · exact Or.inl h2
      · have := pickD_spec v goods hp
        exact Or.inr ⟨by simp, this.1, this.2.2.1⟩
    · exact Or.inr ⟨List.mem_cons_of_mem _ hj, hg, hpos⟩

theorem aux_unique : ∀ (L : List A) {base : G → Option A} {j : A}, L.Nodup → (∀ g, base g ≠ some j) →
    ∀ {g g' : G}, draftAux v goods L base g = some j → draftAux v goods L base g' = some j → g = g'
  | [], _, _, _, hb, g, _, h, _ => absurd h (hb g)
  | i :: rest, base, j, hnd, hb, g, g', h, h' => by
    have hi : i ∉ rest := (List.nodup_cons.mp hnd).1
    by_cases hji : j = i
    · subst hji
      have pick_of : ∀ {x : G}, draftAux v goods rest (step v goods j base) x = some j →
          pickD v goods j base = some x := by
        intro x hx
        rcases aux_eq v goods rest hx with h1 | ⟨hj, _⟩
        · rcases step_eq v goods h1 with h2 | ⟨_, hp⟩
          · exact absurd h2 (hb x)
          · exact hp
        · exact absurd hj hi
      have e1 := pick_of h
      have e2 := pick_of h'
      rw [e1] at e2
      exact Option.some.inj e2
    · refine aux_unique rest (List.nodup_cons.mp hnd).2 (fun x hx => ?_) h h'
      rcases step_eq v goods hx with h2 | ⟨h2, _⟩
      · exact hb x h2
      · exact hji h2

theorem aux_best : ∀ (L : List A) {base : G → Option A} {i : A}, i ∈ L → ∀ {g : G}, g ∈ goods →
    draftAux v goods L base g = none → 0 < v i g → ∃ p, draftAux v goods L base p = some i ∧ v i g ≤ v i p
  | [], _, _, hi, _, _, _, _ => by simp at hi
  | i' :: rest, base, i, hi, g, hg, hnone, hpos => by
    by_cases hii : i = i'
    · subst hii
      have hbg : base g = none := by
        cases hb : base g with
        | none => rfl
        | some k =>
          have := aux_of_some v goods (i :: rest) hb
          rw [this] at hnone
          exact absurd hnone (by simp)
      cases hp : pickD v goods i base with
      | none =>
        have hc : g ∈ candidates v goods i base := by simp [candidates, hg, hbg, hpos]
        have : candidates v goods i base = [] := (favorite_eq_none_iff (v i)).mp hp
        rw [this] at hc
        simp at hc
      | some p =>
        refine ⟨p, aux_of_some v goods rest (step_pick v goods hp), ?_⟩
        exact (pickD_spec v goods hp).2.2.2 g hg hbg hpos
    · have hi' : i ∈ rest := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h hii
        · exact h
      exact aux_best rest hi' hg hnone hpos

variable {v goods}

theorem draft_hold_length {agents : List A} (hag : agents.Nodup) (hgd : goods.Nodup) (i : A) :
    (hold goods (draft v goods agents) i).length ≤ 1 := by
  apply length_le_one_of_eq (hgd.filter _)
  intro a ha b hb
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  by_cases hi : i ∈ agents
  · exact aux_unique v goods agents hag (fun _ h => by simp at h) ha.2 hb.2
  · rcases aux_eq v goods agents ha.2 with h | ⟨h, _⟩
    · simp at h
    · exact absurd h hi

/-- **Lemma 2**: the draft is a valid state. -/
theorem draft_valid {agents : List A} (hag : agents.Nodup) (hgd : goods.Nodup) :
    Valid v agents goods (draft v goods agents) := by
  have hlen := draft_hold_length (v := v) hag hgd
  have owner : ∀ {g : G} {j : A}, draft v goods agents g = some j → j ∈ agents ∧ g ∈ goods ∧ 0 < v j g := by
    intro g j h
    rcases aux_eq v goods agents h with h | h
    · simp at h
    · exact h
  refine ⟨fun g _ j h => (owner h).1, fun i _ => Or.inl ⟨hlen i, fun g hg => ?_⟩, ?_, ?_⟩
  · rw [mem_hold] at hg
    exact (owner hg.2).2.2
  · intro i hi g hg hlt
    cases hF : draft v goods agents g with
    | none =>
      obtain ⟨p, hp, hle⟩ := aux_best v goods agents hi hg hF (by omega)
      have hpm : p ∈ hold goods (draft v goods agents) i := mem_hold.mpr ⟨(owner hp).2.1, hp⟩
      have := le_value_of_mem v i hpm
      omega
    | some j =>
      have hj := owner hF
      refine ⟨j, hj.1, eq_singleton_of_length_le_one (hlen j) (mem_hold.mpr ⟨hg, hF⟩)⟩
  · intro i _ j _ _ h hh
    have hl := hlen j
    have hs := eq_singleton_of_length_le_one hl hh
    rw [hs]
    simp

end draft

/-! ## Maxima, Lemma 3 and TARGET₄ -/

/-- Every instance has a maximum. -/
theorem exists_maximum (v : A → G → Nat) {agents : List A} {goods : List G} (hag : agents.Nodup)
    (hgd : goods.Nodup) : ∃ base, IsMaximum v agents goods base :=
  exists_maximum_of_valid v agents goods (draft_valid hag hgd)

/-- The improvement form implies Conjecture DE4: a maximum has no better valid state. -/
theorem conjDE4_of_imp (h : ConjDE4Imp A G) : ConjDE4 A G := by
  intro v agents goods hne hag hgd hc hs base hmax
  refine Classical.byContradiction fun hnc => ?_
  obtain ⟨b', hv', hb'⟩ := h v agents goods hne hag hgd hc hs base hmax.1 hnc
  exact hmax.2 b' hv' hb'

/-- **Lemma 3** (`k4/de4.md` §2), on one instance: Conjecture DE4 gives an EFX₀ allocation of every strict R1-core
with at most four relevant goods per agent. -/
theorem exists_efx0_of_conjDE4 (h : ConjDE4 A G) (v : A → G → Nat) {agents : List A} {goods : List G}
    (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨base, hmax⟩ := exists_maximum v hag hgd
  obtain ⟨X, hX, -, hE⟩ := h v agents goods hne hag hgd hc hs base hmax
  exact ⟨X, hX, hE⟩

/-- **Conjecture DE4 implies TARGET₄** (`k4/de4.md` Lemma 3, with K4.CORE and K4.TIE): if DE4 holds, every
instance in which each agent positively values at most four goods has an EFX₀ allocation. -/
theorem target4_of_conjDE4 (I : Inst) (hn : 0 < I.n) (h : ConjDE4 (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _)
    (fun w agents _ hag hgd _ hcore _ hs _ =>
      exists_efx0_of_conjDE4 h w (fun he => by have := hcore.1; rw [he] at this; simp at this) hag hgd
        (fun i hi => ⟨(hcore.2.1 i hi).1, (hcore.2.1 i hi).2, hcore.2.2.1 i hi⟩) hs) h4

/-- **The improvement form of DE4 implies TARGET₄.** -/
theorem target4_of_conjDE4Imp (I : Inst) (hn : 0 < I.n) (h : ConjDE4Imp (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjDE4 I hn (conjDE4_of_imp h) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.mem_hold
#print axioms EFX.DE4.value_hold_le
#print axioms EFX.DE4.level_le_five
#print axioms EFX.DE4.sum_map_le
#print axioms EFX.DE4.sum_map_lt
#print axioms EFX.DE4.sum_map_le_mul
#print axioms EFX.DE4.length_le_one_of_eq
#print axioms EFX.DE4.eq_singleton_of_length_le_one
#print axioms EFX.DE4.totalValue_le
#print axioms EFX.DE4.potential_le
#print axioms EFX.DE4.measure_le
#print axioms EFX.DE4.measure_lt_of_better
#print axioms EFX.DE4.exists_maximum_of_valid
#print axioms EFX.DE4.pickD_spec
#print axioms EFX.DE4.step_of_some
#print axioms EFX.DE4.step_eq
#print axioms EFX.DE4.step_pick
#print axioms EFX.DE4.aux_of_some
#print axioms EFX.DE4.aux_eq
#print axioms EFX.DE4.aux_unique
#print axioms EFX.DE4.aux_best
#print axioms EFX.DE4.draft_hold_length
#print axioms EFX.DE4.draft_valid
#print axioms EFX.DE4.exists_maximum
#print axioms EFX.DE4.conjDE4_of_imp
#print axioms EFX.DE4.exists_efx0_of_conjDE4
#print axioms EFX.DE4.target4_of_conjDE4
#print axioms EFX.DE4.target4_of_conjDE4Imp
