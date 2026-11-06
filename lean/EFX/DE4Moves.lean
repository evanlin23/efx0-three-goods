import EFX.DE4

/-!
# DE4: levels, trades and the easy moves (`k4/de4.md` §3; ledger K4.DE4.LEAN)

Lemmas of `k4/de4.md` §3 on the definitions of `EFX/DE4.lean`.

**Definitions.**
- `leftover goods base` (**J**): the goods no agent holds.
- `Frozen agents goods base v i`: `i` holds a single good that some listed agent wants; `Free` is its negation.

**Results.**
- `level_mono` (**Lemma 1(a)**): for allowed holdings, more value never means a lower level.
- `better_of_monotone`: a state in which no listed agent's value and no level drops, and some value rises, is
  `Better`.
- `valid_of_gain` (**the trade lemma**, the common core of Lemma 4's chain, Lemma 4′ and the rings): a state whose
  holdings are allowed, in which no listed agent's value drops, every good some listed agent wanted is a one-good
  holding, and no holding of three or more goods threatens anyone, is valid. Holdings of at most two goods threaten
  nobody once (V1) holds (Lemma 1(c)).
- `exists_better_of_selfUpgrade` (**Lemma 4′**): a free agent with an allowed holding of at most two goods, from its
  own goods and the leftover goods, worth more than its holding, gives a better valid state.
- `completable_of_empty` (**Corollary 5(b)**): if nobody is threatened by the leftover goods alone and some listed
  agent holds nothing, the state is completable.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `J`: the goods no agent holds. -/
def leftover (goods : List G) (base : G → Option A) : List G :=
  goods.filter (fun g => decide (base g = none))

/-- `i` is frozen: it holds a single good that some listed agent wants. -/
def Frozen (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (i : A) : Prop :=
  ∃ y, hold goods base i = [y] ∧ ∃ w ∈ agents, value v w (hold goods base w) < v w y

/-! ## Values and levels -/

section levels
variable (v : A → G → Nat) (i : A) (goods : List G)

omit [DecidableEq A] [DecidableEq G] in
theorem le_topV {g : G} (hg : g ∈ goods) : v i g ≤ topV v i goods := by
  unfold topV
  induction goods with
  | nil => simp at hg
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hg) (Nat.le_max_right _ _)

omit [DecidableEq A] [DecidableEq G] in
theorem exists_topV (h : 0 < topV v i goods) : ∃ g ∈ goods, v i g = topV v i goods := by
  unfold topV at *
  induction goods with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons] at *
    by_cases hle : (l.map (v i)).foldr max 0 ≤ v i a
    · exact ⟨a, by simp, by rw [Nat.max_eq_left hle]⟩
    · have hlt : v i a < (l.map (v i)).foldr max 0 := Nat.lt_of_not_le hle
      rw [Nat.max_eq_right (Nat.le_of_lt hlt)] at h ⊢
      obtain ⟨g, hg, he⟩ := ih h
      exact ⟨g, List.mem_cons_of_mem _ hg, he⟩

omit [DecidableEq A] [DecidableEq G] in
theorem value_singleton (g : G) : value v i [g] = v i g := by simp [value]

omit [DecidableEq A] [DecidableEq G] in
theorem level_single (g : G) :
    level v i goods [g] = 4 - ((relevant v i goods).filter (fun g' => decide (v i g < v i g'))).length := rfl

omit [DecidableEq A] [DecidableEq G] in
theorem level_multi {S : List G} (hS : 2 ≤ S.length) :
    level v i goods S = if topV v i goods < value v i S then 5 else 3 := by
  match S, hS with
  | _ :: _ :: _, _ => rfl

omit [DecidableEq A] [DecidableEq G] in
/-- The count of relevant goods worth more than `t` is at most that for `s` when `v(s) ≤ v(t)`. -/
theorem count_better_le {s t : G} (h : v i s ≤ v i t) :
    ((relevant v i goods).filter (fun g' => decide (v i t < v i g'))).length ≤
      ((relevant v i goods).filter (fun g' => decide (v i s < v i g'))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun g _ hg => by simp only [decide_eq_true_eq] at hg ⊢; omega)

omit [DecidableEq A] [DecidableEq G] in
theorem level_single_le_four (g : G) : level v i goods [g] ≤ 4 := by
  rw [level_single]; omega

omit [DecidableEq A] [DecidableEq G] in
theorem three_le_level_multi {S : List G} (hS : 2 ≤ S.length) : 3 ≤ level v i goods S := by
  rw [level_multi v i goods hS]; split <;> omega

omit [DecidableEq A] in
/-- **Lemma 1(a)**: among allowed holdings of `i`, more value never means a lower level. -/
theorem level_mono {S T : List G} (hS : Allowed v i goods S) (hT : Allowed v i goods T)
    (hSg : ∀ g ∈ S, g ∈ goods) (hTg : ∀ g ∈ T, g ∈ goods) (hST : value v i S < value v i T) :
    level v i goods S ≤ level v i goods T := by
  match S, T, hS, hT, hSg, hTg, hST with
  | [], _, _, _, _, _, _ => simp [level]
  | [_], [], _, _, _, _, hST => simp [value] at hST
  | [s], [t], _, _, _, _, hST =>
    rw [value_singleton, value_singleton] at hST
    rw [level_single, level_single]
    have := count_better_le v i goods (Nat.le_of_lt hST)
    omega
  | [s], t1 :: t2 :: T', _, hT, hSg, _, hST =>
    rw [value_singleton] at hST
    by_cases hup : topV v i goods < value v i (t1 :: t2 :: T')
    · rw [level_multi v i goods (S := t1 :: t2 :: T') (by simp)]
      simp only [hup, ↓reduceIte]
      have := level_single_le_four v i goods s
      omega
    · rw [level_multi v i goods (S := t1 :: t2 :: T') (by simp)]
      simp only [hup, ↓reduceIte]
      rcases hT with hT | hT | hT
      · simp at hT
      · exact absurd hT.2.1 hup
      · have hlt : v i s < topV v i goods := Nat.lt_trans hST hT.2.2.2.1
        obtain ⟨g, hg, hgv⟩ := exists_topV v i goods (by omega)
        have hgr : g ∈ (relevant v i goods).filter (fun g' => decide (v i s < v i g')) := by
          simp only [relevant, List.mem_filter, decide_eq_true_eq]
          exact ⟨⟨hg, by omega⟩, by omega⟩
        have := List.length_pos_of_mem hgr
        rw [level_single]
        omega
  | _ :: _ :: _, [], _, _, _, _, hST => simp [value] at hST
  | s1 :: s2 :: S', [t], hS, _, _, hTg, hST =>
    rw [value_singleton] at hST
    rcases hS with hS | hS | hS
    · simp at hS
    · have := le_topV v i goods (hTg t (by simp))
      have := hS.2.1
      omega
    · have hl : level v i goods (s1 :: s2 :: S') = 3 := by
        rw [level_multi v i goods (S := s1 :: s2 :: S') (by simp)]
        have : ¬ topV v i goods < value v i (s1 :: s2 :: S') := by have := hS.2.2.2.1; omega
        simp only [this, ↓reduceIte]
      rw [hl, level_single]
      have htS : t ∉ s1 :: s2 :: S' := fun ht => by
        have := le_value_of_mem v i ht
        omega
      have htop : topV v i goods ≤ v i t := by
        refine Nat.le_of_not_lt fun hlt => ?_
        have := hS.2.2.2.2.2 t (by
          simp only [relevant, List.mem_filter, decide_eq_true_eq]
          exact ⟨hTg t (by simp), by omega⟩) htS hlt
        omega
      have h0 : ((relevant v i goods).filter (fun g' => decide (v i t < v i g'))).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro g hg
        simp only [relevant, List.mem_filter, decide_eq_true_eq] at hg
        have := le_topV v i goods hg.1
        simp only [decide_eq_true_eq]
        omega
      omega
  | s1 :: s2 :: S', t1 :: t2 :: T', hS, _, _, _, hST =>
    rcases hS with hS | hS | hS
    · simp at hS
    · rw [level_multi v i goods (S := s1 :: s2 :: S') (by simp),
        level_multi v i goods (S := t1 :: t2 :: T') (by simp)]
      have h1 : topV v i goods < value v i (t1 :: t2 :: T') := Nat.lt_trans hS.2.1 hST
      simp only [hS.2.1, h1, ↓reduceIte, Nat.le_refl]
    · rw [level_multi v i goods (S := s1 :: s2 :: S') (by simp)]
      have : ¬ topV v i goods < value v i (s1 :: s2 :: S') := by have := hS.2.2.2.1; omega
      simp only [this, ↓reduceIte]
      exact three_le_level_multi v i goods (by simp)

end levels

/-! ## The order and the trade lemma -/

section trades
variable (v : A → G → Nat) (agents : List A) (goods : List G)

omit [DecidableEq G] in
/-- A state in which no listed agent's level or value drops and some value rises is `Better`. -/
theorem better_of_monotone {base base' : G → Option A}
    (hlev : ∀ i ∈ agents, level v i goods (hold goods base i) ≤ level v i goods (hold goods base' i))
    (hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i))
    (hlt : ∃ i ∈ agents, value v i (hold goods base i) < value v i (hold goods base' i)) :
    Better v agents goods base' base := by
  have hP : potential v agents goods base ≤ potential v agents goods base' := sum_map_le hlev
  rcases Nat.lt_or_eq_of_le hP with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hval, hlt⟩

/-- **The trade lemma.** A state whose holdings go to listed agents and are allowed, in which no listed agent's value
drops, every good some listed agent wanted is a one-good holding, and no holding of three or more goods threatens
another listed agent, is valid. -/
theorem valid_of_gain {base base' : G → Option A}
    (howners : ∀ g ∈ goods, ∀ j, base' g = some j → j ∈ agents)
    (hallowed : ∀ i ∈ agents, Allowed v i goods (hold goods base' i))
    (hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods base' i))
    (hsingle : ∀ i ∈ agents, ∀ g ∈ goods, value v i (hold goods base i) < v i g →
      ∃ j ∈ agents, hold goods base' j = [g])
    (hbig : ∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → 3 ≤ (hold goods base' j).length → ∀ h ∈ hold goods base' j,
      value v i ((hold goods base' j).erase h) ≤ value v i (hold goods base' i)) :
    Valid v agents goods base' := by
  have hv1 : ∀ i ∈ agents, ∀ g ∈ goods, value v i (hold goods base' i) < v i g →
      ∃ j ∈ agents, hold goods base' j = [g] :=
    fun i hi g hg hlt => hsingle i hi g hg (Nat.lt_of_le_of_lt (hval i hi) hlt)
  refine ⟨howners, hallowed, hv1, fun i hi j hj hij h hh => ?_⟩
  by_cases h3 : 3 ≤ (hold goods base' j).length
  · exact hbig i hi j hj hij h3 h hh
  · have hlen : ((hold goods base' j).erase h).length ≤ 1 := by
      rw [List.length_erase_of_mem hh]; omega
    match hE : (hold goods base' j).erase h, hlen with
    | [], _ => simp [value]
    | [q], _ =>
      rw [value_singleton]
      have hq : q ∈ hold goods base' j := List.mem_of_mem_erase (by rw [hE]; simp)
      have hq' := mem_hold.mp hq
      refine Nat.le_of_not_lt fun hlt => ?_
      obtain ⟨k, _, hk⟩ := hv1 i hi q hq'.1 hlt
      have hqk : base' q = some k := (mem_hold.mp (by rw [hk]; simp)).2
      rw [hq'.2] at hqk
      have hkj : j = k := Option.some.inj hqk
      subst hkj
      rw [hk] at hh hE
      simp only [List.mem_singleton] at hh
      subst hh
      simp at hE

end trades

/-! ## Lemma 4′ and Corollary 5(b) -/

section moves
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- The state after `x` takes the goods that pass `p` (its own goods or leftover goods) and releases the rest of its
holding. -/
def retake (base : G → Option A) (x : A) (p : G → Bool) : G → Option A :=
  fun g => if p g = true then some x else if base g = some x then none else base g

omit [DecidableEq G] in
theorem hold_retake_self (base : G → Option A) (x : A) (p : G → Bool) :
    hold goods (retake base x p) x = goods.filter p := by
  unfold hold retake
  apply List.filter_congr
  intro g _
  by_cases hp : p g = true
  · simp [hp]
  · by_cases hb : base g = some x
    · simp [hp, hb]
    · simp [hp, hb]

omit [DecidableEq G] in
theorem hold_retake_other {base : G → Option A} {x : A} {p : G → Bool}
    (hp : ∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) {j : A} (hj : j ≠ x) :
    hold goods (retake base x p) j = hold goods base j := by
  unfold hold retake
  apply List.filter_congr
  intro g hg
  by_cases hpg : p g = true
  · have hne : base g ≠ some j := by
      rcases hp g hg hpg with h | h <;> rw [h] <;> simp [Ne.symm hj]
    simp [hpg, hne, Ne.symm hj]
  · by_cases hb : base g = some x
    · simp [hpg, hb, Ne.symm hj]
    · simp [hpg, hb]

omit [DecidableEq G] in
theorem mem_goods_of_mem_hold {base : G → Option A} {i : A} {g : G} (h : g ∈ hold goods base i) : g ∈ goods :=
  (mem_hold.mp h).1

/-- **Lemma 4′** (free self-upgrades): a free agent `x` (no listed agent wants a good of its holding) with an allowed
holding of at most two goods, made of its own goods and leftover goods and worth more than its holding, gives a better
valid state: `x` takes it and releases the rest. -/
theorem exists_better_of_selfUpgrade {base : G → Option A} (hb : Valid v agents goods base)
    {x : A} (hx : x ∈ agents)
    (hfree : ∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y)
    (p : G → Bool) (hp : ∀ g ∈ goods, p g = true → base g = some x ∨ base g = none)
    (hN : Allowed v x goods (goods.filter p)) (hN2 : (goods.filter p).length ≤ 2)
    (hgain : value v x (hold goods base x) < value v x (goods.filter p)) :
    ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base := by
  have hself := hold_retake_self (goods := goods) base x p
  have hother : ∀ j, j ≠ x → hold goods (retake base x p) j = hold goods base j :=
    fun j hj => hold_retake_other hp hj
  have hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods (retake base x p) i) := by
    intro i _
    by_cases hix : i = x
    · subst hix; rw [hself]; exact Nat.le_of_lt hgain
    · rw [hother i hix]; exact Nat.le_refl _
  refine ⟨retake base x p, valid_of_gain v agents goods (base := base) ?_ ?_ hval ?_ ?_, ?_⟩
  · intro g hg j hj
    unfold retake at hj
    by_cases hpg : p g = true
    · simp only [hpg, ite_true, Option.some.injEq] at hj; subst hj; exact hx
    · by_cases hbx : base g = some x
      · simp [hpg, hbx] at hj
      · simp only [hpg, hbx, ite_false, Bool.false_eq_true] at hj
        exact hb.owners g hg j hj
  · intro i hi
    by_cases hix : i = x
    · subst hix; rw [hself]; exact hN
    · rw [hother i hix]; exact hb.allowed i hi
  · intro i hi g hg hlt
    obtain ⟨j, hj, hjg⟩ := hb.v1 i hi g hg hlt
    have hjx : j ≠ x := by
      rintro rfl
      exact hfree g (by rw [hjg]; simp) i hi hlt
    exact ⟨j, hj, by rw [hother j hjx]; exact hjg⟩
  · intro i hi j hj hij h3 h hh
    have hjx : j ≠ x := by
      rintro rfl
      rw [hself] at h3
      omega
    rw [hother j hjx] at h3 hh ⊢
    exact Nat.le_trans (hb.v2 i hi j hj hij h hh) (hval i hi)
  · refine better_of_monotone v agents goods ?_ hval ⟨x, hx, by rw [hself]; exact hgain⟩
    intro i hi
    by_cases hix : i = x
    · subst hix
      rw [hself]
      exact level_mono v i goods (hb.allowed i hi) hN (fun g hg => mem_goods_of_mem_hold hg)
        (fun g hg => (List.mem_filter.mp hg).1) hgain
    · rw [hother i hix]; exact Nat.le_refl _

/-- **Corollary 5(b)**: if the leftover goods alone threaten nobody (`v_i(J) ≤ v_i(Y_i)` for every listed agent) and
some listed agent holds nothing, the state is completable: that agent takes every leftover good. -/
theorem completable_of_empty {base : G → Option A} (hb : Valid v agents goods base) {o : A} (ho : o ∈ agents)
    (hempty : hold goods base o = [])
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) :
    Completable v agents goods base := by
  let X : G → A := fun g => (base g).getD o
  have hXo : bundle goods X o = leftover goods base := by
    unfold bundle leftover
    apply List.filter_congr
    intro g hg
    cases hbg : base g with
    | none => simp [X, hbg]
    | some k =>
      have hk : k ≠ o := by
        rintro rfl
        have : g ∈ hold goods base k := mem_hold.mpr ⟨hg, hbg⟩
        rw [hempty] at this
        simp at this
      simp [X, hbg, hk]
  have hXj : ∀ j, j ≠ o → bundle goods X j = hold goods base j := by
    intro j hj
    unfold bundle hold
    apply List.filter_congr
    intro g _
    cases hbg : base g with
    | none => simp [X, hbg, Ne.symm hj]
    | some k => simp [X, hbg]
  have hlow : ∀ i, value v i (hold goods base i) ≤ value v i (bundle goods X i) := by
    intro i
    by_cases hio : i = o
    · subst hio; rw [hempty]; simp [value]
    · rw [hXj i hio]; exact Nat.le_refl _
  refine ⟨X, fun g hg => ?_, fun g _ j hj => by simp [X, hj], ?_⟩
  · cases hbg : base g with
    | none => simp [X, hbg, ho]
    | some k => simpa [X, hbg] using hb.owners g hg k hbg
  · intro i hi j hj hij g hg
    by_cases hjo : j = o
    · subst hjo
      rw [hXo] at hg ⊢
      have hio : i ≠ j := hij
      calc value v i ((leftover goods base).erase g) ≤ value v i (leftover goods base) :=
            value_sublist v i (List.erase_sublist)
        _ ≤ value v i (hold goods base i) := hJ i hi
        _ ≤ value v i (bundle goods X i) := hlow i
    · rw [hXj j hjo] at hg ⊢
      exact Nat.le_trans (hb.v2 i hi j hj hij g hg) (hlow i)

end moves

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.le_topV
#print axioms EFX.DE4.exists_topV
#print axioms EFX.DE4.value_singleton
#print axioms EFX.DE4.level_single
#print axioms EFX.DE4.level_multi
#print axioms EFX.DE4.count_better_le
#print axioms EFX.DE4.level_single_le_four
#print axioms EFX.DE4.three_le_level_multi
#print axioms EFX.DE4.level_mono
#print axioms EFX.DE4.better_of_monotone
#print axioms EFX.DE4.valid_of_gain
#print axioms EFX.DE4.hold_retake_self
#print axioms EFX.DE4.hold_retake_other
#print axioms EFX.DE4.mem_goods_of_mem_hold
#print axioms EFX.DE4.exists_better_of_selfUpgrade
#print axioms EFX.DE4.completable_of_empty
