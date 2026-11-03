import EFX.DE4Upgrade

/-!
# DE4: the ring step where every free agent holds one good (`k4/de4.md` §7, Lemmas 7, 8, Theorem 9, Corollary 10;
ledger K4.DE4.LEAN)

**Definitions.**
- `IsDanger v goods base i D` (**danger set**): goods of `goods` outside `i`'s holding, each worth at most the
  holding to `i`, worth more than the holding together, and at most the holding after removing any one good.
- `rotateL` (**the trade along a cycle with labels**): every giver `c` (with `σ c = some w`) hands its holding and
  the leftover goods labelled `c` to `w`.

**Results.**
- `danger_of_threat` (**Lemma 7(a)**, the direction used): a bundle of goods outside `i`'s holding, each worth at most
  the holding, that threatens `i` (removing some good leaves more than the holding) strictly contains a danger set of
  `i`.
- `rotateL_valid_better` (**Theorem 9's trade**): trading along a cycle where each agent takes its predecessor's
  holding and its label, an allowed holding worth more, with the single goods of frozen givers passed alone and new
  holdings of three or more goods threatening nobody, gives a valid, better state.
- `lemma8` (**Lemma 8**): under (H) (valid, not completable, the leftover goods alone threatening nobody), the
  non-frozen agents holding one good `o` (any duplicate-free list of them) have *arcs*: agents `x o ≠ o` with danger
  sets made of goods of `o`'s holding (at least one) and leftover goods, threatening nobody but `o` (*tight*), whose
  leftover goods (the *labels*) are pairwise disjoint. Each step (`exists_arc_avoiding`) uses non-completability: if
  no arc avoided the labels already chosen, giving `o` the other leftover goods would complete the state.

**Faithfulness.** A danger set is a set of goods (`goods.filter d`); the order of goods plays no role. Lemma 8 is
stated for the free agents holding one good, as in `k4/de4.md` §7 (free agents holding two or three goods are the
case F₂ ≠ ∅, not covered here).
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Danger sets (Lemma 7) -/

section danger
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- A danger set of `i` (`k4/de4.md` Lemma 7). -/
def IsDanger (v : A → G → Nat) (goods : List G) (base : G → Option A) (i : A) (D : List G) : Prop :=
  D.Nodup ∧ (∀ g ∈ D, g ∈ goods ∧ base g ≠ some i ∧ v i g ≤ value v i (hold goods base i)) ∧
    value v i (hold goods base i) < value v i D ∧
    ∀ g ∈ D, value v i (D.erase g) ≤ value v i (hold goods base i)

/-- **Lemma 7(a)** (the direction used): a bundle of goods outside `i`'s holding, each worth at most the holding,
that threatens `i` contains a danger set of `i` that misses the good whose removal shows the threat. -/
theorem danger_of_threat (hgd : goods.Nodup) {base : G → Option A} {i : A} {B : List G} (hBnd : B.Nodup)
    (hB : ∀ g ∈ B, g ∈ goods ∧ base g ≠ some i ∧ v i g ≤ value v i (hold goods base i))
    {h : G} (_hh : h ∈ B) (hlt : value v i (hold goods base i) < value v i (B.erase h)) :
    ∃ d : G → Bool, IsDanger v goods base i (goods.filter d) ∧ ∀ g ∈ goods.filter d, g ∈ B ∧ g ≠ h := by
  let q₀ : G → Bool := fun g => decide (g ∈ B ∧ g ≠ h)
  have hmem : ∀ g, g ∈ goods.filter q₀ ↔ g ∈ B.erase h := by
    intro g
    rw [List.mem_filter, List.Nodup.mem_erase_iff hBnd]
    simp only [q₀, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hB', hne⟩; exact ⟨hne, hB'⟩
    · rintro ⟨hne, hB'⟩; exact ⟨(hB g hB').1, hB', hne⟩
  have hv : value v i (goods.filter q₀) = value v i (B.erase h) := by
    have h1 := value_le_of_subset v i (hgd.filter q₀) (hBnd.erase h) (fun g hg => (hmem g).mp hg)
    have h2 := value_le_of_subset v i (hBnd.erase h) (hgd.filter q₀) (fun g hg => (hmem g).mpr hg)
    omega
  obtain ⟨q', hq', hval, hmin⟩ :=
    shrink v i hgd (value v i (hold goods base i)) _ q₀ (Nat.le_refl _) (by rw [hv]; exact hlt)
  have hsub : ∀ g ∈ goods.filter q', g ∈ B ∧ g ≠ h := by
    intro g hg
    have := hq' g (List.mem_filter.mp hg).2
    simp only [q₀, decide_eq_true_eq] at this
    exact this
  exact ⟨q', ⟨hgd.filter q', fun g hg => hB g (hsub g hg).1, hval, hmin⟩, hsub⟩

end danger

/-! ## The trade along a cycle with labels (Theorem 9) -/

section rotL
variable {v : A → G → Nat} {agents : List A} {goods : List G}

open Classical in
/-- Every giver `c` (`σ c = some w`) hands its holding, and the leftover goods labelled `c` (`lab g = some c`), to
`w`; every other holding is unchanged. -/
noncomputable def rotateL (base : G → Option A) (σ : A → Option A) (lab : G → Option A) : G → Option A :=
  fun g => match lab g with
    | some c => σ c
    | none => match base g with
      | none => none
      | some j => match σ j with
        | some w => some w
        | none => some j

/-- What `w` takes from the giver `c`: its holding and its label. -/
def taken (goods : List G) (base : G → Option A) (lab : G → Option A) (c : A) : List G :=
  goods.filter (fun g => decide (base g = some c ∨ lab g = some c))

omit [DecidableEq A] [DecidableEq G] in
theorem rotateL_eq_some {base : G → Option A} {σ : A → Option A} {lab : G → Option A}
    (hlab : ∀ g c, lab g = some c → base g = none ∧ σ c ≠ none) {g : G} {i : A} :
    rotateL base σ lab g = some i ↔ (∃ c, (base g = some c ∨ lab g = some c) ∧ σ c = some i) ∨
      (lab g = none ∧ base g = some i ∧ σ i = none) := by
  unfold rotateL
  cases hl : lab g with
  | some c =>
    simp only
    have hbn := (hlab g c hl).1
    constructor
    · intro e; exact Or.inl ⟨c, Or.inr rfl, e⟩
    · rintro (⟨c', h1 | h1, e⟩ | ⟨h1, _, _⟩)
      · rw [hbn] at h1; exact absurd h1 (by simp)
      · have : c = c' := Option.some.inj h1; subst this; exact e
      · exact absurd h1 (by simp)
  | none =>
    simp only
    cases hb : base g with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro (⟨c, h1 | h1, _⟩ | ⟨_, h1, _⟩)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
    | some j =>
      simp only
      cases hs : σ j with
      | some w =>
        simp only
        constructor
        · intro e; exact Or.inl ⟨j, Or.inl rfl, by rw [hs]; exact e⟩
        · rintro (⟨c, h1 | h1, e⟩ | ⟨_, h1, h2⟩)
          · have : j = c := Option.some.inj h1; subst this; rw [hs] at e; exact e
          · exact absurd h1 (by simp)
          · have : j = i := Option.some.inj h1; subst this; rw [hs] at h2; exact absurd h2 (by simp)
      | none =>
        simp only
        constructor
        · intro e
          have hji : j = i := Option.some.inj e
          subst hji
          exact Or.inr ⟨trivial, rfl, hs⟩
        · rintro (⟨c, h1 | h1, e⟩ | ⟨_, h1, _⟩)
          · have : j = c := Option.some.inj h1; subst this; rw [hs] at e; exact absurd e (by simp)
          · exact absurd h1 (by simp)
          · exact h1

/-- **Theorem 9's trade.** Let `σ` be injective, with the agents that give exactly those that receive, and let the
labels be leftover goods of givers. Suppose every giver `c` with `σ c = some w` hands `w` an allowed holding worth more
to it (`taken`), frozen givers hand their single good alone (no label), and every new holding of three or more goods
threatens nobody. Then the rotated state is valid and better. -/
theorem rotateL_valid_better {base : G → Option A} (hb : Valid v agents goods base) {σ : A → Option A}
    {lab : G → Option A} (hlab : ∀ g c, lab g = some c → base g = none ∧ σ c ≠ none)
    (hgive : ∀ c w, σ c = some w → c ∈ agents ∧ w ∈ agents ∧ Allowed v w goods (taken goods base lab c) ∧
      value v w (hold goods base w) < value v w (taken goods base lab c))
    (hinj : ∀ c c' w, σ c = some w → σ c' = some w → c = c')
    (hcyc : ∀ w, (∃ c, σ c = some w) ↔ σ w ≠ none)
    (hfrozen : ∀ c, (∃ i ∈ agents, ∃ y, hold goods base c = [y] ∧ value v i (hold goods base i) < v i y) →
      ∀ g, lab g ≠ some c)
    (hbig : ∀ c w, σ c = some w → 3 ≤ (taken goods base lab c).length → ∀ i ∈ agents, i ≠ w →
      ∀ hh ∈ taken goods base lab c, value v i ((taken goods base lab c).erase hh) ≤
        value v i (hold goods (rotateL base σ lab) i))
    (hsome : ∃ c w, σ c = some w) :
    Valid v agents goods (rotateL base σ lab) ∧ Better v agents goods (rotateL base σ lab) base := by
  have hrecv : ∀ {c w}, σ c = some w → hold goods (rotateL base σ lab) w = taken goods base lab c := by
    intro c w hcw
    unfold hold taken
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    rw [rotateL_eq_some hlab]
    constructor
    · rintro (⟨c', h1, e⟩ | ⟨_, _, h2⟩)
      · rw [hinj c' c w e hcw] at h1; exact h1
      · exact absurd h2 ((hcyc w).mp ⟨c, hcw⟩)
    · intro h1; exact Or.inl ⟨c, h1, hcw⟩
  have hother : ∀ {i}, (¬ ∃ c, σ c = some i) → hold goods (rotateL base σ lab) i = hold goods base i := by
    intro i hir
    have hsi : σ i = none := Classical.byContradiction fun hn => hir ((hcyc i).mpr hn)
    unfold hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    rw [rotateL_eq_some hlab]
    constructor
    · rintro (⟨c, _, e⟩ | ⟨_, h1, _⟩)
      · exact absurd ⟨c, e⟩ hir
      · exact h1
    · intro h1
      cases hl : lab g with
      | none => exact Or.inr ⟨rfl, h1, hsi⟩
      | some c =>
        have := (hlab g c hl).1
        rw [h1] at this; exact absurd this (by simp)
  have hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods (rotateL base σ lab) i) := by
    intro i _
    by_cases hir : ∃ c, σ c = some i
    · obtain ⟨c, hc⟩ := hir
      rw [hrecv hc]; exact Nat.le_of_lt (hgive c i hc).2.2.2
    · rw [hother hir]; exact Nat.le_refl _
  have hvalid : Valid v agents goods (rotateL base σ lab) := by
    refine valid_of_gain v agents goods (base := base) ?_ ?_ hval ?_ ?_
    · intro g hg j hj
      rcases (rotateL_eq_some hlab).mp hj with ⟨c, _, e⟩ | ⟨_, h1, _⟩
      · exact (hgive c j e).2.1
      · exact hb.owners g hg _ h1
    · intro i hi
      by_cases hir : ∃ c, σ c = some i
      · obtain ⟨c, hc⟩ := hir
        rw [hrecv hc]; exact (hgive c i hc).2.2.1
      · rw [hother hir]; exact hb.allowed i hi
    · intro i hi g hg hlt
      obtain ⟨j, hj, hjg⟩ := hb.v1 i hi g hg hlt
      cases hs : σ j with
      | some w =>
        refine ⟨w, (hgive j w hs).2.1, ?_⟩
        rw [hrecv hs]
        have hnolab := hfrozen j ⟨i, hi, g, hjg, hlt⟩
        unfold taken
        rw [← hjg]
        unfold hold
        apply List.filter_congr
        intro g' _
        apply decide_eq_decide.mpr
        constructor
        · rintro (h1 | h1)
          · exact h1
          · exact absurd h1 (hnolab g')
        · exact Or.inl
      | none =>
        have hjr : ¬ ∃ c, σ c = some j := fun h => (hcyc j).mp h hs
        exact ⟨j, hj, by rw [hother hjr]; exact hjg⟩
    · intro i hi j hj hij h3 hh hhm
      by_cases hjr : ∃ c, σ c = some j
      · obtain ⟨c, hc⟩ := hjr
        rw [hrecv hc] at h3 hhm ⊢
        exact hbig c j hc h3 i hi hij hh hhm
      · rw [hother hjr] at hhm ⊢
        exact Nat.le_trans (hb.v2 i hi j hj hij hh hhm) (hval i hi)
  refine ⟨hvalid, better_of_monotone v agents goods ?_ hval ?_⟩
  · intro i hi
    by_cases hir : ∃ c, σ c = some i
    · obtain ⟨c, hc⟩ := hir
      rw [hrecv hc]
      exact level_mono v i goods (hb.allowed i hi) (hgive c i hc).2.2.1
        (fun g hg => mem_goods_of_mem_hold hg) (fun g hg => (List.mem_filter.mp hg).1) (hgive c i hc).2.2.2
    · rw [hother hir]; exact Nat.le_refl _
  · obtain ⟨c, w, hcw⟩ := hsome
    exact ⟨w, (hgive c w hcw).2.1, by rw [hrecv hcw]; exact (hgive c w hcw).2.2.2⟩

theorem rotateL_value_ge {base : G → Option A} {σ : A → Option A} {lab : G → Option A}
    (hlab : ∀ g c, lab g = some c → base g = none ∧ σ c ≠ none)
    (hgive : ∀ c w, σ c = some w → c ∈ agents ∧ w ∈ agents ∧ Allowed v w goods (taken goods base lab c) ∧
      value v w (hold goods base w) < value v w (taken goods base lab c))
    (hinj : ∀ c c' w, σ c = some w → σ c' = some w → c = c')
    (hcyc : ∀ w, (∃ c, σ c = some w) ↔ σ w ≠ none) :
    ∀ i, value v i (hold goods base i) ≤ value v i (hold goods (rotateL base σ lab) i) := by
  intro i
  by_cases hir : ∃ c, σ c = some i
  · obtain ⟨c, hc⟩ := hir
    have : hold goods (rotateL base σ lab) i = taken goods base lab c := by
      unfold hold taken
      apply List.filter_congr
      intro g _
      apply decide_eq_decide.mpr
      rw [rotateL_eq_some hlab]
      constructor
      · rintro (⟨c', h1, e⟩ | ⟨_, _, h2⟩)
        · rw [hinj c' c i e hc] at h1; exact h1
        · exact absurd h2 ((hcyc i).mp ⟨c, hc⟩)
      · intro h1; exact Or.inl ⟨c, h1, hc⟩
    rw [this]; exact Nat.le_of_lt (hgive c i hc).2.2.2
  · have hsi : σ i = none := Classical.byContradiction fun hn => hir ((hcyc i).mpr hn)
    have : hold goods (rotateL base σ lab) i = hold goods base i := by
      unfold hold
      apply List.filter_congr
      intro g _
      apply decide_eq_decide.mpr
      rw [rotateL_eq_some hlab]
      constructor
      · rintro (⟨c, _, e⟩ | ⟨_, h1, _⟩)
        · exact absurd ⟨c, e⟩ hir
        · exact h1
      · intro h1
        cases hl : lab g with
        | none => exact Or.inr ⟨rfl, h1, hsi⟩
        | some c =>
          have := (hlab g c hl).1
          rw [h1] at this; exact absurd this (by simp)
    rw [this]
    exact Nat.le_refl _

omit [DecidableEq G] in
theorem rotateL_hold_recv {base : G → Option A} {σ : A → Option A} {lab : G → Option A}
    (hlab : ∀ g c, lab g = some c → base g = none ∧ σ c ≠ none)
    (hinj : ∀ c c' w, σ c = some w → σ c' = some w → c = c')
    (hcyc : ∀ w, (∃ c, σ c = some w) ↔ σ w ≠ none) {c w : A} (hcw : σ c = some w) :
    hold goods (rotateL base σ lab) w = taken goods base lab c := by
  unfold hold taken
  apply List.filter_congr
  intro g _
  apply decide_eq_decide.mpr
  rw [rotateL_eq_some hlab]
  constructor
  · rintro (⟨c', h1, e⟩ | ⟨_, _, h2⟩)
    · rw [hinj c' c w e hcw] at h1; exact h1
    · exact absurd h2 ((hcyc w).mp ⟨c, hcw⟩)
  · intro h1; exact Or.inl ⟨c, h1, hcw⟩

end rotL

/-! ## Lemma 8: self-absorption of the free agents holding one good -/

section lemma8
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- An arc into the free agent `o`: an agent `x ≠ o` with a danger set made of goods of `o`'s holding and leftover
goods, meeting `o`'s holding. -/
def ArcInto (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o x : A)
    (d : G → Bool) : Prop :=
  x ∈ agents ∧ x ≠ o ∧ IsDanger v goods base x (goods.filter d) ∧
    (∀ g ∈ goods, d g = true → base g = some o ∨ base g = none) ∧ ∃ g ∈ goods, d g = true ∧ base g = some o

/-- The arc's set threatens nobody but `o` (as `o`'s bundle in a completion). -/
def Tight (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A) (d : G → Bool) :
    Prop :=
  ∀ i ∈ agents, i ≠ o → ∀ hh ∈ goods.filter d, value v i ((goods.filter d).erase hh) ≤ value v i (hold goods base i)

omit [DecidableEq A] [DecidableEq G] in
theorem exists_min_len {α : Type} (f : α → Nat) (P : α → Prop) :
    ∀ n, (∃ a, P a ∧ f a ≤ n) → ∃ a, P a ∧ ∀ b, P b → f a ≤ f b := by
  intro n
  induction n with
  | zero =>
    rintro ⟨a, ha, hle⟩
    exact ⟨a, ha, fun b _ => by omega⟩
  | succ n ih =>
    rintro ⟨a, ha, hle⟩
    by_cases h : ∃ a, P a ∧ f a ≤ n
    · exact ih h
    · refine ⟨a, ha, fun b hb => Nat.le_of_not_lt fun hlt => h ⟨b, hb, by omega⟩⟩

/-- A danger set of goods of `o`'s holding and leftover goods meets `o`'s holding (Lemma 7(c)), when the leftover
goods alone threaten nobody. -/
theorem meets_of_danger {base : G → Option A} (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤
      value v i (hold goods base i)) {i o : A} (hi : i ∈ agents) {d : G → Bool}
    (hdan : IsDanger v goods base i (goods.filter d)) (hsub : ∀ g ∈ goods, d g = true → base g = some o ∨ base g = none) :
    ∃ g ∈ goods, d g = true ∧ base g = some o := by
  refine Classical.byContradiction fun hn => ?_
  have hall : ∀ g ∈ goods, d g = true → decide (base g = none) = true := by
    intro g hg hdg
    rcases hsub g hg hdg with h | h
    · exact absurd ⟨g, hg, hdg, h⟩ hn
    · simp [h]
  have h1 : value v i (goods.filter d) ≤ value v i (leftover goods base) :=
    value_sublist v i (filter_sublist_filter hall)
  have := hdan.2.2.1
  have := hJ i hi
  omega

/-- The goods of a free agent's holding and the leftover goods are worth at most each listed agent's holding. -/
theorem unwanted_of_free {base : G → Option A} (hb : Valid v agents goods base) {o : A}
    (hof : ¬ Frozen v agents goods base o) {i : A} (hi : i ∈ agents) {g : G} (hg : g ∈ goods)
    (hbg : base g = some o ∨ base g = none) : v i g ≤ value v i (hold goods base i) := by
  rcases hbg with h | h
  · exact Nat.le_of_not_lt (free_of_not_frozen hb hof g (mem_hold.mpr ⟨hg, h⟩) i hi)
  · exact leftover_le hb hi hg h

/-- A shortest arc into `o` among those avoiding a set of goods is tight. -/
theorem tight_of_min {base : G → Option A} (hb : Valid v agents goods base) (hgd : goods.Nodup)
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) {o : A}
    (hof : ¬ Frozen v agents goods base o) (avoid : G → Prop) {x₀ : A} {d₀ : G → Bool}
    (harc : ArcInto v agents goods base o x₀ d₀) (hav : ∀ g ∈ goods, d₀ g = true → base g = none → avoid g)
    (hmin : ∀ x₁ d₁, ArcInto v agents goods base o x₁ d₁ → (∀ g ∈ goods, d₁ g = true → base g = none → avoid g) →
      (goods.filter d₀).length ≤ (goods.filter d₁).length) :
    Tight v agents goods base o d₀ := by
  intro i hi hio hh hhm
  refine Nat.le_of_not_lt fun hlt => ?_
  have hB : ∀ g ∈ goods.filter d₀, g ∈ goods ∧ base g ≠ some i ∧ v i g ≤ value v i (hold goods base i) := by
    intro g hg
    have hgg := (List.mem_filter.mp hg).1
    have hdg := (List.mem_filter.mp hg).2
    have hbo := harc.2.2.2.1 g hgg hdg
    refine ⟨hgg, fun e => ?_, unwanted_of_free hb hof hi hgg hbo⟩
    rcases hbo with h | h <;> rw [h] at e <;> simp at e <;> exact hio e.symm
  obtain ⟨d₁, hdan, hsub⟩ := danger_of_threat hgd (hgd.filter d₀) hB hhm hlt
  have hsub1 : ∀ g ∈ goods, d₁ g = true → base g = some o ∨ base g = none := by
    intro g hg hdg
    have := (hsub g (List.mem_filter.mpr ⟨hg, hdg⟩)).1
    exact harc.2.2.2.1 g hg (List.mem_filter.mp this).2
  have harc1 : ArcInto v agents goods base o i d₁ :=
    ⟨hi, hio, hdan, hsub1, meets_of_danger hJ hi hdan hsub1⟩
  have hav1 : ∀ g ∈ goods, d₁ g = true → base g = none → avoid g := by
    intro g hg hdg hn
    have := (hsub g (List.mem_filter.mpr ⟨hg, hdg⟩)).1
    exact hav g hg (List.mem_filter.mp this).2 hn
  have hle := hmin i d₁ harc1 hav1
  have hlen : (goods.filter d₁).length ≤ ((goods.filter d₀).erase hh).length :=
    List.Nodup.length_le_of_subset (hgd.filter d₁) (fun g hg => by
      have h1 := hsub g hg
      exact (List.Nodup.mem_erase_iff (hgd.filter d₀)).mpr ⟨h1.2, h1.1⟩)
  rw [List.length_erase_of_mem hhm] at hlen
  have : 0 < (goods.filter d₀).length := List.length_pos_of_mem hhm
  omega

/-- **Lemma 8, one step.** If the agents of `rest` have tight arcs with pairwise disjoint labels, then a free agent
`o` outside `rest` has an arc whose label avoids them: otherwise the completion in which every agent of `rest` takes
its label and `o` takes the other leftover goods would be EFX₀. -/
theorem exists_arc_avoiding {base : G → Option A} (hb : Valid v agents goods base) (hgd : goods.Nodup)
    (hnc : ¬ Completable v agents goods base)
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i))
    {rest : List A} (hrest1 : ∀ r ∈ rest, ∃ y, hold goods base r = [y])
    (x' : A → A) (d' : A → G → Bool) (harcs : ∀ r ∈ rest, ArcInto v agents goods base r (x' r) (d' r) ∧
      Tight v agents goods base r (d' r))
    (hdisj : ∀ r ∈ rest, ∀ r' ∈ rest, r ≠ r' → ∀ g ∈ goods, base g = none → d' r g = true → d' r' g = false)
    {o : A} (ho : o ∈ agents) (hof : ¬ Frozen v agents goods base o) (hor : o ∉ rest) :
    ∃ x₀ d₀, ArcInto v agents goods base o x₀ d₀ ∧
      ∀ g ∈ goods, d₀ g = true → base g = none → ∀ r ∈ rest, d' r g = false := by
  refine Classical.byContradiction fun hno => hnc ?_
  let X : G → A := fun g => match base g with
    | some j => j
    | none => match rest.find? (fun r => d' r g) with
      | some r => r
      | none => o
  -- the agent X gives a leftover good to
  have hXn : ∀ {g}, g ∈ goods → base g = none →
      (∃ r ∈ rest, d' r g = true ∧ X g = r) ∨ ((∀ r ∈ rest, d' r g = false) ∧ X g = o) := by
    intro g _ h
    cases hf : rest.find? (fun r => d' r g) with
    | some r =>
      refine Or.inl ⟨r, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, by simp [X, h, hf]⟩
    | none =>
      refine Or.inr ⟨fun r hr => ?_, by simp [X, h, hf]⟩
      have := List.find?_eq_none.mp hf r hr
      simpa using this
  have hbr : ∀ r ∈ rest, bundle goods X r = goods.filter (d' r) := by
    intro r hr
    unfold bundle
    apply List.filter_congr
    intro g hg
    obtain ⟨y, hy⟩ := hrest1 r hr
    have harc := (harcs r hr).1
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    cases hbg : base g with
    | some j =>
      have hXg : X g = j := by simp [X, hbg]
      rw [hXg]
      constructor
      · rintro rfl
        obtain ⟨g₀, hg₀, hd₀, hb₀⟩ := harc.2.2.2.2
        have h1 : g₀ ∈ hold goods base j := mem_hold.mpr ⟨hg₀, hb₀⟩
        have h2 : g ∈ hold goods base j := mem_hold.mpr ⟨hg, hbg⟩
        rw [hy] at h1 h2
        simp at h1 h2
        rw [h2, ← h1]; exact hd₀
      · intro hd
        rcases harc.2.2.2.1 g hg hd with h | h
        · rw [hbg] at h; exact Option.some.inj h
        · rw [hbg] at h; exact absurd h (by simp)
    | none =>
      constructor
      · intro hX
        rcases hXn hg hbg with ⟨r', hr', hd, e⟩ | ⟨_, e⟩
        · rw [e] at hX; subst hX; exact hd
        · rw [e] at hX; subst hX; exact absurd hr hor
      · intro hd
        rcases hXn hg hbg with ⟨r', hr', hd', e⟩ | ⟨hall, _⟩
        · by_cases hrr : r' = r
          · rw [e, hrr]
          · exact absurd (hdisj r' hr' r hr hrr g hg hbg hd') (by simp [hd])
        · exact absurd (hall r hr) (by simp [hd])
  have hbo : ∀ g ∈ bundle goods X o, (base g = some o ∨ base g = none) ∧
      (base g = none → ∀ r ∈ rest, d' r g = false) := by
    intro g hg
    have hgg := (List.mem_filter.mp hg).1
    have hXo : X g = o := by simpa using (List.mem_filter.mp hg).2
    cases hbg : base g with
    | some j =>
      have : X g = j := by simp [X, hbg]
      rw [hXo] at this; subst this
      exact ⟨Or.inl rfl, fun h => absurd h (by simp)⟩
    | none =>
      refine ⟨Or.inr rfl, fun _ => ?_⟩
      rcases hXn hgg hbg with ⟨r', hr', _, e⟩ | ⟨hall, _⟩
      · rw [hXo] at e; subst e; exact absurd hr' hor
      · exact hall
  have hbj : ∀ j, j ∉ rest → j ≠ o → bundle goods X j = hold goods base j := by
    intro j hjr hjo
    unfold bundle hold
    apply List.filter_congr
    intro g hg
    apply decide_eq_decide.mpr
    cases hbg : base g with
    | some k =>
      have : X g = k := by simp [X, hbg]
      rw [this]
      exact ⟨fun e => by rw [e], fun e => Option.some.inj e⟩
    | none =>
      constructor
      · intro hX
        rcases hXn hg hbg with ⟨r', hr', _, e⟩ | ⟨_, e⟩
        · rw [e] at hX; subst hX; exact absurd hr' hjr
        · rw [e] at hX; exact absurd hX.symm hjo
      · intro h; exact absurd h (by simp)
  have hlow : ∀ i, value v i (hold goods base i) ≤ value v i (bundle goods X i) := by
    intro i
    apply value_sublist v i
    apply filter_sublist_filter
    intro g _ h
    have hb' : base g = some i := by simpa using h
    simp [X, hb']
  refine ⟨X, fun g hg => ?_, fun g _ j hj => by simp [X, hj], ?_⟩
  · cases hbg : base g with
    | some j => simpa [X, hbg] using hb.owners g hg j hbg
    | none =>
      rcases hXn hg hbg with ⟨r', hr', _, e⟩ | ⟨_, e⟩
      · rw [e]; exact (harcs r' hr').1.1 |> fun _ => (by
          obtain ⟨y, hy⟩ := hrest1 r' hr'
          have : y ∈ hold goods base r' := by rw [hy]; simp
          exact hb.owners y (mem_hold.mp this).1 r' (mem_hold.mp this).2)
      · rw [e]; exact ho
  · intro i hi j hj hij g hg
    by_cases hjr : j ∈ rest
    · rw [hbr j hjr] at hg ⊢
      exact Nat.le_trans ((harcs j hjr).2 i hi hij g hg) (hlow i)
    · by_cases hjo : j = o
      · subst hjo
        refine Nat.le_of_not_lt fun hlt => hno ?_
        have hlt' : value v i (hold goods base i) < value v i ((bundle goods X j).erase g) :=
          Nat.lt_of_le_of_lt (hlow i) hlt
        have hB : ∀ g' ∈ bundle goods X j, g' ∈ goods ∧ base g' ≠ some i ∧
            v i g' ≤ value v i (hold goods base i) := by
          intro g' hg'
          have hgg := (List.mem_filter.mp hg').1
          have h1 := (hbo g' hg').1
          refine ⟨hgg, fun e => ?_, unwanted_of_free hb hof hi hgg h1⟩
          rcases h1 with h | h <;> rw [h] at e <;> simp at e
          exact hij e.symm
        obtain ⟨d₀, hdan, hsub⟩ := danger_of_threat hgd (hgd.filter _) hB hg hlt'
        have hsub1 : ∀ g' ∈ goods, d₀ g' = true → base g' = some j ∨ base g' = none := by
          intro g' hg' hd
          exact (hbo g' (hsub g' (List.mem_filter.mpr ⟨hg', hd⟩)).1).1
        refine ⟨i, d₀, ⟨hi, hij, hdan, hsub1, meets_of_danger hJ hi hdan hsub1⟩, ?_⟩
        intro g' hg' hd hn
        exact (hbo g' (hsub g' (List.mem_filter.mpr ⟨hg', hd⟩)).1).2 hn
      · rw [hbj j hjr hjo] at hg ⊢
        exact Nat.le_trans (hb.v2 i hi j hj hij g hg) (hlow i)

/-- **Lemma 8.** Under (H) (valid, not completable, the leftover goods alone threatening nobody), the free agents
holding one good can be given tight arcs with pairwise disjoint labels. -/
theorem lemma8 {base : G → Option A} (hb : Valid v agents goods base) (hgd : goods.Nodup)
    (hnc : ¬ Completable v agents goods base)
    (hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) :
    ∀ os : List A, os.Nodup →
      (∀ o ∈ os, o ∈ agents ∧ ¬ Frozen v agents goods base o ∧ ∃ y, hold goods base o = [y]) →
      ∃ (x : A → A) (d : A → G → Bool),
        (∀ o ∈ os, ArcInto v agents goods base o (x o) (d o) ∧ Tight v agents goods base o (d o)) ∧
        ∀ o ∈ os, ∀ o' ∈ os, o ≠ o' → ∀ g ∈ goods, base g = none → d o g = true → d o' g = false
  | [], _, _ => ⟨id, fun _ _ => false, by simp, by simp⟩
  | o :: rest, hnd, hos => by
    obtain ⟨x', d', harcs, hdisj⟩ := lemma8 hb hgd hnc hJ rest (List.nodup_cons.mp hnd).2
      (fun r hr => hos r (List.mem_cons_of_mem _ hr))
    have ho := hos o List.mem_cons_self
    have hor : o ∉ rest := (List.nodup_cons.mp hnd).1
    obtain ⟨x₀, d₀, harc, hav⟩ := exists_arc_avoiding hb hgd hnc hJ
      (fun r hr => (hos r (List.mem_cons_of_mem _ hr)).2.2) x' d' harcs hdisj ho.1 ho.2.1 hor
    let P : A × (G → Bool) → Prop := fun p => ArcInto v agents goods base o p.1 p.2 ∧
      ∀ g ∈ goods, p.2 g = true → base g = none → ∀ r ∈ rest, d' r g = false
    obtain ⟨⟨x₁, d₁⟩, hP, hmin⟩ := exists_min_len (fun p : A × (G → Bool) => (goods.filter p.2).length) P _
      ⟨(x₀, d₀), ⟨harc, hav⟩, Nat.le_refl _⟩
    have htight : Tight v agents goods base o d₁ :=
      tight_of_min hb hgd hJ ho.2.1 (fun g => ∀ r ∈ rest, d' r g = false) hP.1 hP.2
        (fun x₂ d₂ h2 hav2 => hmin (x₂, d₂) ⟨h2, hav2⟩)
    refine ⟨fun a => if a = o then x₁ else x' a, fun a => if a = o then d₁ else d' a, ?_, ?_⟩
    · intro a ha
      by_cases hao : a = o
      · subst hao; simp only [↓reduceIte]; exact ⟨hP.1, htight⟩
      · have ha' : a ∈ rest := by
          rcases List.mem_cons.mp ha with e | h
          · exact absurd e hao
          · exact h
        simp only [hao, ↓reduceIte]
        exact harcs a ha'
    · intro a ha a' ha' haa g hg hn hd
      by_cases hao : a = o
      · subst hao
        have ha'r : a' ∈ rest := by
          rcases List.mem_cons.mp ha' with e | h
          · exact absurd e.symm haa
          · exact h
        have ha'o : a' ≠ a := fun e => haa e.symm
        simp only [↓reduceIte] at hd
        simp only [ha'o, ↓reduceIte]
        exact hP.2 g hg hd hn a' ha'r
      · have har : a ∈ rest := by
          rcases List.mem_cons.mp ha with e | h
          · exact absurd e hao
          · exact h
        simp only [hao, ↓reduceIte] at hd
        by_cases ha'o : a' = o
        · subst ha'o
          simp only [↓reduceIte]
          cases h1 : d₁ g with
          | false => rfl
          | true => exact absurd (hP.2 g hg h1 hn a har) (by simp [hd])
        · simp only [ha'o, ↓reduceIte]
          have ha'r : a' ∈ rest := by
            rcases List.mem_cons.mp ha' with e | h
            · exact absurd e ha'o
            · exact h
          exact hdisj a har a' ha'r haa g hg hn hd

end lemma8

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.danger_of_threat
#print axioms EFX.DE4.rotateL_eq_some
#print axioms EFX.DE4.rotateL_valid_better
#print axioms EFX.DE4.rotateL_value_ge
#print axioms EFX.DE4.rotateL_hold_recv
#print axioms EFX.DE4.exists_min_len
#print axioms EFX.DE4.meets_of_danger
#print axioms EFX.DE4.unwanted_of_free
#print axioms EFX.DE4.tight_of_min
#print axioms EFX.DE4.exists_arc_avoiding
#print axioms EFX.DE4.lemma8
