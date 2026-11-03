import EFX.DE4Moves

/-!
# DE4: the upgrade lemma and the frame Conjecture 11″ ⟹ TARGET₄ (`k4/de4.md` Lemma 4, §7.7; ledger K4.DE4.LEAN)

**Lemma 4** (`exists_better_of_threat`). In a valid state of a strict R1-core, if the leftover goods are worth more
to some listed agent `x` than its holding, there is a better valid state.

**Structure of the proof** (as in `k4/de4.md` §3).
- `shrink`: a minimal set of leftover goods worth more than the holding (removing any one good leaves at most the
  holding's value).
- `exists_upgrade` (step (i)): that minimal set is an allowed holding of `x`: an upper set, or the lower pair when
  `x` holds a good below its top. It has at most two goods unless `x` holds its top alone and the set has three goods.
  The cases are by the holding of `x` (nothing; one good, the top or not; an upper set; the lower pair), with the
  counting `|R_x| ≤ 4` and strictness.
- `trade`, `TradeOK`, `trade_valid_better` (step (ii)): trading along a map `r` that sends givers of single goods to
  agents wanting them is valid and better, if `r` is injective, every giver is a receiver or the upgrading `x`, and
  every receiver that gives nothing is free.
- `exists_walk`: from a frozen agent, wanters lead to a free agent along a simple path (`tradeOK_path`, the chain), or
  close a cycle (`tradeOK_cycle`, a want-ring).
- `exists_better_small`: Lemma 4 for an upgrade of at most two goods (Lemma 4′ if `x` is free, the walk if frozen).
- The three-good case (step (iii)): a free `x` takes its top with one good of the triple (an upper pair). For a frozen
  `x`, if the triple threatens some agent `i` after the trade, then the leftover goods threaten `i` too, and `i`'s own
  minimal upgrade has at most two goods (if it had three, the goods `i` values in `x`'s triple would lie in it, so
  they would be worth at most `i`'s top); so `exists_better_small` applies to `i`.

**Rotations** (`rotate_valid_better`, Lemma 14 in general form): if the agents of a rotation each take their
predecessor's whole holding, an allowed holding worth more to them, the rotated state is valid and better. Want-rings
and the label-free cycles of Lemma 14 are rotations (for a closed arc, the taken holding is a danger set of the taker,
an allowed holding by Lemma 7(b) of the paper, which is not formalized here: `TakesAll` asks for allowedness).

**The frame.** `ConjDE4H` (Conjecture 11″ in its weakest form: every non-completable valid state satisfying (H) has
a better valid state) ⟹ `ConjDE4Imp` (`conjDE4Imp_of_H`, using Lemma 4, Lemma 4′ and Corollary 5(b)) ⟹ `ConjDE4`
⟹ TARGET₄ (`target4_of_conjDE4H`). `ConjDE4H` is a hypothesis, never an axiom; it is open.

**Faithfulness.** (H) is stated as in `k4/de4.md` §7: every listed agent holds a good; the leftover goods alone are
worth at most each listed agent's holding (Corollary 5(a), i.e. Lemma 4 does not apply); no free listed agent has an
allowed holding of at most two goods from its own and the leftover goods worth more than its holding (Lemma 4′ does
not apply). "Better" is the order of §1, as in the paper's Conjecture 11″. Its strong form, which asks moreover that
no level drop, is false (V11 of `attempts/k4-de4-variants.md`).
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Lists -/

section lists
variable (v : A → G → Nat) (i : A)

omit [DecidableEq A] in
theorem value_cons_erase {l : List G} {g : G} (h : g ∈ l) : value v i l = v i g + value v i (l.erase g) := by
  have hp := List.perm_cons_erase h
  unfold value
  rw [(hp.map (v i)).sum_nat]
  simp

omit [DecidableEq A] in
theorem value_le_of_subset : ∀ {T L : List G}, T.Nodup → L.Nodup → (∀ g ∈ T, g ∈ L) →
    value v i T ≤ value v i L
  | [], _, _, _, _ => by simp [value]
  | a :: t, L, hT, hL, hsub => by
    have ha : a ∈ L := hsub a (by simp)
    have hta : ∀ g ∈ t, g ∈ L.erase a := by
      intro g hg
      have hne : g ≠ a := fun e => (List.nodup_cons.mp hT).1 (e ▸ hg)
      exact (List.mem_erase_of_ne hne).mpr (hsub g (List.mem_cons_of_mem _ hg))
    have := value_le_of_subset (List.nodup_cons.mp hT).2 (hL.erase a) hta
    rw [value_cons, value_cons_erase v i ha]
    omega

omit [DecidableEq A] in
theorem filter_erase_eq {goods : List G} (hgd : goods.Nodup) (q : G → Bool) (g : G) :
    (goods.filter q).erase g = goods.filter (fun g' => q g' && g' != g) := by
  rw [List.Nodup.erase_eq_filter (hgd.filter q) g, List.filter_filter]
  apply List.filter_congr
  intro a _
  simp [Bool.and_comm]

omit [DecidableEq A] in
/-- A minimal set worth more than `V`: removing any one good leaves at most `V`. -/
theorem shrink {goods : List G} (hgd : goods.Nodup) (V : Nat) :
    ∀ (k : Nat) (q : G → Bool), (goods.filter q).length ≤ k → V < value v i (goods.filter q) →
      ∃ q' : G → Bool, (∀ g, q' g = true → q g = true) ∧ V < value v i (goods.filter q') ∧
        ∀ g ∈ goods.filter q', value v i ((goods.filter q').erase g) ≤ V := by
  intro k
  induction k with
  | zero =>
    intro q hk hV
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hk)] at hV
    simp [value] at hV
  | succ k ih =>
    intro q hk hV
    by_cases hmin : ∀ g ∈ goods.filter q, value v i ((goods.filter q).erase g) ≤ V
    · exact ⟨q, fun _ h => h, hV, hmin⟩
    · obtain ⟨g, hg⟩ := Classical.not_forall.mp hmin
      have hgm : g ∈ goods.filter q := Classical.byContradiction fun hn => hg fun h => absurd h hn
      have hlt : V < value v i ((goods.filter q).erase g) :=
        Nat.lt_of_not_le fun hle => hg fun _ => hle
      have hlen : (goods.filter (fun g' => q g' && g' != g)).length ≤ k := by
        rw [← filter_erase_eq hgd, List.length_erase_of_mem hgm]
        omega
      obtain ⟨q', hq', h1, h2⟩ := ih _ hlen (by rw [← filter_erase_eq hgd]; exact hlt)
      refine ⟨q', fun g' h => ?_, h1, h2⟩
      have := hq' g' h
      simp only [Bool.and_eq_true] at this
      exact this.1

end lists

/-! ## Step (i): the upgrade -/

section upgrade
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem length_append_le {l₁ l₂ r : List G} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hdis : ∀ g ∈ l₁, g ∉ l₂)
    (hsub : ∀ g ∈ l₁ ++ l₂, g ∈ r) : l₁.length + l₂.length ≤ r.length := by
  have hnd : (l₁ ++ l₂).Nodup :=
    List.nodup_append.mpr ⟨h₁, h₂, fun a ha b hb e => hdis a ha (e ▸ hb)⟩
  have := List.Nodup.length_le_of_subset hnd (fun g hg => hsub g hg)
  simpa using this

omit [DecidableEq A] [DecidableEq G] in
theorem subset_of_length_le {l₁ l₂ : List G} (h₁ : l₁.Nodup) (hsub : ∀ g ∈ l₁, g ∈ l₂)
    (hlen : l₂.length ≤ l₁.length) : ∀ g ∈ l₂, g ∈ l₁ := by
  intro g hg
  refine Classical.byContradiction fun hn => ?_
  have hnd : (g :: l₁).Nodup := List.nodup_cons.mpr ⟨hn, h₁⟩
  have := List.Nodup.length_le_of_subset hnd (fun a ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hg
    · exact hsub a ha)
  simp at this
  omega

omit [DecidableEq A] [DecidableEq G] in
theorem value_le_of_length_le_one' (i : A) {S : List G} (hS : S.length ≤ 1) {c : Nat}
    (h : ∀ g ∈ S, v i g ≤ c) : value v i S ≤ c := by
  match S, hS with
  | [], _ => simp [value]
  | [g], _ => simpa [value] using h g (by simp)

omit [DecidableEq G] in
theorem nodup_hold (hgd : goods.Nodup) (base : G → Option A) (i : A) : (hold goods base i).Nodup :=
  hgd.filter _

/-- A leftover good is worth at most an agent's holding: otherwise the agent would want it, and (V1) makes a wanted
good a one-good holding. -/
theorem leftover_le {base : G → Option A} (hb : Valid v agents goods base) {x : A} (hx : x ∈ agents) {g : G}
    (hg : g ∈ goods) (hn : base g = none) : v x g ≤ value v x (hold goods base x) := by
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨j, _, hj⟩ := hb.v1 x hx g hg hlt
  have hm : g ∈ hold goods base j := by rw [hj]; simp
  rw [(mem_hold.mp hm).2] at hn
  exact absurd hn (by simp)

omit [DecidableEq A] [DecidableEq G] in
theorem strict_ne (hs : Strict v agents goods) {i : A} (hi : i ∈ agents) {g g' : G} (hg : g ∈ goods)
    (hg' : g' ∈ goods) (hne : g ≠ g') (hpos : 0 < v i g) : v i g ≠ v i g' := by
  intro heq
  have := hs i hi [g] [g'] (List.singleton_sublist.mpr hg) (List.singleton_sublist.mpr hg')
    (by simp [hne]) (by simp [value, heq])
  simp [value] at this
  omega

omit [DecidableEq A] [DecidableEq G] in
theorem topV_pos (hc : R1Core4 v agents goods) {i : A} (hi : i ∈ agents) : 0 < topV v i goods := by
  have h3 := (hc i hi).1
  match hr : relevant v i goods, h3 with
  | g :: _, _ =>
    have hg : g ∈ relevant v i goods := by rw [hr]; simp
    simp only [relevant, List.mem_filter, decide_eq_true_eq] at hg
    exact Nat.lt_of_lt_of_le hg.2 (le_topV v i goods hg.1)

omit [DecidableEq A] in
theorem allowed_pos {i : A} {S : List G} (h : Allowed v i goods S) : ∀ g ∈ S, 0 < v i g := by
  rcases h with h | h | h
  · exact h.2
  · exact h.1
  · exact h.2.2.1

/-- **Step (i) of Lemma 4.** If the leftover goods are worth more to `x` than its holding, a minimal set `N` of
leftover goods worth more than the holding is an allowed holding of `x`. It has at most two goods, unless `x` holds
its top alone and `N` has three goods. -/
theorem exists_upgrade {base : G → Option A} (hb : Valid v agents goods base) (hgd : goods.Nodup)
    (hs : Strict v agents goods) (hc : R1Core4 v agents goods) {x : A} (hx : x ∈ agents)
    (hJ : value v x (hold goods base x) < value v x (leftover goods base)) :
    ∃ q : G → Bool, (∀ g ∈ goods, q g = true → base g = none) ∧ Allowed v x goods (goods.filter q) ∧
      value v x (hold goods base x) < value v x (goods.filter q) ∧
      (∀ g ∈ goods.filter q, value v x ((goods.filter q).erase g) ≤ value v x (hold goods base x)) ∧
      ((goods.filter q).length ≤ 2 ∨
        ∃ y, hold goods base x = [y] ∧ v x y = topV v x goods ∧ (goods.filter q).length = 3) := by
  obtain ⟨q, hq, hval, hmin⟩ :=
    shrink v x hgd (value v x (hold goods base x)) _ (fun g => decide (base g = none)) (Nat.le_refl _) hJ
  refine ⟨q, fun g _ h => by simpa using hq g h, ?_⟩
  generalize hNdef : goods.filter q = N at hval hmin ⊢
  generalize hYdef : hold goods base x = Y at hval hmin ⊢
  have hNg : ∀ g ∈ N, g ∈ goods ∧ base g = none := by
    intro g hg
    rw [← hNdef] at hg
    have := List.mem_filter.mp hg
    exact ⟨this.1, by simpa using hq g this.2⟩
  have hYg : ∀ g ∈ Y, g ∈ goods ∧ base g = some x := fun g hg => mem_hold.mp (hYdef ▸ hg)
  have hNle : ∀ g ∈ N, v x g ≤ value v x Y := fun g hg => hYdef ▸ leftover_le hb hx (hNg g hg).1 (hNg g hg).2
  have hNpos : ∀ g ∈ N, 0 < v x g := by
    intro g hg
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := hmin g hg
    rw [value_cons_erase v x hg] at hval
    omega
  have hN2 : 2 ≤ N.length := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := value_le_of_length_le_one' x (by omega : N.length ≤ 1) hNle
    omega
  have hNnd : N.Nodup := hNdef ▸ hgd.filter q
  have hYnd : Y.Nodup := hYdef ▸ nodup_hold hgd base x
  have hdis : ∀ g ∈ N, g ∉ Y := fun g hg hgY => by
    have h1 := (hNg g hg).2
    have h2 := (hYg g hgY).2
    rw [h1] at h2
    exact absurd h2 (by simp)
  have hYall : Allowed v x goods Y := hYdef ▸ hb.allowed x hx
  have hYpos := allowed_pos hYall
  have hNrel : ∀ g ∈ N, g ∈ relevant v x goods := fun g hg => by
    simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨(hNg g hg).1, hNpos g hg⟩
  have hYrel : ∀ g ∈ Y, g ∈ relevant v x goods := fun g hg => by
    simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨(hYg g hg).1, hYpos g hg⟩
  have hR4 := (hc x hx).2.1
  have hNY : N.length + Y.length ≤ 4 :=
    Nat.le_trans (length_append_le hNnd hYnd hdis (fun g hg => by
      rcases List.mem_append.mp hg with h | h
      · exact hNrel g h
      · exact hYrel g h)) hR4
  have hNtop : ∀ g ∈ N, v x g ≤ topV v x goods := fun g hg => le_topV v x goods (hNg g hg).1
  have hpair_upper : N.length = 2 → topV v x goods < value v x N → IsUpper v x goods N := by
    intro hl hlt
    refine ⟨hNpos, hlt, fun g hg => ?_⟩
    have hl1 : (N.erase g).length ≤ 1 := by rw [List.length_erase_of_mem hg]; omega
    exact value_le_of_length_le_one' x hl1 (fun g' hg' => hNtop g' (List.mem_of_mem_erase hg'))
  have htpos := topV_pos hc hx
  by_cases hVtop : topV v x goods ≤ value v x Y
  · -- (I) the holding is worth at least the top
    rcases hYall with ⟨hYl, _⟩ | hYup | hYlp
    · rcases Y with _ | ⟨y, _ | ⟨y', T⟩⟩
      · simp [value] at hVtop; omega
      · -- the holding is a single good worth the top
        have hyv : value v x [y] = v x y := by simp [value]
        have hy : v x y = topV v x goods := by
          have := le_topV v x goods (hYg y (by simp)).1
          rw [hyv] at hVtop
          omega
        have hup : IsUpper v x goods N := by
          refine ⟨hNpos, ?_, fun g hg => ?_⟩
          · rw [hyv] at hval; omega
          · have := hmin g hg; rw [hyv] at this; omega
        refine ⟨Or.inr (Or.inl hup), hval, hmin, ?_⟩
        by_cases h2 : N.length ≤ 2
        · exact Or.inl h2
        · exact Or.inr ⟨y, rfl, hy, by simp at hNY; omega⟩
      · simp at hYl
    · have hY2 : 2 ≤ Y.length := by
        refine Nat.le_of_not_lt fun hlt => ?_
        have := value_le_of_length_le_one' x (by omega : Y.length ≤ 1)
          (fun g hg => le_topV v x goods (hYg g hg).1)
        have := hYup.2.1
        omega
      have hl : N.length = 2 := by omega
      refine ⟨Or.inr (Or.inl (hpair_upper hl (Nat.lt_trans hYup.2.1 hval))), hval, hmin, Or.inl (by omega)⟩
    · have := hYlp.2.2.2.1
      omega
  · -- (II) the holding is worth less than the top: the top is wanted, so it is not leftover
    have hVlt : value v x Y < topV v x goods := Nat.lt_of_not_le hVtop
    obtain ⟨a, ha, hav⟩ := exists_topV v x goods htpos
    have haN : a ∉ N := fun haN => by have := hNle a haN; omega
    have haY : a ∉ Y := fun haY => by have := le_value_of_mem v x haY; omega
    have harel : a ∈ relevant v x goods := by
      simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨ha, by omega⟩
    have haNY : 1 + (N.length + Y.length) ≤ 4 := by
      have := length_append_le (l₁ := [a]) (l₂ := N ++ Y) (by simp)
        (List.nodup_append.mpr ⟨hNnd, hYnd, fun g hg g' hg' e => hdis g hg (e ▸ hg')⟩)
        (by intro g hg hm; rcases List.mem_append.mp hm with h | h
            · simp at hg; subst hg; exact haN h
            · simp at hg; subst hg; exact haY h)
        (by intro g hg
            rcases List.mem_append.mp hg with h | h
            · simp at h; subst h; exact harel
            · rcases List.mem_append.mp h with h | h
              · exact hNrel g h
              · exact hYrel g h)
      simp at this
      omega
    rcases hYall with ⟨hYl, _⟩ | hYup | hYlp
    · rcases Y with _ | ⟨y, _ | ⟨y', T⟩⟩
      · -- nothing held: every leftover good is worthless to x
        obtain ⟨g, hg⟩ : ∃ g, g ∈ N := by
          match N, hN2 with
          | g :: _, _ => exact ⟨g, by simp⟩
        have h1 := hNle g hg
        have h2 := hNpos g hg
        simp [value] at h1
        omega
      · -- one good, worth less than the top
        have hl : N.length = 2 := by simp at haNY; omega
        refine ⟨?_, hval, hmin, Or.inl (by omega)⟩
        rcases Nat.lt_trichotomy (topV v x goods) (value v x N) with hlt | heq | hgt
        · exact Or.inr (Or.inl (hpair_upper hl hlt))
        · exfalso
          have := hs x hx N [a] (hNdef ▸ List.filter_sublist) (List.singleton_sublist.mpr ha)
            (fun g hg hga => by simp at hga; subst hga; exact haN hg) (by simp [value, hav, heq])
          omega
        · -- the lower pair
          have hya : y ≠ a := fun e => haY (by simp [e])
          have hrel4 : (relevant v x goods).length = 4 := by
            have := length_append_le (l₁ := [a, y]) (l₂ := N) (by simp [Ne.symm hya]) hNnd
              (by intro g hg hm; simp at hg; rcases hg with rfl | rfl
                  · exact haN hm
                  · exact hdis g hm (by simp))
              (by intro g hg
                  rcases List.mem_append.mp hg with h | h
                  · simp at h; rcases h with rfl | rfl
                    · exact harel
                    · exact hYrel g (by simp)
                  · exact hNrel g h)
            simp at this
            omega
          have hall : ∀ g' ∈ relevant v x goods, g' = a ∨ g' = y ∨ g' ∈ N := by
            have hsub := subset_of_length_le (l₁ := [a, y] ++ N) (l₂ := relevant v x goods)
              (List.nodup_append.mpr ⟨by simp [Ne.symm hya], hNnd, by
                intro g hg g' hg' e; subst e; simp at hg; rcases hg with rfl | rfl
                · exact haN hg'
                · exact hdis _ hg' (by simp)⟩)
              (by intro g hg
                  rcases List.mem_append.mp hg with h | h
                  · simp at h; rcases h with rfl | rfl
                    · exact harel
                    · exact hYrel g (by simp)
                  · exact hNrel g h)
              (by simp; omega)
            intro g' hg'
            have := hsub g' hg'
            simp at this
            rcases this with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hyv : value v x [y] = v x y := by simp [value]
          refine Or.inr (Or.inr ⟨hrel4, hl, hNpos, hgt, ?_, ?_⟩)
          · intro g hg g' hg' hg'N
            rcases hall g' hg' with rfl | rfl | h
            · have := hNle g hg; omega
            · have hle := hNle g hg
              rw [hyv] at hle
              have hne : v x g ≠ v x g' := strict_ne hs hx (hNg g hg).1 (hYg g' (by simp)).1
                (fun e => hdis g hg (by simp [e])) (hNpos g hg)
              omega
            · exact absurd h hg'N
          · intro g' hg' hg'N hlt
            rcases hall g' hg' with rfl | rfl | h
            · omega
            · rw [hyv] at hval; exact hval
            · exact absurd h hg'N
      · simp at hYl
    · have := hYup.2.1
      omega
    · have := hYlp.2.1
      omega

omit [DecidableEq A] in
/-- **Lemma 7(b), general form.** Let `Y` be an allowed holding of `x` and `N ⊆ goods` (a filter of `goods`) a set
of goods outside `Y`, each worth at most `Y` to `x`, worth more than `Y` together but at most `Y` after removing any
one good. Then `N` is an allowed holding of `x`, with at most two goods unless `Y` is `x`'s top alone and `N` has
three goods. -/
theorem allowed_of_minimal (hgd : goods.Nodup) (hs : Strict v agents goods) (hc : R1Core4 v agents goods)
    {x : A} (hx : x ∈ agents) {q : G → Bool} {N Y : List G} (hNdef : goods.filter q = N)
    (hNgoods : ∀ g ∈ N, g ∈ goods) (hYgoods : ∀ g ∈ Y, g ∈ goods) (hNle : ∀ g ∈ N, v x g ≤ value v x Y)
    (hdis : ∀ g ∈ N, g ∉ Y) (hYnd : Y.Nodup) (hYall : Allowed v x goods Y)
    (hval : value v x Y < value v x N) (hmin : ∀ g ∈ N, value v x (N.erase g) ≤ value v x Y) :
    Allowed v x goods N ∧ value v x Y < value v x N ∧ (∀ g ∈ N, value v x (N.erase g) ≤ value v x Y) ∧
      (N.length ≤ 2 ∨ ∃ y, Y = [y] ∧ v x y = topV v x goods ∧ N.length = 3) := by
  have hNnd : N.Nodup := hNdef ▸ hgd.filter q
  have hNpos : ∀ g ∈ N, 0 < v x g := by
    intro g hg
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := hmin g hg
    rw [value_cons_erase v x hg] at hval
    omega
  have hN2 : 2 ≤ N.length := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := value_le_of_length_le_one' x (by omega : N.length ≤ 1) hNle
    omega
  have hYpos := allowed_pos hYall
  have hNrel : ∀ g ∈ N, g ∈ relevant v x goods := fun g hg => by
    simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨hNgoods g hg, hNpos g hg⟩
  have hYrel : ∀ g ∈ Y, g ∈ relevant v x goods := fun g hg => by
    simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨hYgoods g hg, hYpos g hg⟩
  have hR4 := (hc x hx).2.1
  have hNY : N.length + Y.length ≤ 4 :=
    Nat.le_trans (length_append_le hNnd hYnd hdis (fun g hg => by
      rcases List.mem_append.mp hg with h | h
      · exact hNrel g h
      · exact hYrel g h)) hR4
  have hNtop : ∀ g ∈ N, v x g ≤ topV v x goods := fun g hg => le_topV v x goods (hNgoods g hg)
  have hpair_upper : N.length = 2 → topV v x goods < value v x N → IsUpper v x goods N := by
    intro hl hlt
    refine ⟨hNpos, hlt, fun g hg => ?_⟩
    have hl1 : (N.erase g).length ≤ 1 := by rw [List.length_erase_of_mem hg]; omega
    exact value_le_of_length_le_one' x hl1 (fun g' hg' => hNtop g' (List.mem_of_mem_erase hg'))
  have htpos := topV_pos hc hx
  by_cases hVtop : topV v x goods ≤ value v x Y
  · -- (I) the holding is worth at least the top
    rcases hYall with ⟨hYl, _⟩ | hYup | hYlp
    · rcases Y with _ | ⟨y, _ | ⟨y', T⟩⟩
      · simp [value] at hVtop; omega
      · -- the holding is a single good worth the top
        have hyv : value v x [y] = v x y := by simp [value]
        have hy : v x y = topV v x goods := by
          have := le_topV v x goods (hYgoods y (by simp))
          rw [hyv] at hVtop
          omega
        have hup : IsUpper v x goods N := by
          refine ⟨hNpos, ?_, fun g hg => ?_⟩
          · rw [hyv] at hval; omega
          · have := hmin g hg; rw [hyv] at this; omega
        refine ⟨Or.inr (Or.inl hup), hval, hmin, ?_⟩
        by_cases h2 : N.length ≤ 2
        · exact Or.inl h2
        · exact Or.inr ⟨y, rfl, hy, by simp at hNY; omega⟩
      · simp at hYl
    · have hY2 : 2 ≤ Y.length := by
        refine Nat.le_of_not_lt fun hlt => ?_
        have := value_le_of_length_le_one' x (by omega : Y.length ≤ 1)
          (fun g hg => le_topV v x goods (hYgoods g hg))
        have := hYup.2.1
        omega
      have hl : N.length = 2 := by omega
      refine ⟨Or.inr (Or.inl (hpair_upper hl (Nat.lt_trans hYup.2.1 hval))), hval, hmin, Or.inl (by omega)⟩
    · have := hYlp.2.2.2.1
      omega
  · -- (II) the holding is worth less than the top: the top is wanted, so it is not leftover
    have hVlt : value v x Y < topV v x goods := Nat.lt_of_not_le hVtop
    obtain ⟨a, ha, hav⟩ := exists_topV v x goods htpos
    have haN : a ∉ N := fun haN => by have := hNle a haN; omega
    have haY : a ∉ Y := fun haY => by have := le_value_of_mem v x haY; omega
    have harel : a ∈ relevant v x goods := by
      simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨ha, by omega⟩
    have haNY : 1 + (N.length + Y.length) ≤ 4 := by
      have := length_append_le (l₁ := [a]) (l₂ := N ++ Y) (by simp)
        (List.nodup_append.mpr ⟨hNnd, hYnd, fun g hg g' hg' e => hdis g hg (e ▸ hg')⟩)
        (by intro g hg hm; rcases List.mem_append.mp hm with h | h
            · simp at hg; subst hg; exact haN h
            · simp at hg; subst hg; exact haY h)
        (by intro g hg
            rcases List.mem_append.mp hg with h | h
            · simp at h; subst h; exact harel
            · rcases List.mem_append.mp h with h | h
              · exact hNrel g h
              · exact hYrel g h)
      simp at this
      omega
    rcases hYall with ⟨hYl, _⟩ | hYup | hYlp
    · rcases Y with _ | ⟨y, _ | ⟨y', T⟩⟩
      · -- nothing held: every leftover good is worthless to x
        obtain ⟨g, hg⟩ : ∃ g, g ∈ N := by
          match N, hN2 with
          | g :: _, _ => exact ⟨g, by simp⟩
        have h1 := hNle g hg
        have h2 := hNpos g hg
        simp [value] at h1
        omega
      · -- one good, worth less than the top
        have hl : N.length = 2 := by simp at haNY; omega
        refine ⟨?_, hval, hmin, Or.inl (by omega)⟩
        rcases Nat.lt_trichotomy (topV v x goods) (value v x N) with hlt | heq | hgt
        · exact Or.inr (Or.inl (hpair_upper hl hlt))
        · exfalso
          have := hs x hx N [a] (hNdef ▸ List.filter_sublist) (List.singleton_sublist.mpr ha)
            (fun g hg hga => by simp at hga; subst hga; exact haN hg) (by simp [value, hav, heq])
          omega
        · -- the lower pair
          have hya : y ≠ a := fun e => haY (by simp [e])
          have hrel4 : (relevant v x goods).length = 4 := by
            have := length_append_le (l₁ := [a, y]) (l₂ := N) (by simp [Ne.symm hya]) hNnd
              (by intro g hg hm; simp at hg; rcases hg with rfl | rfl
                  · exact haN hm
                  · exact hdis g hm (by simp))
              (by intro g hg
                  rcases List.mem_append.mp hg with h | h
                  · simp at h; rcases h with rfl | rfl
                    · exact harel
                    · exact hYrel g (by simp)
                  · exact hNrel g h)
            simp at this
            omega
          have hall : ∀ g' ∈ relevant v x goods, g' = a ∨ g' = y ∨ g' ∈ N := by
            have hsub := subset_of_length_le (l₁ := [a, y] ++ N) (l₂ := relevant v x goods)
              (List.nodup_append.mpr ⟨by simp [Ne.symm hya], hNnd, by
                intro g hg g' hg' e; subst e; simp at hg; rcases hg with rfl | rfl
                · exact haN hg'
                · exact hdis _ hg' (by simp)⟩)
              (by intro g hg
                  rcases List.mem_append.mp hg with h | h
                  · simp at h; rcases h with rfl | rfl
                    · exact harel
                    · exact hYrel g (by simp)
                  · exact hNrel g h)
              (by simp; omega)
            intro g' hg'
            have := hsub g' hg'
            simp at this
            rcases this with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hyv : value v x [y] = v x y := by simp [value]
          refine Or.inr (Or.inr ⟨hrel4, hl, hNpos, hgt, ?_, ?_⟩)
          · intro g hg g' hg' hg'N
            rcases hall g' hg' with rfl | rfl | h
            · have := hNle g hg; omega
            · have hle := hNle g hg
              rw [hyv] at hle
              have hne : v x g ≠ v x g' := strict_ne hs hx (hNgoods g hg) (hYgoods g' (by simp))
                (fun e => hdis g hg (by simp [e])) (hNpos g hg)
              omega
            · exact absurd h hg'N
          · intro g' hg' hg'N hlt
            rcases hall g' hg' with rfl | rfl | h
            · omega
            · rw [hyv] at hval; exact hval
            · exact absurd h hg'N
      · simp at hYl
    · have := hYup.2.1
      omega
    · have := hYlp.2.1
      omega

end upgrade

/-! ## Step (ii): trading along a want map -/

section trade
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- A receiver of the map `r`: some giver hands it its good. -/
def Receives (r : A → Option A) (w : A) : Prop := ∃ j, r j = some w

open Classical in
/-- The trade: if `up`, `x` takes the goods passing `q`; every giver `j` (with `r j = some w`) hands its good to
`w`; a receiver that gives nothing, and `x` when `up`, releases its old goods; every other holding is unchanged. -/
noncomputable def trade (base : G → Option A) (x : A) (q : G → Bool) (r : A → Option A) (up : Bool) :
    G → Option A :=
  fun g => if up = true ∧ q g = true then some x else
    match base g with
    | none => none
    | some j =>
      match r j with
      | some w => some w
      | none => if Receives r j ∨ (up = true ∧ j = x) then none else some j

/-- The hypotheses on a trade: givers hold one good and hand it to a listed agent wanting it, injectively; every
giver is a receiver or the upgrading `x`; receivers that give nothing are free; `x`'s upgrade is made of leftover
goods. -/
structure TradeOK (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (x : A)
    (q : G → Bool) (r : A → Option A) (up : Bool) : Prop where
  give : ∀ j w, r j = some w → j ∈ agents ∧ w ∈ agents ∧
    ∃ y ∈ goods, hold goods base j = [y] ∧ value v w (hold goods base w) < v w y
  inj : ∀ j j' w, r j = some w → r j' = some w → j = j'
  comp : ∀ j, r j ≠ none → Receives r j ∨ (up = true ∧ j = x)
  last : ∀ w, Receives r w → r w = none → ∀ y ∈ hold goods base w, ∀ i ∈ agents,
    ¬ value v i (hold goods base i) < v i y
  upx : up = true → ¬ Receives r x ∧ x ∈ agents ∧ (∀ g ∈ goods, q g = true → base g = none) ∧
    Allowed v x goods (goods.filter q) ∧ value v x (hold goods base x) < value v x (goods.filter q) ∧
    (r x = none → ∀ y ∈ hold goods base x, ∀ i ∈ agents, ¬ value v i (hold goods base i) < v i y)

omit [DecidableEq G] in
theorem trade_eq_some {base : G → Option A} {x : A} {q : G → Bool} {r : A → Option A} {up : Bool} {g : G}
    {i : A} : trade base x q r up g = some i ↔
      (up = true ∧ q g = true ∧ x = i) ∨
      (¬ (up = true ∧ q g = true) ∧ ∃ j, base g = some j ∧
        (r j = some i ∨ (r j = none ∧ ¬ (Receives r j ∨ (up = true ∧ j = x)) ∧ j = i))) := by
  unfold trade
  split
  · rename_i hqg
    simp only [Option.some.injEq]
    constructor
    · intro e; exact Or.inl ⟨hqg.1, hqg.2, e⟩
    · rintro (⟨_, _, e⟩ | ⟨hn, _⟩)
      · exact e
      · exact absurd hqg hn
  · rename_i hqg
    cases hbg : base g with
    | none =>
      constructor
      · intro e; exact absurd e (by simp)
      · rintro (⟨hu, hq, _⟩ | ⟨_, j, hj, _⟩)
        · exact absurd ⟨hu, hq⟩ hqg
        · exact absurd hj (by simp)
    | some k =>
      simp only
      cases hrk : r k with
      | some w =>
        simp only [Option.some.injEq]
        constructor
        · intro e; exact Or.inr ⟨hqg, k, rfl, Or.inl (by rw [hrk, e])⟩
        · rintro (⟨hu, hq, _⟩ | ⟨_, j, hj, h1 | ⟨h1, _⟩⟩)
          · exact absurd ⟨hu, hq⟩ hqg
          · subst hj; rw [hrk] at h1; exact Option.some.inj h1
          · subst hj; rw [hrk] at h1; exact absurd h1 (by simp)
      | none =>
        simp only
        split
        · rename_i hc
          constructor
          · intro e; exact absurd e (by simp)
          · rintro (⟨hu, hq, _⟩ | ⟨_, j, hj, h1 | ⟨_, hn, _⟩⟩)
            · exact absurd ⟨hu, hq⟩ hqg
            · have hkj : k = j := Option.some.inj hj
              subst hkj; rw [hrk] at h1; exact absurd h1 (by simp)
            · have hkj : k = j := Option.some.inj hj
              subst hkj; exact absurd hc hn
        · rename_i hc
          simp only [Option.some.injEq]
          constructor
          · intro e; exact Or.inr ⟨hqg, k, rfl, Or.inr ⟨hrk, hc, e⟩⟩
          · rintro (⟨hu, hq, _⟩ | ⟨_, j, hj, h1 | ⟨_, _, e⟩⟩)
            · exact absurd ⟨hu, hq⟩ hqg
            · subst hj; rw [hrk] at h1; exact absurd h1 (by simp)
            · subst hj; exact e

theorem hold_trade_recv {base : G → Option A} {x : A} {q : G → Bool} {r : A → Option A} {up : Bool}
    (hgd : goods.Nodup) (h : TradeOK v agents goods base x q r up) {j w : A} (hjw : r j = some w)
    (hwx : up = true → w ≠ x) {y : G} (hy : hold goods base j = [y]) :
    hold goods (trade base x q r up) w = [y] := by
  have hyg : y ∈ goods := (mem_hold.mp (by rw [hy]; simp)).1
  have hyb : base y = some j := (mem_hold.mp (by rw [hy]; simp)).2
  have hq : ¬ (up = true ∧ q y = true) := fun ⟨hu, hqy⟩ => by
    have := (h.upx hu).2.2.1 y hyg hqy
    rw [hyb] at this; exact absurd this (by simp)
  have hmem : y ∈ hold goods (trade base x q r up) w :=
    mem_hold.mpr ⟨hyg, trade_eq_some.mpr (Or.inr ⟨hq, j, hyb, Or.inl hjw⟩)⟩
  apply eq_singleton_of_length_le_one _ hmem
  apply length_le_one_of_eq (hgd.filter _)
  have key : ∀ g ∈ hold goods (trade base x q r up) w, g = y := by
    intro g hg
    obtain ⟨hgg, hgt⟩ := mem_hold.mp hg
    rcases trade_eq_some.mp hgt with ⟨hu, _, e⟩ | ⟨_, k, hbk, h1 | ⟨_, hc, e⟩⟩
    · exact absurd e.symm (hwx hu)
    · have hkj : k = j := h.inj k j w h1 hjw
      subst hkj
      have : g ∈ hold goods base k := mem_hold.mpr ⟨hgg, hbk⟩
      rw [hy] at this
      simpa using this
    · subst e
      exact absurd (Or.inl ⟨j, hjw⟩) hc
  exact fun a ha b hb => (key a ha).trans (key b hb).symm

theorem hold_trade_up {base : G → Option A} {x : A} {q : G → Bool} {r : A → Option A}
    (h : TradeOK v agents goods base x q r true) :
    hold goods (trade base x q r true) x = goods.filter q := by
  have hnr := (h.upx rfl).1
  unfold hold
  apply List.filter_congr
  intro g _
  by_cases hqg : q g = true
  · rw [hqg]
    exact decide_eq_true (trade_eq_some.mpr (Or.inl ⟨rfl, hqg, rfl⟩))
  · have hqf : q g = false := by simpa using hqg
    rw [hqf]
    refine decide_eq_false fun ht => ?_
    rcases trade_eq_some.mp ht with ⟨_, hq, _⟩ | ⟨_, k, _, h1 | ⟨_, hc, e⟩⟩
    · exact hqg hq
    · exact hnr ⟨k, h1⟩
    · subst e; exact hc (Or.inr ⟨rfl, rfl⟩)

theorem hold_trade_other {base : G → Option A} {x : A} {q : G → Bool} {r : A → Option A} {up : Bool}
    (h : TradeOK v agents goods base x q r up) {i : A} (hir : ¬ Receives r i) (hix : up = true → i ≠ x) :
    hold goods (trade base x q r up) i = hold goods base i := by
  have hri : r i = none := by
    cases hr : r i with
    | none => rfl
    | some w =>
      rcases h.comp i (by rw [hr]; simp) with h1 | ⟨hu, hx⟩
      · exact absurd h1 hir
      · exact absurd hx (hix hu)
  unfold hold
  apply List.filter_congr
  intro g hg
  apply decide_eq_decide.mpr
  constructor
  · intro ht
    rcases trade_eq_some.mp ht with ⟨hu, _, e⟩ | ⟨_, k, hbk, h1 | ⟨_, _, e⟩⟩
    · exact absurd e.symm (hix hu)
    · exact absurd ⟨k, h1⟩ hir
    · subst e; exact hbk
  · intro hb
    have hq : ¬ (up = true ∧ q g = true) := fun ⟨hu, hqg⟩ => by
      have := (h.upx hu).2.2.1 g hg hqg
      rw [hb] at this; exact absurd this (by simp)
    refine trade_eq_some.mpr (Or.inr ⟨hq, i, hb, Or.inr ⟨hri, ?_, rfl⟩⟩)
    rintro (h1 | ⟨hu, hx⟩)
    · exact hir h1
    · exact hix hu hx

/-- **The trade is valid and better** (step (ii) of Lemma 4, and the want-rings). -/
theorem trade_valid_better {base : G → Option A} (hb : Valid v agents goods base) (hgd : goods.Nodup)
    {x : A} {q : G → Bool} {r : A → Option A} {up : Bool} (h : TradeOK v agents goods base x q r up)
    (hbig : up = true → 3 ≤ (goods.filter q).length → ∀ i ∈ agents, i ≠ x → ∀ hh ∈ goods.filter q,
      value v i ((goods.filter q).erase hh) ≤ value v i (hold goods (trade base x q r up) i))
    (hsome : up = true ∨ ∃ j w, r j = some w) :
    Valid v agents goods (trade base x q r up) ∧ Better v agents goods (trade base x q r up) base := by
  -- the three kinds of agents
  have hrecv : ∀ {w}, Receives r w → ∃ j y, r j = some w ∧ hold goods base j = [y] ∧ y ∈ goods ∧
      hold goods (trade base x q r up) w = [y] ∧ value v w (hold goods base w) < v w y := by
    intro w ⟨j, hj⟩
    obtain ⟨_, _, y, hyg, hy, hlt⟩ := h.give j w hj
    have hwx : up = true → w ≠ x := fun hu e => (h.upx hu).1 (e ▸ ⟨j, hj⟩)
    exact ⟨j, y, hj, hy, hyg, hold_trade_recv hgd h hj hwx hy, hlt⟩
  have hup : up = true → hold goods (trade base x q r up) x = goods.filter q := by
    intro hu; subst hu; exact hold_trade_up h
  have hother : ∀ {i}, ¬ Receives r i → (up = true → i ≠ x) →
      hold goods (trade base x q r up) i = hold goods base i := fun hir hix => hold_trade_other h hir hix
  have hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods (trade base x q r up) i) := by
    intro i _
    by_cases hir : Receives r i
    · obtain ⟨_, y, _, _, _, hh, hlt⟩ := hrecv hir
      rw [hh, value_singleton]; exact Nat.le_of_lt hlt
    · by_cases hix : up = true ∧ i = x
      · obtain ⟨hu, rfl⟩ := hix
        rw [hup hu]; exact Nat.le_of_lt (h.upx hu).2.2.2.2.1
      · rw [hother hir (fun hu e => hix ⟨hu, e⟩)]; exact Nat.le_refl _
  have hvalid : Valid v agents goods (trade base x q r up) := by
    refine valid_of_gain v agents goods (base := base) ?_ ?_ hval ?_ ?_
    · intro g hg j hj
      rcases trade_eq_some.mp hj with ⟨hu, _, rfl⟩ | ⟨_, k, hbk, h1 | ⟨_, _, rfl⟩⟩
      · exact (h.upx hu).2.1
      · exact (h.give k j h1).2.1
      · exact hb.owners g hg _ hbk
    · intro i hi
      by_cases hir : Receives r i
      · obtain ⟨_, y, _, _, hyg, hh, hlt⟩ := hrecv hir
        rw [hh]
        exact Or.inl ⟨by simp, fun g hg => by
          simp at hg; subst hg; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt⟩
      · by_cases hix : up = true ∧ i = x
        · obtain ⟨hu, rfl⟩ := hix
          rw [hup hu]; exact (h.upx hu).2.2.2.1
        · rw [hother hir (fun hu e => hix ⟨hu, e⟩)]; exact hb.allowed i hi
    · intro i hi g hg hlt
      obtain ⟨j, hj, hjg⟩ := hb.v1 i hi g hg hlt
      have hgj : g ∈ hold goods base j := by rw [hjg]; simp
      cases hrj : r j with
      | some w =>
        obtain ⟨_, hw, y, _, hy, _⟩ := h.give j w hrj
        rw [hjg] at hy
        have hgy : g = y := by simpa using hy
        subst hgy
        have hwx : up = true → w ≠ x := fun hu e => (h.upx hu).1 (e ▸ ⟨j, hrj⟩)
        exact ⟨w, hw, hold_trade_recv hgd h hrj hwx hjg⟩
      | none =>
        by_cases hjr : Receives r j
        · exact absurd hlt (h.last j hjr hrj g hgj i hi)
        · by_cases hjx : up = true ∧ j = x
          · obtain ⟨hu, rfl⟩ := hjx
            exact absurd hlt ((h.upx hu).2.2.2.2.2 hrj g hgj i hi)
          · exact ⟨j, hj, by rw [hother hjr (fun hu e => hjx ⟨hu, e⟩)]; exact hjg⟩
    · intro i hi j hj hij h3 hh hhm
      by_cases hjr : Receives r j
      · obtain ⟨_, y, _, _, _, hy, _⟩ := hrecv hjr
        rw [hy] at h3; simp at h3
      · by_cases hjx : up = true ∧ j = x
        · obtain ⟨hu, rfl⟩ := hjx
          rw [hup hu] at h3 hhm ⊢
          exact hbig hu h3 i hi hij hh hhm
        · have he := hother hjr (fun hu e => hjx ⟨hu, e⟩)
          rw [he] at hhm ⊢
          exact Nat.le_trans (hb.v2 i hi j hj hij hh hhm) (hval i hi)
  refine ⟨hvalid, better_of_monotone v agents goods ?_ hval ?_⟩
  · intro i hi
    by_cases hir : Receives r i
    · obtain ⟨_, y, _, _, hyg, hh, hlt⟩ := hrecv hir
      rw [hh]
      refine level_mono v i goods (hb.allowed i hi) ?_ (fun g hg => mem_goods_of_mem_hold hg)
        (fun g hg => by simp at hg; subst hg; exact hyg) (by rw [value_singleton]; exact hlt)
      exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt⟩
    · by_cases hix : up = true ∧ i = x
      · obtain ⟨hu, rfl⟩ := hix
        rw [hup hu]
        exact level_mono v i goods (hb.allowed i hi) (h.upx hu).2.2.2.1
          (fun g hg => mem_goods_of_mem_hold hg) (fun g hg => (List.mem_filter.mp hg).1)
          (h.upx hu).2.2.2.2.1
      · rw [hother hir (fun hu e => hix ⟨hu, e⟩)]; exact Nat.le_refl _
  · rcases hsome with hu | ⟨j, w, hjw⟩
    · refine ⟨x, (h.upx hu).2.1, ?_⟩
      rw [hup hu]; exact (h.upx hu).2.2.2.2.1
    · obtain ⟨_, hw, _⟩ := h.give j w hjw
      obtain ⟨_, y, _, _, _, hh, hlt⟩ := hrecv ⟨j, hjw⟩
      exact ⟨w, hw, by rw [hh, value_singleton]; exact hlt⟩

end trade

/-! ## Paths and cycles of wanters -/

section walks

/-- Consecutive elements of the list are related. -/
def IsChain (R : A → A → Prop) : List A → Prop
  | a :: b :: t => R a b ∧ IsChain R (b :: t)
  | _ => True

/-- The element after `j` in the list. -/
def nextIn : List A → A → Option A
  | a :: b :: t, j => if j = a then some b else nextIn (b :: t) j
  | _, _ => none

omit [DecidableEq A] in
theorem isChain_cons {R : A → A → Prop} {a b : A} {t : List A} :
    IsChain R (a :: b :: t) ↔ R a b ∧ IsChain R (b :: t) := Iff.rfl

omit [DecidableEq A] in
theorem isChain_tail {R : A → A → Prop} : ∀ {a : A} {t : List A}, IsChain R (a :: t) → IsChain R t
  | _, [], _ => trivial
  | _, _ :: _, h => h.2

omit [DecidableEq A] in
theorem isChain_append {R : A → A → Prop} : ∀ {l : List A} {a w : A}, l.getLast? = some a → IsChain R l →
    R a w → IsChain R (l ++ [w])
  | [], _, _, h, _, _ => by simp at h
  | [b], a, w, h, _, hr => by simp at h; subst h; exact ⟨hr, trivial⟩
  | b :: c :: t, a, w, h, hc, hr => by
    have h' : (c :: t).getLast? = some a := by simpa [List.getLast?_cons_cons] using h
    exact ⟨hc.1, isChain_append h' hc.2 hr⟩

omit [DecidableEq A] in
theorem isChain_right {R : A → A → Prop} : ∀ {l₁ l₂ : List A}, IsChain R (l₁ ++ l₂) → IsChain R l₂
  | [], _, h => h
  | _ :: t, _, h => isChain_right (l₁ := t) (isChain_tail h)

theorem nextIn_none_of_not_mem : ∀ {l : List A} {j : A}, j ∉ l → nextIn l j = none
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: t, j, h => by
    have hja : j ≠ a := fun e => h (e ▸ List.mem_cons_self)
    simp only [nextIn, hja, ↓reduceIte]
    exact nextIn_none_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))

theorem nextIn_spec {R : A → A → Prop} : ∀ {l : List A} {j w : A}, IsChain R l → nextIn l j = some w →
    R j w ∧ j ∈ l ∧ w ∈ l.tail
  | [], _, _, _, h => by simp [nextIn] at h
  | [_], _, _, _, h => by simp [nextIn] at h
  | a :: b :: t, j, w, hc, h => by
    by_cases hja : j = a
    · subst hja
      simp only [nextIn, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨hc.1, List.mem_cons_self, List.mem_cons_self⟩
    · simp only [nextIn, hja, ↓reduceIte] at h
      obtain ⟨h1, h2, h3⟩ := nextIn_spec hc.2 h
      refine ⟨h1, List.mem_cons_of_mem _ h2, ?_⟩
      simp only [List.tail_cons] at h3 ⊢
      exact List.mem_cons_of_mem _ h3

omit [DecidableEq A] in
theorem isChain_true : ∀ l : List A, IsChain (fun _ _ => True) l
  | [] => trivial
  | [_] => trivial
  | _ :: b :: t => ⟨trivial, isChain_true (b :: t)⟩

theorem nextIn_mem_tail {l : List A} {j w : A} (h : nextIn l j = some w) : j ∈ l ∧ w ∈ l.tail :=
  (nextIn_spec (isChain_true l) h).2

theorem nextIn_inj : ∀ {l : List A}, l.Nodup → ∀ {j j' w : A}, nextIn l j = some w → nextIn l j' = some w →
    j = j'
  | [], _, _, _, _, h, _ => by simp [nextIn] at h
  | [_], _, _, _, _, h, _ => by simp [nextIn] at h
  | a :: b :: t, hnd, j, j', w, h, h' => by
    have hrest : (b :: t).Nodup := (List.nodup_cons.mp hnd).2
    have ha : a ∉ b :: t := (List.nodup_cons.mp hnd).1
    by_cases hja : j = a <;> by_cases hj'a : j' = a
    · rw [hja, hj'a]
    · subst hja
      simp only [nextIn, ↓reduceIte, Option.some.injEq] at h
      simp only [nextIn, hj'a, ↓reduceIte] at h'
      subst h
      -- b is the head of b :: t, so it is nobody's successor there
      have := (nextIn_mem_tail h').2
      exact absurd this (fun hm => (List.nodup_cons.mp hrest).1 hm)
    · subst hj'a
      simp only [nextIn, ↓reduceIte, Option.some.injEq] at h'
      simp only [nextIn, hja, ↓reduceIte] at h
      subst h'
      have := (nextIn_mem_tail h).2
      exact absurd this (fun hm => (List.nodup_cons.mp hrest).1 hm)
    · simp only [nextIn, hja, hj'a, ↓reduceIte] at h h'
      exact nextIn_inj hrest h h'

theorem exists_nextIn_of_mem_tail : ∀ {l : List A}, l.Nodup → ∀ {w : A}, w ∈ l.tail → ∃ j, nextIn l j = some w
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: t, hnd, w, h => by
    by_cases hwb : w = b
    · subst hwb; exact ⟨a, by simp [nextIn]⟩
    · have hw : w ∈ (b :: t).tail := by
        simp only [List.tail_cons] at h ⊢
        rcases List.mem_cons.mp h with e | hm
        · exact absurd e hwb
        · exact hm
      obtain ⟨j, hj⟩ := exists_nextIn_of_mem_tail (List.nodup_cons.mp hnd).2 hw
      have hja : j ≠ a := by
        rintro rfl
        exact (List.nodup_cons.mp hnd).1 (nextIn_mem_tail hj).1
      exact ⟨j, by simp [nextIn, hja, hj]⟩

theorem nextIn_last : ∀ {l : List A}, l.Nodup → ∀ {j : A}, l.getLast? = some j → nextIn l j = none
  | [], _, _, h => by simp at h
  | [_], _, _, _ => rfl
  | a :: b :: t, hnd, j, h => by
    rw [List.getLast?_cons_cons] at h
    have hj : j ∈ b :: t := List.mem_of_getLast? h
    have hja : j ≠ a := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hj)
    simp only [nextIn, hja, ↓reduceIte]
    exact nextIn_last (List.nodup_cons.mp hnd).2 h

theorem nextIn_some : ∀ {l : List A}, l.Nodup → ∀ {j : A}, j ∈ l → l.getLast? ≠ some j → ∃ w, nextIn l j = some w
  | [], _, _, h, _ => by simp at h
  | [a], _, j, h, h' => by simp at h; subst h; simp at h'
  | a :: b :: t, hnd, j, h, h' => by
    by_cases hja : j = a
    · subst hja; exact ⟨b, by simp [nextIn]⟩
    · have hj : j ∈ b :: t := by
        rcases List.mem_cons.mp h with e | hm
        · exact absurd e hja
        · exact hm
      rw [List.getLast?_cons_cons] at h'
      obtain ⟨w, hw⟩ := nextIn_some (List.nodup_cons.mp hnd).2 hj h'
      exact ⟨w, by simp [nextIn, hja, hw]⟩

/-- The suffix of `l` from the first occurrence of `w`. -/
def fromFirst (w : A) : List A → List A
  | [] => []
  | a :: t => if a = w then a :: t else fromFirst w t

theorem fromFirst_suffix (w : A) : ∀ l : List A, ∃ pre, l = pre ++ fromFirst w l
  | [] => ⟨[], rfl⟩
  | a :: t => by
    by_cases h : a = w
    · exact ⟨[], by simp [fromFirst, h]⟩
    · obtain ⟨pre, hpre⟩ := fromFirst_suffix w t
      exact ⟨a :: pre, by simp only [fromFirst, h, ↓reduceIte]; rw [List.cons_append, ← hpre]⟩

theorem fromFirst_sublist (w : A) : ∀ l : List A, (fromFirst w l).Sublist l
  | [] => List.Sublist.slnil
  | a :: t => by
    by_cases h : a = w
    · simp [fromFirst, h]
    · simp only [fromFirst, h, ↓reduceIte]
      exact (fromFirst_sublist w t).cons a

theorem fromFirst_head (w : A) : ∀ {l : List A}, w ∈ l → (fromFirst w l).head? = some w
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : a = w
    · simp [fromFirst, ha]
    · have : w ∈ t := by
        rcases List.mem_cons.mp h with e | hm
        · exact absurd e.symm ha
        · exact hm
      simp only [fromFirst, ha, ↓reduceIte]
      exact fromFirst_head w this

theorem fromFirst_getLast (w : A) : ∀ {l : List A}, w ∈ l → (fromFirst w l).getLast? = l.getLast?
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : a = w
    · simp [fromFirst, ha]
    · have hw : w ∈ t := by
        rcases List.mem_cons.mp h with e | hm
        · exact absurd e.symm ha
        · exact hm
      simp only [fromFirst, ha, ↓reduceIte]
      rw [fromFirst_getLast w hw]
      match t, hw with
      | b :: t', _ => rw [List.getLast?_cons_cons]

end walks

/-! ## The walk from a frozen agent -/

section walk
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- `w` wants `j`'s single good. -/
def WantsGood (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (j w : A) : Prop :=
  w ∈ agents ∧ ∃ y ∈ goods, hold goods base j = [y] ∧ value v w (hold goods base w) < v w y

/-- In a valid state, an agent that is not frozen holds no good that a listed agent wants. -/
theorem free_of_not_frozen {base : G → Option A} (hb : Valid v agents goods base) {j : A}
    (hj : ¬ Frozen v agents goods base j) :
    ∀ y ∈ hold goods base j, ∀ i ∈ agents, ¬ value v i (hold goods base i) < v i y := by
  intro y hy i hi hlt
  obtain ⟨k, _, hk⟩ := hb.v1 i hi y (mem_hold.mp hy).1 hlt
  have hyk : base y = some k := (mem_hold.mp (by rw [hk]; simp)).2
  rw [(mem_hold.mp hy).2] at hyk
  have hjk : j = k := Option.some.inj hyk
  subst hjk
  exact hj ⟨y, hk, i, hi, hlt⟩

omit [DecidableEq G] in
theorem wantsGood_of_frozen {base : G → Option A} {j : A} (hj : Frozen v agents goods base j) :
    ∃ w, WantsGood v agents goods base j w := by
  obtain ⟨y, hy, w, hw, hlt⟩ := hj
  exact ⟨w, hw, y, (mem_hold.mp (by rw [hy]; simp)).1, hy, hlt⟩

omit [DecidableEq G] in
/-- **The walk.** From a path of frozen agents, each wanting the good of the one before, wanters lead to a free agent
along a simple path, or close a cycle. -/
theorem exists_walk {base : G → Option A} :
    ∀ (k : Nat) (P : List A), agents.length - P.length ≤ k → P ≠ [] → P.Nodup →
      (∀ j ∈ P, j ∈ agents ∧ Frozen v agents goods base j) → IsChain (WantsGood v agents goods base) P →
      (∃ Q : List A, Q.head? = P.head? ∧ Q.Nodup ∧ IsChain (WantsGood v agents goods base) Q ∧
          (∀ j ∈ Q, j ∈ agents) ∧ ∃ l, Q.getLast? = some l ∧ ¬ Frozen v agents goods base l) ∨
      (∃ C : List A, C.Nodup ∧ IsChain (WantsGood v agents goods base) C ∧ (∀ j ∈ C, j ∈ agents) ∧
          ∃ c w, C.getLast? = some c ∧ C.head? = some w ∧ WantsGood v agents goods base c w) := by
  intro k
  induction k with
  | zero =>
    intro P hk hne hnd hP hc
    obtain ⟨c, hcl⟩ : ∃ c, P.getLast? = some c := by
      cases h : P.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some c => exact ⟨c, rfl⟩
    have hcP : c ∈ P := List.mem_of_getLast? hcl
    obtain ⟨w, hw⟩ := wantsGood_of_frozen (hP c hcP).2
    by_cases hfw : Frozen v agents goods base w
    · by_cases hwP : w ∈ P
      · obtain ⟨pre, hpre⟩ := fromFirst_suffix w P
        refine Or.inr ⟨fromFirst w P, ?_, ?_, fun j hj => (hP j ?_).1, c, w, ?_, fromFirst_head w hwP, hw⟩
        · exact hnd.sublist (fromFirst_sublist w P)
        · rw [hpre] at hc; exact isChain_right hc
        · rw [hpre]; exact List.mem_append_right _ hj
        · rw [fromFirst_getLast w hwP]; exact hcl
      · exfalso
        have hnd' : (P ++ [w]).Nodup := List.nodup_append.mpr ⟨hnd, by simp,
          fun a ha b hb e => by simp at hb; subst hb; subst e; exact hwP ha⟩
        have := List.Nodup.length_le_of_subset hnd' (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · exact (hP a h).1
          · simp at h; subst h; exact hw.1)
        simp at this
        omega
    · refine Or.inl ⟨P ++ [w], ?_, ?_, isChain_append hcl hc hw, ?_, w, by simp, hfw⟩
      · cases P with
        | nil => exact absurd rfl hne
        | cons a t => rfl
      · exact List.nodup_append.mpr ⟨hnd, by simp,
          fun a ha b hb e => by simp at hb; subst hb; subst e; exact hfw (hP a ha).2⟩
      · intro j hj
        rcases List.mem_append.mp hj with h | h
        · exact (hP j h).1
        · simp at h; subst h; exact hw.1
  | succ k ih =>
    intro P hk hne hnd hP hc
    obtain ⟨c, hcl⟩ : ∃ c, P.getLast? = some c := by
      cases h : P.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some c => exact ⟨c, rfl⟩
    have hcP : c ∈ P := List.mem_of_getLast? hcl
    obtain ⟨w, hw⟩ := wantsGood_of_frozen (hP c hcP).2
    by_cases hfw : Frozen v agents goods base w
    · by_cases hwP : w ∈ P
      · obtain ⟨pre, hpre⟩ := fromFirst_suffix w P
        refine Or.inr ⟨fromFirst w P, ?_, ?_, fun j hj => (hP j ?_).1, c, w, ?_, fromFirst_head w hwP, hw⟩
        · exact hnd.sublist (fromFirst_sublist w P)
        · rw [hpre] at hc; exact isChain_right hc
        · rw [hpre]; exact List.mem_append_right _ hj
        · rw [fromFirst_getLast w hwP]; exact hcl
      · have hnd' : (P ++ [w]).Nodup := List.nodup_append.mpr ⟨hnd, by simp,
          fun a ha b hb e => by simp at hb; subst hb; subst e; exact hwP ha⟩
        have hres := ih (P ++ [w]) (by simp; omega) (by simp) hnd'
          (fun j hj => by
            rcases List.mem_append.mp hj with h | h
            · exact hP j h
            · simp at h; subst h; exact ⟨hw.1, hfw⟩)
          (isChain_append hcl hc hw)
        rcases hres with ⟨Q, hQ1, hQ⟩ | hC
        · refine Or.inl ⟨Q, ?_, hQ⟩
          rw [hQ1]
          cases P with
          | nil => exact absurd rfl hne
          | cons a t => rfl
        · exact Or.inr hC
    · refine Or.inl ⟨P ++ [w], ?_, ?_, isChain_append hcl hc hw, ?_, w, by simp, hfw⟩
      · cases P with
        | nil => exact absurd rfl hne
        | cons a t => rfl
      · exact List.nodup_append.mpr ⟨hnd, by simp,
          fun a ha b hb e => by simp at hb; subst hb; subst e; exact hfw (hP a ha).2⟩
      · intro j hj
        rcases List.mem_append.mp hj with h | h
        · exact (hP j h).1
        · simp at h; subst h; exact hw.1

end walk

/-! ## The two trades: along a path, around a cycle -/

section trades2
variable {v : A → G → Nat} {agents : List A} {goods : List G}

theorem tradeOK_path {base : G → Option A} (hb : Valid v agents goods base) {x : A} {q : G → Bool}
    {Q : List A} (hQh : Q.head? = some x) (hQnd : Q.Nodup) (hQc : IsChain (WantsGood v agents goods base) Q)
    (hQa : ∀ j ∈ Q, j ∈ agents) {l : A} (hl : Q.getLast? = some l) (hlf : ¬ Frozen v agents goods base l)
    (hxf : Frozen v agents goods base x) (hq : ∀ g ∈ goods, q g = true → base g = none)
    (hN : Allowed v x goods (goods.filter q))
    (hgain : value v x (hold goods base x) < value v x (goods.filter q)) :
    TradeOK v agents goods base x q (nextIn Q) true := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = x :: t := by
    cases Q with
    | nil => simp at hQh
    | cons a t => simp at hQh; exact ⟨t, by rw [hQh]⟩
  have hxt : x ∉ t := (List.nodup_cons.mp hQnd).1
  have last_of : ∀ {w}, w ∈ x :: t → nextIn (x :: t) w = none → w = l := by
    intro w hw hn
    refine Classical.byContradiction fun hwl => ?_
    have : (x :: t).getLast? ≠ some w := by rw [hl]; exact fun e => hwl (Option.some.inj e).symm
    obtain ⟨u, hu⟩ := nextIn_some hQnd hw this
    rw [hn] at hu; exact absurd hu (by simp)
  refine ⟨fun j w hjw => ?_, fun j j' w h1 h2 => nextIn_inj hQnd h1 h2, fun j hj => ?_, fun w hw hwn => ?_,
    fun _ => ⟨?_, hQa x (by simp), hq, hN, hgain, fun hxn => ?_⟩⟩
  · obtain ⟨hW, hjQ, _⟩ := nextIn_spec hQc hjw
    exact ⟨hQa j hjQ, hW⟩
  · obtain ⟨w, hw⟩ : ∃ w, nextIn (x :: t) j = some w := by
      cases h : nextIn (x :: t) j with
      | none => exact absurd h hj
      | some w => exact ⟨w, rfl⟩
    have hjQ := (nextIn_mem_tail hw).1
    by_cases hjx : j = x
    · exact Or.inr ⟨rfl, hjx⟩
    · have hjt : j ∈ (x :: t).tail := by
        rcases List.mem_cons.mp hjQ with e | hm
        · exact absurd e hjx
        · exact hm
      exact Or.inl (exists_nextIn_of_mem_tail hQnd hjt)
  · obtain ⟨j, hj⟩ := hw
    have hwQ : w ∈ x :: t := List.mem_of_mem_tail (nextIn_mem_tail hj).2
    have := last_of hwQ hwn
    subst this
    exact free_of_not_frozen hb hlf
  · rintro ⟨j, hj⟩
    exact hxt (nextIn_mem_tail hj).2
  · have := last_of (by simp) hxn
    subst this
    exact absurd hxf hlf

/-- The cyclic successor on `C`: the next element, and the head after the last. -/
def cycNext (C : List A) (c w₀ : A) (j : A) : Option A := if j = c then some w₀ else nextIn C j

theorem tradeOK_cycle {base : G → Option A} {C : List A} (hCnd : C.Nodup)
    (hCc : IsChain (WantsGood v agents goods base) C) (hCa : ∀ j ∈ C, j ∈ agents) {c w₀ : A}
    (hc : C.getLast? = some c) (hw₀ : C.head? = some w₀) (hcw : WantsGood v agents goods base c w₀) :
    TradeOK v agents goods base w₀ (fun _ => false) (cycNext C c w₀) false := by
  obtain ⟨t, rfl⟩ : ∃ t, C = w₀ :: t := by
    cases C with
    | nil => simp at hw₀
    | cons a t => simp at hw₀; exact ⟨t, by rw [hw₀]⟩
  have hw₀t : w₀ ∉ t := (List.nodup_cons.mp hCnd).1
  have hcC : c ∈ w₀ :: t := List.mem_of_getLast? hc
  have hcnone : nextIn (w₀ :: t) c = none := nextIn_last hCnd hc
  have hne : ∀ {j}, j ∈ w₀ :: t → cycNext (w₀ :: t) c w₀ j ≠ none := by
    intro j hj
    unfold cycNext
    by_cases hjc : j = c
    · simp [hjc]
    · simp only [hjc, ↓reduceIte]
      have : (w₀ :: t).getLast? ≠ some j := by rw [hc]; exact fun e => hjc (Option.some.inj e).symm
      obtain ⟨u, hu⟩ := nextIn_some hCnd hj this
      rw [hu]; simp
  have mem_of : ∀ {j w}, cycNext (w₀ :: t) c w₀ j = some w → j ∈ w₀ :: t ∧ w ∈ w₀ :: t := by
    intro j w h
    unfold cycNext at h
    by_cases hjc : j = c
    · simp only [hjc, ↓reduceIte, Option.some.injEq] at h
      subst hjc; subst h; exact ⟨hcC, by simp⟩
    · simp only [hjc, ↓reduceIte] at h
      exact ⟨(nextIn_mem_tail h).1, List.mem_of_mem_tail (nextIn_mem_tail h).2⟩
  refine ⟨fun j w hjw => ?_, fun j j' w h1 h2 => ?_, fun j hj => Or.inl ?_, fun w hw hwn => ?_,
    fun h => absurd h (by simp)⟩
  · unfold cycNext at hjw
    by_cases hjc : j = c
    · simp only [hjc, ↓reduceIte, Option.some.injEq] at hjw
      subst hjc; subst hjw
      exact ⟨hCa j hcC, hcw⟩
    · simp only [hjc, ↓reduceIte] at hjw
      obtain ⟨hW, hjC, _⟩ := nextIn_spec hCc hjw
      exact ⟨hCa j hjC, hW⟩
  · unfold cycNext at h1 h2
    by_cases hjc : j = c <;> by_cases hj'c : j' = c
    · rw [hjc, hj'c]
    · simp only [hjc, ↓reduceIte, Option.some.injEq] at h1
      simp only [hj'c, ↓reduceIte] at h2
      subst h1
      exact absurd (nextIn_mem_tail h2).2 hw₀t
    · simp only [hj'c, ↓reduceIte, Option.some.injEq] at h2
      simp only [hjc, ↓reduceIte] at h1
      subst h2
      exact absurd (nextIn_mem_tail h1).2 hw₀t
    · simp only [hjc, hj'c, ↓reduceIte] at h1 h2
      exact nextIn_inj hCnd h1 h2
  · have hjC : j ∈ w₀ :: t := by
      refine Classical.byContradiction fun hn => ?_
      apply hj
      unfold cycNext
      have hjc : j ≠ c := fun e => hn (e ▸ hcC)
      simp only [hjc, ↓reduceIte]
      exact nextIn_none_of_not_mem hn
    by_cases hjw : j = w₀
    · subst hjw; exact ⟨c, by simp [cycNext]⟩
    · have hjt : j ∈ (w₀ :: t).tail := by
        rcases List.mem_cons.mp hjC with e | hm
        · exact absurd e hjw
        · exact hm
      obtain ⟨j', hj'⟩ := exists_nextIn_of_mem_tail hCnd hjt
      have hj'c : j' ≠ c := fun e => by rw [e, hcnone] at hj'; exact absurd hj' (by simp)
      exact ⟨j', by simp [cycNext, hj'c, hj']⟩
  · obtain ⟨j, hj⟩ := hw
    exact absurd hwn (hne (mem_of hj).2)

end trades2

/-! ## Lemma 4 -/

section lemma4
variable {v : A → G → Nat} {agents : List A} {goods : List G}

theorem trade_value_ge {base : G → Option A} (hgd : goods.Nodup) {x : A} {q : G → Bool} {r : A → Option A}
    {up : Bool} (h : TradeOK v agents goods base x q r up) :
    ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods (trade base x q r up) i) := by
  intro i _
  by_cases hir : Receives r i
  · obtain ⟨j, hj⟩ := hir
    obtain ⟨_, _, y, _, hy, hlt⟩ := h.give j i hj
    have hwx : up = true → i ≠ x := fun hu e => (h.upx hu).1 (e ▸ ⟨j, hj⟩)
    rw [hold_trade_recv hgd h hj hwx hy, value_singleton]
    exact Nat.le_of_lt hlt
  · by_cases hix : up = true ∧ i = x
    · obtain ⟨hu, rfl⟩ := hix
      subst hu
      rw [hold_trade_up h]
      exact Nat.le_of_lt (h.upx rfl).2.2.2.2.1
    · rw [hold_trade_other h hir (fun hu e => hix ⟨hu, e⟩)]
      exact Nat.le_refl _

omit [DecidableEq A] [DecidableEq G] in
theorem filter_sublist_filter {p p' : G → Bool} : ∀ {l : List G}, (∀ g ∈ l, p g = true → p' g = true) →
    (l.filter p).Sublist (l.filter p')
  | [], _ => List.Sublist.slnil
  | a :: t, h => by
    have ih := filter_sublist_filter (l := t) (fun g hg => h g (List.mem_cons_of_mem _ hg))
    by_cases hp : p a = true
    · have hp' := h a (by simp) hp
      simp only [List.filter_cons, hp, hp', ↓reduceIte]
      exact ih.cons_cons a
    · by_cases hp' : p' a = true
      · simp only [List.filter_cons, hp, hp', ↓reduceIte, Bool.false_eq_true]
        exact ih.cons a
      · simp only [List.filter_cons, hp, hp', ↓reduceIte, Bool.false_eq_true]
        exact ih

omit [DecidableEq A] [DecidableEq G] in
theorem value_filter_pos (i : A) : ∀ l : List G, value v i (l.filter (fun g => decide (0 < v i g))) = value v i l
  | [] => rfl
  | a :: t => by
    have ih := value_filter_pos i t
    by_cases ha : 0 < v i a
    · simp [ha, value_cons, ih]
    · have : v i a = 0 := by omega
      simp [value_cons, ih, this]

/-- Lemma 4 for an upgrade of at most two goods. -/
theorem exists_better_small {base : G → Option A} (hb : Valid v agents goods base)
    (hgd : goods.Nodup) {x : A} (hx : x ∈ agents) {q : G → Bool}
    (hq : ∀ g ∈ goods, q g = true → base g = none) (hN : Allowed v x goods (goods.filter q))
    (hgain : value v x (hold goods base x) < value v x (goods.filter q)) (h2 : (goods.filter q).length ≤ 2) :
    ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base := by
  by_cases hfx : Frozen v agents goods base x
  · have hwalk := exists_walk (v := v) (agents := agents) (goods := goods) (base := base) agents.length [x]
      (by omega) (by simp) (by simp) (fun j hj => by simp at hj; subst hj; exact ⟨hx, hfx⟩) trivial
    rcases hwalk with ⟨Q, hQh, hQnd, hQc, hQa, l, hl, hlf⟩ | ⟨C, hCnd, hCc, hCa, c, w₀, hc, hw₀, hcw⟩
    · have hok := tradeOK_path hb (by simpa using hQh) hQnd hQc hQa hl hlf hfx hq hN hgain
      exact ⟨_, trade_valid_better hb hgd hok (fun _ h3 => absurd h3 (by omega)) (Or.inl rfl)⟩
    · have hok := tradeOK_cycle hCnd hCc hCa hc hw₀ hcw
      exact ⟨_, trade_valid_better hb hgd hok (fun h => absurd h (by simp))
        (Or.inr ⟨c, w₀, by simp [cycNext]⟩)⟩
  · exact exists_better_of_selfUpgrade hb hx (free_of_not_frozen hb hfx) q
      (fun g hg hqg => Or.inr (hq g hg hqg)) hN h2 hgain

/-- **Lemma 4** (`k4/de4.md` §3): in a valid state of a strict R1-core, if the leftover goods are worth more to a
listed agent than its holding, there is a better valid state. -/
theorem exists_better_of_threat {base : G → Option A} (hb : Valid v agents goods base)
    (hgd : goods.Nodup) (hs : Strict v agents goods) (hc : R1Core4 v agents goods) {x : A} (hx : x ∈ agents)
    (hJ : value v x (hold goods base x) < value v x (leftover goods base)) :
    ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base := by
  obtain ⟨q, hq, hN, hgain, _, hlen⟩ := exists_upgrade hb hgd hs hc hx hJ
  rcases hlen with h2 | ⟨y, hy, hytop, h3⟩
  · exact exists_better_small hb hgd hx hq hN hgain h2
  have hNsub : ∀ g ∈ goods.filter q, g ∈ goods ∧ base g = none := fun g hg =>
    ⟨(List.mem_filter.mp hg).1, hq g (List.mem_filter.mp hg).1 (List.mem_filter.mp hg).2⟩
  have hNpos := allowed_pos hN
  have hyg : y ∈ goods ∧ base y = some x := mem_hold.mp (by rw [hy]; simp)
  by_cases hfx : Frozen v agents goods base x
  · -- frozen: the walk from x
    have hwalk := exists_walk (v := v) (agents := agents) (goods := goods) (base := base) agents.length [x]
      (by omega) (by simp) (by simp) (fun j hj => by simp at hj; subst hj; exact ⟨hx, hfx⟩) trivial
    rcases hwalk with ⟨Q, hQh, hQnd, hQc, hQa, l, hl, hlf⟩ | ⟨C, hCnd, hCc, hCa, c, w₀, hc, hw₀, hcw⟩
    · have hok := tradeOK_path hb (by simpa using hQh) hQnd hQc hQa hl hlf hfx hq hN hgain
      by_cases hbig : ∀ i ∈ agents, i ≠ x → ∀ hh ∈ goods.filter q,
          value v i ((goods.filter q).erase hh) ≤ value v i (hold goods (trade base x q (nextIn Q) true) i)
      · exact ⟨_, trade_valid_better hb hgd hok (fun _ _ => hbig) (Or.inl rfl)⟩
      · -- the three-good switch: an agent threatened by the triple has an upgrade of at most two goods
        obtain ⟨i, hi⟩ := Classical.not_forall.mp hbig
        have hi' : i ∈ agents := Classical.byContradiction fun hn => hi fun h => absurd h hn
        have hix : i ≠ x := Classical.byContradiction fun hn => hi fun _ h => absurd h hn
        obtain ⟨hh, hhh⟩ : ∃ hh ∈ goods.filter q, value v i (hold goods (trade base x q (nextIn Q) true) i) <
            value v i ((goods.filter q).erase hh) := by
          refine Classical.byContradiction fun hn => hi fun _ _ hh hhm => Nat.le_of_not_lt fun hlt => hn ⟨hh, hhm, hlt⟩
        obtain ⟨hhm, hlt⟩ := hhh
        have hge := trade_value_ge hgd hok i hi'
        have hsub : ((goods.filter q).erase hh).Sublist (leftover goods base) :=
          List.erase_sublist.trans (filter_sublist_filter (fun g hg hqg => by
            simpa using hq g hg hqg))
        have hJi : value v i (hold goods base i) < value v i (leftover goods base) :=
          Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hge hlt) (value_sublist v i hsub)
        obtain ⟨qi, hqi, hNi, hgaini, hmini, hleni⟩ := exists_upgrade hb hgd hs hc hi' hJi
        rcases hleni with h2i | ⟨ai, hai, haitop, h3i⟩
        · exact exists_better_small hb hgd hi' hqi hNi hgaini h2i
        · exfalso
          -- the goods of the triple that i values all lie in i's own triple, so they are worth at most its top
          have haig : ai ∈ goods ∧ base ai = some i := mem_hold.mp (by rw [hai]; simp)
          let T := ((goods.filter q).erase hh).filter (fun g => decide (0 < v i g))
          have hTv : value v i T = value v i ((goods.filter q).erase hh) := value_filter_pos i _
          have hTnd : T.Nodup := ((hgd.filter q).sublist List.erase_sublist).sublist List.filter_sublist
          have hTmem : ∀ g ∈ T, g ∈ goods ∧ base g = none ∧ 0 < v i g := by
            intro g hg
            have h1 := List.mem_filter.mp hg
            have h2 := hNsub g (List.mem_of_mem_erase h1.1)
            exact ⟨h2.1, h2.2, by simpa using h1.2⟩
          have hNind : (goods.filter qi).Nodup := hgd.filter qi
          have hNimem : ∀ g ∈ goods.filter qi, g ∈ goods ∧ base g = none :=
            fun g hg => ⟨(List.mem_filter.mp hg).1, hqi g (List.mem_filter.mp hg).1 (List.mem_filter.mp hg).2⟩
          have hNipos := allowed_pos hNi
          have hrel : ∀ g, g ∈ goods → 0 < v i g → g ∈ relevant v i goods := fun g hg hp => by
            simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨hg, hp⟩
          have haiN : ai ∉ goods.filter qi := fun hm => by
            rw [(hNimem ai hm).2] at haig; exact absurd haig.2 (by simp)
          have hR4 := (hc i hi').2.1
          have hallrel : ∀ g ∈ relevant v i goods, g = ai ∨ g ∈ goods.filter qi := by
            have hsub' := subset_of_length_le (l₁ := ai :: goods.filter qi) (l₂ := relevant v i goods)
              (List.nodup_cons.mpr ⟨haiN, hNind⟩)
              (fun g hg => by
                rcases List.mem_cons.mp hg with rfl | hm
                · exact hrel g haig.1 (by rw [haitop]; exact topV_pos hc hi')
                · exact hrel g (hNimem g hm).1 (hNipos g hm))
              (by simp; omega)
            intro g hg
            have := hsub' g hg
            rcases List.mem_cons.mp this with e | hm
            · exact Or.inl e
            · exact Or.inr hm
          have hTN : ∀ g ∈ T, g ∈ goods.filter qi := by
            intro g hg
            obtain ⟨hgg, hgb, hgp⟩ := hTmem g hg
            rcases hallrel g (hrel g hgg hgp) with rfl | hm
            · rw [hgb] at haig; exact absurd haig.2 (by simp)
            · exact hm
          have hTlen : T.length ≤ 2 := by
            have := List.length_filter_le (fun g => decide (0 < v i g)) ((goods.filter q).erase hh)
            rw [List.length_erase_of_mem hhm, h3] at this
            exact Nat.le_trans this (by omega)
          obtain ⟨g, hgN, hgT⟩ : ∃ g ∈ goods.filter qi, g ∉ T := by
            refine Classical.byContradiction fun hn => ?_
            have hall : ∀ g ∈ goods.filter qi, g ∈ T := fun g hg =>
              Classical.byContradiction fun hgT => hn ⟨g, hg, hgT⟩
            have := List.Nodup.length_le_of_subset hNind hall
            omega
          have hTsub : ∀ g' ∈ T, g' ∈ (goods.filter qi).erase g := by
            intro g' hg'
            have hne : g' ≠ g := fun e => hgT (e ▸ hg')
            exact (List.mem_erase_of_ne hne).mpr (hTN g' hg')
          have h1 := value_le_of_subset v i hTnd (hNind.erase g) hTsub
          have h2 := hmini g hgN
          omega
    · have hok := tradeOK_cycle hCnd hCc hCa hc hw₀ hcw
      exact ⟨_, trade_valid_better hb hgd hok (fun h => absurd h (by simp))
        (Or.inr ⟨c, w₀, by simp [cycNext]⟩)⟩
  · -- free: take the top and the best... any good b of the triple: {a, b} is an upper set
    obtain ⟨b, hb₁⟩ : ∃ b, b ∈ goods.filter q := by
      match hm : goods.filter q, h3 with
      | b :: _, _ => exact ⟨b, by simp⟩
    have hbg := hNsub b hb₁
    have hyb : y ≠ b := fun e => by rw [e] at hyg; rw [hyg.2] at hbg; exact absurd hbg.2 (by simp)
    let p : G → Bool := fun g => decide (g = y ∨ g = b)
    have hLnd : (goods.filter p).Nodup := hgd.filter p
    have hLmem : ∀ g, g ∈ goods.filter p ↔ g = y ∨ g = b := by
      intro g
      simp only [List.mem_filter, p, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨hyg.1, Or.inl rfl⟩
        · exact ⟨hbg.1, Or.inr rfl⟩
    have hyb' : [y, b].Nodup := by simp [hyb]
    have hval2 : value v x (goods.filter p) = v x y + v x b := by
      have h1 := value_le_of_subset v x hLnd hyb' (fun g hg => by
        rcases (hLmem g).mp hg with rfl | rfl <;> simp)
      have h2 := value_le_of_subset v x hyb' hLnd (fun g hg => by
        simp at hg; exact (hLmem g).mpr hg)
      simp [value] at h1 h2
      simp only [value] at *
      omega
    have hlen2 : (goods.filter p).length = 2 := by
      have h1 := List.Nodup.length_le_of_subset hLnd (l₂ := [y, b]) (fun g hg => by
        rcases (hLmem g).mp hg with rfl | rfl <;> simp)
      have h2 := List.Nodup.length_le_of_subset hyb' (l₂ := goods.filter p) (fun g hg => by
        simp at hg; exact (hLmem g).mpr hg)
      simp at h1 h2
      omega
    have hbpos := hNpos b hb₁
    have hupper : IsUpper v x goods (goods.filter p) := by
      refine ⟨fun g hg => ?_, by rw [hval2, hytop]; omega, fun g hg => ?_⟩
      · rcases (hLmem g).mp hg with rfl | rfl
        · rw [hytop]; exact topV_pos hc hx
        · exact hbpos
      · have hl1 : ((goods.filter p).erase g).length ≤ 1 := by rw [List.length_erase_of_mem hg]; omega
        exact value_le_of_length_le_one' x hl1 (fun g' hg' => le_topV v x goods
          ((hLmem g').mp (List.mem_of_mem_erase hg') |>.elim (fun e => e ▸ hyg.1) (fun e => e ▸ hbg.1)))
    refine exists_better_of_selfUpgrade hb hx (free_of_not_frozen hb hfx) p (fun g hg hpg => ?_)
      (Or.inr (Or.inl hupper)) (by omega) (by rw [hy, value_singleton, hval2]; omega)
    have : g = y ∨ g = b := (hLmem g).mp (List.mem_filter.mpr ⟨hg, hpg⟩)
    rcases this with rfl | rfl
    · exact Or.inl hyg.2
    · exact Or.inr hbg.2

end lemma4

/-! ## The frame: Conjecture 11″ ⟹ TARGET₄ -/

/-- **Conjecture 11″ in its weakest form** (`k4/de4.md` §7.7): on every strict R1-core with at most four relevant
goods per agent, every valid state that is not completable and satisfies (H) has a better valid state. (H): every
listed agent holds a good; the leftover goods alone are worth at most each listed agent's holding (no Lemma 4 move);
no free listed agent has an allowed holding of at most two goods, made of its own and leftover goods, worth more than
its holding (no Lemma 4′ move). A hypothesis, never an axiom. Its strong form, which asks moreover that no level
drop, is false (V11 of `attempts/k4-de4-variants.md`). -/
def ConjDE4H (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, Valid v agents goods base → ¬ Completable v agents goods base →
      (∀ i ∈ agents, hold goods base i ≠ []) →
      (∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)) →
      (∀ x ∈ agents, (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) →
        ∀ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) →
          Allowed v x goods (goods.filter p) → (goods.filter p).length ≤ 2 →
          ¬ value v x (hold goods base x) < value v x (goods.filter p)) →
      ∃ base', Valid v agents goods base' ∧ Better v agents goods base' base

/-- Conjecture 11″ (with Lemmas 4, 4′ and Corollary 5(b), machine-checked here) implies the improvement form. -/
theorem conjDE4Imp_of_H (h : ConjDE4H A G) : ConjDE4Imp A G := by
  intro v agents goods hne hag hgd hc hs base hb hnc
  by_cases hJ : ∃ x ∈ agents, value v x (hold goods base x) < value v x (leftover goods base)
  · obtain ⟨x, hx, hJx⟩ := hJ
    exact exists_better_of_threat hb hgd hs hc hx hJx
  have hJ' : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i) :=
    fun i hi => Nat.le_of_not_lt fun hlt => hJ ⟨i, hi, hlt⟩
  by_cases hE : ∃ o ∈ agents, hold goods base o = []
  · obtain ⟨o, ho, he⟩ := hE
    exact absurd (completable_of_empty hb ho he hJ') hnc
  have hE' : ∀ i ∈ agents, hold goods base i ≠ [] := fun i hi he => hE ⟨i, hi, he⟩
  by_cases hU : ∃ x ∈ agents, (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) ∧
      ∃ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) ∧
        Allowed v x goods (goods.filter p) ∧ (goods.filter p).length ≤ 2 ∧
        value v x (hold goods base x) < value v x (goods.filter p)
  · obtain ⟨x, hx, hfree, p, hp, hN, h2, hgain⟩ := hU
    exact exists_better_of_selfUpgrade hb hx hfree p hp hN h2 hgain
  · refine h v agents goods hne hag hgd hc hs base hb hnc hE' hJ' (fun x hx hfree p hp hN h2 hgain => hU ?_)
    exact ⟨x, hx, hfree, p, hp, hN, h2, hgain⟩

/-- **Conjecture 11″ implies TARGET₄** (machine-checked: Lemmas 2, 4, 4′, Corollary 5(b), the existence of maxima
and Lemma 3): if every non-completable valid state satisfying (H) has a better valid state, every instance in which
each agent positively values at most four goods has an EFX₀ allocation. -/
theorem target4_of_conjDE4H (I : Inst) (hn : 0 < I.n) (h : ConjDE4H (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjDE4Imp I hn (conjDE4Imp_of_H h) h4


/-! ## Rotations (`k4/de4.md` Lemma 14) -/

section rotate
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- `w` takes `j`'s whole holding: it is an allowed holding of `w`, worth more to `w` than its own. Want arcs (a
frozen agent's single good) and the closed arcs of Lemma 14 (a holding that is a danger set of `w`) are such arcs. -/
def TakesAll (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (j w : A) : Prop :=
  w ∈ agents ∧ Allowed v w goods (hold goods base j) ∧ value v w (hold goods base w) < value v w (hold goods base j)

open Classical in
/-- Rotate the holdings along `σ`: every good of an agent `j` with `σ j = some w` goes to `w`. -/
noncomputable def rotate (base : G → Option A) (σ : A → Option A) : G → Option A :=
  fun g => match base g with
    | none => none
    | some j => match σ j with
      | some w => some w
      | none => some j

omit [DecidableEq G] in
omit [DecidableEq A] in
theorem rotate_eq_some {base : G → Option A} {σ : A → Option A} {g : G} {i : A} :
    rotate base σ g = some i ↔ ∃ j, base g = some j ∧ (σ j = some i ∨ (σ j = none ∧ j = i)) := by
  unfold rotate
  cases hb : base g with
  | none => simp
  | some j =>
    simp only
    cases hs : σ j with
    | some w =>
      simp only [Option.some.injEq]
      constructor
      · intro e; exact ⟨j, rfl, Or.inl (by rw [hs, e])⟩
      · rintro ⟨k, hk, h1 | ⟨h1, _⟩⟩
        · subst hk; rw [hs] at h1; exact Option.some.inj h1
        · subst hk; rw [hs] at h1; exact absurd h1 (by simp)
    | none =>
      simp only [Option.some.injEq]
      constructor
      · intro e; exact ⟨j, rfl, Or.inr ⟨hs, e⟩⟩
      · rintro ⟨k, hk, h1 | ⟨_, e⟩⟩
        · subst hk; rw [hs] at h1; exact absurd h1 (by simp)
        · subst hk; exact e

/-- **Lemma 14 in general form (rotations).** If `σ` is injective, the agents that give (`σ j = some w`) are exactly
those that receive, and every such `w` takes `j`'s whole holding (`TakesAll`), then rotating the holdings along `σ`
gives a valid state that is better. -/
theorem rotate_valid_better {base : G → Option A} (hb : Valid v agents goods base) {σ : A → Option A}
    (hgive : ∀ j w, σ j = some w → j ∈ agents ∧ TakesAll v agents goods base j w)
    (hinj : ∀ j j' w, σ j = some w → σ j' = some w → j = j')
    (hcyc : ∀ w, (∃ j, σ j = some w) ↔ σ w ≠ none)
    (hsome : ∃ j w, σ j = some w) :
    Valid v agents goods (rotate base σ) ∧ Better v agents goods (rotate base σ) base := by
  have hrecv : ∀ {j w}, σ j = some w → hold goods (rotate base σ) w = hold goods base j := by
    intro j w hjw
    unfold hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    rw [rotate_eq_some]
    constructor
    · rintro ⟨k, hk, h1 | ⟨h1, e⟩⟩
      · rw [hinj k j w h1 hjw] at hk; exact hk
      · subst e; exact absurd h1 ((hcyc k).mp ⟨j, hjw⟩)
    · intro hg; exact ⟨j, hg, Or.inl hjw⟩
  have hother : ∀ {i}, (¬ ∃ j, σ j = some i) → hold goods (rotate base σ) i = hold goods base i := by
    intro i hir
    have hsi : σ i = none := Classical.byContradiction fun hn => hir ((hcyc i).mpr hn)
    unfold hold
    apply List.filter_congr
    intro g _
    apply decide_eq_decide.mpr
    rw [rotate_eq_some]
    constructor
    · rintro ⟨k, hk, h1 | ⟨_, e⟩⟩
      · exact absurd ⟨k, h1⟩ hir
      · subst e; exact hk
    · intro hg; exact ⟨i, hg, Or.inr ⟨hsi, rfl⟩⟩
  have hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods (rotate base σ) i) := by
    intro i _
    by_cases hir : ∃ j, σ j = some i
    · obtain ⟨j, hj⟩ := hir
      rw [hrecv hj]; exact Nat.le_of_lt (hgive j i hj).2.2.2
    · rw [hother hir]; exact Nat.le_refl _
  have hvalid : Valid v agents goods (rotate base σ) := by
    refine valid_of_gain v agents goods (base := base) ?_ ?_ hval ?_ ?_
    · intro g hg j hj
      obtain ⟨k, hk, h1 | ⟨_, e⟩⟩ := rotate_eq_some.mp hj
      · exact (hgive k j h1).2.1
      · subst e; exact hb.owners g hg _ hk
    · intro i hi
      by_cases hir : ∃ j, σ j = some i
      · obtain ⟨j, hj⟩ := hir
        rw [hrecv hj]; exact (hgive j i hj).2.2.1
      · rw [hother hir]; exact hb.allowed i hi
    · intro i hi g hg hlt
      obtain ⟨j, hj, hjg⟩ := hb.v1 i hi g hg hlt
      cases hs : σ j with
      | some w => exact ⟨w, (hgive j w hs).2.1, by rw [hrecv hs]; exact hjg⟩
      | none =>
        have hjr : ¬ ∃ k, σ k = some j := fun h => (hcyc j).mp h hs
        exact ⟨j, hj, by rw [hother hjr]; exact hjg⟩
    · intro i hi j hj hij h3 hh hhm
      by_cases hjr : ∃ k, σ k = some j
      · obtain ⟨k, hk⟩ := hjr
        rw [hrecv hk] at hhm ⊢
        by_cases hik : i = k
        · subst hik
          calc value v i ((hold goods base i).erase hh) ≤ value v i (hold goods base i) :=
                value_sublist v i List.erase_sublist
            _ ≤ value v i (hold goods (rotate base σ) i) := hval i hi
        · exact Nat.le_trans (hb.v2 i hi k (hgive k j hk).1 hik hh hhm) (hval i hi)
      · rw [hother hjr] at hhm ⊢
        exact Nat.le_trans (hb.v2 i hi j hj hij hh hhm) (hval i hi)
  refine ⟨hvalid, better_of_monotone v agents goods ?_ hval ?_⟩
  · intro i hi
    by_cases hir : ∃ j, σ j = some i
    · obtain ⟨j, hj⟩ := hir
      rw [hrecv hj]
      exact level_mono v i goods (hb.allowed i hi) (hgive j i hj).2.2.1
        (fun g hg => mem_goods_of_mem_hold hg) (fun g hg => mem_goods_of_mem_hold hg) (hgive j i hj).2.2.2
    · rw [hother hir]; exact Nat.le_refl _
  · obtain ⟨j, w, hjw⟩ := hsome
    exact ⟨w, (hgive j w hjw).2.1, by rw [hrecv hjw]; exact (hgive j w hjw).2.2.2⟩

end rotate

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.value_cons_erase
#print axioms EFX.DE4.value_le_of_subset
#print axioms EFX.DE4.filter_erase_eq
#print axioms EFX.DE4.shrink
#print axioms EFX.DE4.length_append_le
#print axioms EFX.DE4.subset_of_length_le
#print axioms EFX.DE4.value_le_of_length_le_one'
#print axioms EFX.DE4.nodup_hold
#print axioms EFX.DE4.leftover_le
#print axioms EFX.DE4.strict_ne
#print axioms EFX.DE4.topV_pos
#print axioms EFX.DE4.allowed_pos
#print axioms EFX.DE4.exists_upgrade
#print axioms EFX.DE4.trade_eq_some
#print axioms EFX.DE4.hold_trade_recv
#print axioms EFX.DE4.hold_trade_up
#print axioms EFX.DE4.hold_trade_other
#print axioms EFX.DE4.trade_valid_better
#print axioms EFX.DE4.isChain_cons
#print axioms EFX.DE4.isChain_tail
#print axioms EFX.DE4.isChain_append
#print axioms EFX.DE4.isChain_right
#print axioms EFX.DE4.nextIn_none_of_not_mem
#print axioms EFX.DE4.nextIn_spec
#print axioms EFX.DE4.isChain_true
#print axioms EFX.DE4.nextIn_mem_tail
#print axioms EFX.DE4.nextIn_inj
#print axioms EFX.DE4.exists_nextIn_of_mem_tail
#print axioms EFX.DE4.nextIn_last
#print axioms EFX.DE4.nextIn_some
#print axioms EFX.DE4.fromFirst_suffix
#print axioms EFX.DE4.fromFirst_sublist
#print axioms EFX.DE4.fromFirst_head
#print axioms EFX.DE4.fromFirst_getLast
#print axioms EFX.DE4.free_of_not_frozen
#print axioms EFX.DE4.wantsGood_of_frozen
#print axioms EFX.DE4.exists_walk
#print axioms EFX.DE4.tradeOK_path
#print axioms EFX.DE4.tradeOK_cycle
#print axioms EFX.DE4.trade_value_ge
#print axioms EFX.DE4.filter_sublist_filter
#print axioms EFX.DE4.value_filter_pos
#print axioms EFX.DE4.exists_better_small
#print axioms EFX.DE4.exists_better_of_threat
#print axioms EFX.DE4.conjDE4Imp_of_H
#print axioms EFX.DE4.target4_of_conjDE4H
#print axioms EFX.DE4.rotate_eq_some
#print axioms EFX.DE4.rotate_valid_better
#print axioms EFX.DE4.allowed_of_minimal
