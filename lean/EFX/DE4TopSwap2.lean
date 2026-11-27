import EFX.DE4LowerPair

/-!
# Lemma 27′ for two lower-pair holders: the double top swap (`k4/de4.md` §10.4; ledger K4.DE4V3R.L27)

Two lower-pair holders `u₁`, `u₂` take their tops `a₁`, `a₂` from the agents `t₁`, `t₂` holding them alone, and each
`tᵢ` takes the good `jᵢ` it values just below `aᵢ`, a leftover good or a good of `u₁`'s or `u₂`'s pair (the other goods
of the pairs are released). Unless some `tᵢ` threatens a holding of three or more goods with `v(jᵢ)`, the state is
valid, its robust level sum does not drop, and it has fewer lower-pair holders. So a maximum of the lower-pair order
admits no double top swap. In GM4-B's double clash this is the case where each frozen agent's b lies in the other
lower-pair holder's pair (Corollary 28(c)).

**Results.** `t_pair_bound`; `topSwap2`, `TopSwap2Hyp`; `hold_topSwap2_u1`, `_u2`, `_t1`, `_t2`, `_other`;
`topSwap2_valid`, `topSwap2_numLP`, `topSwap2_potentialR`, `top_swap2`; `not_maxLP_of_top_swap2`.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section topswap2
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- An agent `t` holding `[a]` alone, with nothing strictly between `j` and `a`, values every good of another
holding of at most two goods at most `v_t(j)` (a better good would be wanted by `t` and so held alone). -/
theorem t_pair_bound {base : G → Option A} (hb : Valid v agents goods base) {t : A} (ht : t ∈ agents) {a j : G}
    (hta : hold goods base t = [a]) (hjust : ∀ g ∈ goods, g ≠ a → v t j < v t g → v t a < v t g)
    {k : A} (hkt : k ≠ t) (hlen : (hold goods base k).length ≤ 2) {h : G} (hh : h ∈ hold goods base k) :
    value v t ((hold goods base k).erase h) ≤ v t j := by
  have hl1 : ((hold goods base k).erase h).length ≤ 1 := by rw [List.length_erase_of_mem hh]; omega
  match he : (hold goods base k).erase h, hl1 with
  | [], _ => simp
  | [g'], _ =>
    have hg'm : g' ∈ hold goods base k := List.mem_of_mem_erase (by rw [he]; simp)
    rw [value_singleton]
    refine Nat.le_of_not_lt fun hlt => ?_
    have hg'g := (mem_hold.mp hg'm).1
    have hbk := (mem_hold.mp hg'm).2
    have hbt : base a = some t := (mem_hold.mp (by rw [hta]; simp : a ∈ hold goods base t)).2
    have hg'a : g' ≠ a := fun e => by rw [e, hbt] at hbk; exact hkt (Option.some.inj hbk).symm
    have h1 := hjust g' hg'g hg'a hlt
    have h2 : value v t (hold goods base t) < v t g' := by rw [hta, value_singleton]; exact h1
    obtain ⟨k', _, hk'g⟩ := hb.v1 t ht g' hg'g h2
    have hk'k : k' = k := by
      have : g' ∈ hold goods base k' := by rw [hk'g]; simp
      rw [(mem_hold.mp this).2] at hbk; exact Option.some.inj hbk
    subst hk'k
    have := List.length_erase_of_mem hh
    rw [he, hk'g] at this; simp at this

/-- The double top swap. -/
def topSwap2 (base : G → Option A) (u₁ u₂ t₁ t₂ : A) (a₁ a₂ j₁ j₂ : G) : G → Option A :=
  fun g => if g = a₁ then some u₁ else if g = a₂ then some u₂ else if g = j₁ then some t₁ else
    if g = j₂ then some t₂ else if base g = some u₁ ∨ base g = some u₂ then none else base g

/-- The hypotheses of the double top swap on a valid state. -/
structure TopSwap2Hyp (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A)
    (u₁ u₂ t₁ t₂ : A) (a₁ a₂ j₁ j₂ : G) : Prop where
  hu₁ : u₁ ∈ agents
  hu₂ : u₂ ∈ agents
  ht₁ : t₁ ∈ agents
  ht₂ : t₂ ∈ agents
  hu : u₁ ≠ u₂
  ht : t₁ ≠ t₂
  h11 : u₁ ≠ t₁
  h12 : u₁ ≠ t₂
  h21 : u₂ ≠ t₁
  h22 : u₂ ≠ t₂
  hlp₁ : IsLowerPair v u₁ goods (hold goods base u₁)
  hlp₂ : IsLowerPair v u₂ goods (hold goods base u₂)
  ha₁ : a₁ ∈ goods
  ha₂ : a₂ ∈ goods
  hat₁ : v u₁ a₁ = topV v u₁ goods
  hat₂ : v u₂ a₂ = topV v u₂ goods
  hta₁ : hold goods base t₁ = [a₁]
  hta₂ : hold goods base t₂ = [a₂]
  hj₁ : j₁ ∈ goods
  hj₂ : j₂ ∈ goods
  hjb₁ : base j₁ = none ∨ base j₁ = some u₁ ∨ base j₁ = some u₂
  hjb₂ : base j₂ = none ∨ base j₂ = some u₁ ∨ base j₂ = some u₂
  hj : j₁ ≠ j₂
  hj0₁ : 0 < v t₁ j₁
  hj0₂ : 0 < v t₂ j₂
  hja₁ : v t₁ j₁ < v t₁ a₁
  hja₂ : v t₂ j₂ < v t₂ a₂
  hjust₁ : ∀ g ∈ goods, g ≠ a₁ → v t₁ j₁ < v t₁ g → v t₁ a₁ < v t₁ g
  hjust₂ : ∀ g ∈ goods, g ≠ a₂ → v t₂ j₂ < v t₂ g → v t₂ a₂ < v t₂ g
  htrip₁ : ∀ y ∈ agents, y ≠ u₁ → y ≠ u₂ → y ≠ t₁ → y ≠ t₂ → 3 ≤ (hold goods base y).length →
    ∀ h ∈ hold goods base y, value v t₁ ((hold goods base y).erase h) ≤ v t₁ j₁
  htrip₂ : ∀ y ∈ agents, y ≠ u₁ → y ≠ u₂ → y ≠ t₁ → y ≠ t₂ → 3 ≤ (hold goods base y).length →
    ∀ h ∈ hold goods base y, value v t₂ ((hold goods base y).erase h) ≤ v t₂ j₂

variable {base : G → Option A} {u₁ u₂ t₁ t₂ : A} {a₁ a₂ j₁ j₂ : G}

theorem TopSwap2Hyp.base_a₁ (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) : base a₁ = some t₁ :=
  (mem_hold.mp (by rw [H.hta₁]; simp : a₁ ∈ hold goods base t₁)).2

theorem TopSwap2Hyp.base_a₂ (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) : base a₂ = some t₂ :=
  (mem_hold.mp (by rw [H.hta₂]; simp : a₂ ∈ hold goods base t₂)).2

theorem TopSwap2Hyp.eq_a₁ (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) {g : G} (hg : g ∈ goods)
    (h : base g = some t₁) : g = a₁ := by
  have : g ∈ hold goods base t₁ := mem_hold.mpr ⟨hg, h⟩
  rw [H.hta₁] at this; simpa using this

theorem TopSwap2Hyp.eq_a₂ (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) {g : G} (hg : g ∈ goods)
    (h : base g = some t₂) : g = a₂ := by
  have : g ∈ hold goods base t₂ := mem_hold.mpr ⟨hg, h⟩
  rw [H.hta₂] at this; simpa using this

theorem TopSwap2Hyp.ne_a (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) : a₁ ≠ a₂ := by
  intro e; have h1 := H.base_a₁; rw [e, H.base_a₂] at h1; exact H.ht (Option.some.inj h1).symm

omit [DecidableEq A] [DecidableEq G] in
/-- A good whose holder in `base` is `none`, `u₁` or `u₂` is not held by `t`. -/
theorem ne_of_jb {g : G} {t : A} (ht1 : t ≠ u₁) (ht2 : t ≠ u₂)
    (hg : base g = none ∨ base g = some u₁ ∨ base g = some u₂) : base g ≠ some t := by
  rcases hg with h | h | h <;> rw [h] <;> simp [Ne.symm ht1, Ne.symm ht2]

theorem TopSwap2Hyp.ne_aj (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    a₁ ≠ j₁ ∧ a₁ ≠ j₂ ∧ a₂ ≠ j₁ ∧ a₂ ≠ j₂ := by
  have n1 := ne_of_jb (t := t₁) (Ne.symm H.h11) (Ne.symm H.h21) H.hjb₁
  have n2 := ne_of_jb (t := t₁) (Ne.symm H.h11) (Ne.symm H.h21) H.hjb₂
  have n3 := ne_of_jb (t := t₂) (Ne.symm H.h12) (Ne.symm H.h22) H.hjb₁
  have n4 := ne_of_jb (t := t₂) (Ne.symm H.h12) (Ne.symm H.h22) H.hjb₂
  refine ⟨fun e => n1 (e ▸ H.base_a₁), fun e => n2 (e ▸ H.base_a₁), fun e => n3 (e ▸ H.base_a₂),
    fun e => n4 (e ▸ H.base_a₂)⟩

theorem topSwap2_at_a1 : topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ a₁ = some u₁ := by simp [topSwap2]

theorem topSwap2_at_a2 (h : a₂ ≠ a₁) : topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ a₂ = some u₂ := by
  simp [topSwap2, h]

theorem topSwap2_at_j1 (h1 : j₁ ≠ a₁) (h2 : j₁ ≠ a₂) : topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ j₁ = some t₁ := by
  simp [topSwap2, h1, h2]

theorem topSwap2_at_j2 (h1 : j₂ ≠ a₁) (h2 : j₂ ≠ a₂) (h3 : j₂ ≠ j₁) :
    topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ j₂ = some t₂ := by
  simp [topSwap2, h1, h2, h3]

theorem topSwap2_at_else {g : G} (h1 : g ≠ a₁) (h2 : g ≠ a₂) (h3 : g ≠ j₁) (h4 : g ≠ j₂) :
    topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = if base g = some u₁ ∨ base g = some u₂ then none else base g := by
  simp [topSwap2, h1, h2, h3, h4]

/-- The new holder of each good, by cases. -/
theorem topSwap2_cases (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) (g : G) :
    (g = a₁ ∧ topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = some u₁) ∨
    (g = a₂ ∧ topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = some u₂) ∨
    (g = j₁ ∧ topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = some t₁) ∨
    (g = j₂ ∧ topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = some t₂) ∨
    (g ≠ a₁ ∧ g ≠ a₂ ∧ g ≠ j₁ ∧ g ≠ j₂ ∧ (base g = some u₁ ∨ base g = some u₂) ∧
      topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = none) ∨
    (g ≠ a₁ ∧ g ≠ a₂ ∧ g ≠ j₁ ∧ g ≠ j₂ ∧ ¬ (base g = some u₁ ∨ base g = some u₂) ∧
      topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = base g) := by
  obtain ⟨n11, n12, n21, n22⟩ := H.ne_aj
  by_cases g1 : g = a₁
  · subst g1; exact Or.inl ⟨rfl, topSwap2_at_a1⟩
  by_cases g2 : g = a₂
  · subst g2; exact Or.inr (Or.inl ⟨rfl, topSwap2_at_a2 g1⟩)
  by_cases g3 : g = j₁
  · subst g3; exact Or.inr (Or.inr (Or.inl ⟨rfl, topSwap2_at_j1 g1 g2⟩))
  by_cases g4 : g = j₂
  · subst g4; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, topSwap2_at_j2 g1 g2 g3⟩)))
  rw [topSwap2_at_else g1 g2 g3 g4]
  by_cases hb : base g = some u₁ ∨ base g = some u₂
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g1, g2, g3, g4, hb, by simp [hb]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g1, g2, g3, g4, hb, by simp [hb]⟩))))

theorem hold_topSwap2_eq (i : A) (c : G)
    (hpos : ∀ g ∈ goods, topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = some i ↔ g = c) (hgd : goods.Nodup)
    (hc : c ∈ goods) : hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i = [c] := by
  have : hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i = goods.filter (fun g => decide (g = c)) := by
    unfold hold
    apply List.filter_congr
    intro g hg
    have hiff := hpos g hg
    by_cases h : g = c
    · rw [hiff.mpr h]; simp [h]
    · have hz : ¬ topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂ g = some i := fun e => h (hiff.mp e)
      simp [h, hz]
  rw [this]; exact filter_eq_single hgd hc

theorem hold_topSwap2_u1 (hgd : goods.Nodup) (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) u₁ = [a₁] := by
  refine hold_topSwap2_eq u₁ a₁ (fun g _ => ?_) hgd H.ha₁
  rcases topSwap2_cases H g with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨g1, -, -, -, -, h⟩ | ⟨g1, -, -, -, hb, h⟩
  · exact ⟨fun _ => e, fun _ => h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.hu),
      fun hh => absurd (e.symm.trans hh) (Ne.symm H.ne_a)⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h11),
      fun hh => absurd (e.symm.trans hh) (Ne.symm H.ne_aj.1)⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h12),
      fun hh => absurd (e.symm.trans hh) (Ne.symm H.ne_aj.2.1)⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh g1⟩
  · exact ⟨fun hh => absurd (Or.inl (h.symm.trans hh)) hb, fun hh => absurd hh g1⟩

theorem hold_topSwap2_u2 (hgd : goods.Nodup) (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) u₂ = [a₂] := by
  refine hold_topSwap2_eq u₂ a₂ (fun g _ => ?_) hgd H.ha₂
  rcases topSwap2_cases H g with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, g2, -, -, -, h⟩ | ⟨-, g2, -, -, hb, h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.hu,
      fun hh => absurd (e.symm.trans hh) H.ne_a⟩
  · exact ⟨fun _ => e, fun _ => h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h21),
      fun hh => absurd (e.symm.trans hh) (Ne.symm H.ne_aj.2.2.1)⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h22),
      fun hh => absurd (e.symm.trans hh) (Ne.symm H.ne_aj.2.2.2)⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh g2⟩
  · exact ⟨fun hh => absurd (Or.inr (h.symm.trans hh)) hb, fun hh => absurd hh g2⟩

theorem hold_topSwap2_t1 (hgd : goods.Nodup) (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) t₁ = [j₁] := by
  refine hold_topSwap2_eq t₁ j₁ (fun g hg => ?_) hgd H.hj₁
  rcases topSwap2_cases H g with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, -, g3, -, -, h⟩ | ⟨g1, -, g3, -, -, h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h11,
      fun hh => absurd (e.symm.trans hh) H.ne_aj.1⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h21,
      fun hh => absurd (e.symm.trans hh) H.ne_aj.2.2.1⟩
  · exact ⟨fun _ => e, fun _ => h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.ht),
      fun hh => absurd (e.symm.trans hh) (Ne.symm H.hj)⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh g3⟩
  · exact ⟨fun hh => absurd (H.eq_a₁ hg (h.symm.trans hh)) g1, fun hh => absurd hh g3⟩

theorem hold_topSwap2_t2 (hgd : goods.Nodup) (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) t₂ = [j₂] := by
  refine hold_topSwap2_eq t₂ j₂ (fun g hg => ?_) hgd H.hj₂
  rcases topSwap2_cases H g with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, -, -, g4, -, h⟩ | ⟨-, g2, -, g4, -, h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h12,
      fun hh => absurd (e.symm.trans hh) H.ne_aj.2.1⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h22,
      fun hh => absurd (e.symm.trans hh) H.ne_aj.2.2.2⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.ht,
      fun hh => absurd (e.symm.trans hh) H.hj⟩
  · exact ⟨fun _ => e, fun _ => h⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh g4⟩
  · exact ⟨fun hh => absurd (H.eq_a₂ hg (h.symm.trans hh)) g2, fun hh => absurd hh g4⟩

theorem hold_topSwap2_other (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) {i : A}
    (i1 : i ≠ u₁) (i2 : i ≠ u₂) (i3 : i ≠ t₁) (i4 : i ≠ t₂) :
    hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i = hold goods base i := by
  unfold hold
  apply List.filter_congr
  intro g _
  rcases topSwap2_cases H g with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, -, -, -, hb, h⟩ | ⟨-, -, -, -, -, h⟩
  · rw [h, e, H.base_a₁]; simp [Ne.symm i1, Ne.symm i3]
  · rw [h, e, H.base_a₂]; simp [Ne.symm i2, Ne.symm i4]
  · rw [h, e]; simp [ne_of_jb (t := i) i1 i2 H.hjb₁, Ne.symm i3]
  · rw [h, e]; simp [ne_of_jb (t := i) i1 i2 H.hjb₂, Ne.symm i4]
  · have : base g ≠ some i := by rcases hb with h' | h' <;> rw [h'] <;> simp [Ne.symm i1, Ne.symm i2]
    rw [h]; simp [this]
  · rw [h]

theorem topSwap2_valid (hgd : goods.Nodup) (hb : Valid v agents goods base)
    (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    Valid v agents goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) := by
  have hU1 := hold_topSwap2_u1 hgd H
  have hU2 := hold_topSwap2_u2 hgd H
  have hT1 := hold_topSwap2_t1 hgd H
  have hT2 := hold_topSwap2_t2 hgd H
  have hO := fun {i : A} (i1 : i ≠ u₁) (i2 : i ≠ u₂) (i3 : i ≠ t₁) (i4 : i ≠ t₂) => hold_topSwap2_other H i1 i2 i3 i4
  have hlen1 : (hold goods base u₁).length = 2 := H.hlp₁.2.1
  have hlen2 : (hold goods base u₂).length = 2 := H.hlp₂.2.1
  have halone : ∀ k ∈ agents, ∀ g, hold goods base k = [g] →
      ∃ k' ∈ agents, hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) k' = [g] := by
    intro k hk g hkg
    by_cases k1 : k = u₁
    · subst k1; rw [hkg] at hlen1; simp at hlen1
    · by_cases k2 : k = u₂
      · subst k2; rw [hkg] at hlen2; simp at hlen2
      · by_cases k3 : k = t₁
        · subst k3
          have : g = a₁ := by rw [H.hta₁] at hkg; simpa using hkg.symm
          subst this; exact ⟨u₁, H.hu₁, hU1⟩
        · by_cases k4 : k = t₂
          · subst k4
            have : g = a₂ := by rw [H.hta₂] at hkg; simpa using hkg.symm
            subst this; exact ⟨u₂, H.hu₂, hU2⟩
          · exact ⟨k, hk, by rw [hO k1 k2 k3 k4]; exact hkg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- owners
    intro g hg k hk
    rcases topSwap2_cases H g with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ <;>
      rw [h] at hk
    · cases hk; exact H.hu₁
    · cases hk; exact H.hu₂
    · cases hk; exact H.ht₁
    · cases hk; exact H.ht₂
    · cases hk
    · exact hb.owners g hg k hk
  · -- allowed
    intro i hi
    by_cases i1 : i = u₁
    · subst i1; rw [hU1]
      exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; have := H.hlp₁.2.2.2.1; have := H.hat₁; omega⟩
    · by_cases i2 : i = u₂
      · subst i2; rw [hU2]
        exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; have := H.hlp₂.2.2.2.1; have := H.hat₂; omega⟩
      · by_cases i3 : i = t₁
        · subst i3; rw [hT1]; exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; exact H.hj0₁⟩
        · by_cases i4 : i = t₂
          · subst i4; rw [hT2]; exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; exact H.hj0₂⟩
          · rw [hO i1 i2 i3 i4]; exact hb.allowed i hi
  · -- (V1)
    intro i hi g hg hlt
    by_cases i1 : i = u₁
    · subst i1; rw [hU1, value_singleton, H.hat₁] at hlt
      have := le_topV v i goods hg; omega
    · by_cases i2 : i = u₂
      · subst i2; rw [hU2, value_singleton, H.hat₂] at hlt
        have := le_topV v i goods hg; omega
      · by_cases i3 : i = t₁
        · subst i3; rw [hT1, value_singleton] at hlt
          by_cases ga : g = a₁
          · subst ga; exact ⟨u₁, H.hu₁, hU1⟩
          · have h2 : value v i (hold goods base i) < v i g := by
              rw [H.hta₁, value_singleton]; exact H.hjust₁ g hg ga hlt
            obtain ⟨k, hk, hkg⟩ := hb.v1 i hi g hg h2
            exact halone k hk g hkg
        · by_cases i4 : i = t₂
          · subst i4; rw [hT2, value_singleton] at hlt
            by_cases ga : g = a₂
            · subst ga; exact ⟨u₂, H.hu₂, hU2⟩
            · have h2 : value v i (hold goods base i) < v i g := by
                rw [H.hta₂, value_singleton]; exact H.hjust₂ g hg ga hlt
              obtain ⟨k, hk, hkg⟩ := hb.v1 i hi g hg h2
              exact halone k hk g hkg
          · rw [hO i1 i2 i3 i4] at hlt
            obtain ⟨k, hk, hkg⟩ := hb.v1 i hi g hg hlt
            exact halone k hk g hkg
  · -- (V2)
    intro i hi k hk hik h hh
    by_cases k1 : k = u₁
    · subst k1; rw [hU1] at hh ⊢; simp at hh; subst hh; simp
    · by_cases k2 : k = u₂
      · subst k2; rw [hU2] at hh ⊢; simp at hh; subst hh; simp
      · by_cases k3 : k = t₁
        · subst k3; rw [hT1] at hh ⊢; simp at hh; subst hh; simp
        · by_cases k4 : k = t₂
          · subst k4; rw [hT2] at hh ⊢; simp at hh; subst hh; simp
          · rw [hO k1 k2 k3 k4] at hh ⊢
            by_cases i1 : i = u₁
            · subst i1; rw [hU1, value_singleton, H.hat₁]
              have := hb.v2 i hi k hk hik h hh
              have := H.hlp₁.2.2.2.1
              omega
            · by_cases i2 : i = u₂
              · subst i2; rw [hU2, value_singleton, H.hat₂]
                have := hb.v2 i hi k hk hik h hh
                have := H.hlp₂.2.2.2.1
                omega
              · by_cases i3 : i = t₁
                · subst i3; rw [hT1, value_singleton]
                  by_cases h3 : 3 ≤ (hold goods base k).length
                  · exact H.htrip₁ k hk k1 k2 k3 k4 h3 h hh
                  · exact t_pair_bound hb H.ht₁ H.hta₁ H.hjust₁ k3 (by omega) hh
                · by_cases i4 : i = t₂
                  · subst i4; rw [hT2, value_singleton]
                    by_cases h3 : 3 ≤ (hold goods base k).length
                    · exact H.htrip₂ k hk k1 k2 k3 k4 h3 h hh
                    · exact t_pair_bound hb H.ht₂ H.hta₂ H.hjust₂ k4 (by omega) hh
                  · rw [hO i1 i2 i3 i4]; exact hb.v2 i hi k hk hik h hh

theorem topSwap2_numLP (hgd : goods.Nodup) (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    numLP v agents goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) < numLP v agents goods base := by
  classical
  have hU1 := hold_topSwap2_u1 hgd H
  have hU2 := hold_topSwap2_u2 hgd H
  have hT1 := hold_topSwap2_t1 hgd H
  have hT2 := hold_topSwap2_t2 hgd H
  have hsingle : ∀ i, (∃ g, hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i = [g]) →
      ¬ IsLowerPair v i goods (hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i) := by
    intro i ⟨g, hg⟩ h; rw [hg] at h; have := h.2.1; simp at this
  unfold numLP
  apply sum_map_lt
  · intro i _
    by_cases i1 : i = u₁
    · subst i1; simp [hsingle _ ⟨a₁, hU1⟩]
    · by_cases i2 : i = u₂
      · subst i2; simp [hsingle _ ⟨a₂, hU2⟩]
      · by_cases i3 : i = t₁
        · subst i3; simp [hsingle _ ⟨j₁, hT1⟩]
        · by_cases i4 : i = t₂
          · subst i4; simp [hsingle _ ⟨j₂, hT2⟩]
          · rw [hold_topSwap2_other H i1 i2 i3 i4]; exact Nat.le_refl _
  · exact ⟨u₁, H.hu₁, by simp [hsingle _ ⟨a₁, hU1⟩, H.hlp₁]⟩

theorem topSwap2_potentialR (hag : agents.Nodup) (hgd : goods.Nodup)
    (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    potentialR v agents goods base ≤ potentialR v agents goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) := by
  have hU1 := hold_topSwap2_u1 hgd H
  have hU2 := hold_topSwap2_u2 hgd H
  have hT1 := hold_topSwap2_t1 hgd H
  have hT2 := hold_topSwap2_t2 hgd H
  let F := fun i => levelR v i goods (hold goods base i)
  let Gf := fun i => levelR v i goods (hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i)
  have hup : ∀ {u : A} {a : G}, IsLowerPair v u goods (hold goods base u) → a ∈ goods →
      v u a = topV v u goods → hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) u = [a] → F u + 1 = Gf u := by
    intro u a hlp ha hat hZ
    show levelR v u goods (hold goods base u) + 1 = levelR v u goods (hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) u)
    rw [levelR_lowerPair hlp, hZ, levelR_single u a ha, level_single]
    have h0 := filter_len_le (l := relevant v u goods) (p := fun g' => decide (v u a < v u g'))
      (q := fun _ => false) (fun g hg hp => by
        have := le_topV v u goods (List.mem_filter.mp hg).1
        simp only [decide_eq_true_eq] at hp; omega)
    have h1 : ((relevant v u goods).filter (fun _ => false)).length = 0 := by simp
    omega
  have hdown : ∀ {t : A} {a j : G}, hold goods base t = [a] → a ∈ goods → j ∈ goods →
      (∀ g ∈ goods, g ≠ a → v t j < v t g → v t a < v t g) →
      hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) t = [j] → F t ≤ Gf t + 1 := by
    intro t a j hta ha hj hjust hZ
    show levelR v t goods (hold goods base t) ≤ levelR v t goods (hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) t) + 1
    rw [hta, hZ, levelR_single t a ha, levelR_single t j hj, level_single, level_single]
    have := filter_len_le_succ (l := relevant v t goods) (hgd.filter _) (p := fun g' => decide (v t j < v t g'))
      (q := fun g' => decide (v t a < v t g')) (a := a) (fun g hg hp => by
        simp only [decide_eq_true_eq] at hp ⊢
        by_cases hga : g = a
        · exact Or.inl hga
        · exact Or.inr (hjust g (List.mem_filter.mp hg).1 hga hp))
    omega
  have e1 := hup H.hlp₁ H.ha₁ H.hat₁ hU1
  have e2 := hup H.hlp₂ H.ha₂ H.hat₂ hU2
  have d1 := hdown H.hta₁ H.ha₁ H.hj₁ H.hjust₁ hT1
  have d2 := hdown H.hta₂ H.ha₂ H.hj₂ H.hjust₂ hT2
  have hpt : ∀ i ∈ agents, (F i + (if i = u₁ then 1 else 0)) + (if i = u₂ then 1 else 0) ≤
      (Gf i + (if i = t₁ then 1 else 0)) + (if i = t₂ then 1 else 0) := by
    intro i _
    by_cases i1 : i = u₁
    · subst i1; simp [H.hu, H.h11, H.h12]; omega
    · by_cases i2 : i = u₂
      · subst i2; simp [i1, H.h21, H.h22]; omega
      · by_cases i3 : i = t₁
        · subst i3; simp [i1, i2, H.ht]; omega
        · by_cases i4 : i = t₂
          · subst i4; simp [i1, i2, i3]; omega
          · simp [i1, i2, i3, i4]
            show levelR v i goods (hold goods base i) ≤
              levelR v i goods (hold goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) i)
            rw [hold_topSwap2_other H i1 i2 i3 i4]
            exact Nat.le_refl _
  have h1 := sum_map_le hpt
  rw [sum_map_ind hag H.hu₂ (fun i => F i + if i = u₁ then 1 else 0),
    sum_map_ind hag H.ht₂ (fun i => Gf i + if i = t₁ then 1 else 0),
    sum_map_ind hag H.hu₁ F, sum_map_ind hag H.ht₁ Gf] at h1
  show (agents.map F).sum ≤ (agents.map Gf).sum
  omega

/-- **The double top swap** (Lemma 27′ with two lower-pair holders): valid, the robust level sum does not drop, fewer
lower-pair holders. -/
theorem top_swap2 (hag : agents.Nodup) (hgd : goods.Nodup) (hb : Valid v agents goods base)
    (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) :
    Valid v agents goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) ∧
      potentialR v agents goods base ≤ potentialR v agents goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) ∧
      numLP v agents goods (topSwap2 base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) < numLP v agents goods base :=
  ⟨topSwap2_valid hgd hb H, topSwap2_potentialR hag hgd H, topSwap2_numLP hgd H⟩

/-- A maximum of the lower-pair order admits no double top swap. -/
theorem not_maxLP_of_top_swap2 (hag : agents.Nodup) (hgd : goods.Nodup) (hmax : IsMaximumLP v agents goods base)
    (H : TopSwap2Hyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j₁ j₂) : False := by
  obtain ⟨hZ, hP, hN⟩ := top_swap2 hag hgd hmax.1.1 H
  obtain ⟨Z', hZ', hP', hN'⟩ := exists_validV3_numLP hgd _ _ (Nat.le_refl _) hZ
  rcases Nat.lt_or_eq_of_le (Nat.le_trans hP hP') with hlt | heq
  · exact hmax.2 Z' hZ' (Or.inl hlt)
  · exact hmax.2 Z' hZ' (Or.inr (Or.inl ⟨heq, by omega⟩))

end topswap2

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.t_pair_bound
#print axioms EFX.DE4.TopSwap2Hyp.base_a₁
#print axioms EFX.DE4.TopSwap2Hyp.base_a₂
#print axioms EFX.DE4.TopSwap2Hyp.eq_a₁
#print axioms EFX.DE4.TopSwap2Hyp.eq_a₂
#print axioms EFX.DE4.TopSwap2Hyp.ne_a
#print axioms EFX.DE4.ne_of_jb
#print axioms EFX.DE4.topSwap2_at_a1
#print axioms EFX.DE4.topSwap2_at_a2
#print axioms EFX.DE4.topSwap2_at_j1
#print axioms EFX.DE4.topSwap2_at_j2
#print axioms EFX.DE4.topSwap2_at_else
#print axioms EFX.DE4.topSwap2_cases
#print axioms EFX.DE4.hold_topSwap2_eq
#print axioms EFX.DE4.TopSwap2Hyp.ne_aj
#print axioms EFX.DE4.hold_topSwap2_u1
#print axioms EFX.DE4.hold_topSwap2_u2
#print axioms EFX.DE4.hold_topSwap2_t1
#print axioms EFX.DE4.hold_topSwap2_t2
#print axioms EFX.DE4.hold_topSwap2_other
#print axioms EFX.DE4.topSwap2_valid
#print axioms EFX.DE4.topSwap2_numLP
#print axioms EFX.DE4.topSwap2_potentialR
#print axioms EFX.DE4.top_swap2
#print axioms EFX.DE4.not_maxLP_of_top_swap2
