import EFX.DE4TopSwap2
import EFX.DE4LowerPairFrame

/-!
# Lemma 30(a): the cross swap (`k4/de4.md` §10.4; ledger K4.DE4V3R.L27)

In GM4-B's double clash, let `t₁` (holding `a₁`, the top of the lower-pair holder `u₁`) have the danger set
`{j, g}` with `j` leftover and `g` in `u₂`'s lower pair, worth more than its top, and let `t₂` (holding `a₂`, the top of
`u₂`) have its next good `b₂` in one of the two lower pairs, `b₂ ≠ g`. The cross swap gives `u₁`, `u₂` their tops,
`t₁` the upper set `{j, g}` and `t₂` the good `b₂`, and releases the rest of the two pairs. Unless `t₁` or `t₂` threatens
a holding of three or more goods, the state is valid and its robust level sum is larger by at least 2: so no top state
(in particular no maximum of the robust order or of the lower-pair order) admits a cross swap.

**Results.** `hold_eq_filter`, `pair_value`, `five_le_levelR_of_upper`; `crossSwap`, `CrossHyp`, the holdings
`hold_cross_u1`, `_u2`, `_t1`, `_t2`, `_other`; `crossSwap_valid`, `crossSwap_potentialR`, `crossSwap_numLP`,
`cross_swap`, `not_top_of_cross_swap`.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section cross
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq G] in
theorem hold_eq_filter {base : G → Option A} {i : A} {P : G → Prop} [DecidablePred P]
    (h : ∀ x ∈ goods, base x = some i ↔ P x) : hold goods base i = goods.filter (fun x => decide (P x)) := by
  unfold hold
  apply List.filter_congr
  intro x hx
  by_cases hp : P x
  · simp [hp, (h x hx).mpr hp]
  · have : ¬ base x = some i := fun e => hp ((h x hx).mp e)
    simp [hp, this]

omit [DecidableEq A] in
/-- A duplicate-free list whose elements are exactly `j` and `g` (distinct). -/
theorem pair_value (i : A) {S : List G} (hnd : S.Nodup) {j g : G} (hjg : j ≠ g) (hmem : ∀ x, x ∈ S ↔ x = j ∨ x = g) :
    value v i S = v i j + v i g ∧ S.erase j = [g] ∧ S.erase g = [j] := by
  have hjS : j ∈ S := (hmem j).mpr (Or.inl rfl)
  have hgS : g ∈ S := (hmem g).mpr (Or.inr rfl)
  have e1 : S.erase j = [g] := by
    have hnd' := hnd.erase j
    have hall : ∀ x ∈ S.erase j, x = g := by
      intro x hx
      rcases (hmem x).mp (List.mem_of_mem_erase hx) with e | e
      · subst e; exact absurd hx (hnd.not_mem_erase)
      · exact e
    have hl := length_le_one_of_eq hnd' (fun a ha b hb => (hall a ha).trans (hall b hb).symm)
    exact eq_singleton_of_length_le_one hl ((List.mem_erase_of_ne (Ne.symm hjg)).mpr hgS)
  have e2 : S.erase g = [j] := by
    have hnd' := hnd.erase g
    have hall : ∀ x ∈ S.erase g, x = j := by
      intro x hx
      rcases (hmem x).mp (List.mem_of_mem_erase hx) with e | e
      · exact e
      · subst e; exact absurd hx (hnd.not_mem_erase)
    have hl := length_le_one_of_eq hnd' (fun a ha b hb => (hall a ha).trans (hall b hb).symm)
    exact eq_singleton_of_length_le_one hl ((List.mem_erase_of_ne hjg).mpr hjS)
  refine ⟨?_, e1, e2⟩
  rw [value_cons_erase v i hjS, e1, value_singleton]

omit [DecidableEq A] in
/-- An upper set of two or more goods has robust level at least 5. -/
theorem five_le_levelR_of_upper {i : A} {S : List G} (hU : IsUpper v i goods S) (h2 : 2 ≤ S.length) :
    5 ≤ levelR v i goods S := by
  unfold levelR
  split
  · omega
  · rw [level_multi v i goods h2]
    simp [hU.2.1]

/-- The cross swap. -/
def crossSwap (base : G → Option A) (u₁ u₂ t₁ t₂ : A) (a₁ a₂ j g b₂ : G) : G → Option A :=
  fun x => if x = a₁ then some u₁ else if x = a₂ then some u₂ else if x = j ∨ x = g then some t₁ else
    if x = b₂ then some t₂ else if base x = some u₁ ∨ base x = some u₂ then none else base x

/-- The hypotheses of the cross swap on a valid state. -/
structure CrossHyp (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A)
    (u₁ u₂ t₁ t₂ : A) (a₁ a₂ j g b₂ : G) : Prop where
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
  htop₂ : v t₂ a₂ = topV v t₂ goods
  hj : j ∈ goods
  hjn : base j = none
  hg : g ∈ goods
  hgb : base g = some u₂
  hj0 : 0 < v t₁ j
  hg0 : 0 < v t₁ g
  hup : topV v t₁ goods < v t₁ j + v t₁ g
  hb₂ : b₂ ∈ goods
  hbb : base b₂ = some u₁ ∨ base b₂ = some u₂
  hbg : b₂ ≠ g
  hb0 : 0 < v t₂ b₂
  hjust₂ : ∀ x ∈ goods, x ≠ a₂ → v t₂ b₂ < v t₂ x → v t₂ a₂ < v t₂ x
  htrip₁ : ∀ y ∈ agents, y ≠ u₁ → y ≠ u₂ → y ≠ t₁ → y ≠ t₂ → 3 ≤ (hold goods base y).length →
    ∀ h ∈ hold goods base y, value v t₁ ((hold goods base y).erase h) ≤ v t₁ j + v t₁ g
  htrip₂ : ∀ y ∈ agents, y ≠ u₁ → y ≠ u₂ → y ≠ t₁ → y ≠ t₂ → 3 ≤ (hold goods base y).length →
    ∀ h ∈ hold goods base y, value v t₂ ((hold goods base y).erase h) ≤ v t₂ b₂

variable {base : G → Option A} {u₁ u₂ t₁ t₂ : A} {a₁ a₂ j g b₂ : G}

theorem CrossHyp.base_a₁ (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) : base a₁ = some t₁ :=
  (mem_hold.mp (by rw [H.hta₁]; simp : a₁ ∈ hold goods base t₁)).2

theorem CrossHyp.base_a₂ (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) : base a₂ = some t₂ :=
  (mem_hold.mp (by rw [H.hta₂]; simp : a₂ ∈ hold goods base t₂)).2

theorem CrossHyp.eq_a₁ (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) {x : G} (hx : x ∈ goods)
    (h : base x = some t₁) : x = a₁ := by
  have : x ∈ hold goods base t₁ := mem_hold.mpr ⟨hx, h⟩
  rw [H.hta₁] at this; simpa using this

theorem CrossHyp.eq_a₂ (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) {x : G} (hx : x ∈ goods)
    (h : base x = some t₂) : x = a₂ := by
  have : x ∈ hold goods base t₂ := mem_hold.mpr ⟨hx, h⟩
  rw [H.hta₂] at this; simpa using this

/-- The distinctness of the five goods of the swap. -/
theorem CrossHyp.ne (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    a₁ ≠ a₂ ∧ a₁ ≠ j ∧ a₁ ≠ g ∧ a₁ ≠ b₂ ∧ a₂ ≠ j ∧ a₂ ≠ g ∧ a₂ ≠ b₂ ∧ j ≠ g ∧ j ≠ b₂ := by
  have A1 := H.base_a₁
  have A2 := H.base_a₂
  have hbt : ∀ {t : A}, t ≠ u₁ → t ≠ u₂ → base b₂ ≠ some t := fun h1 h2 => ne_of_jb h1 h2 (Or.inr H.hbb)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_,
    fun e => ?_⟩
  · rw [e, A2] at A1; exact H.ht (Option.some.inj A1).symm
  · rw [e, H.hjn] at A1; simp at A1
  · rw [e, H.hgb] at A1; exact H.h21 (Option.some.inj A1)
  · rw [e] at A1; exact hbt (Ne.symm H.h11) (Ne.symm H.h21) A1
  · rw [e, H.hjn] at A2; simp at A2
  · rw [e, H.hgb] at A2; exact H.h22 (Option.some.inj A2)
  · rw [e] at A2; exact hbt (Ne.symm H.h12) (Ne.symm H.h22) A2
  · have := H.hjn; rw [e, H.hgb] at this; simp at this
  · have := H.hjn; rw [e] at this; rcases H.hbb with h | h <;> rw [h] at this <;> simp at this

/-- The new holder of each good. -/
theorem cross_cases (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) (x : G) :
    (x = a₁ ∧ crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂ x = some u₁) ∨
    (x = a₂ ∧ crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂ x = some u₂) ∨
    ((x = j ∨ x = g) ∧ crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂ x = some t₁) ∨
    (x = b₂ ∧ crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂ x = some t₂) ∨
    (x ≠ a₁ ∧ x ≠ a₂ ∧ x ≠ j ∧ x ≠ g ∧ x ≠ b₂ ∧ (base x = some u₁ ∨ base x = some u₂) ∧
      crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂ x = none) ∨
    (x ≠ a₁ ∧ x ≠ a₂ ∧ x ≠ j ∧ x ≠ g ∧ x ≠ b₂ ∧ ¬ (base x = some u₁ ∨ base x = some u₂) ∧
      crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂ x = base x) := by
  obtain ⟨n12, n1j, n1g, n1b, n2j, n2g, n2b, njg, njb⟩ := H.ne
  by_cases x1 : x = a₁
  · subst x1; exact Or.inl ⟨rfl, by simp [crossSwap]⟩
  by_cases x2 : x = a₂
  · subst x2; exact Or.inr (Or.inl ⟨rfl, by simp [crossSwap, Ne.symm n12]⟩)
  by_cases x3 : x = j ∨ x = g
  · exact Or.inr (Or.inr (Or.inl ⟨x3, by simp [crossSwap, x1, x2, x3]⟩))
  have x3' : x ≠ j := fun e => x3 (Or.inl e)
  have x4' : x ≠ g := fun e => x3 (Or.inr e)
  by_cases x5 : x = b₂
  · subst x5; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [crossSwap, x1, x2, x3]⟩)))
  by_cases hb : base x = some u₁ ∨ base x = some u₂
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x1, x2, x3', x4', x5, hb, by simp [crossSwap, x1, x2, x3, x5, hb]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x1, x2, x3', x4', x5, hb, by simp [crossSwap, x1, x2, x3, x5, hb]⟩))))

theorem hold_cross_u1 (hgd : goods.Nodup) (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) u₁ = [a₁] := by
  rw [hold_eq_filter (P := fun x => x = a₁) (fun x _ => ?_)]
  · exact filter_eq_single hgd H.ha₁
  obtain ⟨n12, n1j, n1g, n1b, -, -, -, -, -⟩ := H.ne
  rcases cross_cases H x with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨x1, -, -, -, -, -, h⟩ | ⟨x1, -, -, -, -, hb, h⟩
  · exact ⟨fun _ => e, fun _ => h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.hu),
      fun hh => absurd (e.symm.trans hh) (Ne.symm n12)⟩
  · refine ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h11), fun hh => ?_⟩
    rcases e with e | e
    · exact absurd (e.symm.trans hh) (Ne.symm n1j)
    · exact absurd (e.symm.trans hh) (Ne.symm n1g)
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h12),
      fun hh => absurd (e.symm.trans hh) (Ne.symm n1b)⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh x1⟩
  · exact ⟨fun hh => absurd (Or.inl (h.symm.trans hh)) hb, fun hh => absurd hh x1⟩

theorem hold_cross_u2 (hgd : goods.Nodup) (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) u₂ = [a₂] := by
  rw [hold_eq_filter (P := fun x => x = a₂) (fun x _ => ?_)]
  · exact filter_eq_single hgd H.ha₂
  obtain ⟨n12, -, -, -, n2j, n2g, n2b, -, -⟩ := H.ne
  rcases cross_cases H x with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, x2, -, -, -, -, h⟩ | ⟨-, x2, -, -, -, hb, h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.hu, fun hh => absurd (e.symm.trans hh) n12⟩
  · exact ⟨fun _ => e, fun _ => h⟩
  · refine ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h21), fun hh => ?_⟩
    rcases e with e | e
    · exact absurd (e.symm.trans hh) (Ne.symm n2j)
    · exact absurd (e.symm.trans hh) (Ne.symm n2g)
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.h22),
      fun hh => absurd (e.symm.trans hh) (Ne.symm n2b)⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh x2⟩
  · exact ⟨fun hh => absurd (Or.inr (h.symm.trans hh)) hb, fun hh => absurd hh x2⟩

theorem hold_cross_t1 (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) t₁ = goods.filter (fun x => decide (x = j ∨ x = g)) := by
  refine hold_eq_filter (fun x hx => ?_)
  obtain ⟨-, n1j, n1g, -, n2j, n2g, -, -, -⟩ := H.ne
  rcases cross_cases H x with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, -, x3, x4, -, -, h⟩ | ⟨x1, -, x3, x4, -, -, h⟩
  · refine ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h11, fun hh => ?_⟩
    rcases hh with hh | hh
    · exact absurd (e.symm.trans hh) n1j
    · exact absurd (e.symm.trans hh) n1g
  · refine ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h21, fun hh => ?_⟩
    rcases hh with hh | hh
    · exact absurd (e.symm.trans hh) n2j
    · exact absurd (e.symm.trans hh) n2g
  · exact ⟨fun _ => e, fun _ => h⟩
  · refine ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) (Ne.symm H.ht), fun hh => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, njb⟩ := H.ne
    rcases hh with hh | hh
    · exact absurd (hh.symm.trans e) njb
    · exact absurd (hh.symm.trans e) (Ne.symm H.hbg)
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => hh.elim (fun e => absurd e x3) (fun e => absurd e x4)⟩
  · exact ⟨fun hh => absurd (H.eq_a₁ hx (h.symm.trans hh)) x1,
      fun hh => hh.elim (fun e => absurd e x3) (fun e => absurd e x4)⟩

theorem hold_cross_t2 (hgd : goods.Nodup) (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) t₂ = [b₂] := by
  rw [hold_eq_filter (P := fun x => x = b₂) (fun x hx => ?_)]
  · exact filter_eq_single hgd H.hb₂
  obtain ⟨-, -, -, n1b, -, -, n2b, -, njb⟩ := H.ne
  rcases cross_cases H x with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, -, -, -, x5, -, h⟩ | ⟨-, x2, -, -, x5, -, h⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h12, fun hh => absurd (e.symm.trans hh) n1b⟩
  · exact ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.h22, fun hh => absurd (e.symm.trans hh) n2b⟩
  · refine ⟨fun hh => absurd (Option.some.inj (h.symm.trans hh)) H.ht, fun hh => ?_⟩
    rcases e with e | e
    · exact absurd (e.symm.trans hh) njb
    · exact absurd (e.symm.trans hh) (Ne.symm H.hbg)
  · exact ⟨fun _ => e, fun _ => h⟩
  · exact ⟨fun hh => absurd (h.symm.trans hh) (by simp), fun hh => absurd hh x5⟩
  · exact ⟨fun hh => absurd (H.eq_a₂ hx (h.symm.trans hh)) x2, fun hh => absurd hh x5⟩

theorem hold_cross_other (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) {i : A}
    (i1 : i ≠ u₁) (i2 : i ≠ u₂) (i3 : i ≠ t₁) (i4 : i ≠ t₂) :
    hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) i = hold goods base i := by
  unfold hold
  apply List.filter_congr
  intro x _
  rcases cross_cases H x with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨-, -, -, -, -, hb, h⟩ | ⟨-, -, -, -, -, -, h⟩
  · rw [h, e, H.base_a₁]; simp [Ne.symm i1, Ne.symm i3]
  · rw [h, e, H.base_a₂]; simp [Ne.symm i2, Ne.symm i4]
  · rcases e with e | e
    · rw [h, e, H.hjn]; simp [Ne.symm i3]
    · rw [h, e, H.hgb]; simp [Ne.symm i2, Ne.symm i3]
  · rw [h, e]; simp [ne_of_jb (t := i) i1 i2 (Or.inr H.hbb), Ne.symm i4]
  · have : base x ≠ some i := by rcases hb with h' | h' <;> rw [h'] <;> simp [Ne.symm i1, Ne.symm i2]
    rw [h]; simp [this]
  · rw [h]

/-- `t₁`'s new holding: the upper set `{j, g}`. -/
theorem cross_t1_pair (hgd : goods.Nodup) (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) (i : A) :
    value v i (goods.filter (fun x => decide (x = j ∨ x = g))) = v i j + v i g ∧
      (goods.filter (fun x => decide (x = j ∨ x = g))).erase j = [g] ∧
      (goods.filter (fun x => decide (x = j ∨ x = g))).erase g = [j] := by
  obtain ⟨-, -, -, -, -, -, -, njg, -⟩ := H.ne
  refine pair_value i (hgd.filter _) njg (fun x => ?_)
  constructor
  · intro hx; simpa using (List.mem_filter.mp hx).2
  · intro hx
    refine List.mem_filter.mpr ⟨?_, by simpa using hx⟩
    rcases hx with e | e <;> subst e
    · exact H.hj
    · exact H.hg

theorem cross_t1_upper (hgd : goods.Nodup) (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    IsUpper v t₁ goods (goods.filter (fun x => decide (x = j ∨ x = g))) := by
  obtain ⟨hv, e1, e2⟩ := cross_t1_pair hgd H t₁
  refine ⟨fun x hx => ?_, by rw [hv]; exact H.hup, fun x hx => ?_⟩
  · have : x = j ∨ x = g := by simpa using (List.mem_filter.mp hx).2
    rcases this with e | e <;> subst e
    · exact H.hj0
    · exact H.hg0
  · have : x = j ∨ x = g := by simpa using (List.mem_filter.mp hx).2
    rcases this with e | e <;> subst e
    · rw [e1, value_singleton]; exact le_topV v t₁ goods H.hg
    · rw [e2, value_singleton]; exact le_topV v t₁ goods H.hj

theorem crossSwap_valid (hgd : goods.Nodup) (hb : Valid v agents goods base)
    (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    Valid v agents goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) := by
  have hU1 := hold_cross_u1 hgd H
  have hU2 := hold_cross_u2 hgd H
  have hT1 := hold_cross_t1 H
  have hT2 := hold_cross_t2 hgd H
  have hO := fun {i : A} (i1 : i ≠ u₁) (i2 : i ≠ u₂) (i3 : i ≠ t₁) (i4 : i ≠ t₂) => hold_cross_other H i1 i2 i3 i4
  obtain ⟨hpv, he1, he2⟩ := cross_t1_pair hgd H t₁
  have hUp := cross_t1_upper hgd H
  have hlen1 : (hold goods base u₁).length = 2 := H.hlp₁.2.1
  have hlen2 : (hold goods base u₂).length = 2 := H.hlp₂.2.1
  -- `t₂` values every good other than its top at most `v(b₂)`
  have hb2top : ∀ x ∈ goods, x ≠ a₂ → v t₂ x ≤ v t₂ b₂ := fun x hx hxa =>
    Nat.le_of_not_lt fun hlt => by
      have := H.hjust₂ x hx hxa hlt; have := le_topV v t₂ goods hx; have := H.htop₂; omega
  -- goods unwanted in `base` stay below the holding of every unchanged agent
  have hunw : ∀ i ∈ agents, ∀ x ∈ goods, (∀ k, hold goods base k ≠ [x]) → v i x ≤ value v i (hold goods base i) :=
    fun i hi x hx hk => Nat.le_of_not_lt fun hlt => by
      obtain ⟨k, _, hkx⟩ := hb.v1 i hi x hx hlt; exact hk k hkx
  have hjk : ∀ k, hold goods base k ≠ [j] := fun k hk => by
    have : j ∈ hold goods base k := by rw [hk]; simp
    have hbj := (mem_hold.mp this).2
    rw [H.hjn] at hbj; simp at hbj
  have hgk : ∀ k, hold goods base k ≠ [g] := fun k hk => by
    have : g ∈ hold goods base k := by rw [hk]; simp
    have hbg := (mem_hold.mp this).2
    rw [H.hgb] at hbg
    have hku : k = u₂ := (Option.some.inj hbg).symm
    subst hku; rw [hk] at hlen2; simp at hlen2
  have halone : ∀ k ∈ agents, ∀ x, hold goods base k = [x] →
      ∃ k' ∈ agents, hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) k' = [x] := by
    intro k hk x hkx
    by_cases k1 : k = u₁
    · subst k1; rw [hkx] at hlen1; simp at hlen1
    · by_cases k2 : k = u₂
      · subst k2; rw [hkx] at hlen2; simp at hlen2
      · by_cases k3 : k = t₁
        · subst k3
          have : x = a₁ := by rw [H.hta₁] at hkx; simpa using hkx.symm
          subst this; exact ⟨u₁, H.hu₁, hU1⟩
        · by_cases k4 : k = t₂
          · subst k4
            have : x = a₂ := by rw [H.hta₂] at hkx; simpa using hkx.symm
            subst this; exact ⟨u₂, H.hu₂, hU2⟩
          · exact ⟨k, hk, by rw [hO k1 k2 k3 k4]; exact hkx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- owners
    intro x hx k hk
    rcases cross_cases H x with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨-, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ <;>
      rw [h] at hk
    · cases hk; exact H.hu₁
    · cases hk; exact H.hu₂
    · cases hk; exact H.ht₁
    · cases hk; exact H.ht₂
    · cases hk
    · exact hb.owners x hx k hk
  · -- allowed
    intro i hi
    by_cases i1 : i = u₁
    · subst i1; rw [hU1]
      exact Or.inl ⟨by simp, fun x hx => by simp at hx; subst hx; have := H.hlp₁.2.2.2.1; have := H.hat₁; omega⟩
    · by_cases i2 : i = u₂
      · subst i2; rw [hU2]
        exact Or.inl ⟨by simp, fun x hx => by simp at hx; subst hx; have := H.hlp₂.2.2.2.1; have := H.hat₂; omega⟩
      · by_cases i3 : i = t₁
        · subst i3; rw [hT1]; exact Or.inr (Or.inl hUp)
        · by_cases i4 : i = t₂
          · subst i4; rw [hT2]; exact Or.inl ⟨by simp, fun x hx => by simp at hx; subst hx; exact H.hb0⟩
          · rw [hO i1 i2 i3 i4]; exact hb.allowed i hi
  · -- (V1)
    intro i hi x hx hlt
    by_cases i1 : i = u₁
    · subst i1; rw [hU1, value_singleton, H.hat₁] at hlt
      have := le_topV v i goods hx; omega
    · by_cases i2 : i = u₂
      · subst i2; rw [hU2, value_singleton, H.hat₂] at hlt
        have := le_topV v i goods hx; omega
      · by_cases i3 : i = t₁
        · subst i3; rw [hT1, hpv] at hlt
          have := le_topV v i goods hx; have := H.hup; omega
        · by_cases i4 : i = t₂
          · subst i4; rw [hT2, value_singleton] at hlt
            by_cases xa : x = a₂
            · subst xa; exact ⟨u₂, H.hu₂, hU2⟩
            · have := hb2top x hx xa; omega
          · rw [hO i1 i2 i3 i4] at hlt
            obtain ⟨k, hk, hkx⟩ := hb.v1 i hi x hx hlt
            exact halone k hk x hkx
  · -- (V2)
    intro i hi k hk hik h hh
    by_cases k1 : k = u₁
    · subst k1; rw [hU1] at hh ⊢; simp at hh; subst hh; simp
    · by_cases k2 : k = u₂
      · subst k2; rw [hU2] at hh ⊢; simp at hh; subst hh; simp
      · by_cases k4 : k = t₂
        · subst k4; rw [hT2] at hh ⊢; simp at hh; subst hh; simp
        · by_cases k3 : k = t₁
          · -- the pair {j, g} of t₁: one good is left, which nobody else values above its holding
            subst k3
            rw [hT1] at hh ⊢
            have hx : h = j ∨ h = g := by simpa using (List.mem_filter.mp hh).2
            have key : ∀ y ∈ [j, g], v i y ≤ value v i (hold goods (crossSwap base u₁ u₂ k t₂ a₁ a₂ j g b₂) i) := by
              intro y hy
              have hyg : y ∈ goods := by
                simp at hy; rcases hy with e | e <;> subst e <;> first | exact H.hj | exact H.hg
              have hyk : ∀ k', hold goods base k' ≠ [y] := by
                simp at hy; rcases hy with e | e <;> subst e <;> first | exact hjk | exact hgk
              by_cases i1 : i = u₁
              · subst i1; rw [hU1, value_singleton, H.hat₁]; exact le_topV v i goods hyg
              · by_cases i2 : i = u₂
                · subst i2; rw [hU2, value_singleton, H.hat₂]; exact le_topV v i goods hyg
                · by_cases i4 : i = t₂
                  · subst i4; rw [hT2, value_singleton]
                    obtain ⟨-, -, -, -, n2j, n2g, -, -, -⟩ := H.ne
                    have hya : y ≠ a₂ := by
                      simp at hy
                      rcases hy with e | e <;> subst e <;> first | exact Ne.symm n2j | exact Ne.symm n2g
                    exact hb2top y hyg hya
                  · rw [hO i1 i2 hik i4]; exact hunw i hi y hyg hyk
            rcases hx with e | e <;> subst e
            · rw [he1, value_singleton]; exact key g (by simp)
            · rw [he2, value_singleton]; exact key j (by simp)
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
                · subst i3; rw [hT1, hpv]
                  by_cases h3 : 3 ≤ (hold goods base k).length
                  · exact H.htrip₁ k hk k1 k2 k3 k4 h3 h hh
                  · have hl1 : ((hold goods base k).erase h).length ≤ 1 := by
                      rw [List.length_erase_of_mem hh]; omega
                    have : value v i ((hold goods base k).erase h) ≤ topV v i goods := by
                      match he : (hold goods base k).erase h, hl1 with
                      | [], _ => simp
                      | [y], _ =>
                        rw [value_singleton]
                        exact le_topV v i goods (mem_hold.mp (List.mem_of_mem_erase (by rw [he]; simp))).1
                    have := H.hup; omega
                · by_cases i4 : i = t₂
                  · subst i4; rw [hT2, value_singleton]
                    by_cases h3 : 3 ≤ (hold goods base k).length
                    · exact H.htrip₂ k hk k1 k2 k3 k4 h3 h hh
                    · exact t_pair_bound hb H.ht₂ H.hta₂ H.hjust₂ k4 (by omega) hh
                  · rw [hO i1 i2 i3 i4]; exact hb.v2 i hi k hk hik h hh

theorem crossSwap_numLP (hgd : goods.Nodup) (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    numLP v agents goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) < numLP v agents goods base := by
  classical
  have hU1 := hold_cross_u1 hgd H
  have hU2 := hold_cross_u2 hgd H
  have hT1 := hold_cross_t1 H
  have hT2 := hold_cross_t2 hgd H
  have hsingle : ∀ i, (∃ x, hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) i = [x]) →
      ¬ IsLowerPair v i goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) i) := by
    intro i ⟨x, hx⟩ h; rw [hx] at h; have := h.2.1; simp at this
  have ht1 : ¬ IsLowerPair v t₁ goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) t₁) := by
    rw [hT1]; intro h; have := h.2.2.2.1; have := (cross_t1_upper hgd H).2.1; omega
  unfold numLP
  apply sum_map_lt
  · intro i _
    by_cases i1 : i = u₁
    · subst i1; simp [hsingle _ ⟨a₁, hU1⟩]
    · by_cases i2 : i = u₂
      · subst i2; simp [hsingle _ ⟨a₂, hU2⟩]
      · by_cases i3 : i = t₁
        · subst i3; simp [ht1]
        · by_cases i4 : i = t₂
          · subst i4; simp [hsingle _ ⟨b₂, hT2⟩]
          · rw [hold_cross_other H i1 i2 i3 i4]; exact Nat.le_refl _
  · exact ⟨u₁, H.hu₁, by simp [hsingle _ ⟨a₁, hU1⟩, H.hlp₁]⟩

theorem crossSwap_potentialR (hag : agents.Nodup) (hgd : goods.Nodup)
    (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    potentialR v agents goods base + 2 ≤ potentialR v agents goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) := by
  have hU1 := hold_cross_u1 hgd H
  have hU2 := hold_cross_u2 hgd H
  have hT1 := hold_cross_t1 H
  have hT2 := hold_cross_t2 hgd H
  let F := fun i => levelR v i goods (hold goods base i)
  let Gf := fun i => levelR v i goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) i)
  have hup : ∀ {u : A} {a : G}, IsLowerPair v u goods (hold goods base u) → a ∈ goods →
      v u a = topV v u goods → hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) u = [a] → F u + 1 = Gf u := by
    intro u a hlp ha hat hZ
    show levelR v u goods (hold goods base u) + 1 =
      levelR v u goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) u)
    rw [levelR_lowerPair hlp, hZ, levelR_single u a ha, level_single]
    have h0 := filter_len_le (l := relevant v u goods) (p := fun g' => decide (v u a < v u g'))
      (q := fun _ => false) (fun x hx hp => by
        have := le_topV v u goods (List.mem_filter.mp hx).1
        simp only [decide_eq_true_eq] at hp; omega)
    have h1 : ((relevant v u goods).filter (fun _ => false)).length = 0 := by simp
    omega
  have e1 := hup H.hlp₁ H.ha₁ H.hat₁ hU1
  have e2 := hup H.hlp₂ H.ha₂ H.hat₂ hU2
  have d1 : F t₁ + 1 ≤ Gf t₁ := by
    show levelR v t₁ goods (hold goods base t₁) + 1 ≤
      levelR v t₁ goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) t₁)
    rw [H.hta₁, hT1, levelR_single t₁ a₁ H.ha₁]
    have h4 := level_single_le_four v t₁ goods a₁
    have hl : 2 ≤ (goods.filter (fun x => decide (x = j ∨ x = g))).length := by
      have hm : j ∈ goods.filter (fun x => decide (x = j ∨ x = g)) :=
        List.mem_filter.mpr ⟨H.hj, by simp⟩
      have hle := List.length_erase_of_mem hm
      rw [(cross_t1_pair hgd H t₁).2.1, List.length_singleton] at hle
      have hpos := List.length_pos_of_mem hm
      omega
    have h5 := five_le_levelR_of_upper (cross_t1_upper hgd H) hl
    omega
  have d2 : F t₂ ≤ Gf t₂ + 1 := by
    show levelR v t₂ goods (hold goods base t₂) ≤
      levelR v t₂ goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) t₂) + 1
    rw [H.hta₂, hT2, levelR_single t₂ a₂ H.ha₂, levelR_single t₂ b₂ H.hb₂, level_single, level_single]
    have := filter_len_le_succ (l := relevant v t₂ goods) (hgd.filter _) (p := fun g' => decide (v t₂ b₂ < v t₂ g'))
      (q := fun g' => decide (v t₂ a₂ < v t₂ g')) (a := a₂) (fun x hx hp => by
        simp only [decide_eq_true_eq] at hp ⊢
        by_cases hxa : x = a₂
        · exact Or.inl hxa
        · exact Or.inr (H.hjust₂ x (List.mem_filter.mp hx).1 hxa hp))
    omega
  have hpt : ∀ i ∈ agents, ((F i + (if i = u₁ then 1 else 0)) + (if i = u₂ then 1 else 0)) +
      (if i = t₁ then 1 else 0) ≤ Gf i + (if i = t₂ then 1 else 0) := by
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
              levelR v i goods (hold goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) i)
            rw [hold_cross_other H i1 i2 i3 i4]
            exact Nat.le_refl _
  have h1 := sum_map_le hpt
  rw [sum_map_ind hag H.ht₁ (fun i => (F i + if i = u₁ then 1 else 0) + if i = u₂ then 1 else 0),
    sum_map_ind hag H.hu₂ (fun i => F i + if i = u₁ then 1 else 0), sum_map_ind hag H.hu₁ F,
    sum_map_ind hag H.ht₂ Gf] at h1
  show (agents.map F).sum + 2 ≤ (agents.map Gf).sum
  omega

/-- **Lemma 30(a), the cross swap**: valid, the robust level sum rises by at least 2, fewer lower-pair holders. -/
theorem cross_swap (hag : agents.Nodup) (hgd : goods.Nodup) (hb : Valid v agents goods base)
    (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) :
    Valid v agents goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) ∧
      potentialR v agents goods base + 2 ≤ potentialR v agents goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) ∧
      numLP v agents goods (crossSwap base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) < numLP v agents goods base :=
  ⟨crossSwap_valid hgd hb H, crossSwap_potentialR hag hgd H, crossSwap_numLP hgd H⟩

/-- No top state (a maximum of the robust order or of the lower-pair order) admits a cross swap. -/
theorem not_top_of_cross_swap (hag : agents.Nodup) (hgd : goods.Nodup) (hmax : TopR v agents goods base)
    (H : CrossHyp v agents goods base u₁ u₂ t₁ t₂ a₁ a₂ j g b₂) : False := by
  obtain ⟨hZ, hP, _⟩ := cross_swap hag hgd hmax.1.1 H
  have := hmax.2 _ hZ
  omega

end cross

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.hold_eq_filter
#print axioms EFX.DE4.pair_value
#print axioms EFX.DE4.five_le_levelR_of_upper
#print axioms EFX.DE4.CrossHyp.base_a₁
#print axioms EFX.DE4.CrossHyp.base_a₂
#print axioms EFX.DE4.CrossHyp.eq_a₁
#print axioms EFX.DE4.CrossHyp.eq_a₂
#print axioms EFX.DE4.CrossHyp.ne
#print axioms EFX.DE4.cross_cases
#print axioms EFX.DE4.hold_cross_u1
#print axioms EFX.DE4.hold_cross_u2
#print axioms EFX.DE4.hold_cross_t1
#print axioms EFX.DE4.hold_cross_t2
#print axioms EFX.DE4.hold_cross_other
#print axioms EFX.DE4.cross_t1_pair
#print axioms EFX.DE4.cross_t1_upper
#print axioms EFX.DE4.crossSwap_valid
#print axioms EFX.DE4.crossSwap_numLP
#print axioms EFX.DE4.crossSwap_potentialR
#print axioms EFX.DE4.cross_swap
#print axioms EFX.DE4.not_top_of_cross_swap
