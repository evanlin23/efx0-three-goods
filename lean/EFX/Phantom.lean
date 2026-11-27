import EFX.Lift1

/-!
# Lemma PHANTOM and Lemma LIFT\* (`k4/matching.md` §6, "Iterated reduction")

Both refereed CORRECT in `k4/referee/lift.md` §8. They are proof tools of the reduction route RSD and of its round
form ROUND-RSD: a *reduction step* settles a dangerous agent `k` with a set `T` of goods and deletes both; a *round*
settles several agents at once.

**Lemma PHANTOM** (`phantom_three`, `phantom_two`, and the core `phantom_only`): with `|R_k| ≤ 4`, let `k` hold
`T ⊆ R_k` with `v_k(T) > v_k(y)` for some `y ∈ R_k ∖ T` (its former pick), and let `X` be a bundle disjoint from `T`.
1. If `|T| = 3`, `X` never threatens `k` at `v_k(T)`.
2. If `|T| = 2` and `R_k = T ∪ {y, ℓ}`, `X` threatens `k` at `v_k(T)` exactly when
   - (P1) `ℓ ∈ X`, `|X| ≥ 2` and `v_k(ℓ) > v_k(T)`, or
   - (P2) `{y, ℓ} ⊆ X`, `|X| ≥ 3` and `v_k(y) + v_k(ℓ) > v_k(T)`.

**Lemma LIFT\*** (`liftStar`): the iterated lift. Let agents `k ∈ ks` be settled with pairwise disjoint sets `T k`, in
rounds `rd k` (sequential steps when `rd` is injective; a round of several settlements otherwise), and let `X` be an
EFX₀ allocation of the remaining goods to the remaining agents. Suppose
- (Φ) no bundle of `X`, and no `T k'` of a later round, threatens `k` at `v_k(T k)`;
- (L\*) when `k` is settled, `T k` threatens no agent `a` still present at `a`'s value `w k a` then (for a round:
  at the round's end, so a round-mate is counted at its threshold);
- values never fall: `w k a` is at most `a`'s final value (its bundle of `X`, or `v_a(T a)` if `a` is settled at
  `k`'s round or later).

Then `X` together with all the `T k` (`liftAlloc`) is an EFX₀ allocation of the whole instance. The proof needs
nothing about `k ≤ 4` or `|T|`.
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Lemma PHANTOM -/

section phantom
variable {v : A → G → Nat} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
/-- With at most four relevant goods, a duplicate-free list of four relevant goods contains every relevant good. -/
theorem relevant_mem_of_four {k : A} (hrel : (relevant v k goods).length ≤ 4) {S : List G} (hS : S.Nodup)
    (hSR : ∀ g ∈ S, g ∈ goods ∧ 0 < v k g) (h4 : S.length = 4) {g : G} (hg : g ∈ goods) (hpos : 0 < v k g) :
    g ∈ S := by
  apply Classical.byContradiction
  intro hgS
  have hnd : (g :: S).Nodup := List.nodup_cons.mpr ⟨hgS, hS⟩
  have hsub : g :: S ⊆ relevant v k goods := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mem_relevant.mpr ⟨hg, hpos⟩
    · exact mem_relevant.mpr (hSR x hx)
  have := hnd.length_le_of_subset hsub
  simp only [List.length_cons] at this; omega

omit [DecidableEq A] in
/-- The value of a duplicate-free list whose only relevant good can be `y`. -/
theorem value_eq_one {k : A} {y : G} : ∀ {L : List G}, L.Nodup → (∀ g ∈ L, 0 < v k g → g = y) →
    value v k L = if y ∈ L then v k y else 0
  | [], _, _ => by simp
  | a :: L, hnd, h => by
    have ha : a ∉ L := (List.nodup_cons.mp hnd).1
    have ih := value_eq_one (List.nodup_cons.mp hnd).2 fun g hg => h g (List.mem_cons_of_mem _ hg)
    rw [value_cons, ih]
    by_cases hay : a = y
    · rw [hay] at ha ⊢; simp [ha]
    · have h0 : v k a = 0 := Nat.eq_zero_of_not_pos fun hpos => hay (h a List.mem_cons_self hpos)
      have hya : y ≠ a := fun e => hay e.symm
      simp [h0, hya]

omit [DecidableEq A] in
/-- The value of a duplicate-free list whose only relevant goods can be `y` and `ℓ`. -/
theorem value_eq_two {k : A} {y ℓ : G} (hyl : y ≠ ℓ) : ∀ {L : List G}, L.Nodup →
    (∀ g ∈ L, 0 < v k g → g = y ∨ g = ℓ) →
    value v k L = (if y ∈ L then v k y else 0) + (if ℓ ∈ L then v k ℓ else 0)
  | [], _, _ => by simp
  | a :: L, hnd, h => by
    have ha : a ∉ L := (List.nodup_cons.mp hnd).1
    have ih := value_eq_two hyl (List.nodup_cons.mp hnd).2 fun g hg => h g (List.mem_cons_of_mem _ hg)
    rw [value_cons, ih]
    by_cases hay : a = y
    · rw [hay] at ha ⊢
      have hly : ℓ ≠ y := fun e => hyl e.symm
      simp [ha, hly]
    · by_cases hal : a = ℓ
      · rw [hal] at ha ⊢
        simp [ha, hyl]; omega
      · have h0 : v k a = 0 := Nat.eq_zero_of_not_pos fun hpos =>
          (h a List.mem_cons_self hpos).elim hay hal
        have hya : y ≠ a := fun e => hay e.symm
        have hla : ℓ ≠ a := fun e => hal e.symm
        simp [h0, hya, hla]

omit [DecidableEq A] in
/-- **PHANTOM's core**: if the only good of `X` that `k` values can be `y`, and `v_k(y) < c`, then `X` does not
threaten `k` at `c`. -/
theorem phantom_only {k : A} {y : G} {c : Nat} (hyc : v k y < c) {X : List G} (hX : X.Nodup)
    (honly : ∀ g ∈ X, 0 < v k g → g = y) : ¬ Threat v k X c := by
  refine not_threat_of_value_le ?_
  rw [value_eq_one hX honly]
  split <;> omega

omit [DecidableEq A] in
/-- **Lemma PHANTOM, case 1** (`|T| = 3`): a bundle disjoint from `T` never threatens `k` at `v_k(T)`. -/
theorem phantom_three {k : A} (hrel : (relevant v k goods).length ≤ 4) {T : List G} (hT : T.Nodup)
    (hTR : ∀ g ∈ T, g ∈ goods ∧ 0 < v k g) (hT3 : T.length = 3) {y : G} (hy : y ∈ goods ∧ 0 < v k y)
    (hyT : y ∉ T) (himp : v k y < value v k T) {X : List G} (hX : X.Nodup) (hXg : ∀ g ∈ X, g ∈ goods)
    (hXT : ∀ g ∈ X, g ∉ T) : ¬ Threat v k X (value v k T) := by
  have hS : (y :: T).Nodup := List.nodup_cons.mpr ⟨hyT, hT⟩
  have hSR : ∀ g ∈ y :: T, g ∈ goods ∧ 0 < v k g := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hy
    · exact hTR g hg
  refine phantom_only himp hX fun g hg hpos => ?_
  have := relevant_mem_of_four hrel hS hSR (by simp [hT3]) (hXg g hg) hpos
  rcases List.mem_cons.mp this with h | h
  · exact h
  · exact absurd h (hXT g hg)

omit [DecidableEq A] [DecidableEq G] in
/-- Two different elements of a duplicate-free list. -/
theorem two_le_length {X : List G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) : 2 ≤ X.length := by
  have hnd : [a, b].Nodup := by simp [hab]
  have := hnd.length_le_of_subset (l₂ := X) (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ha
    · exact hb)
  simpa using this

omit [DecidableEq A] [DecidableEq G] in
theorem three_le_length {X : List G} {a b c : G} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ X.length := by
  have hnd : [a, b, c].Nodup := by simp [hab, hac, hbc]
  have := hnd.length_le_of_subset (l₂ := X) (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc)
  simpa using this

omit [DecidableEq A] in
/-- **Lemma PHANTOM, case 2** (`|T| = 2`, `R_k = T ∪ {y, ℓ}`): a bundle `X` disjoint from `T` threatens `k` at
`v_k(T)` exactly when (P1) or (P2) holds. -/
theorem phantom_two {k : A} (hrel : (relevant v k goods).length ≤ 4) {T : List G} (hT : T.Nodup)
    (hTR : ∀ g ∈ T, g ∈ goods ∧ 0 < v k g) (hT2 : T.length = 2) {y ℓ : G} (hy : y ∈ goods ∧ 0 < v k y)
    (hyT : y ∉ T) (hl : ℓ ∈ goods ∧ 0 < v k ℓ) (hlT : ℓ ∉ T) (hyl : y ≠ ℓ) (himp : v k y < value v k T)
    {X : List G} (hX : X.Nodup) (hXg : ∀ g ∈ X, g ∈ goods) (hXT : ∀ g ∈ X, g ∉ T) :
    Threat v k X (value v k T) ↔ (ℓ ∈ X ∧ 2 ≤ X.length ∧ value v k T < v k ℓ) ∨
      (y ∈ X ∧ ℓ ∈ X ∧ 3 ≤ X.length ∧ value v k T < v k y + v k ℓ) := by
  have hS : (y :: ℓ :: T).Nodup :=
    List.nodup_cons.mpr ⟨by simp [hyl, hyT], List.nodup_cons.mpr ⟨hlT, hT⟩⟩
  have hSR : ∀ g ∈ y :: ℓ :: T, g ∈ goods ∧ 0 < v k g := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hy
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact hl
      · exact hTR g hg
  have honly : ∀ g ∈ X, 0 < v k g → g = y ∨ g = ℓ := fun g hg hpos => by
    have := relevant_mem_of_four hrel hS hSR (by simp [hT2]) (hXg g hg) hpos
    rcases List.mem_cons.mp this with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr h
      · exact absurd h (hXT g hg)
  have hval : ∀ x, value v k (X.erase x) =
      (if y ∈ X.erase x then v k y else 0) + (if ℓ ∈ X.erase x then v k ℓ else 0) := fun x =>
    value_eq_two hyl (hX.sublist List.erase_sublist) fun g hg => honly g (List.mem_of_mem_erase hg)
  constructor
  · rintro ⟨x, hx, hlt⟩
    rw [hval x] at hlt
    by_cases hl' : ℓ ∈ X.erase x
    · obtain ⟨hlx, hlX⟩ := hX.mem_erase_iff.mp hl'
      by_cases hy' : y ∈ X.erase x
      · obtain ⟨hyx, hyX⟩ := hX.mem_erase_iff.mp hy'
        simp only [hy', hl', ite_true] at hlt
        exact Or.inr ⟨hyX, hlX, three_le_length hx hyX hlX (fun e => hyx e.symm) (fun e => hlx e.symm) hyl, hlt⟩
      · simp only [hy', hl', ite_true, ite_false, Nat.zero_add] at hlt
        exact Or.inl ⟨hlX, two_le_length hx hlX (fun e => hlx e.symm), hlt⟩
    · simp only [hl', ite_false, Nat.add_zero] at hlt
      split at hlt <;> omega
  · rintro (⟨hlX, h2, hlt⟩ | ⟨hyX, hlX, h3, hlt⟩)
    · obtain ⟨x, hx, hxl⟩ : ∃ x ∈ X, x ≠ ℓ := by
        apply Classical.byContradiction
        intro hno
        have hall : ∀ a ∈ X, a = ℓ := fun a ha => Classical.byContradiction fun h => hno ⟨a, ha, h⟩
        have := length_le_one_of_eq hX fun a ha b hb => (hall a ha).trans (hall b hb).symm
        omega
      have hl' : ℓ ∈ X.erase x := hX.mem_erase_iff.mpr ⟨fun e => hxl e.symm, hlX⟩
      refine ⟨x, hx, ?_⟩
      rw [hval x]; simp only [hl', ite_true]; omega
    · obtain ⟨x, hx, hxy, hxl⟩ : ∃ x ∈ X, x ≠ y ∧ x ≠ ℓ := by
        apply Classical.byContradiction
        intro hno
        have hsub : X ⊆ [y, ℓ] := by
          intro a ha
          by_cases hay : a = y
          · simp [hay]
          · by_cases hal : a = ℓ
            · simp [hal]
            · exact absurd ⟨a, ha, hay, hal⟩ hno
        have := hX.length_le_of_subset hsub
        simp only [List.length_cons, List.length_nil] at this; omega
      have hy' : y ∈ X.erase x := hX.mem_erase_iff.mpr ⟨fun e => hxy e.symm, hyX⟩
      have hl' : ℓ ∈ X.erase x := hX.mem_erase_iff.mpr ⟨fun e => hxl e.symm, hlX⟩
      refine ⟨x, hx, ?_⟩
      rw [hval x]; simp only [hy', hl', ite_true]; omega

end phantom

/-! ## Lemma LIFT\* -/

/-- The goods left after deleting the sets `T k` of the settled agents `k ∈ ks`. -/
def remGoods (goods : List G) (ks : List A) (T : A → List G) : List G :=
  goods.filter (fun g => decide (∀ k ∈ ks, g ∉ T k))

/-- The agents left after deleting the settled agents. -/
def remAgents (agents : List A) (ks : List A) : List A :=
  agents.filter (fun a => decide (a ∉ ks))

/-- The lifted allocation: each settled agent gets its set, every other good goes where `X` puts it. -/
def liftAlloc (ks : List A) (T : A → List G) (X : G → A) (g : G) : A :=
  match ks.find? (fun k => decide (g ∈ T k)) with
  | some k => k
  | none => X g

section liftStar
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] in
theorem mem_remGoods {ks : List A} {T : A → List G} {g : G} :
    g ∈ remGoods goods ks T ↔ g ∈ goods ∧ ∀ k ∈ ks, g ∉ T k := by
  simp [remGoods]

omit [DecidableEq G] in
theorem mem_remAgents {ks : List A} {a : A} : a ∈ remAgents agents ks ↔ a ∈ agents ∧ a ∉ ks := by
  simp [remAgents]

omit [DecidableEq A] in
theorem liftAlloc_of_mem {ks : List A} {T : A → List G}
    (hdisj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → ∀ g ∈ T k, g ∉ T k') (X : G → A) {k : A} (hk : k ∈ ks) {g : G}
    (hg : g ∈ T k) : liftAlloc ks T X g = k := by
  cases h : ks.find? (fun k => decide (g ∈ T k)) with
  | none => exact absurd (List.find?_eq_none.mp h k hk) (by simpa using hg)
  | some k' =>
    have hk' := List.mem_of_find?_eq_some h
    have hg' : g ∈ T k' := by simpa using List.find?_some h
    simp only [liftAlloc, h]
    exact Classical.byContradiction fun hne => hdisj k' hk' k hk hne g hg' hg

omit [DecidableEq A] in
theorem liftAlloc_of_not {ks : List A} {T : A → List G} (X : G → A) {g : G} (hg : ∀ k ∈ ks, g ∉ T k) :
    liftAlloc ks T X g = X g := by
  have h : ks.find? (fun k => decide (g ∈ T k)) = none :=
    List.find?_eq_none.mpr fun k hk => by simpa using hg k hk
  simp only [liftAlloc, h]

/-- A settled agent's bundle in the lifted allocation is its set. -/
theorem mem_bundle_lift_settled {ks : List A} {T : A → List G} (hTg : ∀ k ∈ ks, ∀ g ∈ T k, g ∈ goods)
    (hdisj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → ∀ g ∈ T k, g ∉ T k') {X : G → A}
    (hX : IsAllocation (remAgents agents ks) (remGoods goods ks T) X) {k : A} (hk : k ∈ ks) {g : G} :
    g ∈ bundle goods (liftAlloc ks T X) k ↔ g ∈ T k := by
  rw [mem_bundle]
  constructor
  · rintro ⟨hg, hgk⟩
    by_cases hin : ∃ k' ∈ ks, g ∈ T k'
    · obtain ⟨k', hk', hgk'⟩ := hin
      rw [liftAlloc_of_mem hdisj X hk' hgk'] at hgk
      rw [← hgk]; exact hgk'
    · have hno : ∀ k' ∈ ks, g ∉ T k' := fun k' hk' h => hin ⟨k', hk', h⟩
      rw [liftAlloc_of_not X hno] at hgk
      have := (mem_remAgents.mp (hX g (mem_remGoods.mpr ⟨hg, hno⟩))).2
      rw [hgk] at this
      exact absurd hk this
  · intro hg
    exact ⟨hTg k hk g hg, liftAlloc_of_mem hdisj X hk hg⟩

/-- A remaining agent's bundle in the lifted allocation is its bundle of `X`. -/
theorem mem_bundle_lift_rem {ks : List A} {T : A → List G}
    (hdisj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → ∀ g ∈ T k, g ∉ T k') {X : G → A} {a : A} (ha : a ∉ ks) {g : G} :
    g ∈ bundle goods (liftAlloc ks T X) a ↔ g ∈ bundle (remGoods goods ks T) X a := by
  rw [mem_bundle, mem_bundle, mem_remGoods]
  constructor
  · rintro ⟨hg, hga⟩
    have hno : ∀ k ∈ ks, g ∉ T k := fun k hk h => by
      rw [liftAlloc_of_mem hdisj X hk h] at hga
      exact ha (hga ▸ hk)
    rw [liftAlloc_of_not X hno] at hga
    exact ⟨⟨hg, hno⟩, hga⟩
  · rintro ⟨⟨hg, hno⟩, hga⟩
    exact ⟨hg, by rw [liftAlloc_of_not X hno]; exact hga⟩

/-- **Lemma LIFT\*** (K4.MATCH.LIFTSTAR, `k4/matching.md` §6; refereed CORRECT). Settled agents `k ∈ ks` with
pairwise disjoint sets `T k` (in rounds `rd k`), an EFX₀ allocation `X` of the remaining instance, (Φ) (`hΦ1`,
`hΦ2`), (L\*) at each settlement (`hL`, at values `w k a`) and values that never fall (`hmono`) give an EFX₀
allocation of the whole instance: `X` together with all the `T k`. -/
theorem liftStar (hgd : goods.Nodup) {ks : List A} (hks : ∀ k ∈ ks, k ∈ agents) {T : A → List G}
    (hT : ∀ k ∈ ks, (T k).Nodup ∧ ∀ g ∈ T k, g ∈ goods)
    (hdisj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → ∀ g ∈ T k, g ∉ T k') {X : G → A}
    (hX : IsAllocation (remAgents agents ks) (remGoods goods ks T) X)
    (hefx : EFX0L v (remAgents agents ks) (remGoods goods ks T) X) (rd : A → Nat) (w : A → A → Nat)
    (hΦ1 : ∀ k ∈ ks, ∀ j ∈ remAgents agents ks,
      ¬ Threat v k (bundle (remGoods goods ks T) X j) (value v k (T k)))
    (hΦ2 : ∀ k ∈ ks, ∀ k' ∈ ks, rd k < rd k' → ¬ Threat v k (T k') (value v k (T k)))
    (hL : ∀ k ∈ ks, ∀ a ∈ agents, a ≠ k → (a ∈ ks → rd k ≤ rd a) → ¬ Threat v a (T k) (w k a))
    (hmono : ∀ k ∈ ks, ∀ a ∈ agents, a ≠ k →
      (a ∉ ks → w k a ≤ value v a (bundle (remGoods goods ks T) X a)) ∧
      (a ∈ ks → rd k ≤ rd a → w k a ≤ value v a (T a))) :
    IsAllocation agents goods (liftAlloc ks T X) ∧ EFX0L v agents goods (liftAlloc ks T X) := by
  have hTg : ∀ k ∈ ks, ∀ g ∈ T k, g ∈ goods := fun k hk => (hT k hk).2
  have hrnd : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  -- the bundles of the lifted allocation
  have hBk : ∀ k ∈ ks, ∀ g, g ∈ bundle goods (liftAlloc ks T X) k ↔ g ∈ T k := fun k hk g =>
    mem_bundle_lift_settled hTg hdisj hX hk
  have hBa : ∀ a, a ∉ ks → ∀ g, g ∈ bundle goods (liftAlloc ks T X) a ↔ g ∈ bundle (remGoods goods ks T) X a :=
    fun a ha g => mem_bundle_lift_rem hdisj ha
  have hval_k : ∀ i : A, ∀ k ∈ ks, value v i (bundle goods (liftAlloc ks T X) k) = value v i (T k) := fun i k hk =>
    value_eq_of_mem_iff (nodup_bundle hgd _ k) (hT k hk).1 (hBk k hk)
  have hval_a : ∀ i : A, ∀ a, a ∉ ks →
      value v i (bundle goods (liftAlloc ks T X) a) = value v i (bundle (remGoods goods ks T) X a) :=
    fun i a ha => value_eq_of_mem_iff (nodup_bundle hgd _ a) (nodup_bundle hrnd X a) (hBa a ha)
  have hthr_k : ∀ i : A, ∀ c : Nat, ∀ k ∈ ks,
      Threat v i (bundle goods (liftAlloc ks T X) k) c ↔ Threat v i (T k) c := fun i c k hk =>
    threat_congr (nodup_bundle hgd _ k) (hT k hk).1 (hBk k hk)
  have hthr_a : ∀ i : A, ∀ c : Nat, ∀ a, a ∉ ks →
      (Threat v i (bundle goods (liftAlloc ks T X) a) c ↔ Threat v i (bundle (remGoods goods ks T) X a) c) :=
    fun i c a ha => threat_congr (nodup_bundle hgd _ a) (nodup_bundle hrnd X a) (hBa a ha)
  refine ⟨fun g hg => ?_, efx0L_iff.mpr fun i hi j hj hij => ?_⟩
  · by_cases hin : ∃ k ∈ ks, g ∈ T k
    · obtain ⟨k, hk, hgk⟩ := hin
      rw [liftAlloc_of_mem hdisj X hk hgk]; exact hks k hk
    · have hno : ∀ k ∈ ks, g ∉ T k := fun k hk h => hin ⟨k, hk, h⟩
      rw [liftAlloc_of_not X hno]
      exact (mem_remAgents.mp (hX g (mem_remGoods.mpr ⟨hg, hno⟩))).1
  · have hefx' := efx0L_iff.mp hefx
    by_cases hik : i ∈ ks <;> by_cases hjk : j ∈ ks
    · -- two settled agents
      rw [hval_k i i hik, hthr_k i _ j hjk]
      rcases Nat.lt_or_ge (rd i) (rd j) with hlt | hge
      · exact hΦ2 i hik j hjk hlt
      · exact not_threat_mono (hL j hjk i hi hij fun _ => hge) ((hmono j hjk i hi hij).2 hik hge)
    · -- a settled agent and a remaining bundle: (Φ)
      rw [hval_k i i hik, hthr_a i _ j hjk]
      exact hΦ1 i hik j (mem_remAgents.mpr ⟨hj, hjk⟩)
    · -- a remaining agent and a settled set: (L\*), then monotonicity
      rw [hval_a i i hik, hthr_k i _ j hjk]
      exact not_threat_mono (hL j hjk i hi hij fun h => absurd h hik) ((hmono j hjk i hi hij).1 hik)
    · -- two remaining agents: `X` is EFX₀
      rw [hval_a i i hik, hthr_a i _ j hjk]
      exact hefx' i (mem_remAgents.mpr ⟨hi, hik⟩) j (mem_remAgents.mpr ⟨hj, hjk⟩) hij

end liftStar

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.phantom_only
#print axioms EFX.Round.phantom_three
#print axioms EFX.Round.phantom_two
#print axioms EFX.Round.liftStar
