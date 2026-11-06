import EFX.DE4Robust

/-!
# Theorem A′: states in which every agent holds an upper set (`k4/de4.md` §10; ledger K4.DE4V3R.IMP)

In the robust order, a non-completable (V3)-valid state in which every agent holds an upper set has a better
(V3)-valid state: a free self-upgrade (Lemma 4′), or the rotation along a cycle of the threat relation, which raises
the robust level sum (`thmAllUpper`). With `conjRob_of_claimT` this gives `target4_of_claimT`: Claim T implies
TARGET₄.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section owner
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- The bundle of an owner `o` that takes every leftover good. -/
def ownerB (goods : List G) (base : G → Option A) (o : A) : List G :=
  goods.filter (fun g => decide (base g = some o ∨ base g = none))

/-- If some listed owner's bundle threatens no other listed agent, the state is completable (the owner takes every
leftover good). -/
theorem completable_of_owner {base : G → Option A} (hb : Valid v agents goods base) {o : A} (ho : o ∈ agents)
    (hown : ∀ i ∈ agents, i ≠ o → ∀ h ∈ ownerB goods base o,
      value v i ((ownerB goods base o).erase h) ≤ value v i (hold goods base i)) :
    Completable v agents goods base := by
  let X : G → A := fun g => (base g).getD o
  have hXo : bundle goods X o = ownerB goods base o := by
    unfold bundle ownerB
    apply List.filter_congr
    intro g _
    cases hbg : base g with
    | none => simp [X, hbg]
    | some k => by_cases hk : k = o <;> simp [X, hbg, hk]
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
    · subst hio; rw [hXo]
      exact value_sublist v i (filter_sublist_filter (fun g _ h => by
        simp only [decide_eq_true_eq] at h ⊢; exact Or.inl h))
    · rw [hXj i hio]; exact Nat.le_refl _
  refine ⟨X, fun g hg => ?_, fun g _ j hj => by simp [X, hj], ?_⟩
  · cases hbg : base g with
    | none => simp [X, hbg, ho]
    | some k => simpa [X, hbg] using hb.owners g hg k hbg
  · intro i hi j hj hij g hg
    by_cases hjo : j = o
    · subst hjo
      rw [hXo] at hg ⊢
      exact Nat.le_trans (hown i hi hij g hg) (hlow i)
    · rw [hXj j hjo] at hg ⊢
      exact Nat.le_trans (hb.v2 i hi j hj hij g hg) (hlow i)

end owner


section threat
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- `D_i`: the relevant goods of `i` outside its holding. -/
def dset (v : A → G → Nat) (goods : List G) (base : G → Option A) (i : A) : List G :=
  goods.filter (fun g => decide (0 < v i g ∧ base g ≠ some i))

omit [DecidableEq A] in
/-- An upper set has at least two goods. -/
theorem two_le_of_upper {i : A} {S : List G} (hS : IsUpper v i goods S) (hSg : ∀ g ∈ S, g ∈ goods) :
    2 ≤ S.length := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := value_le_of_length_le_one' (v := v) i (by omega : S.length ≤ 1) (c := topV v i goods)
    (fun g hg => le_topV v i goods (hSg g hg))
  have := hS.2.1
  omega

/-- `D_i` and the holding of an upper-set holder fill its relevant goods: at most four, so `|D_i| + |Y_i| ≤ 4`. -/
theorem dset_hold_length (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {base : G → Option A} {i : A}
    (hi : i ∈ agents) (hup : IsUpper v i goods (hold goods base i)) :
    (dset v goods base i).length + (hold goods base i).length ≤ 4 := by
  have hle := (hc i hi).2.1
  have := length_append_le (l₁ := dset v goods base i) (l₂ := hold goods base i) (r := relevant v i goods)
    (hgd.filter _) (nodup_hold hgd base i)
    (fun g hg hg' => by
      have h1 : 0 < v i g ∧ base g ≠ some i := by simpa using (List.mem_filter.mp hg).2
      exact h1.2 (mem_hold.mp hg').2)
    (fun g hg => by
      rcases List.mem_append.mp hg with h | h
      · have h1 : 0 < v i g ∧ base g ≠ some i := by simpa using (List.mem_filter.mp h).2
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp h).1, by simpa using h1.1⟩
      · exact List.mem_filter.mpr ⟨(mem_hold.mp h).1, by simpa using hup.1 g h⟩)
  omega

/-- **The threat structure.** If a bundle `B` with no good of `i`'s holding threatens an upper-set holder `i`, then
`i`'s holding and `D_i` have two goods each, `D_i ⊆ B`, and `D_i` is worth more than the holding. -/
theorem threat_struct (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {base : G → Option A} {i : A}
    (hi : i ∈ agents) (hup : IsUpper v i goods (hold goods base i)) {B : List G} (hBnd : B.Nodup)
    (hBg : ∀ g ∈ B, g ∈ goods) (hBdis : ∀ g ∈ B, base g ≠ some i) {h : G} (_hh : h ∈ B)
    (hlt : value v i (hold goods base i) < value v i (B.erase h)) :
    (∀ g ∈ dset v goods base i, g ∈ B) ∧ value v i (hold goods base i) < value v i (dset v goods base i) ∧
      (dset v goods base i).length = 2 ∧ (hold goods base i).length = 2 := by
  have hlen := dset_hold_length hgd hc hi hup
  have hY2 := two_le_of_upper hup (fun g hg => (mem_hold.mp hg).1)
  have hsubD : ∀ g ∈ (B.erase h).filter (fun g => decide (0 < v i g)), g ∈ dset v goods base i := by
    intro g hg
    have h1 := List.mem_filter.mp hg
    have hgB : g ∈ B := List.mem_of_mem_erase h1.1
    exact List.mem_filter.mpr ⟨hBg g hgB, by simpa using ⟨by simpa using h1.2, hBdis g hgB⟩⟩
  have hvB : value v i (B.erase h) ≤ value v i (dset v goods base i) := by
    rw [← value_filter_pos (v := v) i (B.erase h)]
    exact value_le_of_subset v i (((hBnd.erase h)).filter _) (hgd.filter _) hsubD
  have hgtD : value v i (hold goods base i) < value v i (dset v goods base i) := Nat.lt_of_lt_of_le hlt hvB
  have htop := hup.2.1
  have hD2 : 2 ≤ (dset v goods base i).length := by
    refine Nat.le_of_not_lt fun hl => ?_
    have := value_le_of_length_le_one' (v := v) i (by omega : (dset v goods base i).length ≤ 1)
      (c := topV v i goods) (fun g hg => le_topV v i goods (List.mem_filter.mp hg).1)
    omega
  refine ⟨fun g₀ hg₀ => Classical.byContradiction fun hn => ?_, hgtD, by omega, by omega⟩
  have hsub' : ∀ g ∈ (B.erase h).filter (fun g => decide (0 < v i g)), g ∈ (dset v goods base i).erase g₀ := by
    intro g hg
    have hgD := hsubD g hg
    have hgB : g ∈ B := List.mem_of_mem_erase (List.mem_filter.mp hg).1
    have hDnd : (dset v goods base i).Nodup := hgd.filter _
    rw [List.Nodup.mem_erase_iff hDnd]
    exact ⟨fun e => hn (e ▸ hgB), hgD⟩
  have hv1 : value v i (B.erase h) ≤ value v i ((dset v goods base i).erase g₀) := by
    rw [← value_filter_pos (v := v) i (B.erase h)]
    exact value_le_of_subset v i ((hBnd.erase h).filter _) ((hgd.filter (fun g => decide (0 < v i g ∧ base g ≠ some i))).erase g₀) hsub'
  have hlen1 : ((dset v goods base i).erase g₀).length ≤ 1 := by
    rw [List.length_erase_of_mem hg₀]; omega
  have := value_le_of_length_le_one' (v := v) i hlen1 (c := topV v i goods)
    (fun g hg => le_topV v i goods (List.mem_filter.mp (List.mem_of_mem_erase hg)).1)
  omega

end threat


section dsets
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem pair_of_length {α : Type} {l : List α} (h : l.length = 2) : ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

/-- No listed agent has a self-upgrade of at most two goods (Lemma 4′ does not apply). -/
def NoSelfUp (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ∀ x ∈ agents, ∀ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) →
    Allowed v x goods (goods.filter p) → (goods.filter p).length ≤ 2 →
    ¬ value v x (hold goods base x) < value v x (goods.filter p)

/-- `D_i` of a threatened upper-set holder is an upper set and robust. -/
theorem dset_upper_robust (hgd : goods.Nodup) {base : G → Option A} {i : A}
    (hup : IsUpper v i goods (hold goods base i))
    (hgt : value v i (hold goods base i) < value v i (dset v goods base i)) (hD2 : (dset v goods base i).length = 2) :
    IsUpper v i goods (dset v goods base i) ∧ IsRobust v i goods (dset v goods base i) := by
  have hDnd : (dset v goods base i).Nodup := hgd.filter _
  refine ⟨⟨fun g hg => by
      have : 0 < v i g ∧ base g ≠ some i := by simpa using (List.mem_filter.mp hg).2
      exact this.1, Nat.lt_trans hup.2.1 hgt, fun g hg => ?_⟩, ?_⟩
  · have hl : ((dset v goods base i).erase g).length ≤ 1 := by rw [List.length_erase_of_mem hg]; omega
    exact value_le_of_length_le_one' (v := v) i hl
      (fun g' hg' => le_topV v i goods (List.mem_filter.mp (List.mem_of_mem_erase hg')).1)
  · unfold IsRobust
    have hsub : ∀ g ∈ (goods.filter (fun g => decide (g ∉ dset v goods base i))).filter (fun g => decide (0 < v i g)),
        g ∈ hold goods base i := by
      intro g hg
      have h1 := List.mem_filter.mp hg
      have h2 := List.mem_filter.mp h1.1
      have hpos : 0 < v i g := by simpa using h1.2
      have hnot : g ∉ dset v goods base i := by simpa using h2.2
      refine mem_hold.mpr ⟨h2.1, Classical.byContradiction fun hn => hnot ?_⟩
      exact List.mem_filter.mpr ⟨h2.1, by simpa using ⟨hpos, hn⟩⟩
    rw [← value_filter_pos (v := v) i]
    have := value_le_of_subset v i ((hgd.filter _).filter _) (nodup_hold hgd base i) hsub
    omega

/-- `D_i` is not made of leftover goods only: otherwise `i` would take it (Lemma 4′). -/
theorem dset_not_leftover (hgd : goods.Nodup) {base : G → Option A} (hno : NoSelfUp v agents goods base) {i : A}
    (hi : i ∈ agents) (hup : IsUpper v i goods (hold goods base i))
    (hgt : value v i (hold goods base i) < value v i (dset v goods base i)) (hD2 : (dset v goods base i).length = 2) :
    ∃ g ∈ dset v goods base i, base g ≠ none := by
  refine Classical.byContradiction fun hn => ?_
  have hall : ∀ g ∈ dset v goods base i, base g = none := by
    intro g hg
    refine Classical.byContradiction fun h => hn ⟨g, hg, h⟩
  have hUR := dset_upper_robust hgd hup hgt hD2
  refine hno i hi (fun g => decide (0 < v i g ∧ base g ≠ some i)) (fun g hg hp => Or.inr (hall g ?_))
    (Or.inr (Or.inl hUR.1)) (by unfold dset at hD2; omega) (by unfold dset at hgt; exact hgt)
  exact List.mem_filter.mpr ⟨hg, hp⟩

end dsets


section top
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] in
theorem value_filter_pair (hgd : goods.Nodup) (i : A) {a b : G} (ha : a ∈ goods) (hb : b ∈ goods) (hab : a ≠ b) :
    value v i (goods.filter (fun g => decide (g = a ∨ g = b))) = v i a + v i b ∧
      (goods.filter (fun g => decide (g = a ∨ g = b))).length = 2 := by
  have hnd : [a, b].Nodup := by simp [hab]
  have h1 := value_le_of_subset v i (hgd.filter (fun g => decide (g = a ∨ g = b))) hnd
    (fun g hg => by have := (List.mem_filter.mp hg).2; simp at this; rcases this with rfl | rfl <;> simp)
  have h2 := value_le_of_subset v i hnd (hgd.filter (fun g => decide (g = a ∨ g = b)))
    (fun g hg => by
      simp at hg
      rcases hg with rfl | rfl
      · exact List.mem_filter.mpr ⟨ha, by simp⟩
      · exact List.mem_filter.mpr ⟨hb, by simp⟩)
  have l1 := List.Nodup.length_le_of_subset (hgd.filter (fun g => decide (g = a ∨ g = b)))
    (l₂ := [a, b]) (fun g hg => by have := (List.mem_filter.mp hg).2; simp at this; rcases this with rfl | rfl <;> simp)
  have l2 := List.Nodup.length_le_of_subset hnd (l₂ := goods.filter (fun g => decide (g = a ∨ g = b)))
    (fun g hg => by
      simp at hg
      rcases hg with rfl | rfl
      · exact List.mem_filter.mpr ⟨ha, by simp⟩
      · exact List.mem_filter.mpr ⟨hb, by simp⟩)
  have hab2 : value v i [a, b] = v i a + v i b := by simp [value]
  have hl2 : [a, b].length = 2 := rfl
  exact ⟨by omega, by omega⟩

omit [DecidableEq A] in
/-- The top good with any other relevant good is an upper set. -/
theorem pair_upper (hgd : goods.Nodup) {i : A} {a x : G} (ha : a ∈ goods) (hx : x ∈ goods) (hax : a ≠ x)
    (hta : v i a = topV v i goods) (hpa : 0 < v i a) (hpx : 0 < v i x) :
    IsUpper v i goods (goods.filter (fun g => decide (g = a ∨ g = x))) := by
  obtain ⟨hv, hl⟩ := value_filter_pair (v := v) hgd i ha hx hax
  refine ⟨fun g hg => ?_, by omega, fun g hg => ?_⟩
  · have := (List.mem_filter.mp hg).2; simp at this; rcases this with rfl | rfl <;> assumption
  · have hl1 : ((goods.filter (fun g => decide (g = a ∨ g = x))).erase g).length ≤ 1 := by
      rw [List.length_erase_of_mem hg]; omega
    exact value_le_of_length_le_one' (v := v) i hl1
      (fun g' hg' => le_topV v i goods (List.mem_filter.mp (List.mem_of_mem_erase hg')).1)

/-- **The top of a contested agent.** If `D_i` (two goods, worth more than `i`'s two-good holding) contains a leftover
good, then its other good `t` is `i`'s top, is held, and `{t, x}` is an upper set for every good `x` of `i`'s holding;
otherwise `i` would have a self-upgrade. -/
theorem dset_top (hgd : goods.Nodup) (hs : Strict v agents goods) (hc : R1Core4 v agents goods) {base : G → Option A}
    (hno : NoSelfUp v agents goods base) {i : A} (hi : i ∈ agents) (hup : IsUpper v i goods (hold goods base i))
    (hgt : value v i (hold goods base i) < value v i (dset v goods base i)) (hD2 : (dset v goods base i).length = 2)
    (hY2 : (hold goods base i).length = 2) {s : G} (hsD : s ∈ dset v goods base i) (hsJ : base s = none) :
    ∃ t ∈ dset v goods base i, base t ≠ none ∧ v i t = topV v i goods ∧
      (∀ g ∈ dset v goods base i, base g ≠ none → g = t) ∧
      ∀ x ∈ hold goods base i, IsUpper v i goods (goods.filter (fun g => decide (g = t ∨ g = x))) := by
  have htop := topV_pos hc hi
  obtain ⟨a, ha, hta⟩ := exists_topV v i goods htop
  have hpa : 0 < v i a := by omega
  obtain ⟨y1, y2, hY⟩ := pair_of_length hY2
  obtain ⟨d1, d2, hD⟩ := pair_of_length hD2
  have hDnd : (dset v goods base i).Nodup := hgd.filter _
  have hYnd : (hold goods base i).Nodup := nodup_hold hgd base i
  have hvY : value v i (hold goods base i) = v i y1 + v i y2 := by rw [hY]; simp [value]
  have hvD : value v i (dset v goods base i) = v i d1 + v i d2 := by rw [hD]; simp [value]
  have hmemD : ∀ g, g ∈ dset v goods base i ↔ g ∈ goods ∧ 0 < v i g ∧ base g ≠ some i := by
    intro g; unfold dset; simp
  have hsg : s ∈ goods := ((hmemD s).mp hsD).1
  have hsp : 0 < v i s := ((hmemD s).mp hsD).2.1
  have hy1 : y1 ∈ hold goods base i := by rw [hY]; simp
  have hy2 : y2 ∈ hold goods base i := by rw [hY]; simp
  have hy12 : y1 ≠ y2 := by intro e; rw [hY, e] at hYnd; simp at hYnd
  have hyg : ∀ y ∈ hold goods base i, y ∈ goods ∧ base y = some i := fun y hy => mem_hold.mp hy
  have hyp : ∀ y ∈ hold goods base i, 0 < v i y := fun y hy => hup.1 y hy
  -- the other good of D_i is worth at most the top
  have hoth : ∀ o ∈ dset v goods base i, v i o ≤ v i a := fun o ho => by
    rw [hta]; exact le_topV v i goods ((hmemD o).mp ho).1
  -- a self-upgrade {a, z} is excluded
  have hexcl : ∀ z, z ∈ goods → z ≠ a → 0 < v i z → (base a = some i ∨ base a = none) →
      (base z = some i ∨ base z = none) → ¬ value v i (hold goods base i) < v i a + v i z := by
    intro z hz hza hzp hba hbz hlt
    obtain ⟨hv, hl⟩ := value_filter_pair (v := v) hgd i ha hz (Ne.symm hza)
    refine hno i hi (fun g => decide (g = a ∨ g = z)) (fun g hg hp => ?_)
      (Or.inr (Or.inl (pair_upper hgd ha hz (Ne.symm hza) hta hpa hzp))) (by omega) (by rw [hv]; exact hlt)
    simp at hp; rcases hp with rfl | rfl
    · exact hba
    · exact hbz
  -- a is not in i's holding
  have haY : a ∉ hold goods base i := by
    intro haY
    have hsa : s ≠ a := fun e => by have := (hyg a haY).2; rw [← e, hsJ] at this; simp at this
    -- the other good y of the holding is worth less than s
    have hy : ∃ y ∈ hold goods base i, y ≠ a ∧ value v i (hold goods base i) = v i a + v i y := by
      rw [hY] at haY ⊢; simp at haY
      rcases haY with rfl | rfl
      · exact ⟨y2, by simp, Ne.symm hy12, by simp [value]⟩
      · exact ⟨y1, by simp, hy12, by simp [value]; omega⟩
    obtain ⟨y, hyY, hya, hvy⟩ := hy
    have hlt : v i y < v i s := by
      -- value(D) = v s + v o with v o ≤ v a
      have : ∃ o ∈ dset v goods base i, v i s + v i o = value v i (dset v goods base i) := by
        rw [hD] at hsD ⊢; simp at hsD
        rcases hsD with rfl | rfl
        · exact ⟨d2, by simp, by simp [value]⟩
        · exact ⟨d1, by simp, by simp [value]; omega⟩
      obtain ⟨o, ho, hvo⟩ := this
      have := hoth o ho
      omega
    exact hexcl s hsg hsa hsp (Or.inl (hyg a haY).2) (Or.inr hsJ) (by omega)
  have haD : a ∈ dset v goods base i := (hmemD a).mpr ⟨ha, hpa, fun e => haY (mem_hold.mpr ⟨ha, e⟩)⟩
  -- a is held
  have haJ : base a ≠ none := by
    intro haJ
    have hya1 : y1 ≠ a := fun e => haY (e ▸ hy1)
    have hya2 : y2 ≠ a := fun e => haY (e ▸ hy2)
    have hlt2 : v i y2 < v i a := by
      have hle : v i y2 ≤ v i a := by rw [hta]; exact le_topV v i goods (hyg y2 hy2).1
      have hne := strict_ne hs hi ha (hyg y2 hy2).1 (Ne.symm hya2) hpa
      omega
    exact hexcl y1 (hyg y1 hy1).1 hya1 (hyp y1 hy1) (Or.inr haJ) (Or.inl (hyg y1 hy1).2) (by omega)
  have hsa : s ≠ a := fun e => haJ (e ▸ hsJ)
  refine ⟨a, haD, haJ, hta, fun g hg hgJ => ?_, fun x hx => ?_⟩
  · -- D_i = {a, s}
    rw [hD] at hg hsD haD
    simp at hg hsD haD
    rcases hg with rfl | rfl <;> rcases hsD with rfl | rfl <;> rcases haD with rfl | rfl
    all_goals first | rfl | exact absurd hsJ hgJ | (exfalso; exact hsa rfl) | skip
    all_goals (rw [hD] at hDnd; simp at hDnd)
  · exact pair_upper hgd ha (hyg x hx).1 (fun e => haY (e ▸ hx)) hta hpa (hyp x hx)

end top


section rot
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- `o`'s bundle with every leftover good threatens `i`. -/
def Thr (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o i : A) : Prop :=
  i ∈ agents ∧ i ≠ o ∧ ∃ h ∈ ownerB goods base o,
    value v i (hold goods base i) < value v i ((ownerB goods base o).erase h)

/-- The hypotheses of the rotation: an all-upper valid state with no self-upgrade, and a cycle `C` of the threat
relation with its successor map `succ`. -/
structure RotCtx (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (C : List A)
    (succ : A → Option A) : Prop where
  hag : agents.Nodup
  hgd : goods.Nodup
  hs : Strict v agents goods
  hc : R1Core4 v agents goods
  hb : Valid v agents goods base
  hup : ∀ i ∈ agents, IsUpper v i goods (hold goods base i)
  hno : NoSelfUp v agents goods base
  hCnd : C.Nodup
  hCa : ∀ c ∈ C, c ∈ agents
  hsucc : ∀ c w, succ c = some w → c ∈ C ∧ w ∈ C ∧ Thr v agents goods base c w
  hinj : ∀ c c' w, succ c = some w → succ c' = some w → c = c'
  hpre : ∀ w ∈ C, ∃ p, succ p = some w
  hdef : ∀ c ∈ C, ∃ w, succ c = some w

variable {base : G → Option A} {C : List A} {succ : A → Option A}

/-- The structure of an agent of the cycle, from the threat of its predecessor. -/
theorem RotCtx.cyc (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C) :
    ∃ p, succ p = some c ∧ (∀ g ∈ dset v goods base c, base g = some p ∨ base g = none) ∧
      value v c (hold goods base c) < value v c (dset v goods base c) ∧
      (dset v goods base c).length = 2 ∧ (hold goods base c).length = 2 := by
  obtain ⟨p, hp⟩ := X.hpre c hcC
  obtain ⟨_, _, hca, hcp, h, hh, hlt⟩ := X.hsucc p c hp
  have hT := threat_struct X.hgd X.hc hca (X.hup c hca) (B := ownerB goods base p) (X.hgd.filter _)
    (fun g hg => (List.mem_filter.mp hg).1)
    (fun g hg e => by
      have := (List.mem_filter.mp hg).2
      simp only [decide_eq_true_eq] at this
      rcases this with h1 | h1 <;> rw [e] at h1 <;> simp at h1; exact hcp h1)
    hh hlt
  refine ⟨p, hp, fun g hg => ?_, hT.2.1, hT.2.2.1, hT.2.2.2⟩
  have := (List.mem_filter.mp (hT.1 g hg)).2
  simpa using this

open Classical in
/-- The owner of a leftover good: the first agent of the cycle whose `D` contains it. -/
noncomputable def ownG (v : A → G → Nat) (goods : List G) (base : G → Option A) (C : List A) (g : G) : Option A :=
  C.find? (fun c => decide (g ∈ dset v goods base c))

/-- `c` wins: it owns every leftover good of its `D`. -/
def Win (v : A → G → Nat) (goods : List G) (base : G → Option A) (C : List A) (c : A) : Prop :=
  ∀ g ∈ dset v goods base c, base g = none → ownG v goods base C g = some c

/-- `c`'s new holding: `D_c` for a winner; for a loser, the held goods of `D_c` and the goods of its holding that its
successor does not take. -/
def NewP (v : A → G → Nat) (goods : List G) (base : G → Option A) (C : List A) (succ : A → Option A) (c : A)
    (g : G) : Prop :=
  (Win v goods base C c ∧ g ∈ dset v goods base c) ∨
    (¬ Win v goods base C c ∧ ((g ∈ dset v goods base c ∧ base g ≠ none) ∨
      (base g = some c ∧ ∀ w, succ c = some w → g ∉ dset v goods base w)))

open Classical in
/-- The rotated state. -/
noncomputable def rotS (v : A → G → Nat) (goods : List G) (base : G → Option A) (C : List A)
    (succ : A → Option A) (g : G) : Option A :=
  match C.find? (fun c => decide (NewP v goods base C succ c g)) with
  | some c => some c
  | none => match base g with
    | some j => if j ∈ C then none else some j
    | none => none

/-- The three ways a good enters a new holding. -/
theorem RotCtx.newP_kind (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C) {g : G}
    (h : NewP v goods base C succ c g) :
    (base g = none ∧ ownG v goods base C g = some c) ∨
      (∃ p, succ p = some c ∧ base g = some p ∧ g ∈ dset v goods base c) ∨
      (base g = some c ∧ ∀ w, succ c = some w → g ∉ dset v goods base w) := by
  obtain ⟨p, hp, hsrc, _⟩ := X.cyc hcC
  rcases h with ⟨hW, hgD⟩ | ⟨_, ⟨hgD, hgJ⟩ | hk⟩
  · cases hbg : base g with
    | none => exact Or.inl ⟨rfl, hW g hgD hbg⟩
    | some j =>
      rcases hsrc g hgD with e | e <;> rw [hbg] at e
      · exact Or.inr (Or.inl ⟨p, hp, e, hgD⟩)
      · simp at e
  · rcases hsrc g hgD with e | e
    · exact Or.inr (Or.inl ⟨p, hp, e, hgD⟩)
    · exact absurd e hgJ
  · exact Or.inr (Or.inr hk)

/-- A good enters at most one new holding. -/
theorem RotCtx.newP_unique (X : RotCtx v agents goods base C succ) {g : G} {c c' : A} (hc : c ∈ C) (hc' : c' ∈ C)
    (h1 : NewP v goods base C succ c g) (h2 : NewP v goods base C succ c' g) : c = c' := by
  rcases X.newP_kind hc h1 with ⟨e1, o1⟩ | ⟨p1, hp1, e1, hg1⟩ | ⟨e1, k1⟩ <;>
    rcases X.newP_kind hc' h2 with ⟨e2, o2⟩ | ⟨p2, hp2, e2, hg2⟩ | ⟨e2, k2⟩
  · rw [o1] at o2; exact Option.some.inj o2
  · rw [e1] at e2; simp at e2
  · rw [e1] at e2; simp at e2
  · rw [e1] at e2; simp at e2
  · rw [e1] at e2
    have := Option.some.inj e2; subst this
    rw [hp1] at hp2; exact Option.some.inj hp2
  · rw [e1] at e2
    have := Option.some.inj e2; subst this
    exact absurd hg1 (k2 c hp1)
  · rw [e1] at e2; simp at e2
  · rw [e1] at e2
    have := Option.some.inj e2; subst this
    exact absurd hg2 (k1 c' hp2)
  · rw [e1] at e2; exact Option.some.inj e2

open Classical in
theorem RotCtx.hold_rot_C (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C) :
    hold goods (rotS v goods base C succ) c = goods.filter (fun g => decide (NewP v goods base C succ c g)) := by
  classical
  unfold hold
  apply List.filter_congr
  intro g _
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  unfold rotS
  constructor
  · intro h
    cases hf : C.find? (fun c => decide (NewP v goods base C succ c g)) with
    | some c' =>
      rw [hf] at h
      have := List.find?_some hf
      simp only [decide_eq_true_eq] at this
      simp only [Option.some.injEq] at h
      exact h ▸ this
    | none =>
      rw [hf] at h
      cases hbg : base g with
      | none => rw [hbg] at h; simp at h
      | some j =>
        rw [hbg] at h
        by_cases hjC : j ∈ C
        · simp [hjC] at h
        · simp only [hjC, ↓reduceIte, Option.some.injEq] at h
          exact absurd (h ▸ hcC) hjC
  · intro h
    cases hf : C.find? (fun c => decide (NewP v goods base C succ c g)) with
    | some c' =>
      have h' := List.find?_some hf
      simp only [decide_eq_true_eq] at h'
      rw [X.newP_unique (List.mem_of_find?_eq_some hf) hcC h' h]
    | none =>
      have := List.find?_eq_none.mp hf c hcC
      simp only [decide_eq_true_eq] at this
      exact absurd h this

open Classical in
theorem RotCtx.hold_rot_out (X : RotCtx v agents goods base C succ) {j : A} (hjC : j ∉ C) :
    hold goods (rotS v goods base C succ) j = hold goods base j := by
  classical
  unfold hold
  apply List.filter_congr
  intro g _
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  unfold rotS
  constructor
  · intro h
    cases hf : C.find? (fun c => decide (NewP v goods base C succ c g)) with
    | some c' =>
      rw [hf] at h
      simp only [Option.some.injEq] at h
      exact absurd (h ▸ List.mem_of_find?_eq_some hf) hjC
    | none =>
      rw [hf] at h
      cases hbg : base g with
      | none => rw [hbg] at h; simp at h
      | some j' =>
        rw [hbg] at h
        by_cases hj'C : j' ∈ C
        · simp [hj'C] at h
        · simp only [hj'C, ↓reduceIte] at h; exact h
  · intro h
    have hnone : C.find? (fun c => decide (NewP v goods base C succ c g)) = none := by
      rw [List.find?_eq_none]
      intro c hc hN
      simp only [decide_eq_true_eq] at hN
      rcases X.newP_kind hc hN with ⟨e, _⟩ | ⟨p, hp, e, _⟩ | ⟨e, _⟩
      · rw [h] at e; simp at e
      · rw [h] at e
        have := Option.some.inj e; subst this
        exact hjC (X.hsucc _ _ hp).1
      · rw [h] at e
        have := Option.some.inj e; subst this
        exact hjC hc
    rw [hnone, h]
    simp [hjC]

end rot


section rot2
variable {v : A → G → Nat} {agents : List A} {goods : List G}
variable {base : G → Option A} {C : List A} {succ : A → Option A}

omit [DecidableEq A] in
theorem filter_eq_single {goods : List G} (hgd : goods.Nodup) {t : G} (ht : t ∈ goods) :
    goods.filter (fun g => decide (g = t)) = [t] := by
  have hnd := hgd.filter (fun g => decide (g = t))
  have hmem : ∀ g, g ∈ goods.filter (fun g => decide (g = t)) ↔ g = t := by
    intro g; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => h.2, fun h => ⟨h ▸ ht, h⟩⟩
  have hl : (goods.filter (fun g => decide (g = t))).length ≤ 1 :=
    length_le_one_of_eq hnd (fun a ha b hb => ((hmem a).mp ha).trans ((hmem b).mp hb).symm)
  match hf : goods.filter (fun g => decide (g = t)), hl with
  | [], _ => have := (hmem t).mpr rfl; rw [hf] at this; simp at this
  | [x], _ => have := (hmem x).mp (by rw [hf]; simp); rw [this]

theorem RotCtx.hold_win (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C)
    (hW : Win v goods base C c) : hold goods (rotS v goods base C succ) c = dset v goods base c := by
  classical
  rw [X.hold_rot_C hcC]
  unfold dset
  apply List.filter_congr
  intro g hg
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  have hmem : g ∈ dset v goods base c ↔ 0 < v c g ∧ base g ≠ some c := by unfold dset; simp [hg]
  unfold NewP
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact hmem.mp h
    · exact absurd hW h
  · intro h; exact Or.inl ⟨hW, hmem.mpr h⟩

/-- A loser of the cycle: the held good `t` of its `D` is its top, and its new holding is `t` with the goods of its
holding that its successor does not take. -/
theorem RotCtx.loser (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C)
    (hW : ¬ Win v goods base C c) :
    ∃ t ∈ dset v goods base c, base t ≠ none ∧ v c t = topV v c goods ∧
      (∀ x ∈ hold goods base c, IsUpper v c goods (goods.filter (fun g => decide (g = t ∨ g = x)))) ∧
      hold goods (rotS v goods base C succ) c =
        goods.filter (fun g => decide (g = t ∨ (base g = some c ∧ ∀ w, succ c = some w →
          g ∉ dset v goods base w))) := by
  classical
  have hca := X.hCa c hcC
  obtain ⟨p, hp, hsrc, hgt, hD2, hY2⟩ := X.cyc hcC
  obtain ⟨s, hsD, hsJ⟩ : ∃ s ∈ dset v goods base c, base s = none := by
    refine Classical.byContradiction fun hn => hW fun g hg hgJ => absurd ⟨g, hg, hgJ⟩ hn
  obtain ⟨t, htD, htJ, htop, huniq, hup2⟩ :=
    dset_top X.hgd X.hs X.hc X.hno hca (X.hup c hca) hgt hD2 hY2 hsD hsJ
  refine ⟨t, htD, htJ, htop, hup2, ?_⟩
  rw [X.hold_rot_C hcC]
  apply List.filter_congr
  intro g hg
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  unfold NewP
  constructor
  · rintro (⟨h, _⟩ | ⟨_, ⟨hgD, hgJ⟩ | hk⟩)
    · exact absurd h hW
    · exact Or.inl (huniq g hgD hgJ)
    · exact Or.inr hk
  · rintro (rfl | hk)
    · exact Or.inr ⟨hW, Or.inl ⟨htD, htJ⟩⟩
    · exact Or.inr ⟨hW, Or.inr hk⟩

/-- The successor of `c` takes at least one good of `c`'s holding. -/
theorem RotCtx.succ_takes (X : RotCtx v agents goods base C succ) {c w : A} (hcw : succ c = some w) :
    ∃ y ∈ hold goods base c, y ∈ dset v goods base w := by
  obtain ⟨_, hwC, _⟩ := X.hsucc c w hcw
  have hwa := X.hCa w hwC
  obtain ⟨p, hp, hsrc, hgt, hD2, _⟩ := X.cyc hwC
  have hpc : p = c := X.hinj p c w hp hcw
  subst hpc
  obtain ⟨y, hyD, hyJ⟩ := dset_not_leftover X.hgd X.hno hwa (X.hup w hwa) hgt hD2
  rcases hsrc y hyD with e | e
  · exact ⟨y, mem_hold.mpr ⟨(List.mem_filter.mp hyD).1, e⟩, hyD⟩
  · exact absurd e hyJ

end rot2


section rot3
variable {v : A → G → Nat} {agents : List A} {goods : List G}
variable {base : G → Option A} {C : List A} {succ : A → Option A}

/-- The old robust level of an agent of the cycle is 5: an upper set that is not robust. -/
theorem RotCtx.level_old (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C) :
    levelR v c goods (hold goods base c) = 5 := by
  have hca := X.hCa c hcC
  obtain ⟨_, _, _, hgt, _, hY2⟩ := X.cyc hcC
  have hnr : ¬ IsRobust v c goods (hold goods base c) := by
    unfold IsRobust
    intro hR
    have hsub : ∀ g ∈ dset v goods base c, g ∈ goods.filter (fun g => decide (g ∉ hold goods base c)) := by
      intro g hg
      have h1 : 0 < v c g ∧ base g ≠ some c := by simpa using (List.mem_filter.mp hg).2
      exact List.mem_filter.mpr ⟨(List.mem_filter.mp hg).1, by simpa using fun e => h1.2 (mem_hold.mp e).2⟩
    have := value_le_of_subset v c (T := dset v goods base c)
      (L := goods.filter (fun g => decide (g ∉ hold goods base c))) (X.hgd.filter _) (X.hgd.filter _) hsub
    omega
  unfold levelR
  simp only [hnr, and_false, ↓reduceIte]
  rw [level_multi v c goods (by omega)]
  simp [(X.hup c hca).2.1]

omit [DecidableEq A] in
/-- The level of a single top good is 4. -/
theorem level_top_single {i : A} {t : G} (ht : v i t = topV v i goods) :
    levelR v i goods [t] = 4 := by
  have hnu : ¬ (IsUpper v i goods [t] ∧ IsRobust v i goods [t]) := by
    rintro ⟨hU, _⟩
    have := hU.2.1
    rw [value_singleton] at this
    omega
  unfold levelR
  simp only [hnu, ↓reduceIte]
  rw [level_single]
  have : (relevant v i goods).filter (fun g' => decide (v i t < v i g')) = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg
    have := le_topV v i goods (List.mem_filter.mp hg).1
    simp; omega
  rw [this]; rfl

/-- The new robust level of a winner is 6. -/
theorem RotCtx.level_win (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C)
    (hW : Win v goods base C c) : levelR v c goods (hold goods (rotS v goods base C succ) c) = 6 := by
  obtain ⟨_, _, _, hgt, hD2, _⟩ := X.cyc hcC
  have hUR := dset_upper_robust X.hgd (X.hup c (X.hCa c hcC)) hgt hD2
  rw [X.hold_win hcC hW]
  unfold levelR
  simp [hUR.1, hUR.2]

/-- The shape of a loser's new holding: its top alone if its successor takes all of its holding, else its top and
the good its successor leaves. -/
theorem RotCtx.loser_shape (X : RotCtx v agents goods base C succ) {c w : A} (hcC : c ∈ C) (hcw : succ c = some w)
    (hW : ¬ Win v goods base C c) :
    ∃ t, v c t = topV v c goods ∧ t ∈ goods ∧
      (((∀ x ∈ hold goods base c, x ∈ dset v goods base w) ∧
          hold goods (rotS v goods base C succ) c = [t]) ∨
        (∃ x ∈ hold goods base c, x ∉ dset v goods base w ∧
          hold goods (rotS v goods base C succ) c = goods.filter (fun g => decide (g = t ∨ g = x)) ∧
          IsUpper v c goods (goods.filter (fun g => decide (g = t ∨ g = x))))) := by
  obtain ⟨t, htD, htJ, htop, hup2, hnew⟩ := X.loser hcC hW
  have htg : t ∈ goods := (List.mem_filter.mp htD).1
  refine ⟨t, htop, htg, ?_⟩
  have hcond : ∀ g, (base g = some c ∧ ∀ w', succ c = some w' → g ∉ dset v goods base w') ↔
      (base g = some c ∧ g ∉ dset v goods base w) := by
    intro g
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 w hcw⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun w' hw' => ?_⟩
      rw [hcw] at hw'; cases hw'; exact h2
  by_cases hall : ∀ x ∈ hold goods base c, x ∈ dset v goods base w
  · refine Or.inl ⟨hall, ?_⟩
    rw [hnew, ← filter_eq_single X.hgd htg]
    apply List.filter_congr
    intro g hg
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, hcond]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · exact absurd (hall g (mem_hold.mpr ⟨hg, h1⟩)) h2
    · intro h; exact Or.inl h
  · obtain ⟨x, hx, hxw⟩ : ∃ x ∈ hold goods base c, x ∉ dset v goods base w := by
      refine Classical.byContradiction fun hn => hall fun x hx => ?_
      exact Classical.byContradiction fun hxw => hn ⟨x, hx, hxw⟩
    refine Or.inr ⟨x, hx, hxw, ?_, hup2 x hx⟩
    obtain ⟨y, hy, hyw⟩ := X.succ_takes hcw
    obtain ⟨_, _, _, _, _, hY2⟩ := X.cyc hcC
    rw [hnew]
    apply List.filter_congr
    intro g hg
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, hcond]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ?_
        have hgY : g ∈ hold goods base c := mem_hold.mpr ⟨hg, h1⟩
        obtain ⟨a, b, hab⟩ := pair_of_length hY2
        have hnd := nodup_hold X.hgd base c
        rw [hab] at hgY hx hy hnd
        simp at hgY hx hy hnd
        have hxy : x ≠ y := fun e => hxw (e ▸ hyw)
        have hgy : g ≠ y := fun e => h2 (e ▸ hyw)
        rcases hgY with rfl | rfl <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          first | rfl | exact absurd rfl hxy | exact absurd rfl hgy | exact absurd rfl hnd
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨(mem_hold.mp hx).2, hxw⟩

end rot3


section rot4
variable {v : A → G → Nat} {agents : List A} {goods : List G}
variable {base : G → Option A} {C : List A} {succ : A → Option A}

/-- Every agent's new holding is worth at least its top. -/
theorem RotCtx.value_ge_top (X : RotCtx v agents goods base C succ) {i : A} (hi : i ∈ agents) :
    topV v i goods ≤ value v i (hold goods (rotS v goods base C succ) i) := by
  by_cases hiC : i ∈ C
  · obtain ⟨_, _, _, hgt, hD2, _⟩ := X.cyc hiC
    by_cases hW : Win v goods base C i
    · rw [X.hold_win hiC hW]
      exact Nat.le_of_lt (Nat.lt_trans (X.hup i hi).2.1 hgt)
    · obtain ⟨w, hw⟩ := X.hdef i hiC
      obtain ⟨t, htop, _, h | ⟨x, _, _, hnew, hU⟩⟩ := X.loser_shape hiC hw hW
      · rw [h.2, value_singleton]; omega
      · rw [hnew]; exact Nat.le_of_lt hU.2.1
  · rw [X.hold_rot_out hiC]; exact Nat.le_of_lt (X.hup i hi).2.1

theorem RotCtx.len_le_two (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C) :
    (hold goods (rotS v goods base C succ) c).length ≤ 2 := by
  obtain ⟨_, _, _, _, hD2, _⟩ := X.cyc hcC
  by_cases hW : Win v goods base C c
  · rw [X.hold_win hcC hW]; omega
  · obtain ⟨w, hw⟩ := X.hdef c hcC
    obtain ⟨t, _, _, h | ⟨x, _, _, hnew, _⟩⟩ := X.loser_shape hcC hw hW
    · rw [h.2]; simp
    · rw [hnew]
      have := List.Nodup.length_le_of_subset (X.hgd.filter (fun g => decide (g = t ∨ g = x))) (l₂ := [t, x])
        (fun g hg => by
          have := (List.mem_filter.mp hg).2; simp at this; rcases this with rfl | rfl <;> simp)
      simpa using this

theorem RotCtx.allowed_rot (X : RotCtx v agents goods base C succ) {i : A} (hi : i ∈ agents) :
    Allowed v i goods (hold goods (rotS v goods base C succ) i) := by
  by_cases hiC : i ∈ C
  · obtain ⟨_, _, _, hgt, hD2, _⟩ := X.cyc hiC
    by_cases hW : Win v goods base C i
    · rw [X.hold_win hiC hW]
      exact Or.inr (Or.inl (dset_upper_robust X.hgd (X.hup i hi) hgt hD2).1)
    · obtain ⟨w, hw⟩ := X.hdef i hiC
      obtain ⟨t, htop, _, h | ⟨x, _, _, hnew, hU⟩⟩ := X.loser_shape hiC hw hW
      · rw [h.2]
        have := topV_pos X.hc hi
        exact Or.inl ⟨by simp, fun g hg => by simp at hg; subst hg; omega⟩
      · rw [hnew]; exact Or.inr (Or.inl hU)
  · rw [X.hold_rot_out hiC]; exact X.hb.allowed i hi

/-- An agent of the cycle values no good of an agent outside the cycle. -/
theorem RotCtx.zero_out (X : RotCtx v agents goods base C succ) {i j : A} (hiC : i ∈ C) (hjC : j ∉ C)
    {g : G} (hg : g ∈ hold goods base j) : v i g = 0 := by
  refine Nat.eq_zero_of_not_pos fun hpos => ?_
  obtain ⟨p, hp, hsrc, _⟩ := X.cyc hiC
  have hgj := mem_hold.mp hg
  have hij : i ≠ j := fun e => hjC (e ▸ hiC)
  have hgD : g ∈ dset v goods base i := List.mem_filter.mpr ⟨hgj.1, by
    simp only [decide_eq_true_eq]; exact ⟨hpos, by rw [hgj.2]; simp [Ne.symm hij]⟩⟩
  rcases hsrc g hgD with e | e <;> rw [hgj.2] at e
  · have := Option.some.inj e; subst this; exact hjC (X.hsucc _ _ hp).1
  · simp at e

/-- **The rotated state is (V3)-valid.** -/
theorem RotCtx.validV3 (X : RotCtx v agents goods base C succ) :
    ValidV3 v agents goods (rotS v goods base C succ) := by
  classical
  have hge := fun i hi => X.value_ge_top (i := i) hi
  refine ⟨⟨fun g hg j hj => ?_, fun i hi => X.allowed_rot hi, fun i hi g hg hlt => ?_,
    fun i hi j hj hij h hh => ?_⟩, fun i hi hlp => ?_⟩
  · unfold rotS at hj
    cases hf : C.find? (fun c => decide (NewP v goods base C succ c g)) with
    | some c =>
      rw [hf] at hj; simp only [Option.some.injEq] at hj; subst hj
      exact X.hCa _ (List.mem_of_find?_eq_some hf)
    | none =>
      rw [hf] at hj
      cases hbg : base g with
      | none => rw [hbg] at hj; simp at hj
      | some j' =>
        rw [hbg] at hj
        by_cases hj'C : j' ∈ C
        · simp [hj'C] at hj
        · simp only [hj'C, ↓reduceIte, Option.some.injEq] at hj; subst hj
          exact X.hb.owners g hg j' hbg
  · exfalso
    have := le_topV v i goods hg
    have := hge i hi
    omega
  · by_cases hl : (hold goods (rotS v goods base C succ) j).length ≤ 2
    · have hl1 : ((hold goods (rotS v goods base C succ) j).erase h).length ≤ 1 := by
        rw [List.length_erase_of_mem hh]; omega
      exact Nat.le_trans (value_le_of_length_le_one' (v := v) i hl1
        (fun g hg => le_topV v i goods (mem_hold.mp (List.mem_of_mem_erase hg)).1)) (hge i hi)
    · have hjC : j ∉ C := fun hjC => hl (X.len_le_two hjC)
      rw [X.hold_rot_out hjC] at hh ⊢
      by_cases hiC : i ∈ C
      · have hz : value v i ((hold goods base j).erase h) = 0 := by
          rw [← value_filter_pos (v := v) i]
          have : ((hold goods base j).erase h).filter (fun g => decide (0 < v i g)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro g hg
            have := X.zero_out hiC hjC (List.mem_of_mem_erase hg)
            simp [this]
          rw [this]; rfl
        rw [hz]; exact Nat.zero_le _
      · rw [X.hold_rot_out hiC]
        exact X.hb.v2 i hi j hj hij h hh
  · exfalso
    have := hlp.2.2.2.1
    have := hge i hi
    omega

end rot4


section rot5
variable {v : A → G → Nat} {agents : List A} {goods : List G}
variable {base : G → Option A} {C : List A} {succ : A → Option A}

omit [DecidableEq A] [DecidableEq G] in
theorem sum_map_split {α : Type} (f : α → Nat) (p : α → Bool) :
    ∀ l : List α, (l.map f).sum = ((l.filter p).map f).sum + ((l.filter (fun a => !p a)).map f).sum
  | [] => rfl
  | a :: t => by
    have ih := sum_map_split f p t
    by_cases hp : p a = true <;> simp [hp, ih] <;> omega

omit [DecidableEq A] [DecidableEq G] in
theorem sum_456 {α : Type} (f : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, 4 ≤ f a ∧ f a ≤ 6) →
      (l.map f).sum + (l.filter (fun a => decide (f a = 4))).length =
        5 * l.length + (l.filter (fun a => decide (f a = 6))).length
  | [], _ => rfl
  | a :: t, h => by
    have ih := sum_456 f t (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    by_cases h4 : f a = 4
    · have h6 : ¬ f a = 6 := by omega
      simp [h4] at ih ⊢; omega
    · by_cases h6 : f a = 6
      · simp [h6] at ih ⊢; omega
      · have h5 : f a = 5 := by omega
        simp [h5] at ih ⊢; omega

omit [DecidableEq A] [DecidableEq G] in
theorem sum_const {α : Type} (f : α → Nat) (c : Nat) :
    ∀ l : List α, (∀ a ∈ l, f a = c) → (l.map f).sum = c * l.length
  | [], _ => by simp
  | a :: t, h => by
    have ih := sum_const f c t (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp [h a List.mem_cons_self, ih, Nat.mul_succ]; omega

/-- If a loser's successor takes all of its holding, the successor wins. -/
theorem RotCtx.win_succ (X : RotCtx v agents goods base C succ) {c w : A} (hcw : succ c = some w)
    (hall : ∀ x ∈ hold goods base c, x ∈ dset v goods base w) :
    (∀ g ∈ dset v goods base w, g ∈ hold goods base c) ∧ Win v goods base C w := by
  obtain ⟨hcC, hwC, _⟩ := X.hsucc c w hcw
  obtain ⟨_, _, _, _, hDw, _⟩ := X.cyc hwC
  obtain ⟨_, _, _, _, _, hYc⟩ := X.cyc hcC
  have hsub := subset_of_length_le (nodup_hold X.hgd base c) hall (by omega)
  refine ⟨hsub, fun g hg hgJ => ?_⟩
  have := (mem_hold.mp (hsub g hg)).2
  rw [hgJ] at this; simp at this

/-- The head of the cycle wins: it owns every leftover good of its `D`. -/
theorem win_head {w₀ : A} {t : List A} : Win v goods base (w₀ :: t) w₀ := by
  intro g hg _
  unfold ownG
  simp [hg]

/-- A loser has lost a leftover good to a winner, whose `D` contains a leftover good. -/
theorem RotCtx.winner_of_loser (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C)
    (hW : ¬ Win v goods base C c) :
    ∃ z ∈ C, Win v goods base C z ∧ ∃ s ∈ dset v goods base z, base s = none := by
  classical
  obtain ⟨s, hsD, hsJ⟩ : ∃ s ∈ dset v goods base c, base s = none := by
    refine Classical.byContradiction fun hn => hW fun g hg hgJ => absurd ⟨g, hg, hgJ⟩ hn
  cases hf : ownG v goods base C s with
  | none =>
    unfold ownG at hf
    have := List.find?_eq_none.mp hf c hcC
    simp only [decide_eq_true_eq] at this
    exact absurd hsD this
  | some z =>
    have hzC : z ∈ C := by unfold ownG at hf; exact List.mem_of_find?_eq_some hf
    have hsz : s ∈ dset v goods base z := by
      unfold ownG at hf; have := List.find?_some hf; simpa using this
    have hza := X.hCa z hzC
    obtain ⟨_, _, _, hgt, hD2, _⟩ := X.cyc hzC
    obtain ⟨y, hyD, hyJ⟩ := dset_not_leftover X.hgd X.hno hza (X.hup z hza) hgt hD2
    refine ⟨z, hzC, fun g hg hgJ => ?_, s, hsz, hsJ⟩
    have hgs : g = s := by
      obtain ⟨a, b, hab⟩ := pair_of_length hD2
      have hnd : (dset v goods base z).Nodup := X.hgd.filter _
      rw [hab] at hg hsz hyD hnd
      simp at hg hsz hyD hnd
      have hgy : g ≠ y := fun e => hyJ (e ▸ hgJ)
      have hsy : s ≠ y := fun e => hyJ (e ▸ hsJ)
      rcases hg with rfl | rfl <;> rcases hsz with rfl | rfl <;> rcases hyD with rfl | rfl <;>
        first | rfl | exact absurd rfl hgy | exact absurd rfl hsy | exact absurd rfl hnd
    rw [hgs]; exact hf

/-- The new robust levels of the cycle are 4, 5 or 6, and 4 only for a loser whose successor takes its holding. -/
theorem RotCtx.level_new (X : RotCtx v agents goods base C succ) {c : A} (hcC : c ∈ C) :
    4 ≤ levelR v c goods (hold goods (rotS v goods base C succ) c) ∧
      levelR v c goods (hold goods (rotS v goods base C succ) c) ≤ 6 ∧
      (levelR v c goods (hold goods (rotS v goods base C succ) c) = 4 →
        ∀ w, succ c = some w → ∀ x ∈ hold goods base c, x ∈ dset v goods base w) := by
  refine ⟨?_, levelR_le_six v c goods _, ?_⟩
  · by_cases hW : Win v goods base C c
    · rw [X.level_win hcC hW]; omega
    · obtain ⟨w, hw⟩ := X.hdef c hcC
      obtain ⟨t, htop, _, h | ⟨x, _, _, hnew, hU⟩⟩ := X.loser_shape hcC hw hW
      · rw [h.2, level_top_single htop]; exact Nat.le_refl _
      · rw [hnew]
        have hl := two_le_of_upper hU (fun g hg => (List.mem_filter.mp hg).1)
        have h5 := level_multi v c goods hl
        simp only [hU.2.1, ↓reduceIte] at h5
        have := level_le_levelR v c goods (goods.filter (fun g => decide (g = t ∨ g = x)))
        omega
  · intro h4 w hw
    by_cases hW : Win v goods base C c
    · rw [X.level_win hcC hW] at h4; simp at h4
    · obtain ⟨t, htop, _, h | ⟨x, _, _, hnew, hU⟩⟩ := X.loser_shape hcC hw hW
      · exact h.1
      · exfalso
        rw [hnew] at h4
        have hl := two_le_of_upper hU (fun g hg => (List.mem_filter.mp hg).1)
        have h5 := level_multi v c goods hl
        simp only [hU.2.1, ↓reduceIte] at h5
        have := level_le_levelR v c goods (goods.filter (fun g => decide (g = t ∨ g = x)))
        omega

end rot5


section rot6
variable {v : A → G → Nat} {agents : List A} {goods : List G}
variable {base : G → Option A} {C : List A} {succ : A → Option A}

omit [DecidableEq A] [DecidableEq G] in
theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: t, hl, hinj => by
    have ht := (List.nodup_cons.mp hl)
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_on ht.2
      (fun x hx y hy e => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) e)⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    have := hinj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) e.symm
    exact ht.1 (this ▸ hb)

/-- **The rotation raises the robust level sum.** -/
theorem RotCtx.better (X : RotCtx v agents goods base C succ) {w₀ : A} (hw₀ : C.head? = some w₀) :
    ValidV3 v agents goods (rotS v goods base C succ) ∧
      BetterR v agents goods (rotS v goods base C succ) base := by
  classical
  refine ⟨X.validV3, Or.inl ?_⟩
  let f : A → Nat := fun i => levelR v i goods (hold goods (rotS v goods base C succ) i)
  let g : A → Nat := fun i => levelR v i goods (hold goods base i)
  let p : A → Bool := fun i => decide (i ∈ C)
  let L := agents.filter p
  let R := agents.filter (fun i => !p i)
  have hLC : ∀ i ∈ L, i ∈ C := fun i hi => by simpa [L, p] using (List.mem_filter.mp hi).2
  have hCL : ∀ i ∈ C, i ∈ L := fun i hi => List.mem_filter.mpr ⟨X.hCa i hi, by simpa [p] using hi⟩
  have hRC : ∀ i ∈ R, i ∉ C := fun i hi => by simpa [R, p] using (List.mem_filter.mp hi).2
  have hRfg : R.map f = R.map g := List.map_congr_left (fun i hi => by
    simp only [f, g]; rw [X.hold_rot_out (hRC i hi)])
  have hLg : (L.map g).sum = 5 * L.length := sum_const g 5 L (fun i hi => X.level_old (hLC i hi))
  have hLf := sum_456 f L (fun i hi => ⟨(X.level_new (hLC i hi)).1, (X.level_new (hLC i hi)).2.1⟩)
  -- the key count: more agents at level 6 than at level 4
  let s' : A → A := fun c => (succ c).getD c
  have hs' : ∀ c ∈ C, succ c = some (s' c) := by
    intro c hc
    obtain ⟨w, hw⟩ := X.hdef c hc
    simp [s', hw]
  have h4 : ∀ c ∈ L.filter (fun a => decide (f a = 4)),
      c ∈ C ∧ (∀ x ∈ hold goods base c, x ∈ dset v goods base (s' c)) := by
    intro c hc
    have hcC := hLC c (List.mem_filter.mp hc).1
    have hf4 : f c = 4 := by simpa using (List.mem_filter.mp hc).2
    exact ⟨hcC, (X.level_new hcC).2.2 hf4 (s' c) (hs' c hcC)⟩
  have hsub : ∀ c ∈ (L.filter (fun a => decide (f a = 4))).map s', c ∈ L.filter (fun a => decide (f a = 6)) := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    obtain ⟨hcC, hall⟩ := h4 c hc
    have hW := (X.win_succ (hs' c hcC) hall).2
    have hzC := (X.hsucc c (s' c) (hs' c hcC)).2.1
    exact List.mem_filter.mpr ⟨hCL _ hzC, by simpa [f] using X.level_win hzC hW⟩
  have hnd4 : (L.filter (fun a => decide (f a = 4))).Nodup := (X.hag.filter _).filter _
  have hndm : ((L.filter (fun a => decide (f a = 4))).map s').Nodup := by
    refine nodup_map_on hnd4 (fun x hx y hy e => ?_)
    have hx' := hs' x (h4 x hx).1
    have hy' := hs' y (h4 y hy).1
    rw [e] at hx'
    exact X.hinj x y _ hx' hy'
  have hextra : ∃ z ∈ L.filter (fun a => decide (f a = 6)), z ∉ (L.filter (fun a => decide (f a = 4))).map s' := by
    cases hl4 : L.filter (fun a => decide (f a = 4)) with
    | nil =>
      have hw₀C : w₀ ∈ C := List.mem_of_mem_head? hw₀
      obtain ⟨t, rfl⟩ : ∃ t, C = w₀ :: t := by
        cases C with
        | nil => simp at hw₀
        | cons a t => simp at hw₀; exact ⟨t, by rw [hw₀]⟩
      exact ⟨w₀, List.mem_filter.mpr ⟨hCL _ hw₀C, by simpa [f] using X.level_win hw₀C win_head⟩, by simp⟩
    | cons c rest =>
      have hc : c ∈ L.filter (fun a => decide (f a = 4)) := by rw [hl4]; simp
      have hcC := (h4 c hc).1
      have hf4 : f c = 4 := by simpa using (List.mem_filter.mp hc).2
      have hW : ¬ Win v goods base C c := fun hW => by
        have := X.level_win hcC hW; simp [f] at hf4; omega
      obtain ⟨z, hzC, hWz, s, hsz, hsJ⟩ := X.winner_of_loser hcC hW
      refine ⟨z, List.mem_filter.mpr ⟨hCL _ hzC, by simpa [f] using X.level_win hzC hWz⟩, fun hz => ?_⟩
      rw [← hl4] at hz
      obtain ⟨c', hc', e⟩ := List.mem_map.mp hz
      obtain ⟨hc'C, hall'⟩ := h4 c' hc'
      have hsub' := (X.win_succ (hs' c' hc'C) hall').1
      rw [e] at hsub'
      have := (mem_hold.mp (hsub' s hsz)).2
      rw [hsJ] at this; simp at this
  obtain ⟨z, hz6, hzn⟩ := hextra
  have hlen : (L.filter (fun a => decide (f a = 4))).length + 1 ≤ (L.filter (fun a => decide (f a = 6))).length := by
    have hnd' : (z :: (L.filter (fun a => decide (f a = 4))).map s').Nodup := List.nodup_cons.mpr ⟨hzn, hndm⟩
    have := List.Nodup.length_le_of_subset hnd' (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hz6
      · exact hsub a ha)
    simpa using this
  have hsplitf := sum_map_split f p agents
  have hsplitg := sum_map_split g p agents
  show (agents.map g).sum < (agents.map f).sum
  rw [hsplitf, hsplitg]
  change (L.map g).sum + (R.map g).sum < (L.map f).sum + (R.map f).sum
  rw [hRfg]
  omega

end rot6


section thmA
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- The self-upgrade of Lemma 4′ is a valid state. -/
theorem retake_valid {base : G → Option A} (hb : Valid v agents goods base) {x : A} (hx : x ∈ agents)
    (hfree : ∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y)
    (p : G → Bool) (hp : ∀ g ∈ goods, p g = true → base g = some x ∨ base g = none)
    (hN : Allowed v x goods (goods.filter p)) (hN2 : (goods.filter p).length ≤ 2)
    (hgain : value v x (hold goods base x) < value v x (goods.filter p)) :
    Valid v agents goods (retake base x p) := by
  have hself := hold_retake_self (goods := goods) base x p
  have hother : ∀ j, j ≠ x → hold goods (retake base x p) j = hold goods base j :=
    fun j hj => hold_retake_other hp hj
  have hval : ∀ i ∈ agents, value v i (hold goods base i) ≤ value v i (hold goods (retake base x p) i) := by
    intro i _
    by_cases hix : i = x
    · subst hix; rw [hself]; exact Nat.le_of_lt hgain
    · rw [hother i hix]; exact Nat.le_refl _
  refine valid_of_gain v agents goods (base := base) ?_ ?_ hval ?_ ?_
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

/-- **Theorem A′** (`k4/de4.md` §10). In the robust order, a non-completable (V3)-valid state in which every agent
holds an upper set has a better (V3)-valid state: a free self-upgrade, or the rotation along a cycle of the threat
relation, which raises the robust level sum. -/
theorem thmAllUpper : ThmAllUpper A G := by
  intro v agents goods hne hag hgd hc hs base hv3 hup hnc
  have hb := hv3.1
  have htopv : ∀ i ∈ agents, topV v i goods < value v i (hold goods base i) := fun i hi => (hup i hi).2.1
  by_cases hno : NoSelfUp v agents goods base
  · -- every owner's bundle threatens someone
    have hR : ∀ o ∈ agents, ∃ i ∈ agents, Thr v agents goods base o i := by
      intro o ho
      refine Classical.byContradiction fun hn => hnc (completable_of_owner hb ho fun i hi hio h hh => ?_)
      refine Nat.le_of_not_lt fun hlt => hn ⟨i, hi, hi, hio, h, hh, hlt⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a, a ∈ agents := by
      cases agents with
      | nil => exact absurd rfl hne
      | cons a t => exact ⟨a, List.mem_cons_self⟩
    obtain ⟨C, hCnd, hCc, hCa, c, w₀, hcl, hw₀, hcw⟩ :=
      exists_cycle_rel (Thr v agents goods base) hR agents.length [a₀] (by simp) (by simp) (by simp)
        (by simpa using ha₀) trivial
    obtain ⟨hspec, hinj, hcyc, hdef⟩ := cycNext_spec hCnd hCc hcl hw₀ hcw
    have X : RotCtx v agents goods base C (cycNext C c w₀) :=
      { hag := hag, hgd := hgd, hs := hs, hc := hc, hb := hb, hup := hup, hno := hno, hCnd := hCnd, hCa := hCa,
        hsucc := hspec, hinj := hinj,
        hpre := fun w hw => (hcyc w).mpr (hdef w hw),
        hdef := fun c' hc' => by
          cases h : cycNext C c w₀ c' with
          | none => exact absurd h (hdef c' hc')
          | some w => exact ⟨w, rfl⟩ }
    exact ⟨_, X.better hw₀⟩
  · -- a free self-upgrade (everyone is free: nobody wants anything)
    obtain ⟨x, hx, p, hp, hN, hN2, hgain⟩ : ∃ x ∈ agents, ∃ p : G → Bool,
        (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) ∧ Allowed v x goods (goods.filter p) ∧
        (goods.filter p).length ≤ 2 ∧ value v x (hold goods base x) < value v x (goods.filter p) := by
      refine Classical.byContradiction fun hn => hno fun x hx p hp hN hN2 hgain => hn ⟨x, hx, p, hp, hN, hN2, hgain⟩
    have hfree : ∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y := by
      intro y hy w hw hlt
      have := le_topV v w goods (mem_hold.mp hy).1
      have := htopv w hw
      omega
    have hself := hold_retake_self (goods := goods) base x p
    have hother : ∀ j, j ≠ x → hold goods (retake base x p) j = hold goods base j :=
      fun j hj => hold_retake_other hp hj
    have hvalid := retake_valid hb hx hfree p hp hN hN2 hgain
    have hNtop : topV v x goods < value v x (goods.filter p) := Nat.lt_trans (htopv x hx) hgain
    refine ⟨retake base x p, ⟨hvalid, fun i hi hlp => ?_⟩, ?_⟩
    · exfalso
      have h1 := hlp.2.2.2.1
      by_cases hix : i = x
      · subst hix; rw [hself] at h1; omega
      · rw [hother i hix] at h1; have := htopv i hi; omega
    · refine betterR_of_monotone v agents goods (fun i hi => ?_) (fun i hi => ?_) ⟨x, hx, by rw [hself]; exact hgain⟩
      · by_cases hix : i = x
        · subst hix
          rw [hself]
          exact levelR_mono v hgd (hb.allowed i hi) hN (nodup_hold hgd base i) (hgd.filter p)
            (fun g hg => (mem_hold.mp hg).1) (fun g hg => (List.mem_filter.mp hg).1) hgain
        · rw [hother i hix]; exact Nat.le_refl _
      · by_cases hix : i = x
        · subst hix; rw [hself]; exact Nat.le_of_lt hgain
        · rw [hother i hix]; exact Nat.le_refl _

/-- **Claim T implies TARGET₄** (machine-checked: Theorem A′, the robust order's maxima, and Lemma 3 as for DE4):
if every non-completable (V3)-valid state of the largest robust level sum has every agent holding an upper set, every
instance in which each agent positively values at most four goods has an EFX₀ allocation. -/
theorem target4_of_claimT (I : Inst) (hn : 0 < I.n) (h : ClaimT (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjRob I hn (conjRob_of_claimT h thmAllUpper) h4

end thmA

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.completable_of_owner
#print axioms EFX.DE4.two_le_of_upper
#print axioms EFX.DE4.dset_hold_length
#print axioms EFX.DE4.threat_struct
#print axioms EFX.DE4.pair_of_length
#print axioms EFX.DE4.dset_upper_robust
#print axioms EFX.DE4.dset_not_leftover
#print axioms EFX.DE4.value_filter_pair
#print axioms EFX.DE4.pair_upper
#print axioms EFX.DE4.dset_top
#print axioms EFX.DE4.RotCtx.cyc
#print axioms EFX.DE4.RotCtx.newP_kind
#print axioms EFX.DE4.RotCtx.newP_unique
#print axioms EFX.DE4.RotCtx.hold_rot_C
#print axioms EFX.DE4.RotCtx.hold_rot_out
#print axioms EFX.DE4.filter_eq_single
#print axioms EFX.DE4.RotCtx.hold_win
#print axioms EFX.DE4.RotCtx.loser
#print axioms EFX.DE4.RotCtx.succ_takes
#print axioms EFX.DE4.RotCtx.level_old
#print axioms EFX.DE4.level_top_single
#print axioms EFX.DE4.RotCtx.level_win
#print axioms EFX.DE4.RotCtx.loser_shape
#print axioms EFX.DE4.RotCtx.value_ge_top
#print axioms EFX.DE4.RotCtx.len_le_two
#print axioms EFX.DE4.RotCtx.allowed_rot
#print axioms EFX.DE4.RotCtx.zero_out
#print axioms EFX.DE4.RotCtx.validV3
#print axioms EFX.DE4.sum_map_split
#print axioms EFX.DE4.sum_456
#print axioms EFX.DE4.sum_const
#print axioms EFX.DE4.RotCtx.win_succ
#print axioms EFX.DE4.win_head
#print axioms EFX.DE4.RotCtx.winner_of_loser
#print axioms EFX.DE4.RotCtx.level_new
#print axioms EFX.DE4.nodup_map_on
#print axioms EFX.DE4.RotCtx.better
#print axioms EFX.DE4.retake_valid
#print axioms EFX.DE4.thmAllUpper
#print axioms EFX.DE4.target4_of_claimT
