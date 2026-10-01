import EFX.DL13

/-!
# The move lemmas of the deficit-descent route (`k4/dl2.md` §4; ledger K4.DL2.MOVES.LEAN)

Work in progress (branch `formal/k4-dl2-moves`): Lemmas 1, 1′ and 6 of `k4/dl2.md` §4 (moves inside the min-frozen
class), stated over `InP`, `MinFrozen`, `NA` and `Frozen` of `EFX/C4min.lean` and the moves `MoveT1`, `MoveT3` of
`EFX/DL13.lean`. The deficit criteria follow.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

/-! ## List helpers -/

theorem eq_singleton_of_mem {G : Type} {l : List G} {g : G} (h : g ∈ l) (hl : l.length ≤ 1) : l = [g] := by
  match l, h, hl with
  | [a], h, _ => simp at h; rw [h]
  | _ :: _ :: _, _, hl => simp at hl

/-- If `p ⟹ q` on a list and both count the same, then `q ⟹ p` on it. -/
theorem countP_imp_of_eq {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = true → q a = true) → l.countP p = l.countP q →
      ∀ a ∈ l, q a = true → p a = true
  | [], _, _, a, ha, _ => by simp at ha
  | b :: l, himp, heq, a, ha, hq => by
    have hle : l.countP p ≤ l.countP q := List.countP_mono_left fun x hx => himp x (by simp [hx])
    rw [List.countP_cons, List.countP_cons] at heq
    have hb := himp b (by simp)
    have heq' : l.countP p = l.countP q := by
      by_cases hpb : p b = true
      · simp only [hpb, hb, ↓reduceIte] at heq; omega
      · by_cases hqb : q b = true <;> simp only [hpb, hqb, ↓reduceIte, Bool.false_eq_true] at heq <;> omega
    rcases List.mem_cons.mp ha with rfl | ha
    · by_cases hpb : p a = true
      · exact hpb
      · have : ¬ q a = true → False := fun h => h hq
        simp only [hpb, hq, ↓reduceIte, Bool.false_eq_true] at heq
        omega
    · exact countP_imp_of_eq (fun x hx => himp x (by simp [hx])) heq' a ha hq

/-- `countP p ≤ countP q + countP r` when `p ⟹ q ∨ r`. -/
theorem countP_le_add {α : Type} {p q r : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = true → q a = true ∨ r a = true) →
      l.countP p ≤ l.countP q + l.countP r
  | [], _ => by simp
  | b :: l, h => by
    have ih := countP_le_add (l := l) fun x hx => h x (by simp [hx])
    simp only [List.countP_cons]
    have hb := h b (by simp)
    by_cases hp : p b = true
    · rcases hb hp with hq | hr
      · simp only [hp, hq, ↓reduceIte]; split <;> omega
      · simp only [hp, hr, ↓reduceIte]; split <;> omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]; split <;> split <;> omega

variable {A G : Type} [DecidableEq A] [DecidableEq G]
variable {v : A → G → Nat} {agents : List A} {goods : List G} {base base' : G → Option A}

/-! ## Facts about 𝒫 -/

omit [DecidableEq G] in
/-- Two base maps that give `i` the same base agree on `base g = some i` for every good `g`. -/
theorem base_eq_some_iff {i : A} (h : baseOf goods base' i = baseOf goods base i) {g : G} (hg : g ∈ goods) :
    base' g = some i ↔ base g = some i := by
  constructor
  · intro hb
    have : g ∈ baseOf goods base i := h ▸ (mem_baseOf.mpr ⟨hg, hb⟩ : g ∈ baseOf goods base' i)
    exact (mem_baseOf.mp this).2
  · intro hb
    have : g ∈ baseOf goods base' i := h.symm ▸ (mem_baseOf.mpr ⟨hg, hb⟩ : g ∈ baseOf goods base i)
    exact (mem_baseOf.mp this).2

omit [DecidableEq G] in
/-- **An agent's needs depend only on its own base**: if `i` has the same base in `P` and `P′`, it has the same
value-based needs. -/
theorem vbNeeds_congr {i : A} (h : baseOf goods base' i = baseOf goods base i) (g : G) :
    vbNeeds v goods base' i g ↔ vbNeeds v goods base i g := by
  unfold vbNeeds
  constructor
  · rintro ⟨hg, hb, hlt⟩
    exact ⟨hg, fun e => hb ((base_eq_some_iff h hg).mpr e), h ▸ hlt⟩
  · rintro ⟨hg, hb, hlt⟩
    exact ⟨hg, fun e => hb ((base_eq_some_iff h hg).mp e), h.symm ▸ hlt⟩

omit [DecidableEq G] in
/-- An agent with the same base in `P` and `P′` is frozen in `P′` iff it is frozen in `P`, when the needed sets agree. -/
theorem frozen_congr {i : A} (h : baseOf goods base' i = baseOf goods base i)
    (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) :
    Frozen agents goods base' (vbNeeds v goods base') i ↔ Frozen agents goods base (vbNeeds v goods base) i := by
  unfold Frozen
  rw [h]
  exact exists_congr fun y => and_congr_right fun _ => hNA y

omit [DecidableEq G] in
/-- A needed good is a good of the instance. -/
theorem mem_goods_of_NA {g : G} (h : NA agents (vbNeeds v goods base) g) : g ∈ goods := by
  obtain ⟨_, _, hg, -⟩ := h
  exact hg

omit [DecidableEq G] in
/-- **On 𝒫 every needed good is the whole base of one listed agent** ((V1), (V2); `k4/c4x.md` §1). -/
theorem exists_base_of_NA (hP : InP v agents goods base) {g : G} (hg : NA agents (vbNeeds v goods base) g) :
    ∃ w ∈ agents, base g = some w ∧ baseOf goods base w = [g] := by
  have hgg := mem_goods_of_NA hg
  cases hb : base g with
  | none => exact absurd hg (hP.valid.v1 g (mem_junk.mpr ⟨hgg, hb⟩))
  | some w =>
    refine ⟨w, hP.mem g hgg w hb, rfl, ?_⟩
    have hmem : g ∈ baseOf goods base w := mem_baseOf.mpr ⟨hgg, hb⟩
    exact eq_singleton_of_mem hmem (Nat.le_of_not_lt fun hlt => hP.valid.v2 w hlt g hmem hg)

omit [DecidableEq G] in
/-- On 𝒫 a needed good lies in the base of a frozen listed agent. -/
theorem frozen_of_NA (hP : InP v agents goods base) {g : G} (hg : NA agents (vbNeeds v goods base) g) :
    ∃ w ∈ agents, base g = some w ∧ baseOf goods base w = [g] ∧
      Frozen agents goods base (vbNeeds v goods base) w := by
  obtain ⟨w, hw, hb, hB⟩ := exists_base_of_NA hP hg
  exact ⟨w, hw, hb, hB, g, hB, hg⟩

omit [DecidableEq G] in
/-- **A free agent's base contains no needed good** (`k4/dl2.md` §4, Setting). -/
theorem not_NA_of_mem_free (hP : InP v agents goods base) {i : A}
    (hfree : ¬ Frozen agents goods base (vbNeeds v goods base) i) {g : G} (hg : g ∈ baseOf goods base i) :
    ¬ NA agents (vbNeeds v goods base) g := fun hN => by
  obtain ⟨w, -, hb, hw⟩ := exists_base_of_NA hP hN
  have hi := (mem_baseOf.mp hg).2
  rw [hb] at hi
  cases hi
  exact hfree ⟨g, hw, hN⟩

omit [DecidableEq G] in
/-- A junk good is not needed ((V1)). -/
theorem not_NA_of_junk (hP : InP v agents goods base) {g : G} (hg : g ∈ goods) (hb : base g = none) :
    ¬ NA agents (vbNeeds v goods base) g :=
  hP.valid.v1 g (mem_junk.mpr ⟨hg, hb⟩)

omit [DecidableEq G] in
/-- An agent outside the list has an empty base when every base good goes to a listed agent. -/
theorem baseOf_eq_nil (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) {i : A} (hi : i ∉ agents) :
    baseOf goods base i = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun g hg =>
    hi (hmem g (mem_baseOf.mp hg).1 i (mem_baseOf.mp hg).2)

omit [DecidableEq G] in
/-- `nFrozen = |NA|` on 𝒫 (`EFX.LB4.numFrozen_eq`). -/
theorem nFrozen_eq_numNA (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base) :
    nFrozen v agents goods base = numNA agents goods (vbNeeds v goods base) :=
  numFrozen_eq hP.valid hag hgd hP.mem

/-! ## The general move: validity and the needed set -/

omit [DecidableEq G] in
/-- **The core of Lemmas 1(c), 1′ and 6** (`k4/dl2.md` §4). Let `P` be min-frozen with needed set `𝒩`, and let `P′` be
a base map whose base goods go to listed agents that value them, whose bases have at most two goods, whose needs lie in
`𝒩` (`NA(P′) ⊆ 𝒩`), and in which every good of `𝒩` is the whole base of some agent. Then `P′` is min-frozen and
`NA(P′) = 𝒩`. (Proof: `P′ ∈ 𝒫` by (V); `|F(P′)| = |NA(P′)| ≤ |𝒩| = f`, so equality by minimality.) -/
theorem minFrozen_of_cover (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hrel' : ∀ g ∈ goods, ∀ i, base' g = some i → 0 < v i g)
    (htwo' : ∀ i, (baseOf goods base' i).length ≤ 2)
    (hsub : ∀ i ∈ agents, ∀ g, vbNeeds v goods base' i g → NA agents (vbNeeds v goods base) g)
    (hcov : ∀ g, NA agents (vbNeeds v goods base) g → ∃ i, baseOf goods base' i = [g]) :
    MinFrozen v agents goods base' ∧
      ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g := by
  classical
  have hsubNA : ∀ g, NA agents (vbNeeds v goods base') g → NA agents (vbNeeds v goods base) g :=
    fun g ⟨i, hi, hN⟩ => hsub i hi g hN
  -- `P′ ∈ 𝒫`
  have hP' : InP v agents goods base' := by
    refine ⟨hmem', hrel', htwo', ⟨fun g hgJ hN => ?_, fun i h2 g hg hN => ?_⟩⟩
    · obtain ⟨i, hi⟩ := hcov g (hsubNA g hN)
      have hgi : g ∈ baseOf goods base' i := by rw [hi]; exact List.mem_singleton_self g
      have := (mem_baseOf.mp hgi).2
      rw [(mem_junk.mp hgJ).2] at this
      cases this
    · obtain ⟨w, hw⟩ := hcov g (hsubNA g hN)
      have hgw : g ∈ baseOf goods base' w := by rw [hw]; exact List.mem_singleton_self g
      have hwi : w = i := Option.some.inj ((mem_baseOf.mp hgw).2.symm.trans (mem_baseOf.mp hg).2)
      subst hwi
      rw [hw] at h2
      simp at h2
  -- counting
  have hle : numNA agents goods (vbNeeds v goods base') ≤ numNA agents goods (vbNeeds v goods base) := by
    unfold numNA
    exact List.countP_mono_left fun g _ h => by simpa using hsubNA g (by simpa using h)
  have hge := hM.2 base' hP'
  rw [nFrozen_eq_numNA hag hgd hM.1, nFrozen_eq_numNA hag hgd hP'] at hge
  have heq : numNA agents goods (vbNeeds v goods base') = numNA agents goods (vbNeeds v goods base) := by omega
  have hback : ∀ g, NA agents (vbNeeds v goods base) g → NA agents (vbNeeds v goods base') g := by
    intro g hg
    have := countP_imp_of_eq (l := goods) (p := fun g => decide (NA agents (vbNeeds v goods base') g))
      (q := fun g => decide (NA agents (vbNeeds v goods base) g))
      (fun g _ h => by simpa using hsubNA g (by simpa using h)) heq g (mem_goods_of_NA hg) (by simpa using hg)
    simpa using this
  refine ⟨⟨hP', fun b hb => ?_⟩, fun g => ⟨hsubNA g, hback g⟩⟩
  rw [nFrozen_eq_numNA hag hgd hP', heq, ← nFrozen_eq_numNA hag hgd hM.1]
  exact hM.2 b hb

omit [DecidableEq G] in
/-- With the same needed set, the frozen agents of `P′` are the agents whose base in `P′` is one good of `𝒩`. -/
theorem frozen_iff_of_NA (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g)
    (i : A) :
    Frozen agents goods base' (vbNeeds v goods base') i ↔
      ∃ g, baseOf goods base' i = [g] ∧ NA agents (vbNeeds v goods base) g :=
  exists_congr fun g => and_congr_right fun _ => hNA g

omit [DecidableEq G] in
/-- `ω(P′) = ω(P)` on 𝒫 when the needed sets agree (`ω = |NA| − (2n − m)`). -/
theorem omegaP_eq_of_NA (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base)
    (hP' : InP v agents goods base')
    (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) :
    omegaP v agents goods base' = omegaP v agents goods base := by
  classical
  rw [omegaP_eq hag hgd hP, omegaP_eq hag hgd hP', nFrozen_eq_numNA hag hgd hP, nFrozen_eq_numNA hag hgd hP']
  unfold numNA
  have : (fun g => decide (NA agents (vbNeeds v goods base') g)) =
      (fun g => decide (NA agents (vbNeeds v goods base) g)) := funext fun g => by simp [hNA g]
  rw [this]

/-! ## Lemma 1′, Lemma 1(c): re-bases of free agents -/

omit [DecidableEq G] in
/-- **Lemma 1′** (`k4/dl2.md` §4; several free agents, trades). Let `P` be min-frozen with needed set `𝒩`, `Y` a list of
agents free in `P`, and `P′` a base map in which every listed agent outside `Y` keeps its base and each `y ∈ Y` holds a
base `B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y` of at most two goods with `N_y(B′_y) ⊆ 𝒩` (base goods of `P′` go to listed
agents; the new bases are disjoint since `P′` is a map). Then `P′` is min-frozen, `NA(P′) = 𝒩`, `F(P′) = F(P)` and `ω` is
the same. -/
theorem lemma1' (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {Y : List A}
    (hY : ∀ y ∈ Y, y ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ∉ Y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ y ∈ Y, ∀ g ∈ goods, base' g = some y → (base g = none ∨ ∃ w ∈ Y, base g = some w) ∧ 0 < v y g)
    (htwo : ∀ y ∈ Y, (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ y ∈ Y, ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) :
    MinFrozen v agents goods base' ∧
      (∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) ∧
      (∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
        Frozen agents goods base (vbNeeds v goods base) i) ∧
      omegaP v agents goods base' = omegaP v agents goods base := by
  classical
  have hP := hM.1
  have hrel' : ∀ g ∈ goods, ∀ i, base' g = some i → 0 < v i g := by
    intro g hg i hb
    by_cases hiY : i ∈ Y
    · exact (hnew i hiY g hg hb).2
    · have hi := hmem' g hg i hb
      exact hP.rel g hg i ((base_eq_some_iff (hsame i hi hiY).symm hg).mp hb)
  have htwo' : ∀ i, (baseOf goods base' i).length ≤ 2 := by
    intro i
    by_cases hiY : i ∈ Y
    · exact htwo i hiY
    · by_cases hi : i ∈ agents
      · rw [← hsame i hi hiY]; exact hP.two i
      · rw [baseOf_eq_nil hmem' hi]; simp
  have hsub : ∀ i ∈ agents, ∀ g, vbNeeds v goods base' i g → NA agents (vbNeeds v goods base) g := by
    intro i hi g hN
    by_cases hiY : i ∈ Y
    · exact hadm i hiY g hN
    · exact ⟨i, hi, (vbNeeds_congr (hsame i hi hiY).symm g).mp hN⟩
  have hcov : ∀ g, NA agents (vbNeeds v goods base) g → ∃ i, baseOf goods base' i = [g] := by
    intro g hg
    obtain ⟨w, hw, -, hB, hF⟩ := frozen_of_NA hP hg
    have hwY : w ∉ Y := fun h => (hY w h).2 hF
    exact ⟨w, (hsame w hw hwY).symm.trans hB⟩
  obtain ⟨hM', hNA⟩ := minFrozen_of_cover hag hgd hM hmem' hrel' htwo' hsub hcov
  refine ⟨hM', hNA, fun i hi => ?_, omegaP_eq_of_NA hag hgd hP hM'.1 hNA⟩
  by_cases hiY : i ∈ Y
  · have hfree := (hY i hiY).2
    refine ⟨fun ⟨g, hB, hN⟩ => ?_, fun h => absurd h hfree⟩
    have hg : g ∈ baseOf goods base' i := by rw [hB]; exact List.mem_singleton_self g
    obtain ⟨hgg, hb'⟩ := mem_baseOf.mp hg
    rcases (hnew i hiY g hgg hb').1 with hb | ⟨w, hwY, hb⟩
    · exact (not_NA_of_junk hP hgg hb ((hNA g).mp hN)).elim
    · exact (not_NA_of_mem_free hP (hY w hwY).2 (mem_baseOf.mpr ⟨hgg, hb⟩) ((hNA g).mp hN)).elim
  · exact frozen_congr (hsame i hi hiY).symm hNA

omit [DecidableEq G] in
/-- **Lemma 1(c)** (`k4/dl2.md` §4; an admissible re-base). Let `P` be min-frozen with needed set `𝒩`, `y` free in `P`,
and `P′` the base map in which `y` holds `B′ ⊆ (B_y ∪ J) ∩ R_y` with `|B′| ≤ 2` and `N_y(B′) ⊆ 𝒩` (`B′` admissible for
`𝒩`) and every other listed agent keeps its base. Then `P′` is min-frozen, `NA(P′) = 𝒩`, `F(P′) = F(P)`,
`J(P′) = (J ∖ B′) ∪ (B_y ∖ B′)` and `ω` is the same. (The text also asks `B′ ≠ B_y`, which the conclusion does not
use.) -/
theorem lemma1c (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) :
    MinFrozen v agents goods base' ∧
      (∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) ∧
      (∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
        Frozen agents goods base (vbNeeds v goods base) i) ∧
      (∀ g, g ∈ LB4.junk goods base' ↔ g ∈ goods ∧ base' g ≠ some y ∧ (base g = none ∨ base g = some y)) ∧
      omegaP v agents goods base' = omegaP v agents goods base := by
  have hsame' : ∀ i ∈ agents, i ∉ [y] → baseOf goods base i = baseOf goods base' i :=
    fun i hi hiy => hsame i hi fun e => hiy (e ▸ List.mem_singleton_self i)
  obtain ⟨hM', hNA, hF, hω⟩ := lemma1' hag hgd hM (Y := [y])
    (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact ⟨hy, hyF⟩) hsame' hmem'
    (fun w hw g hg hb => by
      rw [List.mem_singleton] at hw; subst hw
      obtain ⟨h1 | h1, h2⟩ := hnew g hg hb
      · exact ⟨Or.inr ⟨w, List.mem_singleton_self w, h1⟩, h2⟩
      · exact ⟨Or.inl h1, h2⟩)
    (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact htwo)
    (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact hadm)
  refine ⟨hM', hNA, hF, fun g => ?_, hω⟩
  rw [mem_junk]
  constructor
  · rintro ⟨hg, hb'⟩
    refine ⟨hg, by rw [hb']; simp, ?_⟩
    cases hb : base g with
    | none => exact Or.inl rfl
    | some i =>
      by_cases hiy : i = y
      · exact Or.inr (by rw [hiy])
      · have := (base_eq_some_iff (hsame i (hM.1.mem g hg i hb) hiy).symm hg).mpr hb
        rw [hb'] at this; cases this
  · rintro ⟨hg, hby, hb⟩
    refine ⟨hg, ?_⟩
    cases hb' : base' g with
    | none => rfl
    | some i =>
      have hiy : i ≠ y := fun e => hby (by rw [hb', e])
      have := (base_eq_some_iff (hsame i (hmem' g hg i hb') hiy).symm hg).mp hb'
      rcases hb with hb | hb <;> rw [hb] at this <;> cases this
      exact absurd rfl hiy

/-! ## Lemma 1(a), (b): a min-frozen neighbour differing in one base -/

omit [DecidableEq G] in
/-- **Lemma 1(a)** (`k4/dl2.md` §4). If `P, P′ ∈ 𝒫` differ exactly in the base of one listed agent `y`, then `y` is
free in `P` and in `P′`, and `B′_y ⊆ (B_y ∪ J) ∩ R_y`. (The text assumes both min-frozen; only `P, P′ ∈ 𝒫` is used.) -/
theorem lemma1a (hP : InP v agents goods base) (hP' : InP v agents goods base') {y : A} (hy : y ∈ agents)
    (hne : baseOf goods base y ≠ baseOf goods base' y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i) :
    ¬ Frozen agents goods base (vbNeeds v goods base) y ∧ ¬ Frozen agents goods base' (vbNeeds v goods base') y ∧
      ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g := by
  have hsub : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g := by
    intro g hg hb'
    refine ⟨?_, hP'.rel g hg y hb'⟩
    cases hb : base g with
    | none => exact Or.inr rfl
    | some i =>
      refine Or.inl ?_
      by_cases hiy : i = y
      · rw [hiy]
      · have := (base_eq_some_iff (hsame i (hP.mem g hg i hb) hiy).symm hg).mpr hb
        rw [hb'] at this; exact absurd (Option.some.inj this).symm hiy
  have hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y := by
    rintro ⟨g, hB, i, hi, hN⟩
    have hgg : g ∈ goods := hN.1
    have hby : base g = some y := (mem_baseOf.mp (by rw [hB]; exact List.mem_singleton_self g)).2
    have hiy : i ≠ y := fun e => hN.2.1 (by rw [hby, e])
    have hN' : NA agents (vbNeeds v goods base') g :=
      ⟨i, hi, (vbNeeds_congr (hsame i hi hiy).symm g).mpr hN⟩
    obtain ⟨w, hw, hbw, hBw⟩ := exists_base_of_NA hP' hN'
    by_cases hwy : w = y
    · subst hwy; exact hne (hB.trans hBw.symm)
    · have := (base_eq_some_iff (hsame w hw hwy).symm hgg).mp hbw
      rw [hby] at this; exact hwy (Option.some.inj this).symm
  refine ⟨hyF, ?_, hsub⟩
  rintro ⟨h, hB', i, hi, hN⟩
  have hhg : h ∈ goods := hN.1
  have hby : base' h = some y := (mem_baseOf.mp (by rw [hB']; exact List.mem_singleton_self h)).2
  have hiy : i ≠ y := fun e => hN.2.1 (by rw [hby, e])
  have hNP : NA agents (vbNeeds v goods base) h := ⟨i, hi, (vbNeeds_congr (hsame i hi hiy).symm h).mp hN⟩
  rcases (hsub h hhg hby).1 with hb | hb
  · exact not_NA_of_mem_free hP hyF (mem_baseOf.mpr ⟨hhg, hb⟩) hNP
  · exact not_NA_of_junk hP hhg hb hNP

omit [DecidableEq G] in
/-- `|NA(P′)| = |NA(P)|` for two min-frozen pre-allocations. -/
theorem numNA_eq_of_minFrozen (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hM' : MinFrozen v agents goods base') :
    numNA agents goods (vbNeeds v goods base') = numNA agents goods (vbNeeds v goods base) := by
  have h1 := hM.2 base' hM'.1
  have h2 := hM'.2 base hM.1
  rw [nFrozen_eq_numNA hag hgd hM.1, nFrozen_eq_numNA hag hgd hM'.1] at h1 h2
  omega

omit [DecidableEq G] in
/-- Two min-frozen pre-allocations with `NA(P′) ⊆ NA(P)` have the same needed set. -/
theorem NA_eq_of_sub (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hM' : MinFrozen v agents goods base')
    (hsub : ∀ g, NA agents (vbNeeds v goods base') g → NA agents (vbNeeds v goods base) g) :
    ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g := by
  classical
  intro g
  refine ⟨hsub g, fun hg => ?_⟩
  have := countP_imp_of_eq (l := goods) (p := fun g => decide (NA agents (vbNeeds v goods base') g))
    (q := fun g => decide (NA agents (vbNeeds v goods base) g))
    (fun g _ h => by simpa using hsub g (by simpa using h)) (numNA_eq_of_minFrozen hag hgd hM hM')
    g (mem_goods_of_NA hg) (by simpa using hg)
  simpa using this

omit [DecidableEq G] in
/-- **Lemma 1(b)** (`k4/dl2.md` §4). Let `P, P′` be min-frozen and differ exactly in the base of one listed agent `y`.
Then `NA(P′) = 𝒩` iff `N_y(B′_y) ⊆ 𝒩`, and then `F(P′) = F(P)`; otherwise (a need transfer) some listed agent whose
base is unchanged changes its frozen status. -/
theorem lemma1b (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hM' : MinFrozen v agents goods base') {y : A} (hy : y ∈ agents)
    (hne : baseOf goods base y ≠ baseOf goods base' y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i) :
    ((∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) ↔
        ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) ∧
      ((∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) →
        ∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
          Frozen agents goods base (vbNeeds v goods base) i) ∧
      (¬ (∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) →
        ∃ i ∈ agents, i ≠ y ∧ baseOf goods base i = baseOf goods base' i ∧
          ¬ (Frozen agents goods base' (vbNeeds v goods base') i ↔ Frozen agents goods base (vbNeeds v goods base) i)) := by
  obtain ⟨hyF, hyF', -⟩ := lemma1a hM.1 hM'.1 hy hne hsame
  refine ⟨⟨fun h g hN => (h g).mp ⟨y, hy, hN⟩, fun h => NA_eq_of_sub hag hgd hM hM' ?_⟩, fun hNA i hi => ?_, fun hno => ?_⟩
  · rintro g ⟨i, hi, hN⟩
    by_cases hiy : i = y
    · subst hiy; exact h g hN
    · exact ⟨i, hi, (vbNeeds_congr (hsame i hi hiy).symm g).mp hN⟩
  · by_cases hiy : i = y
    · subst hiy; exact ⟨fun h => absurd h hyF', fun h => absurd h hyF⟩
    · exact frozen_congr (hsame i hi hiy).symm hNA
  · obtain ⟨g, hg⟩ : ∃ g, ¬ (NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) :=
      Classical.byContradiction fun h => hno fun g => Classical.byContradiction fun hg => h ⟨g, hg⟩
    by_cases hN : NA agents (vbNeeds v goods base) g
    · have hN' : ¬ NA agents (vbNeeds v goods base') g := fun h => hg ⟨fun _ => hN, fun _ => h⟩
      obtain ⟨w, hw, -, hB, hF⟩ := frozen_of_NA hM.1 hN
      have hwy : w ≠ y := fun e => hyF (e ▸ hF)
      refine ⟨w, hw, hwy, hsame w hw hwy, fun hiff => ?_⟩
      obtain ⟨g', hB', hN''⟩ := hiff.mpr hF
      rw [← hsame w hw hwy, hB] at hB'
      cases hB'
      exact hN' ((hiff.mpr hF).elim fun g'' ⟨hB'', hN3⟩ => by
        rw [← hsame w hw hwy, hB] at hB''; cases hB''; exact hN3)
    · have hN' : NA agents (vbNeeds v goods base') g := Classical.byContradiction fun h => hg ⟨fun h' => absurd h' h, fun h' => absurd h' hN⟩
      obtain ⟨w, hw, -, hB, hF⟩ := frozen_of_NA hM'.1 hN'
      have hwy : w ≠ y := fun e => hyF' (e ▸ hF)
      refine ⟨w, hw, hwy, hsame w hw hwy, fun hiff => ?_⟩
      obtain ⟨g', hB', hN''⟩ := hiff.mp hF
      rw [hsame w hw hwy, hB] at hB'
      cases hB'
      exact hN hN''

/-! ## Lemma 6: role swaps -/

omit [DecidableEq G] in
/-- **Lemma 6, last sentence** (`k4/dl2.md` §4). If `z` needs `g` in `P` (`g ∈ N_z`) and holds `{g}` in `P′`, then
`N_z({g}) ⊆ 𝒩`: a good worth more to `z` than `g` is worth more than `B_z`, so it lies outside `B_z` and in `N_z`. -/
theorem needs_single_sub {z : A} {g : G} (hz : z ∈ agents) (hzN : vbNeeds v goods base z g)
    (hz' : baseOf goods base' z = [g]) :
    ∀ g', vbNeeds v goods base' z g' → NA agents (vbNeeds v goods base) g' := by
  rintro g' ⟨hg', -, hlt⟩
  rw [hz'] at hlt
  have hlt' : v z g < v z g' := by simpa [value] using hlt
  refine ⟨z, hz, hg', fun hb => ?_, Nat.lt_trans hzN.2.2 hlt'⟩
  have := le_value_of_mem v z (mem_baseOf.mpr ⟨hg', hb⟩ : g' ∈ baseOf goods base z)
  have := hzN.2.2
  omega

omit [DecidableEq G] in
/-- **Lemma 6 (role swap)** (`k4/dl2.md` §4). Let `P` be min-frozen with needed set `𝒩`, `x` frozen with `B_x = {g}`,
`z` free with `g ∈ R_z`, and `H` a list of further free agents (the helpers). Let `P′` be `P` with `B′_z = {g}`, and new
bases for `x` and the helpers inside `G ∩ R`, where `G = J ∪ B_z ∪ ⋃_{h ∈ H} B_h`, of at most two goods each (disjoint
since `P′` is a map), every other listed agent keeping its base. If `N_x(B′_x)`, `N_z({g})` and every `N_h(B′_h)` lie in
`𝒩`, then `P′` is min-frozen, `NA(P′) = 𝒩` (so `g` is still needed), `F(P′) = (F ∖ {x}) ∪ {z}` and `ω` is the same. -/
theorem lemma6 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {x z : A} {g : G}
    {H : List A} (hx : x ∈ agents) (hxg : baseOf goods base x = [g]) (hgN : NA agents (vbNeeds v goods base) g)
    (hz : z ∈ agents) (hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z) (hzg : 0 < v z g)
    (hH : ∀ h ∈ H, h ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧ h ≠ x ∧ h ≠ z)
    (hsame : ∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ H → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hz' : baseOf goods base' z = [g])
    (hnew : ∀ i, (i = x ∨ i ∈ H) → ∀ g' ∈ goods, base' g' = some i →
      (base g' = none ∨ base g' = some z ∨ ∃ h ∈ H, base g' = some h) ∧ 0 < v i g')
    (htwo : ∀ i, (i = x ∨ i ∈ H) → (baseOf goods base' i).length ≤ 2)
    (hadm : ∀ i, (i = x ∨ i = z ∨ i ∈ H) → ∀ g', vbNeeds v goods base' i g' → NA agents (vbNeeds v goods base) g') :
    MinFrozen v agents goods base' ∧
      (∀ g', NA agents (vbNeeds v goods base') g' ↔ NA agents (vbNeeds v goods base) g') ∧
      (∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
        (Frozen agents goods base (vbNeeds v goods base) i ∧ i ≠ x) ∨ i = z) ∧
      omegaP v agents goods base' = omegaP v agents goods base := by
  classical
  have hP := hM.1
  have hxF : Frozen agents goods base (vbNeeds v goods base) x := ⟨g, hxg, hgN⟩
  have hxz : x ≠ z := fun e => hzF (e ▸ hxF)
  have hzH : z ∉ H := fun h => (hH z h).2.2.2 rfl
  have hxH : x ∉ H := fun h => (hH x h).2.2.1 rfl
  -- the goods the move may use are not needed
  have hG : ∀ g' ∈ goods, (base g' = none ∨ base g' = some z ∨ ∃ h ∈ H, base g' = some h) →
      ¬ NA agents (vbNeeds v goods base) g' := by
    rintro g' hg' (hb | hb | ⟨h, hh, hb⟩)
    · exact not_NA_of_junk hP hg' hb
    · exact not_NA_of_mem_free hP hzF (mem_baseOf.mpr ⟨hg', hb⟩)
    · exact not_NA_of_mem_free hP (hH h hh).2.1 (mem_baseOf.mpr ⟨hg', hb⟩)
  have hrel' : ∀ g' ∈ goods, ∀ i, base' g' = some i → 0 < v i g' := by
    intro g' hg' i hb
    by_cases hiz : i = z
    · subst hiz
      have : g' ∈ baseOf goods base' i := mem_baseOf.mpr ⟨hg', hb⟩
      rw [hz', List.mem_singleton] at this
      subst this; exact hzg
    by_cases hxH' : i = x ∨ i ∈ H
    · exact (hnew i hxH' g' hg' hb).2
    · have hi := hmem' g' hg' i hb
      have := (base_eq_some_iff (hsame i hi (fun e => hxH' (Or.inl e)) hiz
        (fun e => hxH' (Or.inr e))).symm hg').mp hb
      exact hP.rel g' hg' i this
  have htwo' : ∀ i, (baseOf goods base' i).length ≤ 2 := by
    intro i
    by_cases hiz : i = z
    · subst hiz; rw [hz']; simp
    by_cases hxH' : i = x ∨ i ∈ H
    · exact htwo i hxH'
    by_cases hi : i ∈ agents
    · rw [← hsame i hi (fun e => hxH' (Or.inl e)) hiz (fun e => hxH' (Or.inr e))]; exact hP.two i
    · rw [baseOf_eq_nil hmem' hi]; simp
  have hsub : ∀ i ∈ agents, ∀ g', vbNeeds v goods base' i g' → NA agents (vbNeeds v goods base) g' := by
    intro i hi g' hN
    by_cases hc : i = x ∨ i = z ∨ i ∈ H
    · exact hadm i hc g' hN
    · exact ⟨i, hi, (vbNeeds_congr (hsame i hi (fun e => hc (Or.inl e)) (fun e => hc (Or.inr (Or.inl e)))
        (fun e => hc (Or.inr (Or.inr e)))).symm g').mp hN⟩
  have hcov : ∀ g', NA agents (vbNeeds v goods base) g' → ∃ i, baseOf goods base' i = [g'] := by
    intro g' hg'
    obtain ⟨w, hw, -, hB, hF⟩ := frozen_of_NA hP hg'
    by_cases hwx : w = x
    · subst hwx; rw [hxg] at hB; cases hB; exact ⟨z, hz'⟩
    · have hwz : w ≠ z := fun e => hzF (e ▸ hF)
      have hwH : w ∉ H := fun h => (hH w h).2.1 hF
      exact ⟨w, (hsame w hw hwx hwz hwH).symm.trans hB⟩
  obtain ⟨hM', hNA⟩ := minFrozen_of_cover hag hgd hM hmem' hrel' htwo' hsub hcov
  refine ⟨hM', hNA, fun i hi => ?_, omegaP_eq_of_NA hag hgd hP hM'.1 hNA⟩
  rw [frozen_iff_of_NA hNA]
  by_cases hiz : i = z
  · subst hiz; exact ⟨fun _ => Or.inr rfl, fun _ => ⟨g, hz', hgN⟩⟩
  by_cases hxH' : i = x ∨ i ∈ H
  · refine ⟨fun ⟨g', hB, hN⟩ => ?_, fun h => ?_⟩
    · have : g' ∈ baseOf goods base' i := by rw [hB]; exact List.mem_singleton_self g'
      obtain ⟨hg', hb⟩ := mem_baseOf.mp this
      exact (hG g' hg' (hnew i hxH' g' hg' hb).1 hN).elim
    · rcases h with ⟨hF, hix⟩ | h
      · rcases hxH' with e | hiH
        · exact absurd e hix
        · exact absurd hF (hH i hiH).2.1
      · exact absurd h hiz
  · have hix : i ≠ x := fun e => hxH' (Or.inl e)
    rw [← hsame i hi hix hiz (fun e => hxH' (Or.inr e))]
    exact ⟨fun h => Or.inl ⟨h, hix⟩, fun h => h.elim (fun h => h.1) (fun h => absurd h hiz)⟩

/-! ## Lemmas 1 and 6 make (T1) and (T3) well defined -/

omit [DecidableEq G] in
/-- **(T1) stays in the min-frozen class** (Lemma 1(c)): a (T1) move (`MoveT1`) from a min-frozen `P` to a base map
`P′` whose base goods go to listed agents and whose bases have at most two goods gives a min-frozen `P′` with the same
frozen agents. -/
theorem minFrozen_of_moveT1 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (h : MoveT1 v agents goods base base') (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (htwo' : ∀ i, (baseOf goods base' i).length ≤ 2) :
    MinFrozen v agents goods base' ∧
      ∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
        Frozen agents goods base (vbNeeds v goods base) i := by
  obtain ⟨y, hy, hyF, -, hnew, hsame, hNA⟩ := h
  obtain ⟨hM', -, hF, -⟩ := lemma1c hag hgd hM hy hyF hsame hmem'
    (fun g hg hb => hnew g (mem_baseOf.mpr ⟨hg, hb⟩)) (htwo' y)
    (fun g hN => (hNA g).mpr ⟨y, hy, hN⟩)
  exact ⟨hM', hF⟩

omit [DecidableEq G] in
/-- **An admissible re-base is a (T1) move** (Lemma 1(c)): if `y` is free in the min-frozen `P` and `P′` re-bases `y`
to an admissible `B′ ≠ B_y`, then `P′` is a min-frozen (T1)-neighbour of `P`. -/
theorem moveT1_of_admissible (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hne : baseOf goods base y ≠ baseOf goods base' y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) :
    MinFrozen v agents goods base' ∧ MoveT1 v agents goods base base' := by
  obtain ⟨hM', hNA, -⟩ := lemma1c hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  exact ⟨hM', y, hy, hyF, hne, fun g hg => hnew g (mem_baseOf.mp hg).1 (mem_baseOf.mp hg).2, hsame,
    fun g => (hNA g).symm⟩

omit [DecidableEq G] in
/-- **(T1) on pairs of min-frozen pre-allocations** (Lemma 1(a), (b)): if `P, P′` are min-frozen and differ exactly in
the base of `y`, then `P → P′` is a (T1) move iff `N_y(B′_y) ⊆ 𝒩`. -/
theorem moveT1_iff_needs (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hM' : MinFrozen v agents goods base') {y : A} (hy : y ∈ agents)
    (hne : baseOf goods base y ≠ baseOf goods base' y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i) :
    MoveT1 v agents goods base base' ↔ ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g := by
  have hb := lemma1b hag hgd hM hM' hy hne hsame
  constructor
  · rintro ⟨-, -, -, -, -, -, hNA⟩
    exact hb.1.mp fun g => (hNA g).symm
  · intro h
    have hNA := hb.1.mpr h
    exact moveT1_of_inP hM.1 hM'.1 hy (lemma1a hM.1 hM'.1 hy hne hsame).1 hne hsame fun g => (hNA g).symm

omit [DecidableEq G] in
/-- **(T1) in the code's form** (`k4/dl2_relations.py`, `_one(s, nt_ok=False)`; Lemma 1(b)): if `P, P′` are
min-frozen and differ exactly in the base of `y`, then `P → P′` is a (T1) move (needed set unchanged) iff no listed
agent other than `y` changes its frozen status. This is the agreement that `EFX/DL13.lean` (module doc, item 2) leaves
to the text. -/
theorem moveT1_iff_status (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hM' : MinFrozen v agents goods base') {y : A} (hy : y ∈ agents)
    (hne : baseOf goods base y ≠ baseOf goods base' y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i) :
    MoveT1 v agents goods base base' ↔
      ∀ i ∈ agents, i ≠ y → (Frozen agents goods base' (vbNeeds v goods base') i ↔
        Frozen agents goods base (vbNeeds v goods base) i) := by
  have hb := lemma1b hag hgd hM hM' hy hne hsame
  have hyF := (lemma1a hM.1 hM'.1 hy hne hsame).1
  constructor
  · rintro ⟨-, -, -, -, -, -, hNA⟩ i hi _
    exact hb.2.1 (fun g => (hNA g).symm) i hi
  · intro h
    have hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g :=
      Classical.byContradiction fun hno => by
        obtain ⟨i, hi, hiy, -, hiff⟩ := hb.2.2 hno
        exact hiff (h i hi hiy)
    exact moveT1_of_inP hM.1 hM'.1 hy hyF hne hsame fun g => (hNA g).symm

omit [DecidableEq G] in
/-- **(T3) stays in the min-frozen class** (Lemma 6): a (T3) move (`MoveT3`) from a min-frozen `P` to a base map `P′`
whose base goods go to listed agents that value them and whose bases have at most two goods gives a min-frozen `P′`; the
frozen agents of `P′` are those of `P` with `x` replaced by `z` (`F(P′) = (F ∖ {x}) ∪ {z}`). -/
theorem minFrozen_of_moveT3 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (h : MoveT3 v agents goods base base') (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hrel' : ∀ g ∈ goods, ∀ i, base' g = some i → 0 < v i g)
    (htwo' : ∀ i, (baseOf goods base' i).length ≤ 2) :
    MinFrozen v agents goods base' ∧
      ∃ x ∈ agents, ∃ z ∈ agents, Frozen agents goods base (vbNeeds v goods base) x ∧
        ¬ Frozen agents goods base (vbNeeds v goods base) z ∧
        ∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
          (Frozen agents goods base (vbNeeds v goods base) i ∧ i ≠ x) ∨ i = z := by
  classical
  obtain ⟨x, hx, z, hz, g, hxg, hgN, hzF, -, hz', H, -, hH, hsame, hNA⟩ := h
  have hP := hM.1
  have hxF : Frozen agents goods base (vbNeeds v goods base) x := ⟨g, hxg, hgN⟩
  have hxz : x ≠ z := fun e => hzF (e ▸ hxF)
  have hcov : ∀ g', NA agents (vbNeeds v goods base) g' → ∃ i, baseOf goods base' i = [g'] := by
    intro g' hg'
    obtain ⟨w, hw, -, hB, hF⟩ := frozen_of_NA hP hg'
    by_cases hwx : w = x
    · subst hwx; rw [hxg] at hB; cases hB; exact ⟨z, hz'⟩
    · have hwz : w ≠ z := fun e => hzF (e ▸ hF)
      have hwH : w ∉ H := fun h => (hH w h).2.2.2.1 hF
      exact ⟨w, (hsame w hw hwx hwz hwH).symm.trans hB⟩
  obtain ⟨hM', hNA'⟩ := minFrozen_of_cover hag hgd hM hmem' hrel' htwo'
    (fun i hi g' hN => (hNA g').mpr ⟨i, hi, hN⟩) hcov
  refine ⟨hM', x, hx, z, hz, hxF, hzF, fun i hi => ?_⟩
  rw [frozen_iff_of_NA hNA']
  by_cases hiz : i = z
  · subst hiz; exact ⟨fun _ => Or.inr rfl, fun _ => ⟨g, hz', hgN⟩⟩
  by_cases hxH' : i = x ∨ i ∈ H
  · -- a good of `x`'s or a helper's new base is not needed: its frozen owner in `P` kept it, or it is `g`
    have hno : ∀ g', baseOf goods base' i = [g'] → ¬ NA agents (vbNeeds v goods base) g' := by
      intro g' hB hN
      have hgi : g' ∈ baseOf goods base' i := by rw [hB]; exact List.mem_singleton_self g'
      obtain ⟨hg', hb'⟩ := mem_baseOf.mp hgi
      obtain ⟨w, hw, -, hBw, hF⟩ := frozen_of_NA hP hN
      by_cases hwx : w = x
      · subst hwx; rw [hxg] at hBw
        have e : g = g' := List.singleton_inj.mp hBw
        have hgz : g' ∈ baseOf goods base' z := by rw [hz', e]; exact List.mem_singleton_self g'
        rw [(mem_baseOf.mp hgz).2] at hb'
        exact hiz (Option.some.inj hb').symm
      · have hwz : w ≠ z := fun e => hzF (e ▸ hF)
        have hwH : w ∉ H := fun h => (hH w h).2.2.2.1 hF
        have hgw : g' ∈ baseOf goods base' w := by rw [← hsame w hw hwx hwz hwH, hBw]; exact List.mem_singleton_self g'
        rw [(mem_baseOf.mp hgw).2] at hb'
        have hwi : w = i := Option.some.inj hb'
        subst hwi
        rcases hxH' with e | e
        · exact hwx e
        · exact hwH e
    refine ⟨fun ⟨g', hB, hN⟩ => (hno g' hB hN).elim, fun h => ?_⟩
    rcases h with ⟨hF, hix⟩ | h
    · rcases hxH' with e | hiH
      · exact absurd e hix
      · exact absurd hF (hH i hiH).2.2.2.1
    · exact absurd h hiz
  · have hix : i ≠ x := fun e => hxH' (Or.inl e)
    rw [← hsame i hi hix hiz (fun e => hxH' (Or.inr e))]
    exact ⟨fun h => Or.inl ⟨h, hix⟩, fun h => h.elim (fun h => h.1) (fun h => absurd h hiz)⟩

omit [DecidableEq G] in
/-- **A role swap with a needer and at most one helper giving up a good is a (T3) move** (Lemma 6): under the
hypotheses of `lemma6` with `g ∈ N_z` (so `N_z({g}) ⊆ 𝒩` is automatic), `|H| ≤ 1` and each helper giving up a good of
its base, `P′` is a min-frozen (T3)-neighbour of `P`. -/
theorem moveT3_of_lemma6 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {x z : A}
    {g : G} {H : List A} (hx : x ∈ agents) (hxg : baseOf goods base x = [g]) (hgN : NA agents (vbNeeds v goods base) g)
    (hz : z ∈ agents) (hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z) (hzN : vbNeeds v goods base z g)
    (hzg : 0 < v z g)
    (hH : ∀ h ∈ H, h ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧ h ≠ x ∧ h ≠ z)
    (hHlen : H.length ≤ 1) (hgive : ∀ h ∈ H, ∃ g' ∈ baseOf goods base h, g' ∉ baseOf goods base' h)
    (hsame : ∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ H → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hz' : baseOf goods base' z = [g])
    (hnew : ∀ i, (i = x ∨ i ∈ H) → ∀ g' ∈ goods, base' g' = some i →
      (base g' = none ∨ base g' = some z ∨ ∃ h ∈ H, base g' = some h) ∧ 0 < v i g')
    (htwo : ∀ i, (i = x ∨ i ∈ H) → (baseOf goods base' i).length ≤ 2)
    (hadm : ∀ i, (i = x ∨ i ∈ H) → ∀ g', vbNeeds v goods base' i g' → NA agents (vbNeeds v goods base) g') :
    MinFrozen v agents goods base' ∧ MoveT3 v agents goods base base' := by
  have hadm' : ∀ i, (i = x ∨ i = z ∨ i ∈ H) → ∀ g', vbNeeds v goods base' i g' → NA agents (vbNeeds v goods base) g' := by
    rintro i (e | e | e)
    · exact hadm i (Or.inl e)
    · subst e; exact needs_single_sub hz hzN hz'
    · exact hadm i (Or.inr e)
  obtain ⟨hM', hNA, -⟩ := lemma6 hag hgd hM hx hxg hgN hz hzF hzg hH hsame hmem' hz' hnew htwo hadm'
  exact ⟨hM', x, hx, z, hz, g, hxg, hgN, hzF, hzN, hz', H, hHlen,
    fun h hh => ⟨(hH h hh).1, (hH h hh).2.2.1, (hH h hh).2.2.2, (hH h hh).2.1, hgive h hh⟩, hsame,
    fun g' => (hNA g').symm⟩

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.minFrozen_of_cover
#print axioms EFX.C4min.lemma1'
#print axioms EFX.C4min.lemma1c
#print axioms EFX.C4min.lemma1a
#print axioms EFX.C4min.lemma1b
#print axioms EFX.C4min.needs_single_sub
#print axioms EFX.C4min.lemma6
#print axioms EFX.C4min.minFrozen_of_moveT1
#print axioms EFX.C4min.moveT1_of_admissible
#print axioms EFX.C4min.moveT1_iff_needs
#print axioms EFX.C4min.moveT1_iff_status
#print axioms EFX.C4min.minFrozen_of_moveT3
#print axioms EFX.C4min.moveT3_of_lemma6
