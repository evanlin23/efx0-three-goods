import EFX.DL2Moves

/-!
# Role swaps and frozen rotations: Lemmas 8–12 of `k4/dl13.md` §2 (work in progress)

(module doc written below)
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]
variable {v : A → G → Nat} {agents : List A} {goods : List G} {base base' : G → Option A}

/-! ## `k4/dl13.md` §2.1, Lemma 11: an owner that does not move, through a role swap -/

/-- `countP p + 1 ≤ countP q + countP r` when `p ⟹ q ∨ r` and one listed `z` has `q` but not `p`. -/
theorem countP_succ_le_add {α : Type} {p q r : α → Bool} {z : α} :
    ∀ {l : List α}, l.Nodup → z ∈ l → (∀ a ∈ l, p a = true → q a = true ∨ r a = true) → p z = false →
      q z = true → l.countP p + 1 ≤ l.countP q + l.countP r
  | [], _, hz, _, _, _ => by simp at hz
  | b :: l, hnd, hz, h, hpz, hqz => by
    obtain ⟨hb, hl⟩ := List.nodup_cons.mp hnd
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hz with e | hz'
    · subst e
      have := countP_le_add (l := l) (p := p) (q := q) (r := r) fun a ha => h a (by simp [ha])
      simp only [hpz, hqz, Bool.false_eq_true, ↓reduceIte]
      split <;> omega
    · have ih := countP_succ_le_add hl hz' (fun a ha => h a (by simp [ha])) hpz hqz
      have hb' := h b (by simp)
      by_cases hp : p b = true
      · rcases hb' hp with hq | hr
        · simp only [hp, hq, ↓reduceIte]; split <;> omega
        · simp only [hp, hr, ↓reduceIte]; split <;> omega
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]; split <;> split <;> omega

/-- **Lemma 11 of `k4/dl13.md` §2.1 (an owner that does not move)**, in the generality of Lemma 2*: let `P, P′ ∈ 𝒫`
have the same needed set, `ω ≥ 1`, `o` free in `P` with an unchanged base, `X ⊆ Y` with `Y` a bundle of `o` in `P′`
that is safe in `P′`; let `z` be free in `P` with `B′_z = {g}`, `g ∈ 𝒩` (the needer of a role swap), and `κ = 1`:
`g ∉ N_o(Y)` and no listed agent other than `o, z` needs `g` in `P′` (the text's
`g ∉ N_o(Y) ∪ N_x(A) ∪ N_h(B′_h) ∪ 𝒩_{−{o,x,z,h}}`; `g ∉ N_z({g})` always). Then
`def(P′) ≤ ω + 2 − |Y| − (u_o(X) − e*) − 1`. (With `κ = 0` the bound is Lemma 2*, `lemma2star`. Here `e*` counts the
agents whose base actually changes, a subset of the text's `{x, z} ∪ H`, so it is at most the text's `e*`.) -/
theorem lemma11 (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base)
    (hP' : InP v agents goods base')
    (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g)
    (hω : 0 < omegaP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (hoB : baseOf goods base o = baseOf goods base' o)
    {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y) {z : A} {g : G} (hz : z ∈ agents)
    (hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z) (hz' : baseOf goods base' z = [g])
    (hgN : NA agents (vbNeeds v goods base) g) (hκ1 : ¬ setNeeds v goods o Y g)
    (hκ2 : ∀ i ∈ agents, i ≠ o → i ≠ z → ¬ vbNeeds v goods base' i g) :
    DeficitLE v agents goods base'
      (omegaP v agents goods base + 2 - ((goods.filter Y).length : Int) -
        ((uCount v agents goods base o X : Int) - (eStar v agents goods base base' o X : Int)) - 1) := by
  classical
  have hω' := omegaP_eq_of_NA hag hgd hP hP' hNA
  have hoF' : ¬ Frozen agents goods base' (vbNeeds v goods base') o := fun h =>
    hoF ((frozen_congr hoB.symm hNA).mp h)
  have hb := deficitLE_of_safe hag hP' (by rw [hω']; exact hω) ho hoF' hY hS
  rw [hω'] at hb
  -- `z` is counted in `u′_o(Y)`
  have hzc : Counted v agents goods base' o Y z := by
    refine ⟨⟨g, hz', (hNA g).mpr hgN⟩, fun g' hg' => ?_⟩
    rw [hz', List.mem_singleton] at hg'
    subst hg'
    refine ⟨hκ1, fun i hi hio hN => ?_⟩
    by_cases hiz : i = z
    · subst hiz; obtain ⟨-, hb', -⟩ := hN; exact hb' (mem_baseOf.mp (by rw [hz']; simp)).2
    · exact hκ2 i hi hio hiz hN
  have hu : uCount v agents goods base o X + 1 ≤
      uCount v agents goods base' o Y + eStar v agents goods base base' o X := by
    unfold uCount eStar
    refine countP_succ_le_add hag hz ?_ (by simpa using fun h : Counted v agents goods base o X z => hzF h.1)
      (decide_eq_true hzc)
    intro x _ hx
    have hx := of_decide_eq_true hx
    by_cases he : baseOf goods base x ≠ baseOf goods base' x ∨
        ∃ i ∈ agents, baseOf goods base i ≠ baseOf goods base' i ∧ ∃ g ∈ baseOf goods base x, vbNeeds v goods base' i g
    · exact Or.inr (decide_eq_true ⟨hx, he⟩)
    have hxB : baseOf goods base x = baseOf goods base' x := Classical.byContradiction fun h => he (Or.inl h)
    refine Or.inl (decide_eq_true ⟨(frozen_congr hxB.symm hNA).mpr hx.1, fun g hg => ⟨fun hN => ?_, fun i hi hio hN => ?_⟩⟩)
    · rw [← hxB] at hg
      exact (hx.2 g hg).1 (setNeeds_mono hXY hN)
    · rw [← hxB] at hg
      by_cases hiB : baseOf goods base i = baseOf goods base' i
      · exact (hx.2 g hg).2 i hi hio ((vbNeeds_congr hiB.symm g).mp hN)
      · exact he (Or.inr ⟨i, hi, hiB, g, hg, hN⟩)
  exact deficitLE_mono hb (by push_cast; omega)

/-! ## `u_o` counted over the goods (the bijection `F → 𝒩` on `𝒫`) -/

/-- A good counted by `u_o(Z)`: needed, and outside `N_o(Z) ∪ 𝒩₋ₒ`. -/
def CountGood (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A) (Z : G → Bool)
    (g : G) : Prop :=
  NA agents (vbNeeds v goods base) g ∧ ¬ setNeeds v goods o Z g ∧ ∀ i ∈ agents, i ≠ o → ¬ vbNeeds v goods base i g

omit [DecidableEq G] in
/-- `x` is counted in `u_o(Z)` iff its base is one good counted by `u_o(Z)`. -/
theorem counted_iff {o : A} {Z : G → Bool} {x : A} :
    Counted v agents goods base o Z x ↔ ∃ y, baseOf goods base x = [y] ∧ CountGood v agents goods base o Z y := by
  constructor
  · rintro ⟨⟨y, hB, hN⟩, h⟩
    have := h y (by rw [hB]; exact List.mem_singleton_self y)
    exact ⟨y, hB, hN, this⟩
  · rintro ⟨y, hB, hN, h1, h2⟩
    refine ⟨⟨y, hB, hN⟩, fun g hg => ?_⟩
    rw [hB, List.mem_singleton] at hg; subst hg; exact ⟨h1, h2⟩

omit [DecidableEq G] in
open Classical in
/-- **`u_o(Z)` as a count of goods** (`k4/dl13.md` §2.2, proof of Lemma 12): on `𝒫`, `w ↦ B_w` is a bijection from the
frozen agents to `𝒩`, so `u_o(Z) = #{h ∈ 𝒩 : h ∉ N_o(Z) ∪ 𝒩₋ₒ}`. -/
theorem uCount_eq_goods (hag : agents.Nodup) (hP : InP v agents goods base) (o : A)
    (Z : G → Bool) :
    uCount v agents goods base o Z = goods.countP (fun g => decide (CountGood v agents goods base o Z g)) := by
  have hj : ∀ j, (if Counted v agents goods base o Z j then 1 else 0) =
      goods.countP (fun g => decide (base g = some j) && decide (CountGood v agents goods base o Z g)) := by
    intro j
    have e : goods.countP (fun g => decide (base g = some j) && decide (CountGood v agents goods base o Z g)) =
        (baseOf goods base j).countP (fun g => decide (CountGood v agents goods base o Z g)) := by
      rw [baseOf, List.countP_filter]
      apply List.countP_congr
      intro g _
      simp [Bool.and_comm]
    rw [e]
    by_cases hex : ∃ g ∈ baseOf goods base j, CountGood v agents goods base o Z g
    · obtain ⟨g, hg, hc⟩ := hex
      obtain ⟨w, -, hbw, hBw⟩ := exists_base_of_NA hP hc.1
      have hwj : w = j := Option.some.inj (hbw.symm.trans (mem_baseOf.mp hg).2)
      subst hwj
      have hC : Counted v agents goods base o Z w := counted_iff.mpr ⟨g, hBw, hc⟩
      rw [hBw]; simp [hC, hc]
    · have hC : ¬ Counted v agents goods base o Z j := fun h => by
        obtain ⟨y, hB, hc⟩ := counted_iff.mp h
        exact hex ⟨y, by rw [hB]; exact List.mem_singleton_self y, hc⟩
      simp only [hC, ↓reduceIte]
      symm
      exact List.countP_eq_zero.mpr fun g hg h => hex ⟨g, hg, by simpa using h⟩
  unfold uCount
  rw [countP_eq_sum, countP_eq_sum]
  have e1 : (agents.map (fun j => if decide (Counted v agents goods base o Z j) = true then 1 else 0)) =
      agents.map (fun j => goods.countP
        (fun g => decide (base g = some j) && decide (CountGood v agents goods base o Z g))) := by
    apply List.map_congr_left
    intro j _
    rw [← hj j]
    simp
  rw [e1, sum_countP_comm (fun j g => decide (base g = some j) && decide (CountGood v agents goods base o Z g))
    agents goods]
  congr 1
  apply List.map_congr_left
  intro g hgg
  by_cases hc : CountGood v agents goods base o Z g
  · have hb : base g ≠ none := fun hb => not_NA_of_junk hP hgg hb hc.1
    have := countP_base agents hag (b := base g) (hP.mem g hgg)
    simp only [hb, ↓reduceIte] at this
    simp only [hc, decide_true, Bool.and_true, ↓reduceIte]
    exact this
  · simp [hc]

/-! ## `k4/dl13.md` §2.2, Lemma 12: frozen rotations -/

/-- **A Pareto reassignment** of the frozen agents' goods (`k4/dl13.md` §2.2): `π` maps each frozen listed `x` to a
frozen listed agent, `x` takes `B_{π(x)}` in `P′` and values it at least as much as `B_x`; every frozen agent is some
`π(x)` (so `π` permutes `F`: it is onto, and one-to-one because `P′` is a map); free agents keep their bases; base goods
of `P′` go to listed agents. -/
structure ParetoReassign (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A)
    (π : A → A) : Prop where
  frozen : ∀ x ∈ agents, Frozen agents goods base (vbNeeds v goods base) x →
    π x ∈ agents ∧ Frozen agents goods base (vbNeeds v goods base) (π x) ∧
      baseOf goods base' x = baseOf goods base (π x) ∧
      value v x (baseOf goods base x) ≤ value v x (baseOf goods base (π x))
  onto : ∀ w ∈ agents, Frozen agents goods base (vbNeeds v goods base) w →
    ∃ x ∈ agents, Frozen agents goods base (vbNeeds v goods base) x ∧ π x = w
  free : ∀ i ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) i → baseOf goods base i = baseOf goods base' i
  mem : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents

omit [DecidableEq G] in
/-- **Lemma 12, the move** (`k4/dl13.md` §2.2): a Pareto reassignment `P′` of a min-frozen `P` is min-frozen with the
same needed set, the same frozen agents, the same junk and the same `ω`; the free agents keep their bases and needs. -/
theorem lemma12_move (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {π : A → A}
    (hR : ParetoReassign v agents goods base base' π) :
    MinFrozen v agents goods base' ∧
      (∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g) ∧
      (∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
        Frozen agents goods base (vbNeeds v goods base) i) ∧
      (∀ g ∈ goods, base' g = none ↔ base g = none) ∧
      omegaP v agents goods base' = omegaP v agents goods base ∧
      (∀ i ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) i → ∀ g,
        vbNeeds v goods base' i g ↔ vbNeeds v goods base i g) := by
  classical
  have hP := hM.1
  -- each frozen agent's new base is one good of `𝒩`
  have hfz : ∀ x ∈ agents, Frozen agents goods base (vbNeeds v goods base) x →
      ∃ g', baseOf goods base' x = [g'] ∧ NA agents (vbNeeds v goods base) g' := by
    intro x hx hF
    obtain ⟨-, ⟨g', hB, hN⟩, hB', -⟩ := hR.frozen x hx hF
    exact ⟨g', hB'.trans hB, hN⟩
  have hrel' : ∀ g ∈ goods, ∀ i, base' g = some i → 0 < v i g := by
    intro g hg i hb
    have hi := hR.mem g hg i hb
    by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
    · obtain ⟨-, hπF, hB', hle⟩ := hR.frozen i hi hF
      obtain ⟨y, hBy, -⟩ := hF
      obtain ⟨g'', hB'', -⟩ := hπF
      have hgi : g ∈ baseOf goods base' i := mem_baseOf.mpr ⟨hg, hb⟩
      rw [hB', hB'', List.mem_singleton] at hgi
      subst hgi
      have hymem : y ∈ baseOf goods base i := by rw [hBy]; simp
      have hy := hP.rel y (mem_baseOf.mp hymem).1 i (mem_baseOf.mp hymem).2
      rw [hBy, hB''] at hle
      simp [value] at hle
      omega
    · exact hP.rel g hg i ((base_eq_some_iff (hR.free i hi hF).symm hg).mp hb)
  have htwo' : ∀ i, (baseOf goods base' i).length ≤ 2 := by
    intro i
    by_cases hi : i ∈ agents
    · by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
      · obtain ⟨g', hB, -⟩ := hfz i hi hF; rw [hB]; simp
      · rw [← hR.free i hi hF]; exact hP.two i
    · rw [baseOf_eq_nil hR.mem hi]; simp
  have hsub : ∀ i ∈ agents, ∀ g, vbNeeds v goods base' i g → NA agents (vbNeeds v goods base) g := by
    intro i hi g hN
    by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
    · obtain ⟨-, -, hB', hle⟩ := hR.frozen i hi hF
      exact ⟨i, hi, vbNeeds_mono (by rw [hB']; exact hle) hN⟩
    · exact ⟨i, hi, (vbNeeds_congr (hR.free i hi hF).symm g).mp hN⟩
  have hcov : ∀ g, NA agents (vbNeeds v goods base) g → ∃ i, baseOf goods base' i = [g] := by
    intro g hg
    obtain ⟨w, hw, -, hB, hF⟩ := frozen_of_NA hP hg
    obtain ⟨x, hx, hxF, hπx⟩ := hR.onto w hw hF
    obtain ⟨-, -, hB', -⟩ := hR.frozen x hx hxF
    exact ⟨x, by rw [hB', hπx, hB]⟩
  obtain ⟨hM', hNA⟩ := minFrozen_of_cover hag hgd hM hR.mem hrel' htwo' hsub hcov
  have hFF : ∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
      Frozen agents goods base (vbNeeds v goods base) i := by
    intro i hi
    by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
    · obtain ⟨g', hB, hN⟩ := hfz i hi hF
      exact ⟨fun _ => hF, fun _ => ⟨g', hB, (hNA g').mpr hN⟩⟩
    · exact (frozen_congr (hR.free i hi hF).symm hNA).trans ⟨fun h => h, fun h => h⟩
  refine ⟨hM', hNA, hFF, fun g hg => ⟨fun hb' => ?_, fun hb => ?_⟩, omegaP_eq_of_NA hag hgd hP hM'.1 hNA,
    fun i hi hF g => vbNeeds_congr (hR.free i hi hF).symm g⟩
  · cases hb : base g with
    | none => rfl
    | some i =>
      have hi := hP.mem g hg i hb
      by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
      · obtain ⟨y, hBy, hN⟩ := id hF
        have hgy : g = y := by
          have : g ∈ baseOf goods base i := mem_baseOf.mpr ⟨hg, hb⟩
          rw [hBy, List.mem_singleton] at this; exact this
        subst hgy
        obtain ⟨x, hB'⟩ := hcov g hN
        have : g ∈ baseOf goods base' x := by rw [hB']; simp
        rw [(mem_baseOf.mp this).2] at hb'; cases hb'
      · have := (base_eq_some_iff (hR.free i hi hF).symm hg).mpr hb
        rw [hb'] at this; cases this
  · cases hb' : base' g with
    | none => rfl
    | some i =>
      have hi := hR.mem g hg i hb'
      by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
      · obtain ⟨-, -, hB', -⟩ := hR.frozen i hi hF
        have : g ∈ baseOf goods base (π i) := by rw [← hB']; exact mem_baseOf.mpr ⟨hg, hb'⟩
        rw [(mem_baseOf.mp this).2] at hb; cases hb
      · have := (base_eq_some_iff (hR.free i hi hF).symm hg).mp hb'
        rw [hb] at this; cases this

omit [DecidableEq G] in
/-- `u_o` is monotone: `X ⊆ Y` gives `u_o(X) ≤ u_o(Y)` (by (M1)). -/
theorem uCount_mono {o : A} {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) :
    uCount v agents goods base o X ≤ uCount v agents goods base o Y := by
  classical
  unfold uCount
  apply List.countP_mono_left
  intro x _ h
  obtain ⟨hF, hc⟩ := of_decide_eq_true h
  exact decide_eq_true ⟨hF, fun g hg => ⟨fun hN => (hc g hg).1 (setNeeds_mono hXY hN), (hc g hg).2⟩⟩

/-- **Lemma 12** (`k4/dl13.md` §2.2, frozen rotations never raise the deficit). Let `P` be min-frozen with `ω ≥ 1` and
`P′` a Pareto reassignment of it. Then a free agent's bundles are the same in `P` and `P′`, every set safe for `o` in `P`
is safe in `P′`, `u′_o(Z) ≥ u_o(Z)` for every `o` and `Z`, and `def(P′) ≤ def(P)`. -/
theorem lemma12 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {π : A → A} (hR : ParetoReassign v agents goods base base' π) :
    (∀ o ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o → ∀ Z,
      IsBundle goods base' o Z ↔ IsBundle goods base o Z) ∧
    (∀ o Z, SafeFor v agents goods base o Z → SafeFor v agents goods base' o Z) ∧
    (∀ o Z, uCount v agents goods base o Z ≤ uCount v agents goods base' o Z) ∧
    DeficitDrop v agents goods base' base 0 := by
  classical
  obtain ⟨hM', hNA, hFF, hJ, hω', hNfree⟩ := lemma12_move hag hgd hM hR
  have hP := hM.1
  have hbun : ∀ o ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o → ∀ Z,
      IsBundle goods base' o Z ↔ IsBundle goods base o Z := by
    intro o ho hoF Z
    have hoB := hR.free o ho hoF
    unfold IsBundle
    refine forall_congr' fun g => forall_congr' fun hg => ?_
    rw [base_eq_some_iff hoB.symm hg, hJ g hg]
  have hsafe : ∀ o Z, SafeFor v agents goods base o Z → SafeFor v agents goods base' o Z := by
    intro o Z hS x hx hxo h hh
    refine Nat.le_trans (hS x hx hxo h hh) ?_
    by_cases hF : Frozen agents goods base (vbNeeds v goods base) x
    · obtain ⟨-, -, hB', hle⟩ := hR.frozen x hx hF
      rw [hB']; exact hle
    · rw [hR.free x hx hF]; exact Nat.le_refl _
  have hu : ∀ o Z, uCount v agents goods base o Z ≤ uCount v agents goods base' o Z := by
    intro o Z
    rw [uCount_eq_goods hag hP, uCount_eq_goods hag hM'.1]
    apply List.countP_mono_left
    intro g _ h
    obtain ⟨hN, h1, h2⟩ := of_decide_eq_true h
    refine decide_eq_true ⟨(hNA g).mpr hN, h1, fun i hi hio hN' => h2 i hi hio ?_⟩
    by_cases hF : Frozen agents goods base (vbNeeds v goods base) i
    · obtain ⟨-, -, hB', hle⟩ := hR.frozen i hi hF
      exact vbNeeds_mono (by rw [hB']; exact hle) hN'
    · exact (hNfree i hi hF g).mp hN'
  refine ⟨hbun, hsafe, hu, fun d hd => ?_⟩
  obtain ⟨o, ho, hoF, Z, hZ, hS, hle⟩ := exists_safe_of_deficitLE hag hP hω hd
  have hoF' : ¬ Frozen agents goods base' (vbNeeds v goods base') o := fun h => hoF ((hFF o ho).mp h)
  have hb := deficitLE_of_safe hag hM'.1 (by rw [hω']; exact hω) ho hoF' ((hbun o ho hoF Z).mpr hZ) (hsafe o Z hS)
  rw [hω'] at hb
  have := hu o Z
  exact deficitLE_mono hb (by omega)

/-- **Lemma 12, the strict case** (`k4/dl13.md` §2.2): after a Pareto reassignment, `def(P′) < def(P)` iff some free
listed `o` has a bundle `Z`, safe in `P′`, with `|Z| + u′_o(Z) > Val*(P)`. -/
theorem lemma12_lt_iff (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {π : A → A} (hR : ParetoReassign v agents goods base base' π) :
    DeficitLT v agents goods base' base ↔
      ∃ o ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o ∧ ∃ Z, IsBundle goods base o Z ∧
        SafeFor v agents goods base' o Z ∧
        ∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z', IsBundle goods base o' Z' →
          SafeFor v agents goods base o' Z' →
            ((goods.filter Z').length : Int) + (uCount v agents goods base o' Z' : Int) <
              ((goods.filter Z).length : Int) + (uCount v agents goods base' o Z : Int) := by
  obtain ⟨hM', -, hFF, -, hω', -⟩ := lemma12_move hag hgd hM hR
  obtain ⟨hbun, -, -, -⟩ := lemma12 hag hgd hM hω hR
  have hω'' : 0 < omegaP v agents goods base' := by rw [hω']; exact hω
  constructor
  · rintro ⟨d, hd, hnd⟩
    obtain ⟨o, ho, hoF', Z, hZ, hS, hle⟩ := exists_safe_of_deficitLE hag hM'.1 hω'' hd
    have hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o := fun h => hoF' ((hFF o ho).mpr h)
    refine ⟨o, ho, hoF, Z, (hbun o ho hoF Z).mp hZ, hS, fun o' ho' hoF'' Z' hZ' hS' => ?_⟩
    rw [hω'] at hle
    exact Classical.byContradiction fun hge =>
      hnd (deficitLE_mono (deficitLE_of_safe hag hM.1 hω ho' hoF'' hZ' hS') (by omega))
  · rintro ⟨o, ho, hoF, Z, hZ, hS, hval⟩
    have hoF' : ¬ Frozen agents goods base' (vbNeeds v goods base') o := fun h => hoF ((hFF o ho).mp h)
    have hb := deficitLE_of_safe hag hM'.1 hω'' ho hoF' ((hbun o ho hoF Z).mpr hZ) hS
    rw [hω'] at hb
    have hn := not_deficitLE_of_val_lt hag hM.1 hω hval
    exact ⟨_, hb, fun h => hn (deficitLE_mono h (by omega))⟩

/-- **Lemma 12, the two particular cases** (`k4/dl13.md` §2.2): with `X` an optimal bundle of a best owner `o`, a
Pareto reassignment lowers the deficit when `u′_o(X) > u_o(X)`, or when some junk good `c ∉ X` makes `X ∪ {c}` safe in
`P′` (every blocker of `c` moved, and `X ∪ {c}` threatens none of them holding its new good). -/
theorem lemma12_lt (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {π : A → A} (hR : ParetoReassign v agents goods base base' π)
    {o : A} {X : G → Bool} (hX : OptimalBest v agents goods base o X)
    (h : uCount v agents goods base o X < uCount v agents goods base' o X ∨
      ∃ c ∈ goods, base c = none ∧ X c = false ∧
        SafeFor v agents goods base' o (fun g => X g || decide (g = c))) :
    DeficitLT v agents goods base' base := by
  obtain ⟨ho, hoF, hXb, hXs, hmax⟩ := hX
  obtain ⟨-, hsafe, hu, -⟩ := lemma12 hag hgd hM hω hR
  refine (lemma12_lt_iff hag hgd hM hω hR).mpr ?_
  rcases h with hlt | ⟨c, hc, hcJ, hcX, hS⟩
  · refine ⟨o, ho, hoF, X, hXb, hsafe o X hXs, fun o' ho' hoF' Z' hZ' hS' => ?_⟩
    have := hmax o' ho' hoF' Z' hZ' hS'
    omega
  · have hY : IsBundle goods base o (fun g => X g || decide (g = c)) := by
      intro g hg
      refine ⟨fun hb => by simp [(hXb g hg).1 hb], fun hy => ?_⟩
      rcases Bool.or_eq_true _ _ |>.mp hy with hx | e
      · exact (hXb g hg).2 hx
      · have : g = c := of_decide_eq_true e
        subst this; exact Or.inr hcJ
    have hXY : ∀ g ∈ goods, X g = true → (X g || decide (g = c)) = true := fun g _ hx => by rw [hx]; rfl
    have hlen := (filter_insert_perm hgd hc hcX).length_eq
    simp only [List.length_cons] at hlen
    have hm := uCount_mono (v := v) (agents := agents) (base := base) (o := o) hXY
    have hm' := hu o (fun g => X g || decide (g = c))
    refine ⟨o, ho, hoF, _, hY, hS, fun o' ho' hoF' Z' hZ' hS' => ?_⟩
    have := hmax o' ho' hoF' Z' hZ' hS'
    rw [hlen]
    omega

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.countP_succ_le_add
#print axioms EFX.C4min.lemma11
#print axioms EFX.C4min.counted_iff
#print axioms EFX.C4min.uCount_eq_goods
#print axioms EFX.C4min.lemma12_move
#print axioms EFX.C4min.uCount_mono
#print axioms EFX.C4min.lemma12
#print axioms EFX.C4min.lemma12_lt_iff
#print axioms EFX.C4min.lemma12_lt
