import EFX.DL13

/-!
# The move lemmas of the deficit-descent route (`k4/dl2.md` §4; Lemma H1 of `k4/hall.md` §1)

Ledger K4.DL2.MOVES.LEAN, K4.DL2.DEF.LEAN, K4.HALL.H1.LEAN. The written proofs are those of `k4/dl2.md` §4 (refereed
in the PR #69 review; rows K4.DL2.MOVES, K4.DL2.DEF) and of Lemma H1 in `k4/hall.md` §1 (refereed in PR #46; row
K4.HALL.COVER). Every statement is over the existing definitions: `InP`, `MinFrozen`, `vbNeeds`, `omegaP`, `DeficitLE`,
`ownerBundle`, `roNeeds`, `Unthreatened` (`EFX/C4min.lean`), `baseOf`, `junk`, `NA`, `Frozen`, `cap`, `capSum`,
`otherSlots` (`EFX/PreAllocK.lean`), `DeficitLT`, `Nbhd` (`EFX/C4minDescent.lean`), `MoveT1`, `MoveT3`
(`EFX/DL13.lean`). Nothing of the model is redefined; the new definitions below name the sets of `k4/dl2.md` §4.

**Conventions.** `P` is `base`, `P′` is `base'`; `B_i = baseOf goods base i`, `J = LB4.junk goods base`,
`N_i = vbNeeds v goods base i`, `𝒩 = NA(P) = NA agents (vbNeeds v goods base)`, `F` the listed agents with
`Frozen agents goods base (vbNeeds v goods base)`, `ω = omegaP v agents goods base`. A move `P → P′` is any base map
`base'` such that the listed agents outside the move keep their bases (`baseOf` compared on `goods`, as `MoveT1` and
`MoveT3` do), every base good of `P′` goes to a listed agent (`hmem'`), and the new bases satisfy the stated membership
conditions (e.g. `B′_y ⊆ (B_y ∪ J) ∩ R_y`: `base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g`). New
bases are pairwise disjoint because `P′` is a map. `N_y(B′_y) ⊆ 𝒩` reads `vbNeeds v goods base' y g → NA(P) g`.
`def(P) ≤ d` is `DeficitLE`, `def(P′) < def(P)` is `DeficitLT` (both in `ℤ ∪ {+∞}`).

**New definitions** (`k4/dl2.md` §4, Setting). A set of goods is a test `Z : G → Bool`, read on `goods` (the list
`goods.filter Z`; `|Z|` is its length, `v_x(Z)` its value).
- `IsBundle goods base o Z`: `Z` is a bundle of `o`, `B_o ⊆ Z ⊆ W_o = B_o ∪ J`.
- `SafeFor v agents goods base o Z`: `Z` threatens no listed `x ≠ o` holding `B_x`, `v_x(Z ∖ h) ≤ v_x(B_x)` for every
  `h ∈ Z` (so `θ_x(Z) ≤ v_x(B_x)`; the empty set is safe). It is `Unthreatened` for an arbitrary set
  (`unthreatened_iff`).
- `setNeeds v goods o Z`: `N_o(Z) = {g ∈ R_o ∖ Z : v_o(g) > v_o(Z)}`.
- `Counted … o Z x`: `x ∈ F` and `B_x ∩ (N_o(Z) ∪ 𝒩₋ₒ) = ∅`, `𝒩₋ₒ = ⋃_{listed i ≠ o} N_i`; `uCount … o Z = u_o(Z)`,
  the number of counted listed agents.
- `OptimalBest … o X`: `X` is an optimal bundle of a best owner `o` (a safe bundle of a free listed `o` with
  `|X| + u_o(X) = Val*(P)`: no free listed `o′` has a safe bundle `Z` with a larger `|Z| + u_{o′}(Z)`).
- `DeficitDrop … P′ P k`: `def(P′) ≤ def(P) − k` in `ℤ ∪ {+∞}` (every integer `d ≥ def(P)` gives `def(P′) ≤ d − k`).
- `eStar` (`e*` of Lemma 2*), `eCount` (`e` of Lemma 2), `obPred` (the test of `ownerBundle`).
- `MoveT1Code`, `MoveT3Code`: (T1), (T3) as the code `k4/dl2_relations.py` phrases them (frozen-status changes
  instead of `NA`), as described in `EFX/DL13.lean`, module doc, item 2.

**Results.**
- *Facts about 𝒫*: `exists_base_of_NA`, `frozen_of_NA` (every needed good is the one-good base of a frozen agent),
  `not_NA_of_mem_free`, `not_NA_of_junk` (free bases and the junk miss `𝒩`), `vbNeeds_congr`, `frozen_congr`.
- *The core of Lemmas 1(c), 1′, 6*: `minFrozen_of_cover` (a base map with bases inside the relevant sets, of at most two
  goods, needs inside `𝒩`, and every good of `𝒩` a one-good base, is min-frozen with `NA(P′) = 𝒩`).
- *Lemma 1*: `lemma1a` ((a): `y` free in `P` and `P′`, `B′_y ⊆ (B_y ∪ J) ∩ R_y`), `lemma1b` ((b): `NA(P′) = 𝒩` iff
  `N_y(B′_y) ⊆ 𝒩`, then `F(P′) = F`; otherwise an agent with unchanged base changes status), `lemma1c` ((c):
  min-frozen, same `NA`, `F`, `ω`, and `J(P′) = (J ∖ B′) ∪ (B_y ∖ B′)`); *Lemma 1′*: `lemma1'`; *Lemma 6*: `lemma6`
  (min-frozen, same `NA` and `ω`, `F(P′) = (F ∖ {x}) ∪ {z}`) and `needs_single_sub` (`g ∈ N_z` gives `N_z({g}) ⊆ 𝒩`).
- *(T1), (T3) well defined*: `minFrozen_of_moveT1` (a `MoveT1` move from a min-frozen `P` to a base map with listed
  owners and bases of at most two goods is min-frozen, same `F`), `moveT1_of_admissible` (an admissible re-base is a
  `MoveT1` move), `moveT1_iff_needs` (on min-frozen pairs differing in one base, `MoveT1` iff `N_y(B′_y) ⊆ 𝒩`),
  `minFrozen_of_moveT3` (a `MoveT3` move to a base map with listed owners that value their goods and bases of at most two
  goods is min-frozen, `F(P′) = (F ∖ {x}) ∪ {z}`), `moveT3_of_lemma6` (a role swap with a needer and at most one helper
  giving up a good, under Lemma 6's hypotheses, is a `MoveT3` move); and the code's phrasing: `moveT1_iff_status`,
  `moveT1_iff_code` (on min-frozen pairs), `moveT3_iff_code` (on `𝒫`), `free_of_swap`.
- *Lemma H1*: `h1_core` (`|C| − S_o(C) = ω + 2 − |X_o| − u_o(X_o)` for `X_o = B_o ∪ (J ∖ C)`), `otherSlots_roNeeds`
  (`S_o(C) = s₀ + u_o(X_o)`), `deficitLE_of_safe` and `exists_safe_of_deficitLE` (the two inequalities), `lemmaH1`
  (`def(P) ≤ d` iff some free listed `o` has a safe bundle `Z` with `ω + 2 − |Z| − u_o(Z) ≤ d`: `def(P) = ω + 2 − Val*(P)`),
  `lemmaH1_owner` (the per-owner covering form), `deficit_of_optimalBest`, `not_deficitLE_of_val_lt`.
- *Lemma 2\**: `lemma2star` (`def(P′) ≤ ω + 2 − |Y| − u_o(X) + e*`), `lemma2star_drop` (at an optimal bundle of a best
  owner, `def(P′) ≤ def(P) − (|Y ∖ X| − e*)`), `lemma2star_lt` (`def(P′) < def(P)` once `|Y| + u_o(X) − e* > Val*(P)`),
  `setNeeds_mono` ((M1)), `isBundle_of_disjoint`.
- *Lemma 2*: `lemma2` (`def(P′) ≤ ω + 2 − |Y| − u_o(X) + e`, and `e = 0` if `v_y(B′) ≥ v_y(B_y)`), `lemma2_drop`,
  `lemma2_lt`.
- *Lemma 3*: `W_rebase` (`W′_y = W_y`), `lemma3` (bundles of `y` in `P′` are the `Z` with `B′ ⊆ Z ⊆ W_y`; safety and
  `u_y` are those of `P`), `lemma3_val` (`Val_{P′}(y)` is the max over those `Z`), `lemma3_lt` (the gain).
- *Lemma 7*: `lemma7` (`z` counted, `u′_x(Z) ≥ 1`, `def(P′) ≤ ω + 1 − |Z|`), `lemma7_bigTop` (`R_x ∖ {g} ⊆ Z`).
- *Corollaries 4, 5*: `cor4` (release, `def(P′) ≤ def(P) − 1`), `cor4_i_of_i'` ((i′) ⟹ (i)), `cor5` (unblocking).

**Faithfulness** (paper statement; Lean statement; why they agree). Each theorem's docstring restates the paper
statement it formalizes. They agree because the Lean statement uses the same objects (the definitions above are the
text's, word for word: `B_o ⊆ Z ⊆ B_o ∪ J`; `θ_x(Z) ≤ v_x(B_x)` as `∀ h ∈ Z`; `u_o(Z)` as the count of `x ∈ F` with
`B_x ∩ (N_o(Z) ∪ 𝒩₋ₒ) = ∅`), the same conclusions, and the same or *weaker* hypotheses. Where the prose leaves room:
1. *Weaker hypotheses* (each Lean theorem implies the text's): Lemma 1(a) and Lemma 7 need `P, P′ ∈ 𝒫`, not min-frozen;
   Lemma 7 does not use `g ∈ R_x`; Lemma 2* needs `P, P′ ∈ 𝒫` with `NA(P′) = NA(P)`, not min-frozen; in Lemmas 2 and 2*
   the bound needs only `X ⊆ Y` (the text's "X a bundle of o in P missing the new bases" implies it lies in a bundle of
   `P′`, `isBundle_of_disjoint`, and is what the gain forms use through `OptimalBest`); Lemma 1(c) does not use
   `B′ ≠ B_y`; Corollaries 4, 5 do not use `def(P) > 0` (nor, for 5, `B′ ≠ B_y`); Lemma H1 holds on all of `𝒫` with
   `ω ≥ 1` (the text of `k4/dl2.md` assumes min-frozen and a free agent; without a free agent both sides are `+∞`).
2. *`Val_P(o)` and `Val*(P)`* are not defined as numbers: "`|X| + u_o(X) = Val*(P)`" is `OptimalBest`, "`k > Val*(P)`" is
   "every free listed `o′` and safe bundle `Z` of `o′` have `|Z| + u_{o′}(Z) < k`", and `Val_{P′}(y) = max{…}` is
   `lemma3_val` (the same values `≥ k` are reached on both sides, for every `k`).
3. *`|Y ∖ X|`* is `|Y| − |X|` (`X ⊆ Y` on `goods`, `goods` without duplicates).
4. *Corollary 4*: `B_y = {p, q}` is `∀ g ∈ goods, base g = some y ↔ g = p ∨ g = q` with `p ≠ q`; the release is a base
   map giving `y` exactly `p`; `v_y(X ∩ R_y)` is `v_y(X)` (irrelevant goods are worth 0); (i′) "no agent outside
   `{o, y}` values `q`" is `v_z(q) = 0` and "`X ⊄ R_z`" is "some `h₀ ∈ X` has `v_z(h₀) = 0`".
5. *Lemma 7, big-top*: "`x` has four goods, `g` its top, `b, c` its second and third" is "every good `x` values is one of
   `g, b, c, d`" with `b, c, d` distinct and `v_x(d) ≤ v_x(c) ≤ v_x(b)`, `v_x(b) + v_x(c) < v_x(g)`; the conclusion
   `R_x ∖ {g} ⊆ Z` is "every good `x` values other than `g` is in `Z`".
6. *The code's phrasing* (`MoveT1Code`, `MoveT3Code`) is the description in `EFX/DL13.lean`; the code itself
   (`k4/dl2_relations.py`) is not read here.

No statement of `k4/dl2.md` §4 or of Lemma H1 turned out wrong or ambiguous; the differences above are all weakenings
of hypotheses or choices of encoding.
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
`J(P′) = (J ∖ B′) ∪ (B_y ∖ B′)` and `ω` is the same; every other agent keeps its base, needs and value `v_i(B_i)`. (The
text also asks `B′ ≠ B_y`, which the conclusion does not use.) -/
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
      omegaP v agents goods base' = omegaP v agents goods base ∧
      (∀ i ∈ agents, i ≠ y → (∀ g, vbNeeds v goods base' i g ↔ vbNeeds v goods base i g) ∧
        value v i (baseOf goods base' i) = value v i (baseOf goods base i)) := by
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
  refine ⟨hM', hNA, hF, fun g => ?_, hω, fun i _ hiy =>
    ⟨vbNeeds_congr (hsame i (by assumption) hiy).symm, by rw [hsame i (by assumption) hiy]⟩⟩
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

/-! ## (T1) and (T3) in the code's form (`EFX/DL13.lean`, module doc, item 2) -/

/-- **(T1) as the code phrases it** (`k4/dl2_relations.py`, `_one(s, nt_ok=False)`, as described in `EFX/DL13.lean`):
exactly one listed agent's base changes, and no listed agent with an unchanged base changes its frozen status. -/
def MoveT1Code : Nbhd A G := fun v agents goods base base' =>
  ∃ y ∈ agents, baseOf goods base y ≠ baseOf goods base' y ∧
    (∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i) ∧
    (∀ i ∈ agents, baseOf goods base i = baseOf goods base' i →
      (Frozen agents goods base' (vbNeeds v goods base') i ↔ Frozen agents goods base (vbNeeds v goods base) i))

/-- **(T3) as the code phrases it** (`k4/dl2_relations.py`, `_swap(s, 1, gives=True)`, as described in
`EFX/DL13.lean`): `x` frozen in `P` and free in `P′`; `z` free in `P` and frozen in `P′`, with `B′_z = B_x = {g}` and `z`
needing `g`; at most one further changed agent, free in `P` and `P′`, giving up a good; every other listed agent keeps its
base; no listed agent with an unchanged base changes its frozen status. -/
def MoveT3Code : Nbhd A G := fun v agents goods base base' =>
  ∃ x ∈ agents, ∃ z ∈ agents, ∃ g : G, baseOf goods base x = [g] ∧
    Frozen agents goods base (vbNeeds v goods base) x ∧ ¬ Frozen agents goods base' (vbNeeds v goods base') x ∧
    ¬ Frozen agents goods base (vbNeeds v goods base) z ∧ Frozen agents goods base' (vbNeeds v goods base') z ∧
    baseOf goods base' z = baseOf goods base x ∧ vbNeeds v goods base z g ∧
    ∃ H : List A, H.length ≤ 1 ∧
      (∀ h ∈ H, h ∈ agents ∧ h ≠ x ∧ h ≠ z ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧
        ¬ Frozen agents goods base' (vbNeeds v goods base') h ∧ ∃ g' ∈ baseOf goods base h, g' ∉ baseOf goods base' h) ∧
      (∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ H → baseOf goods base i = baseOf goods base' i) ∧
      (∀ i ∈ agents, baseOf goods base i = baseOf goods base' i →
        (Frozen agents goods base' (vbNeeds v goods base') i ↔ Frozen agents goods base (vbNeeds v goods base) i))

omit [DecidableEq G] in
/-- **(T1): the text's form and the code's agree on min-frozen pairs** (Lemma 1(a), (b)). -/
theorem moveT1_iff_code (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hM' : MinFrozen v agents goods base') :
    MoveT1 v agents goods base base' ↔ MoveT1Code v agents goods base base' := by
  constructor
  · rintro ⟨y, hy, hyF, hne, hsub, hsame, hNA⟩
    exact ⟨y, hy, hne, hsame, fun i _ hB => frozen_congr hB.symm fun g => (hNA g).symm⟩
  · rintro ⟨y, hy, hne, hsame, hst⟩
    exact (moveT1_iff_status hag hgd hM hM' hy hne hsame).mpr fun i hi hiy => hst i hi (hsame i hi hiy)

omit [DecidableEq G] in
/-- In a role swap that keeps the needed set, `x` and the helpers are free in `P′`: a needed good of `P` is `g`, now
`z`'s, or the base of a frozen agent of `P` outside the move. -/
theorem free_of_swap (hP : InP v agents goods base) {x z : A} {g : G} {H : List A}
    (hxg : baseOf goods base x = [g]) (hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z)
    (hHF : ∀ h ∈ H, ¬ Frozen agents goods base (vbNeeds v goods base) h)
    (hz' : baseOf goods base' z = [g])
    (hsame : ∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ H → baseOf goods base i = baseOf goods base' i)
    (hNA : ∀ g', NA agents (vbNeeds v goods base') g' ↔ NA agents (vbNeeds v goods base) g')
    {i : A} (hi : i = x ∨ i ∈ H) (hiz : i ≠ z) : ¬ Frozen agents goods base' (vbNeeds v goods base') i := by
  rintro ⟨g', hB, hN⟩
  have hgi : g' ∈ baseOf goods base' i := by rw [hB]; exact List.mem_singleton_self g'
  obtain ⟨hg', hb'⟩ := mem_baseOf.mp hgi
  obtain ⟨w, hw, -, hBw, hF⟩ := frozen_of_NA hP ((hNA g').mp hN)
  by_cases hwx : w = x
  · subst hwx; rw [hxg] at hBw
    have e : g = g' := List.singleton_inj.mp hBw
    have hgz : g' ∈ baseOf goods base' z := by rw [hz', e]; exact List.mem_singleton_self g'
    rw [(mem_baseOf.mp hgz).2] at hb'
    exact hiz (Option.some.inj hb').symm
  · have hwz : w ≠ z := fun e => hzF (e ▸ hF)
    have hwH : w ∉ H := fun h => hHF w h hF
    have hgw : g' ∈ baseOf goods base' w := by
      rw [← hsame w hw hwx hwz hwH, hBw]; exact List.mem_singleton_self g'
    rw [(mem_baseOf.mp hgw).2] at hb'
    have hwi : w = i := Option.some.inj hb'
    subst hwi
    rcases hi with e | e
    · exact hwx e
    · exact hwH e

omit [DecidableEq G] in
/-- **(T3): the text's form and the code's agree on `𝒫`** (the argument `EFX/DL13.lean` leaves to the text: on `𝒫`, `NA`
is the set of the frozen agents' goods, and `F(P′) = (F ∖ {x}) ∪ {z}`). Only `P, P′ ∈ 𝒫` is used. -/
theorem moveT3_iff_code (hP : InP v agents goods base) (hP' : InP v agents goods base') :
    MoveT3 v agents goods base base' ↔ MoveT3Code v agents goods base base' := by
  constructor
  · rintro ⟨x, hx, z, hz, g, hxg, hgN, hzF, hzN, hz', H, hHlen, hH, hsame, hNA⟩
    have hNA' : ∀ g', NA agents (vbNeeds v goods base') g' ↔ NA agents (vbNeeds v goods base) g' :=
      fun g' => (hNA g').symm
    have hxF : Frozen agents goods base (vbNeeds v goods base) x := ⟨g, hxg, hgN⟩
    have hxz : x ≠ z := fun e => hzF (e ▸ hxF)
    have hHF : ∀ h ∈ H, ¬ Frozen agents goods base (vbNeeds v goods base) h := fun h hh => (hH h hh).2.2.2.1
    refine ⟨x, hx, z, hz, g, hxg, hxF, free_of_swap hP hxg hzF hHF hz' hsame hNA' (Or.inl rfl) hxz, hzF,
      ⟨g, hz', (hNA g).mp hgN⟩, hz'.trans hxg.symm, hzN, H, hHlen, fun h hh => ?_, hsame,
      fun i _ hB => frozen_congr hB.symm hNA'⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hH h hh
    exact ⟨h1, h2, h3, h4, free_of_swap hP hxg hzF hHF hz' hsame hNA' (Or.inr hh) h3, h5⟩
  · rintro ⟨x, hx, z, hz, g, hxg, hxF, hxF', hzF, hzF', hz', hzN, H, hHlen, hH, hsame, hst⟩
    rw [hxg] at hz'
    have hgN : NA agents (vbNeeds v goods base) g := by
      obtain ⟨y, hy, hN⟩ := hxF; rw [hxg] at hy; cases hy; exact hN
    refine ⟨x, hx, z, hz, g, hxg, hgN, hzF, hzN, hz', H, hHlen,
      fun h hh => ⟨(hH h hh).1, (hH h hh).2.1, (hH h hh).2.2.1, (hH h hh).2.2.2.1, (hH h hh).2.2.2.2.2⟩, hsame,
      fun g' => ⟨fun hN => ?_, fun hN => ?_⟩⟩
    · obtain ⟨w, hw, -, hBw, hF⟩ := frozen_of_NA hP hN
      by_cases hwx : w = x
      · subst hwx; rw [hxg] at hBw
        have e : g = g' := List.singleton_inj.mp hBw
        subst e
        obtain ⟨y, hy, hN'⟩ := hzF'; rw [hz'] at hy; cases hy; exact hN'
      · have hwz : w ≠ z := fun e => hzF (e ▸ hF)
        have hwH : w ∉ H := fun h => (hH w h).2.2.2.1 hF
        have hB := hsame w hw hwx hwz hwH
        obtain ⟨y, hy, hN'⟩ := (hst w hw hB).mpr hF
        rw [← hB, hBw] at hy; cases hy; exact hN'
    · obtain ⟨w, hw, -, hBw, hF⟩ := frozen_of_NA hP' hN
      by_cases hwz : w = z
      · subst hwz; rw [hz'] at hBw
        have e : g = g' := List.singleton_inj.mp hBw
        subst e; exact hgN
      · have hwx : w ≠ x := fun e => hxF' (e ▸ hF)
        have hwH : w ∉ H := fun h => (hH w h).2.2.2.2.1 hF
        have hB := hsame w hw hwx hwz hwH
        obtain ⟨y, hy, hN'⟩ := (hst w hw hB).mp hF
        rw [hB, hBw] at hy; cases hy; exact hN'

/-! ## Bundles, safety and the count `u_o` (`k4/dl2.md` §4, Setting; `k4/hall.md` §1) -/

/-- **`Z` is a bundle of `o` in `P`**: `B_o ⊆ Z ⊆ W_o = B_o ∪ J`, for a set of goods given by its test `Z` on `goods`
(the set is `goods.filter Z`). -/
def IsBundle (goods : List G) (base : G → Option A) (o : A) (Z : G → Bool) : Prop :=
  ∀ g ∈ goods, (base g = some o → Z g = true) ∧ (Z g = true → base g = some o ∨ base g = none)

/-- **`Z` is safe for `o` in `P`**: `Z` threatens no listed agent `x ≠ o` holding its base,
`θ_x(Z) = max_{h ∈ Z} v_x(Z ∖ h) ≤ v_x(B_x)` (the empty set threatens nobody). This is `Unthreatened` of
`EFX/C4min.lean` for an arbitrary set in place of `B_o ∪ (J ∖ C)`. -/
def SafeFor (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A) (Z : G → Bool) :
    Prop :=
  ∀ x ∈ agents, x ≠ o → ∀ h ∈ goods.filter Z, value v x ((goods.filter Z).erase h) ≤ value v x (baseOf goods base x)

/-- **`N_o(Z)`** (`k4/dl2.md` §4): the goods outside `Z` worth more to `o` than `Z`,
`N_o(Z) = {g ∈ R_o ∖ Z : v_o(g) > v_o(Z)}`. -/
def setNeeds (v : A → G → Nat) (goods : List G) (o : A) (Z : G → Bool) (g : G) : Prop :=
  g ∈ goods ∧ Z g = false ∧ value v o (goods.filter Z) < v o g

/-- **`x` is counted in `u_o(Z)`** (`k4/dl2.md` §4): `x` is frozen in `P` and its base misses `N_o(Z) ∪ 𝒩₋ₒ`, where
`𝒩₋ₒ = ⋃_{i ≠ o} N_i` over the listed agents. -/
def Counted (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A) (Z : G → Bool)
    (x : A) : Prop :=
  Frozen agents goods base (vbNeeds v goods base) x ∧
    ∀ g ∈ baseOf goods base x, ¬ setNeeds v goods o Z g ∧ ∀ i ∈ agents, i ≠ o → ¬ vbNeeds v goods base i g

open Classical in
/-- **`u_o(Z)`** (`k4/dl2.md` §4): the number of listed agents counted in `u_o(Z)`, i.e. the frozen agents that `o`'s
needs from `Z` unfreeze. -/
noncomputable def uCount (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A)
    (Z : G → Bool) : Nat :=
  agents.countP (fun x => decide (Counted v agents goods base o Z x))

/-- The test of the owner's bundle `X_o = B_o ∪ (J ∖ C)` of `EFX/C4min.lean` (`ownerBundle`). -/
def obPred (base : G → Option A) (o : A) (C : G → Bool) : G → Bool :=
  fun g => decide (base g = some o ∨ (base g = none ∧ C g = false))

omit [DecidableEq G] in
theorem ownerBundle_eq (o : A) (C : G → Bool) : ownerBundle goods base o C = goods.filter (obPred base o C) := rfl

omit [DecidableEq G] in
theorem isBundle_obPred (o : A) (C : G → Bool) : IsBundle goods base o (obPred base o C) := by
  intro g _
  unfold obPred
  constructor
  · intro h; simp [h]
  · intro h
    rcases of_decide_eq_true h with h | h
    · exact Or.inl h
    · exact Or.inr h.1

omit [DecidableEq G] in
/-- A bundle `Z` is the owner's bundle `B_o ∪ (J ∖ C)` for `C = J ∖ Z` (the test `!Z`). -/
theorem obPred_not_eq {o : A} {Z : G → Bool} (hZ : IsBundle goods base o Z) :
    ∀ g ∈ goods, obPred base o (fun g => !Z g) g = Z g := by
  intro g hg
  obtain ⟨h1, h2⟩ := hZ g hg
  unfold obPred
  cases hb : base g with
  | none => cases hz : Z g <;> simp [hz]
  | some i =>
    by_cases hio : i = o
    · subst hio; simp [h1 hb]
    · have : Z g = false := by
        cases hz : Z g with
        | false => rfl
        | true => rcases h2 hz with e | e <;> rw [hb] at e <;> first | exact absurd (Option.some.inj e) hio | cases e
      simp [hio, this]

omit [DecidableEq G] in
theorem filter_congr_goods {Z Z' : G → Bool} (h : ∀ g ∈ goods, Z g = Z' g) : goods.filter Z = goods.filter Z' :=
  List.filter_congr h

omit [DecidableEq A] [DecidableEq G] in
/-- `N_o(Z)` depends only on `Z ∩ goods`. -/
theorem setNeeds_congr {o : A} {Z Z' : G → Bool} (h : ∀ g ∈ goods, Z g = Z' g) (g : G) :
    setNeeds v goods o Z g ↔ setNeeds v goods o Z' g := by
  unfold setNeeds
  rw [filter_congr_goods h]
  exact ⟨fun ⟨hg, hz, hlt⟩ => ⟨hg, (h g hg) ▸ hz, hlt⟩, fun ⟨hg, hz, hlt⟩ => ⟨hg, (h g hg).symm ▸ hz, hlt⟩⟩

omit [DecidableEq G] in
/-- `u_o(Z)` depends only on `Z ∩ goods`. -/
theorem uCount_congr {o : A} {Z Z' : G → Bool} (h : ∀ g ∈ goods, Z g = Z' g) :
    uCount v agents goods base o Z = uCount v agents goods base o Z' := by
  classical
  unfold uCount
  congr 1
  funext x
  apply decide_eq_decide.mpr
  unfold Counted
  simp only [setNeeds_congr (v := v) h]

/-- Safety depends only on `Z ∩ goods`. -/
theorem safeFor_congr {o : A} {Z Z' : G → Bool} (h : ∀ g ∈ goods, Z g = Z' g) :
    SafeFor v agents goods base o Z ↔ SafeFor v agents goods base o Z' := by
  unfold SafeFor
  rw [filter_congr_goods h]

/-- `Unthreatened` of `EFX/C4min.lean` is safety of the owner's bundle. -/
theorem unthreatened_iff (o : A) (C : G → Bool) :
    Unthreatened v agents goods base o C ↔ SafeFor v agents goods base o (obPred base o C) := Iff.rfl

/-! ## The re-base, constructed (Lemma 1(c)) -/

/-- **Re-basing `y` to `B′`** (the move of Lemma 1(c), as a base map): `y` holds exactly the goods of `B′`, the goods of
`B_y ∖ B′` become junk, every other good keeps its owner. -/
def rebase (base : G → Option A) (y : A) (B' : G → Bool) : G → Option A :=
  fun g => if B' g then some y else if base g = some y then none else base g

omit [DecidableEq G] in
theorem rebase_eq_some_self {y : A} {B' : G → Bool} {g : G} : rebase base y B' g = some y ↔ B' g = true := by
  unfold rebase
  by_cases hb : B' g = true
  · simp [hb]
  · by_cases hy : base g = some y
    · simp [hb, hy]
    · simp [hb, hy]

omit [DecidableEq G] in
theorem rebase_eq_some_other {y i : A} (hiy : i ≠ y) {B' : G → Bool} {g : G} :
    rebase base y B' g = some i ↔ B' g = false ∧ base g = some i := by
  unfold rebase
  by_cases hb : B' g = true
  · simp [hb, Ne.symm hiy]
  · by_cases hy : base g = some y
    · simp only [hb, hy, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro _ e; exact hiy (Option.some.inj e).symm
    · simp [hb, hy]

omit [DecidableEq G] in
theorem baseOf_rebase_self {y : A} {B' : G → Bool} : baseOf goods (rebase base y B') y = goods.filter B' := by
  unfold baseOf
  apply List.filter_congr
  intro g _
  simp only [rebase_eq_some_self]
  cases B' g <;> rfl

omit [DecidableEq G] in
theorem baseOf_rebase_other {y i : A} (hiy : i ≠ y) {B' : G → Bool}
    (hB' : ∀ g ∈ goods, B' g = true → base g = some y ∨ base g = none) :
    baseOf goods base i = baseOf goods (rebase base y B') i := by
  unfold baseOf
  apply List.filter_congr
  intro g hg
  refine decide_eq_decide.mpr ?_
  rw [rebase_eq_some_other hiy]
  by_cases hb : B' g = true
  · have : ¬ base g = some i := by
      rcases hB' g hg hb with e | e <;> rw [e]
      · exact fun h => hiy (Option.some.inj h).symm
      · simp
    simp [hb, this]
  · simp [hb]

omit [DecidableEq G] in
/-- The needs of `y` holding `B′` are `N_y(B′)`. -/
theorem vbNeeds_rebase_self {y : A} {B' : G → Bool} (g : G) :
    vbNeeds v goods (rebase base y B') y g ↔ setNeeds v goods y B' g := by
  unfold vbNeeds setNeeds
  rw [baseOf_rebase_self]
  have : rebase base y B' g ≠ some y ↔ B' g = false := by rw [Ne, rebase_eq_some_self]; simp
  rw [this]

omit [DecidableEq G] in
/-- **Lemma 1(c), with the move constructed**: if `y` is free in the min-frozen `P` and `B′ ⊆ (B_y ∪ J) ∩ R_y` has at most
two goods and `N_y(B′) ⊆ 𝒩`, then `rebase base y B′` is a min-frozen pre-allocation with `NA(P′) = 𝒩`, `F(P′) = F(P)`
and the same `ω`, in which `y` holds `B′` and every other agent keeps its base. -/
theorem lemma1c_rebase (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y) {B' : G → Bool}
    (hB' : ∀ g ∈ goods, B' g = true → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (goods.filter B').length ≤ 2)
    (hadm : ∀ g, setNeeds v goods y B' g → NA agents (vbNeeds v goods base) g) :
    MinFrozen v agents goods (rebase base y B') ∧
      (∀ g, NA agents (vbNeeds v goods (rebase base y B')) g ↔ NA agents (vbNeeds v goods base) g) ∧
      (∀ i ∈ agents, Frozen agents goods (rebase base y B') (vbNeeds v goods (rebase base y B')) i ↔
        Frozen agents goods base (vbNeeds v goods base) i) ∧
      baseOf goods (rebase base y B') y = goods.filter B' ∧
      (∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods (rebase base y B') i) ∧
      omegaP v agents goods (rebase base y B') = omegaP v agents goods base := by
  have hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods (rebase base y B') i :=
    fun i _ hiy => baseOf_rebase_other hiy fun g hg hb => (hB' g hg hb).1
  have hmem' : ∀ g ∈ goods, ∀ i, rebase base y B' g = some i → i ∈ agents := by
    intro g hg i hb
    by_cases hiy : i = y
    · rw [hiy]; exact hy
    · exact hM.1.mem g hg i ((rebase_eq_some_other hiy).mp hb).2
  obtain ⟨hM', hNA, hF, -, hω, -⟩ := lemma1c hag hgd hM hy hyF hsame hmem'
    (fun g hg hb => hB' g hg (rebase_eq_some_self.mp hb)) (by rw [baseOf_rebase_self]; exact htwo)
    (fun g hN => hadm g ((vbNeeds_rebase_self g).mp hN))
  exact ⟨hM', hNA, hF, baseOf_rebase_self, hsame, hω⟩

omit [DecidableEq G] in
/-- **An admissible re-base, constructed, is a (T1) move**: under the hypotheses of `lemma1c_rebase` and
`B′ ≠ B_y`, `rebase base y B′` is a min-frozen (T1)-neighbour of `P`. -/
theorem moveT1_rebase (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y) {B' : G → Bool}
    (hB' : ∀ g ∈ goods, B' g = true → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (goods.filter B').length ≤ 2)
    (hadm : ∀ g, setNeeds v goods y B' g → NA agents (vbNeeds v goods base) g)
    (hne : baseOf goods base y ≠ goods.filter B') :
    MinFrozen v agents goods (rebase base y B') ∧ MoveT1 v agents goods base (rebase base y B') := by
  obtain ⟨hM', hNA, -, hB, hsame, -⟩ := lemma1c_rebase hag hgd hM hy hyF hB' htwo hadm
  refine ⟨hM', y, hy, hyF, by rw [hB]; exact hne, fun g hg => ?_, hsame, fun g => (hNA g).symm⟩
  obtain ⟨hgg, hb⟩ := mem_baseOf.mp hg
  exact hB' g hgg (rebase_eq_some_self.mp hb)

/-! ## Lemma H1 -/

omit [DecidableEq G] in
/-- The needs with the owner's taken from its bundle only shrink: `N_o^X ⊆ N_o(B_o)` (`v_o(X) ≥ v_o(B_o)`). -/
theorem roNeeds_sub {o : A} {C : G → Bool} {i : A} {g : G} (h : roNeeds v goods base o C i g) :
    vbNeeds v goods base i g := by
  unfold roNeeds at h
  by_cases hio : i = o
  · subst hio
    simp only [↓reduceIte] at h
    obtain ⟨hg, hX, hlt⟩ := h
    refine ⟨hg, fun hb => hX ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hg, by simp [hb]⟩
    · refine Nat.lt_of_le_of_lt (value_sublist v i ?_) hlt
      exact filter_sublist_of_imp fun g' _ hb => by simp at hb; simp [hb]
  · simpa [hio] using h

omit [DecidableEq G] in
/-- The needed set with the owner's needs from `X_o = B_o ∪ (J ∖ C)`: `N_o(X_o) ∪ 𝒩₋ₒ`. -/
theorem NA_roNeeds_iff {o : A} (ho : o ∈ agents) (C : G → Bool) (g : G) :
    NA agents (roNeeds v goods base o C) g ↔
      setNeeds v goods o (obPred base o C) g ∨ ∃ i ∈ agents, i ≠ o ∧ vbNeeds v goods base i g := by
  constructor
  · rintro ⟨i, hi, hN⟩
    unfold roNeeds at hN
    by_cases hio : i = o
    · subst hio
      simp only [↓reduceIte] at hN
      obtain ⟨hg, hX, hlt⟩ := hN
      refine Or.inl ⟨hg, ?_, hlt⟩
      cases hz : obPred base i C g with
      | false => rfl
      | true => exact absurd (List.mem_filter.mpr ⟨hg, hz⟩) hX
    · simp only [hio, ↓reduceIte] at hN
      exact Or.inr ⟨i, hi, hio, hN⟩
  · rintro (⟨hg, hz, hlt⟩ | ⟨i, hi, hio, hN⟩)
    · refine ⟨o, ho, ?_⟩
      unfold roNeeds
      simp only [↓reduceIte]
      refine ⟨hg, fun hm => ?_, hlt⟩
      rw [ownerBundle_eq, List.mem_filter, hz] at hm
      exact Bool.false_ne_true hm.2
    · refine ⟨i, hi, ?_⟩
      unfold roNeeds
      simpa [hio] using hN

theorem sum_eq_add_countP {α : Type} (f g : α → Nat) (p : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, f a = g a + if p a then 1 else 0) → (l.map f).sum = (l.map g).sum + l.countP p
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    rw [sum_eq_add_countP f g p l (fun b hb => h b (by simp [hb])), h a (by simp)]
    omega

omit [DecidableEq G] in
open Classical in
/-- **The slots of the other agents with the owner's needs from its bundle**: `S_o(C) = s₀ + u_o(X_o)`, where `s₀` is
the other agents' slots with the needs from the bases (`k4/hall.md` §1: taking `o`'s needs from `X` only unfreezes
agents, each unfrozen agent holds one good and gains one slot). -/
theorem otherSlots_roNeeds {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (C : G → Bool) :
    otherSlots agents goods base (roNeeds v goods base o C) o =
      otherSlots agents goods base (vbNeeds v goods base) o + uCount v agents goods base o (obPred base o C) := by
  unfold otherSlots uCount
  apply sum_eq_add_countP
  intro j _
  by_cases hjo : j = o
  · subst hjo
    have : ¬ Counted v agents goods base j (obPred base j C) j := fun h => hoF h.1
    simp [this]
  by_cases hF : Frozen agents goods base (vbNeeds v goods base) j
  · obtain ⟨y, hB, hN⟩ := id hF
    have hro : Frozen agents goods base (roNeeds v goods base o C) j ↔
        NA agents (roNeeds v goods base o C) y := by
      unfold Frozen; rw [hB]
      exact ⟨fun ⟨y', e, h⟩ => by cases e; exact h, fun h => ⟨y, rfl, h⟩⟩
    have hc : Counted v agents goods base o (obPred base o C) j ↔ ¬ NA agents (roNeeds v goods base o C) y := by
      rw [NA_roNeeds_iff ho C y]
      unfold Counted
      rw [hB]
      simp only [List.mem_singleton, forall_eq]
      constructor
      · rintro ⟨-, h1, h2⟩ (h | ⟨i, hi, hio, hN⟩)
        · exact h1 h
        · exact h2 i hi hio hN
      · intro h
        exact ⟨hF, fun h1 => h (Or.inl h1), fun i hi hio hN => h (Or.inr ⟨i, hi, hio, hN⟩)⟩
    by_cases hNro : NA agents (roNeeds v goods base o C) y
    · have : Frozen agents goods base (roNeeds v goods base o C) j := hro.mpr hNro
      have hnc : ¬ Counted v agents goods base o (obPred base o C) j := fun h => hc.mp h hNro
      simp [hjo, this, hF, hnc]
    · have : ¬ Frozen agents goods base (roNeeds v goods base o C) j := fun h => hNro (hro.mp h)
      have hcc : Counted v agents goods base o (obPred base o C) j := hc.mpr hNro
      simp [hjo, this, hF, hcc, hB]
  · have hro : ¬ Frozen agents goods base (roNeeds v goods base o C) j := fun ⟨y, hB, i, hi, hN⟩ =>
      hF ⟨y, hB, i, hi, roNeeds_sub hN⟩
    have hnc : ¬ Counted v agents goods base o (obPred base o C) j := fun h => hF h.1
    simp [hjo, hro, hF, hnc]

/-- Two sums of counts agree when they agree on each element. -/
theorem countP_add_eq {α : Type} {p q r s : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, (if p a then 1 else 0) + (if q a then 1 else 0) =
        (if r a then 1 else 0) + (if s a then 1 else 0)) →
      l.countP p + l.countP q = l.countP r + l.countP s
  | [], _ => by simp
  | a :: l, h => by
    have ih := countP_add_eq (l := l) fun b hb => h b (by simp [hb])
    have ha := h a (by simp)
    simp only [List.countP_cons]
    omega

omit [DecidableEq G] in
/-- Splitting the goods of `W_o`: `|Z| + |J ∖ Z| = |J| + |B_o|` for a bundle `Z` of `o`. -/
theorem length_bundle {o : A} {Z : G → Bool} (hZ : IsBundle goods base o Z) :
    (goods.filter Z).length + ((LB4.junk goods base).filter (fun g => !Z g)).length =
      (LB4.junk goods base).length + (baseOf goods base o).length := by
  unfold LB4.junk baseOf
  rw [List.filter_filter, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply countP_add_eq
  intro g hg
  obtain ⟨h1, h2⟩ := hZ g hg
  cases hb : base g with
  | none => cases Z g <;> simp
  | some i =>
    by_cases hio : i = o
    · subst hio; simp [h1 hb]
    · have hz : Z g = false := by
        cases hz : Z g with
        | false => rfl
        | true => rcases h2 hz with e | e <;> rw [hb] at e <;> first | exact absurd (Option.some.inj e) hio | cases e
      simp [hz, hio]

omit [DecidableEq G] in
open Classical in
/-- **Lemma H1, the slot identity** (`k4/hall.md` §1). For `P ∈ 𝒫`, a free listed owner `o` and any `C`, with
`X_o = B_o ∪ (J ∖ C)`: `|C| − S_o(C) = ω + 2 − |X_o| − u_o(X_o)` (`|C|` counts the junk goods of `C`). -/
theorem h1_core (hag : agents.Nodup) (hP : InP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (C : G → Bool) :
    (((LB4.junk goods base).filter C).length : Int) -
        (otherSlots agents goods base (roNeeds v goods base o C) o : Int) =
      omegaP v agents goods base + 2 - ((ownerBundle goods base o C).length : Int) -
        (uCount v agents goods base o (obPred base o C) : Int) := by
  have hs := otherSlots_roNeeds (v := v) (agents := agents) (goods := goods) ho hoF C
  have hcap := otherSlots_add_cap (M := vbNeeds v goods base) (base := base) (goods := goods) hag ho
    (fun j _ _ => hP.two j)
  have hcapo : cap agents goods base (vbNeeds v goods base) o = 2 - ((baseOf goods base o).length : Int) := by
    unfold cap; simp [hoF]
  have hsplit := length_bundle (base := base) (goods := goods) (isBundle_obPred o C)
  have hJ : (LB4.junk goods base).filter C = (LB4.junk goods base).filter (fun g => !obPred base o C g) := by
    apply List.filter_congr
    intro g hg
    have hb := (mem_junk.mp hg).2
    unfold obPred
    cases C g <;> simp [hb]
  rw [hJ, ownerBundle_eq, hs]
  unfold omegaP
  push_cast
  omega

/-- **Lemma H1, ≤** (`k4/hall.md` §1; `k4/dl2.md` §4). If `P ∈ 𝒫`, `ω ≥ 1`, `o` is a free listed agent and `Z` a safe
bundle of `o`, then `def(P) ≤ ω + 2 − |Z| − u_o(Z)`. -/
theorem deficitLE_of_safe (hag : agents.Nodup) (hP : InP v agents goods base)
    (hω : 0 < omegaP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) {Z : G → Bool} (hZ : IsBundle goods base o Z)
    (hS : SafeFor v agents goods base o Z) :
    DeficitLE v agents goods base
      (omegaP v agents goods base + 2 - ((goods.filter Z).length : Int) - (uCount v agents goods base o Z : Int)) := by
  have he := obPred_not_eq hZ
  refine Or.inr ⟨hω, o, ho, hoF, fun g => !Z g, ?_, ?_⟩
  · rw [unthreatened_iff, safeFor_congr he]; exact hS
  · rw [h1_core hag hP ho hoF, ownerBundle_eq, filter_congr_goods he, uCount_congr he]
    exact Int.le_refl _

/-- **Lemma H1, ≥**: if `P ∈ 𝒫`, `ω ≥ 1` and `def(P) ≤ d`, some free listed `o` has a safe bundle `Z` with
`ω + 2 − |Z| − u_o(Z) ≤ d`. -/
theorem exists_safe_of_deficitLE (hag : agents.Nodup) (hP : InP v agents goods base)
    (hω : 0 < omegaP v agents goods base) {d : Int} (h : DeficitLE v agents goods base d) :
    ∃ o ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o ∧ ∃ Z : G → Bool,
      IsBundle goods base o Z ∧ SafeFor v agents goods base o Z ∧
        omegaP v agents goods base + 2 - ((goods.filter Z).length : Int) - (uCount v agents goods base o Z : Int) ≤ d := by
  rcases h with ⟨h1, -⟩ | ⟨-, o, ho, hoF, C, hU, hle⟩
  · omega
  refine ⟨o, ho, hoF, obPred base o C, isBundle_obPred o C, (unthreatened_iff o C).mp hU, ?_⟩
  rw [h1_core hag hP ho hoF, ownerBundle_eq] at hle
  exact hle

/-- **Lemma H1** (`k4/hall.md` §1, K4.HALL.COVER, as used in `k4/dl2.md` §4): for `P ∈ 𝒫` with `ω ≥ 1`,
`def(P) = ω + 2 − Val*(P)`, where `Val*(P)` is the largest `|Z| + u_o(Z)` over the free listed `o` and the safe bundles
`Z` of `o`; read through `DeficitLE` (`def(P) ≤ d`), and with `def(P) = +∞` when there is no such pair. -/
theorem lemmaH1 (hag : agents.Nodup) (hP : InP v agents goods base) (hω : 0 < omegaP v agents goods base) (d : Int) :
    DeficitLE v agents goods base d ↔
      ∃ o ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o ∧ ∃ Z : G → Bool,
        IsBundle goods base o Z ∧ SafeFor v agents goods base o Z ∧
          omegaP v agents goods base + 2 - ((goods.filter Z).length : Int) - (uCount v agents goods base o Z : Int) ≤ d :=
  ⟨exists_safe_of_deficitLE hag hP hω, fun ⟨_, ho, hoF, _, hZ, hS, hle⟩ =>
    deficitLE_mono (deficitLE_of_safe hag hP hω ho hoF hZ hS) hle⟩

/-- **Lemma H1, per owner** (`k4/hall.md` §1, the covering form): for `P ∈ 𝒫`, a free listed `o` and a bundle `Z` of
`o` (`Z = B_o ∪ K`, `K ⊆ J`), the removal of `C = J ∖ Z` is a removal-only completion with owner `o` and owner bundle
`Z` (`Z` threatens nobody holding its base, and `|C| ≤ S_o(C)`) iff `Z` is safe and `|Z| ≥ ω + 2 − u_o(Z)`. -/
theorem lemmaH1_owner (hag : agents.Nodup) (hP : InP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) {Z : G → Bool} (hZ : IsBundle goods base o Z) :
    (Unthreatened v agents goods base o (fun g => !Z g) ∧
        ((LB4.junk goods base).filter (fun g => !Z g)).length ≤
          otherSlots agents goods base (roNeeds v goods base o (fun g => !Z g)) o) ↔
      SafeFor v agents goods base o Z ∧
        omegaP v agents goods base + 2 ≤ ((goods.filter Z).length : Int) + (uCount v agents goods base o Z : Int) := by
  have he := obPred_not_eq hZ
  have hc := h1_core hag hP ho hoF (fun g => !Z g)
  rw [ownerBundle_eq, filter_congr_goods he, uCount_congr he] at hc
  rw [unthreatened_iff, safeFor_congr he]
  constructor
  · rintro ⟨hS, hle⟩; exact ⟨hS, by omega⟩
  · rintro ⟨hS, hle⟩; exact ⟨hS, by omega⟩

/-! ## Deficit comparisons -/

/-- **`def(P′) ≤ def(P) − k`** in `ℤ ∪ {+∞}`: every integer bound `d ≥ def(P)` gives `def(P′) ≤ d − k` (vacuous when
`def(P) = +∞`). -/
def DeficitDrop (v : A → G → Nat) (agents : List A) (goods : List G) (base' base : G → Option A) (k : Int) : Prop :=
  ∀ d, DeficitLE v agents goods base d → DeficitLE v agents goods base' (d - k)

/-- A drop by `k ≥ 1` from a finite deficit is a strict decrease. -/
theorem deficitLT_of_drop {k : Int} (hk : 1 ≤ k) (h : DeficitDrop v agents goods base' base k) {d : Int}
    (hd : DeficitLE v agents goods base d) : DeficitLT v agents goods base' base := by
  obtain ⟨d₀, hd₀, hleast⟩ := exists_least_deficit hd
  exact ⟨d₀ - k, h d₀ hd₀, fun hle => by have := hleast _ hle; omega⟩

/-- **`X` is an optimal bundle of a best owner `o` of `P`** (`k4/dl2.md` §4): `o` is a free listed agent, `X` a safe
bundle of `o`, and `|X| + u_o(X) = Val*(P)`, i.e. no free listed `o′` has a safe bundle `Z` with a larger `|Z| + u_{o′}(Z)`. -/
def OptimalBest (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A) (X : G → Bool) :
    Prop :=
  o ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) o ∧ IsBundle goods base o X ∧
    SafeFor v agents goods base o X ∧
    ∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z, IsBundle goods base o' Z →
      SafeFor v agents goods base o' Z →
        (goods.filter Z).length + uCount v agents goods base o' Z ≤ (goods.filter X).length + uCount v agents goods base o X

/-- `Val*(P) < k`, through Lemma H1: if every free listed `o′` and safe bundle `Z` of `o′` have `|Z| + u_{o′}(Z) < k`,
then `def(P) > ω + 2 − k`. -/
theorem not_deficitLE_of_val_lt (hag : agents.Nodup) (hP : InP v agents goods base)
    (hω : 0 < omegaP v agents goods base) {k : Int}
    (hval : ∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z, IsBundle goods base o' Z →
      SafeFor v agents goods base o' Z → ((goods.filter Z).length : Int) + (uCount v agents goods base o' Z : Int) < k) :
    ¬ DeficitLE v agents goods base (omegaP v agents goods base + 2 - k) := fun h => by
  obtain ⟨o', ho', hoF', Z, hZ, hS, hle⟩ := exists_safe_of_deficitLE hag hP hω h
  have := hval o' ho' hoF' Z hZ hS
  omega

/-- For an optimal bundle `X` of a best owner `o`, `def(P) = ω + 2 − |X| − u_o(X)` (Lemma H1). -/
theorem deficit_of_optimalBest (hag : agents.Nodup) (hP : InP v agents goods base)
    (hω : 0 < omegaP v agents goods base) {o : A} {X : G → Bool} (hX : OptimalBest v agents goods base o X) :
    DeficitLE v agents goods base
        (omegaP v agents goods base + 2 - ((goods.filter X).length : Int) - (uCount v agents goods base o X : Int)) ∧
      ∀ d, DeficitLE v agents goods base d →
        omegaP v agents goods base + 2 - ((goods.filter X).length : Int) - (uCount v agents goods base o X : Int) ≤ d := by
  obtain ⟨ho, hoF, hXb, hXs, hmax⟩ := hX
  refine ⟨deficitLE_of_safe hag hP hω ho hoF hXb hXs, fun d hd => ?_⟩
  obtain ⟨o', ho', hoF', Z, hZ, hS, hle⟩ := exists_safe_of_deficitLE hag hP hω hd
  have := hmax o' ho' hoF' Z hZ hS
  omega

/-! ## Lemma 2* (extension through any move keeping the needed set) -/

omit [DecidableEq A] [DecidableEq G] in
/-- **(M1)** (`k4/dl2.md` §4): `X ⊆ Y` implies `N_o(Y) ⊆ N_o(X)`. -/
theorem setNeeds_mono {o : A} {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) {g : G}
    (h : setNeeds v goods o Y g) : setNeeds v goods o X g := by
  obtain ⟨hg, hY, hlt⟩ := h
  refine ⟨hg, ?_, Nat.lt_of_le_of_lt (value_sublist v o (filter_sublist_of_imp hXY)) hlt⟩
  cases hX : X g with
  | false => rfl
  | true => rw [hXY g hg hX] at hY; cases hY

open Classical in
/-- **`e*`** (Lemma 2*): the number of listed agents counted in `u_o(X)` that change their base (lie in `Ch`) or whose
good lies in `N_i(B′_i)` for some listed `i` whose base changes. -/
noncomputable def eStar (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) (o : A)
    (X : G → Bool) : Nat :=
  agents.countP (fun x => decide (Counted v agents goods base o X x ∧
    (baseOf goods base x ≠ baseOf goods base' x ∨
      ∃ i ∈ agents, baseOf goods base i ≠ baseOf goods base' i ∧
        ∃ g ∈ baseOf goods base x, vbNeeds v goods base' i g)))

omit [DecidableEq G] in
/-- In Lemma 2*, the bundle `X` of `o` in `P` is a bundle of `o` in `P′` when it misses every new base (the text's
"X ⊆ B_o ∪ J(P′)"; so is every `Y` with `X ⊆ Y ⊆ B_o ∪ J(P′)`). -/
theorem isBundle_of_disjoint {o : A} {X : G → Bool} (hX : IsBundle goods base o X)
    (hoB : baseOf goods base o = baseOf goods base' o)
    (hmiss : ∀ g ∈ goods, X g = true → ∀ i, base' g = some i → i = o) : IsBundle goods base' o X := by
  intro g hg
  refine ⟨fun hb => (hX g hg).1 ((base_eq_some_iff hoB.symm hg).mp hb), fun hx => ?_⟩
  cases hb : base' g with
  | none => exact Or.inr rfl
  | some i => exact Or.inl (by rw [hmiss g hg hx i hb])

/-- **Lemma 2\* (extension through any move)** (`k4/dl2.md` §4). Let `P, P′ ∈ 𝒫` with `NA(P′) = NA(P)` and `ω ≥ 1`,
`o` a listed agent free in `P` whose base does not change, `X ⊆ Y` with `Y` a bundle of `o` in `P′` that is safe in
`P′`. Then `def(P′) ≤ ω + 2 − |Y| − u_o(X) + e*`. (The text takes `P, P′` min-frozen and `X` a bundle of `o` in `P`
missing every new base; the bound needs neither, see `isBundle_of_disjoint` for why such an `X` lies in a bundle of
`P′`.) -/
theorem lemma2star (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base)
    (hP' : InP v agents goods base')
    (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g)
    (hω : 0 < omegaP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (hoB : baseOf goods base o = baseOf goods base' o)
    {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y) :
    DeficitLE v agents goods base'
      (omegaP v agents goods base + 2 - ((goods.filter Y).length : Int) - (uCount v agents goods base o X : Int) +
        (eStar v agents goods base base' o X : Int)) := by
  classical
  have hω' := omegaP_eq_of_NA hag hgd hP hP' hNA
  have hoF' : ¬ Frozen agents goods base' (vbNeeds v goods base') o := fun h =>
    hoF ((frozen_congr hoB.symm hNA).mp h)
  have hb := deficitLE_of_safe hag hP' (by rw [hω']; exact hω) ho hoF' hY hS
  rw [hω'] at hb
  -- `u_o(X) ≤ u′_o(Y) + e*`
  have hu : uCount v agents goods base o X ≤ uCount v agents goods base' o Y + eStar v agents goods base base' o X := by
    unfold uCount eStar
    apply countP_le_add
    intro x _ hx
    have hx := of_decide_eq_true hx
    by_cases he : baseOf goods base x ≠ baseOf goods base' x ∨
        ∃ i ∈ agents, baseOf goods base i ≠ baseOf goods base' i ∧ ∃ g ∈ baseOf goods base x, vbNeeds v goods base' i g
    · exact Or.inr (decide_eq_true ⟨hx, he⟩)
    refine Or.inl (decide_eq_true ⟨(frozen_congr ?_ hNA).mpr hx.1, fun g hg => ⟨fun hN => ?_, fun i hi hio hN => ?_⟩⟩)
    · exact Classical.byContradiction fun h => he (Or.inl fun e => h e.symm)
    · have hxB : baseOf goods base x = baseOf goods base' x :=
        Classical.byContradiction fun h => he (Or.inl h)
      rw [← hxB] at hg
      exact (hx.2 g hg).1 (setNeeds_mono hXY hN)
    · have hxB : baseOf goods base x = baseOf goods base' x :=
        Classical.byContradiction fun h => he (Or.inl h)
      rw [← hxB] at hg
      by_cases hiB : baseOf goods base i = baseOf goods base' i
      · exact (hx.2 g hg).2 i hi hio ((vbNeeds_congr hiB.symm g).mp hN)
      · exact he (Or.inr ⟨i, hi, hiB, g, hg, hN⟩)
  exact deficitLE_mono hb (by push_cast; omega)

/-- **Lemma 2\*, the gain** (`k4/dl2.md` §4): when `X` is an optimal bundle of a best owner `o` of `P`,
`def(P′) ≤ def(P) − (|Y ∖ X| − e*)` (`|Y ∖ X| = |Y| − |X|` as `X ⊆ Y`). -/
theorem lemma2star_drop (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base)
    (hP' : InP v agents goods base')
    (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g)
    (hω : 0 < omegaP v agents goods base) {o : A} {X Y : G → Bool} (hX : OptimalBest v agents goods base o X)
    (hoB : baseOf goods base o = baseOf goods base' o)
    (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y) :
    DeficitDrop v agents goods base' base
      (((goods.filter Y).length : Int) - ((goods.filter X).length : Int) - (eStar v agents goods base base' o X : Int)) := by
  have hb := lemma2star hag hgd hP hP' hNA hω hX.1 hX.2.1 hoB hXY hY hS
  intro d hd
  have := (deficit_of_optimalBest hag hP hω hX).2 d hd
  exact deficitLE_mono hb (by omega)

/-- **Lemma 2\*, any owner**: `def(P′) < def(P)` as soon as `|Y| + u_o(X) − e* > Val*(P)`. -/
theorem lemma2star_lt (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base)
    (hP' : InP v agents goods base')
    (hNA : ∀ g, NA agents (vbNeeds v goods base') g ↔ NA agents (vbNeeds v goods base) g)
    (hω : 0 < omegaP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (hoB : baseOf goods base o = baseOf goods base' o)
    {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y)
    (hval : ∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z, IsBundle goods base o' Z →
      SafeFor v agents goods base o' Z →
        ((goods.filter Z).length : Int) + (uCount v agents goods base o' Z : Int) <
          ((goods.filter Y).length : Int) + (uCount v agents goods base o X : Int) -
            (eStar v agents goods base base' o X : Int)) :
    DeficitLT v agents goods base' base := by
  have hb := lemma2star hag hgd hP hP' hNA hω ho hoF hoB hXY hY hS
  have hn := not_deficitLE_of_val_lt hag hP hω hval
  exact ⟨_, hb, fun h => hn (deficitLE_mono h (by omega))⟩

/-! ## Lemma 2 (extension) -/

open Classical in
/-- **`e`** (Lemma 2): the number of listed agents counted in `u_o(X)` whose good lies in `N_y(B′)`. -/
noncomputable def eCount (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) (o y : A)
    (X : G → Bool) : Nat :=
  agents.countP (fun x => decide (Counted v agents goods base o X x ∧
    ∃ g ∈ baseOf goods base x, vbNeeds v goods base' y g))

/-- **Lemma 2 (extension)** (`k4/dl2.md` §4). Let `P` be min-frozen with `ω ≥ 1`, `y` free, and `P′` the re-base of `y`
to an admissible `B′` (the hypotheses of `lemma1c`). Let `o ≠ y` be free, `X ⊆ Y` with `Y` a bundle of `o` in `P′` that
is safe in `P′`, and `e` the number of agents counted in `u_o(X)` whose good lies in `N_y(B′)`. Then `P′` is min-frozen,
`def(P′) ≤ ω + 2 − |Y| − u_o(X) + e`, and `e = 0` if `v_y(B′) ≥ v_y(B_y)`. (The text takes `X` a bundle of `o` in `P`
with `X ∩ B′ = ∅`; the bound needs only `X ⊆ Y`, and such an `X` lies in `B_o ∪ J(P′)`, `isBundle_of_disjoint`.) -/
theorem lemma2 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g)
    {o : A} (ho : o ∈ agents) (hoy : o ≠ y) (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o)
    {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y) :
    MinFrozen v agents goods base' ∧
      DeficitLE v agents goods base'
        (omegaP v agents goods base + 2 - ((goods.filter Y).length : Int) - (uCount v agents goods base o X : Int) +
          (eCount v agents goods base base' o y X : Int)) ∧
      (value v y (baseOf goods base y) ≤ value v y (baseOf goods base' y) → eCount v agents goods base base' o y X = 0) := by
  classical
  obtain ⟨hM', hNA, -⟩ := lemma1c hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  have hb := lemma2star hag hgd hM.1 hM'.1 hNA hω ho hoF (hsame o ho hoy) hXY hY hS
  have hee : eStar v agents goods base base' o X ≤ eCount v agents goods base base' o y X := by
    unfold eStar eCount
    apply List.countP_mono_left
    intro x hx h
    obtain ⟨hc, he⟩ := of_decide_eq_true h
    refine decide_eq_true ⟨hc, ?_⟩
    rcases he with hne | ⟨i, hi, hne, g, hg, hN⟩
    · have hxy : x = y := Classical.byContradiction fun h => hne (hsame x hx h)
      exact absurd (hxy ▸ hc.1) hyF
    · have hiy : i = y := Classical.byContradiction fun h => hne (hsame i hi h)
      exact ⟨g, hg, hiy ▸ hN⟩
  refine ⟨hM', deficitLE_mono hb (by omega), fun hv => ?_⟩
  unfold eCount
  apply List.countP_eq_zero.mpr
  intro x _ h
  obtain ⟨hc, g, hg, hN⟩ := of_decide_eq_true h
  exact (hc.2 g hg).2 y hy (Ne.symm hoy) (vbNeeds_mono hv hN)

/-- **Lemma 2, the gain at a best owner** (`k4/dl2.md` §4): if `X` is an optimal bundle of a best owner `o ≠ y` of `P`
(and `X ⊆ Y` as in `lemma2`), then `def(P′) ≤ def(P) − (|Y ∖ X| − e)`. -/
theorem lemma2_drop (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g)
    {o : A} (hoy : o ≠ y) {X Y : G → Bool} (hX : OptimalBest v agents goods base o X)
    (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y) :
    DeficitDrop v agents goods base' base
      (((goods.filter Y).length : Int) - ((goods.filter X).length : Int) -
        (eCount v agents goods base base' o y X : Int)) := by
  have hb := (lemma2 hag hgd hM hω hy hyF hsame hmem' hnew htwo hadm hX.1 hoy hX.2.1 hXY hY hS).2.1
  intro d hd
  have := (deficit_of_optimalBest hag hM.1 hω hX).2 d hd
  exact deficitLE_mono hb (by omega)

/-- **Lemma 2, any owner** (`k4/dl2.md` §4): for any free `o ≠ y` and `X ⊆ Y` as in `lemma2`, `def(P′) < def(P)` as
soon as `|Y| + u_o(X) − e > Val*(P)`. -/
theorem lemma2_lt (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g)
    {o : A} (ho : o ∈ agents) (hoy : o ≠ y) (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o)
    {X Y : G → Bool} (hXY : ∀ g ∈ goods, X g = true → Y g = true) (hY : IsBundle goods base' o Y)
    (hS : SafeFor v agents goods base' o Y)
    (hval : ∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z, IsBundle goods base o' Z →
      SafeFor v agents goods base o' Z →
        ((goods.filter Z).length : Int) + (uCount v agents goods base o' Z : Int) <
          ((goods.filter Y).length : Int) + (uCount v agents goods base o X : Int) -
            (eCount v agents goods base base' o y X : Int)) :
    DeficitLT v agents goods base' base := by
  have hb := (lemma2 hag hgd hM hω hy hyF hsame hmem' hnew htwo hadm ho hoy hoF hXY hY hS).2.1
  have hn := not_deficitLE_of_val_lt hag hM.1 hω hval
  exact ⟨_, hb, fun h => hn (deficitLE_mono h (by omega))⟩

/-! ## Lemma 3 (owner re-base) -/

omit [DecidableEq G] in
/-- In a re-base of `y` (Lemma 1(c)), `W′_y = B′ ∪ J(P′) = B_y ∪ J = W_y`. -/
theorem W_rebase (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) {g : G} (hg : g ∈ goods) :
    (base' g = some y ∨ base' g = none) ↔ (base g = some y ∨ base g = none) := by
  obtain ⟨-, -, -, hJ, -⟩ := lemma1c hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  constructor
  · rintro (hb | hb)
    · exact (hnew g hg hb).1
    · obtain ⟨-, -, h⟩ := (hJ g).mp (mem_junk.mpr ⟨hg, hb⟩)
      exact h.symm
  · intro h
    by_cases hb : base' g = some y
    · exact Or.inl hb
    · exact Or.inr (mem_junk.mp ((hJ g).mpr ⟨hg, hb, h.symm⟩)).2

/-- **Lemma 3 (owner re-base)** (`k4/dl2.md` §4). Let `P` be min-frozen, `y` free and `P′` the re-base of `y` to an
admissible `B′` (the hypotheses of `lemma1c`). Then the bundles of `y` in `P′` are the sets `Z` with
`B′ ⊆ Z ⊆ W_y = B_y ∪ J`; a set is safe for `y` in `P′` iff it is safe for `y` in `P`; and `u′_y(Z) = u_y(Z)`.
So `Val_{P′}(y) = max{|Z| + u_y(Z) : B′ ⊆ Z ⊆ W_y, Z safe for y in P}` (`lemma3_val`). -/
theorem lemma3 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) :
    (∀ Z : G → Bool, IsBundle goods base' y Z ↔
      (∀ g ∈ goods, base' g = some y → Z g = true) ∧ (∀ g ∈ goods, Z g = true → base g = some y ∨ base g = none)) ∧
    (∀ Z : G → Bool, SafeFor v agents goods base' y Z ↔ SafeFor v agents goods base y Z) ∧
    (∀ Z : G → Bool, uCount v agents goods base' y Z = uCount v agents goods base y Z) := by
  classical
  obtain ⟨-, -, hF, -, -⟩ := lemma1c hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  have hW := fun {g} hg => W_rebase hag hgd hM hy hyF hsame hmem' hnew htwo hadm (g := g) hg
  refine ⟨fun Z => ⟨fun h => ⟨fun g hg => (h g hg).1, fun g hg hz => (hW hg).mp ((h g hg).2 hz)⟩,
    fun ⟨h1, h2⟩ g hg => ⟨h1 g hg, fun hz => (hW hg).mpr (h2 g hg hz)⟩⟩, fun Z => ?_, fun Z => ?_⟩
  · unfold SafeFor
    constructor
    · intro h x hx hxy h' hh; rw [hsame x hx hxy]; exact h x hx hxy h' hh
    · intro h x hx hxy h' hh; rw [← hsame x hx hxy]; exact h x hx hxy h' hh
  · unfold uCount
    apply List.countP_congr
    intro x hx
    simp only [decide_eq_true_eq]
    by_cases hxy : x = y
    · subst hxy
      exact ⟨fun h => absurd ((hF x hx).mp h.1) hyF, fun h => absurd h.1 hyF⟩
    unfold Counted
    rw [hF x hx, ← hsame x hx hxy]
    refine and_congr_right fun _ => forall_congr' fun g => forall_congr' fun _ => and_congr_right fun _ =>
      forall_congr' fun i => forall_congr' fun hi => forall_congr' fun hiy => ?_
    rw [vbNeeds_congr (hsame i hi hiy).symm g]

/-- **Lemma 3, the value of `y` as owner**: `Val_{P′}(y) ≥ k` iff some `Z` with `B′ ⊆ Z ⊆ W_y`, safe for `y` in `P`,
has `|Z| + u_y(Z) ≥ k` (`u_y` computed in `P`); that is, `Val_{P′}(y) = max{|Z| + u_y(Z) : B′ ⊆ Z ⊆ W_y, Z safe}`. -/
theorem lemma3_val (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) (k : Nat) :
    (∃ Z, IsBundle goods base' y Z ∧ SafeFor v agents goods base' y Z ∧
        k ≤ (goods.filter Z).length + uCount v agents goods base' y Z) ↔
      (∃ Z : G → Bool, (∀ g ∈ goods, base' g = some y → Z g = true) ∧
        (∀ g ∈ goods, Z g = true → base g = some y ∨ base g = none) ∧ SafeFor v agents goods base y Z ∧
        k ≤ (goods.filter Z).length + uCount v agents goods base y Z) := by
  obtain ⟨hb, hs, hu⟩ := lemma3 hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  constructor
  · rintro ⟨Z, hZ, hS, hk⟩
    exact ⟨Z, ((hb Z).mp hZ).1, ((hb Z).mp hZ).2, (hs Z).mp hS, by rw [← hu Z]; exact hk⟩
  · rintro ⟨Z, h1, h2, hS, hk⟩
    exact ⟨Z, (hb Z).mpr ⟨h1, h2⟩, (hs Z).mpr hS, by rw [hu Z]; exact hk⟩

/-- **Lemma 3, the gain** (`k4/dl2.md` §4): `def(P′) < def(P)` as soon as some `Z` with `B′ ⊆ Z ⊆ W_y`, safe for `y` in
`P`, has `|Z| + u_y(Z) > Val*(P)`. -/
theorem lemma3_lt (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {y : A}
    (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g) {Z : G → Bool}
    (h1 : ∀ g ∈ goods, base' g = some y → Z g = true)
    (h2 : ∀ g ∈ goods, Z g = true → base g = some y ∨ base g = none) (hS : SafeFor v agents goods base y Z)
    (hval : ∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z', IsBundle goods base o' Z' →
      SafeFor v agents goods base o' Z' →
        ((goods.filter Z').length : Int) + (uCount v agents goods base o' Z' : Int) <
          ((goods.filter Z).length : Int) + (uCount v agents goods base y Z : Int)) :
    DeficitLT v agents goods base' base := by
  obtain ⟨hM', hNA, hF, -, hω', -⟩ := lemma1c hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  obtain ⟨hb, hs, hu⟩ := lemma3 hag hgd hM hy hyF hsame hmem' hnew htwo hadm
  have hyF' : ¬ Frozen agents goods base' (vbNeeds v goods base') y := fun h => hyF ((hF y hy).mp h)
  have hd := deficitLE_of_safe hag hM'.1 (by rw [hω']; exact hω) hy hyF' ((hb Z).mpr ⟨h1, h2⟩) ((hs Z).mpr hS)
  rw [hω', hu Z] at hd
  have hn := not_deficitLE_of_val_lt hag hM.1 hω hval
  exact ⟨_, hd, fun h => hn (deficitLE_mono h (by omega))⟩

/-! ## Lemma 7 (the unfrozen agent as owner) -/

/-- **Lemma 7** (`k4/dl2.md` §4). Let `P′ ∈ 𝒫` with `ω ≥ 1`, `x` free in `P′`, and `z` frozen in `P′` with base `{g}`,
such that no listed agent other than `x` needs `g` in `P′`. If `Z` is a safe bundle of `x` in `P′` with
`v_x(Z) > v_x(g)`, then `z` is counted in `u′_x(Z)` and `def(P′) ≤ ω + 1 − |Z|`. (The text takes `P′` min-frozen and
`g ∈ R_x`; neither is used.) -/
theorem lemma7 (hag : agents.Nodup) (hP' : InP v agents goods base') (hω : 0 < omegaP v agents goods base')
    {x z : A} {g : G} (hx : x ∈ agents) (hxF : ¬ Frozen agents goods base' (vbNeeds v goods base') x)
    (hz : z ∈ agents) (hzF : Frozen agents goods base' (vbNeeds v goods base') z)
    (hzg : baseOf goods base' z = [g]) (hneed : ∀ i ∈ agents, i ≠ x → ¬ vbNeeds v goods base' i g)
    {Z : G → Bool} (hZ : IsBundle goods base' x Z) (hS : SafeFor v agents goods base' x Z)
    (hval : v x g < value v x (goods.filter Z)) :
    Counted v agents goods base' x Z z ∧ 1 ≤ uCount v agents goods base' x Z ∧
      DeficitLE v agents goods base' (omegaP v agents goods base' + 1 - ((goods.filter Z).length : Int)) := by
  classical
  have hc : Counted v agents goods base' x Z z := by
    refine ⟨hzF, fun g' hg' => ?_⟩
    rw [hzg, List.mem_singleton] at hg'
    subst hg'
    exact ⟨fun ⟨_, _, hlt⟩ => by omega, hneed⟩
  have hu : 1 ≤ uCount v agents goods base' x Z := by
    unfold uCount
    exact List.countP_pos_iff.mpr ⟨z, hz, decide_eq_true hc⟩
  refine ⟨hc, hu, deficitLE_mono (deficitLE_of_safe hag hP' hω hx hxF hZ hS) (by omega)⟩

omit [DecidableEq A] in
/-- **Lemma 7, big-top** (`k4/dl2.md` §4): if `x`'s relevant goods are `g, b, c, d` (`b, c, d` distinct) with
`v_x(d) ≤ v_x(c) ≤ v_x(b)` and `v_x(g) > v_x(b) + v_x(c)` (`x` big-top, `g` its top), then a set `Z` without `g` with
`v_x(Z) > v_x(g)` contains every relevant good of `x` other than `g`: `R_x ∖ {g} ⊆ Z`. -/
theorem lemma7_bigTop (hgd : goods.Nodup) {x : A} {g b c d : G} (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hR : ∀ h ∈ goods, 0 < v x h → h = g ∨ h = b ∨ h = c ∨ h = d)
    (hdc : v x d ≤ v x c) (hcb : v x c ≤ v x b) (htop : v x b + v x c < v x g)
    {Z : G → Bool} (hZg : Z g = false) (hval : v x g < value v x (goods.filter Z)) :
    ∀ h ∈ goods, 0 < v x h → h ≠ g → Z h = true := by
  have hnd : (goods.filter Z).Nodup := hgd.sublist List.filter_sublist
  -- if one of `b, c, d` is missing, the relevant goods of `Z` lie in a pair worth at most `v_x(b) + v_x(c)`
  have key : ∀ p q : G, p ≠ q → v x p + v x q ≤ v x b + v x c →
      (∀ h ∈ goods, 0 < v x h → Z h = true → h = p ∨ h = q) → False := by
    intro p q hpq hle hsub
    have := value_le_of_rel_sub (v := v) (i := x) (T := [p, q]) hnd (by simp [hpq]) fun h hh hpos => by
      obtain ⟨hhg, hz⟩ := List.mem_filter.mp hh
      rcases hsub h hhg hpos hz with e | e <;> simp [e]
    have hpq' : value v x [p, q] = v x p + v x q := by simp [value]
    omega
  have hZ : ∀ h ∈ goods, 0 < v x h → Z h = true → h = b ∨ h = c ∨ h = d := by
    intro h hh hpos hz
    rcases hR h hh hpos with e | e
    · subst e; rw [hZg] at hz; cases hz
    · exact e
  intro h hh hpos hhg
  rcases (hR h hh hpos).resolve_left hhg with e | e | e <;> subst e <;>
    refine Classical.byContradiction fun hn => ?_ <;> have hn : Z h = false := by simpa using hn
  · exact key c d hcd (by omega) fun h' hh' hp hz => by
      rcases hZ h' hh' hp hz with e | e | e
      · subst e; rw [hn] at hz; cases hz
      · exact Or.inl e
      · exact Or.inr e
  · exact key b d hbd (by omega) fun h' hh' hp hz => by
      rcases hZ h' hh' hp hz with e | e | e
      · exact Or.inl e
      · subst e; rw [hn] at hz; cases hz
      · exact Or.inr e
  · exact key b c hbc (by omega) fun h' hh' hp hz => by
      rcases hZ h' hh' hp hz with e | e | e
      · exact Or.inl e
      · exact Or.inr e
      · subst e; rw [hn] at hz; cases hz

/-! ## Corollaries 4 (release) and 5 (unblocking) -/

omit [DecidableEq A] in
/-- `X ∪ {c}` for a good `c ∉ X`: one more good, worth `v_i(c)` more. -/
theorem filter_insert_perm (hgd : goods.Nodup) {X : G → Bool} {c : G} (hc : c ∈ goods) (hXc : X c = false) :
    (goods.filter (fun g => X g || decide (g = c))).Perm (c :: goods.filter X) := by
  apply (List.perm_ext_iff_of_nodup (hgd.sublist List.filter_sublist) ?_).mpr
  · intro g
    simp only [List.mem_filter, List.mem_cons, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hg, hx | e⟩
      · exact Or.inr ⟨hg, hx⟩
      · exact Or.inl e
    · rintro (e | ⟨hg, hx⟩)
      · subst e; exact ⟨hc, Or.inr rfl⟩
      · exact ⟨hg, Or.inl hx⟩
  · refine List.nodup_cons.mpr ⟨fun h => ?_, hgd.sublist List.filter_sublist⟩
    rw [(List.mem_filter.mp h).2] at hXc; cases hXc

/-- In Corollaries 4 and 5, `Y = X ∪ {c}` is a bundle of `o` in `P′` when `X` is a bundle of `o` in `P` missing the
new base of `y` and `c` is junk in `P′`. -/
theorem isBundle_insert {o y : A} (hoB : baseOf goods base o = baseOf goods base' o)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents) {X : G → Bool} (hX : IsBundle goods base o X)
    (hXy : ∀ g ∈ goods, X g = true → base' g ≠ some y) {c : G} (hc' : base' c = none) :
    IsBundle goods base' o (fun g => X g || decide (g = c)) := by
  intro g hg
  refine ⟨fun hb => by simp [(hX g hg).1 ((base_eq_some_iff hoB.symm hg).mp hb)], fun hy => ?_⟩
  rcases Bool.or_eq_true _ _ |>.mp hy with hx | e
  · cases hb : base' g with
    | none => exact Or.inr rfl
    | some i =>
      have hiy : i ≠ y := fun e => hXy g hg hx (by rw [hb, e])
      have := (base_eq_some_iff (hsame i (hmem' g hg i hb) hiy).symm hg).mp hb
      rcases (hX g hg).2 hx with e | e <;> rw [this] at e
      · exact Or.inl e
      · cases e
  · have : g = c := of_decide_eq_true e
    subst this; exact Or.inr hc'

/-- **Corollary 4 (release)** (`k4/dl2.md` §4). Let `P` be min-frozen with `ω ≥ 1`, `X` an optimal bundle of a best
owner `o`, and `y ≠ o` a free agent holding the pair `B_y = {p, q}`; let `P′` be `P` with `B′_y = {p}` (the release of
`q`), with `N_y({p}) ⊆ 𝒩`. Suppose (i) `X ∪ {q}` threatens no listed `z ∉ {o, y}` holding `B_z`;
(ii) `v_y(X ∩ R_y) + v_y(q) ≤ v_y(p)`; (iii) no agent counted in `u_o(X)` has its good in `N_y({p})`. Then `P′` is
min-frozen and `def(P′) ≤ def(P) − 1`. (The text also assumes `def(P) > 0`, which the conclusion does not use.) -/
theorem cor4 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {o y : A} {X : G → Bool} (hX : OptimalBest v agents goods base o X)
    (hoy : o ≠ y) (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    {p q : G} (hp : p ∈ goods) (hq : q ∈ goods) (hpq : p ≠ q) (hBy : ∀ g ∈ goods, base g = some y ↔ g = p ∨ g = q)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hp' : ∀ g ∈ goods, base' g = some y ↔ g = p)
    (hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g)
    (hi : ∀ z ∈ agents, z ≠ o → z ≠ y → ∀ h ∈ goods.filter (fun g => X g || decide (g = q)),
      value v z ((goods.filter (fun g => X g || decide (g = q))).erase h) ≤ value v z (baseOf goods base z))
    (hii : value v y (goods.filter X) + v y q ≤ v y p)
    (hiii : ∀ x ∈ agents, Counted v agents goods base o X x →
      ∀ g ∈ baseOf goods base x, ¬ vbNeeds v goods base' y g) :
    MinFrozen v agents goods base' ∧ DeficitDrop v agents goods base' base 1 := by
  classical
  have hP := hM.1
  have hXb := hX.2.2.1
  have hoB := hsame o hX.1 hoy
  have hXyP : ∀ g ∈ goods, X g = true → base g ≠ some y := fun g hg hx hb => by
    rcases (hXb g hg).2 hx with e | e <;> rw [hb] at e
    · exact hoy (Option.some.inj e).symm
    · cases e
  have hXq : X q = false := by
    cases h : X q with
    | false => rfl
    | true => exact absurd ((hBy q hq).mpr (Or.inr rfl)) (hXyP q hq h)
  have hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g := by
    intro g hg hb
    have e := (hp' g hg).mp hb
    subst e
    exact ⟨Or.inl ((hBy g hg).mpr (Or.inl rfl)), hP.rel g hg y ((hBy g hg).mpr (Or.inl rfl))⟩
  have hB' : baseOf goods base' y = [p] := baseOf_single hgd hp hp'
  have hq' : base' q = none := by
    cases hb : base' q with
    | none => rfl
    | some i =>
      by_cases hiy : i = y
      · subst hiy; exact absurd ((hp' q hq).mp hb).symm hpq
      · have := (base_eq_some_iff (hsame i (hmem' q hq i hb) hiy).symm hq).mp hb
        rw [(hBy q hq).mpr (Or.inr rfl)] at this
        exact absurd (Option.some.inj this).symm hiy
  have hY := isBundle_insert hoB hsame hmem' hXb
    (fun g hg hx hb => hXyP g hg hx ((hBy g hg).mpr (Or.inl ((hp' g hg).mp hb)))) hq'
  have hperm := filter_insert_perm hgd hq hXq
  have hS : SafeFor v agents goods base' o (fun g => X g || decide (g = q)) := by
    intro z hz hzo h hh
    by_cases hzy : z = y
    · subst hzy
      rw [hB']
      have h1 := value_sublist v z (List.erase_sublist (l := goods.filter (fun g => X g || decide (g = q))) (a := h))
      rw [value_perm hperm] at h1
      simp only [value, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at h1 ⊢
      unfold value at hii
      omega
    · rw [← hsame z hz hzy]; exact hi z hz hzo hzy h hh
  have hXY : ∀ g ∈ goods, X g = true → (X g || decide (g = q)) = true := fun g _ hx => by rw [hx]; rfl
  obtain ⟨hM', -, he⟩ := lemma2 hag hgd hM hω hy hyF hsame hmem' hnew (by rw [hB']; simp) hadm hX.1 hoy
    hX.2.1 hXY hY hS
  have hd := lemma2_drop hag hgd hM hω hy hyF hsame hmem' hnew (by rw [hB']; simp) hadm hoy hX hXY hY hS
  have he0 : eCount v agents goods base base' o y X = 0 := by
    unfold eCount
    apply List.countP_eq_zero.mpr
    intro x hx h
    obtain ⟨hc, g, hg, hN⟩ := of_decide_eq_true h
    exact hiii x hx hc g hg hN
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  refine ⟨hM', fun d hd' => ?_⟩
  have := hd d hd'
  rw [hlen, he0] at this
  exact deficitLE_mono this (by omega)

/-- **Corollary 4, (i′) ⟹ (i)**: if no listed agent outside `{o, y}` values `q` and `X ⊄ R_z` for every such `z`, then
`X ∪ {q}` threatens none of them (given that `X` is safe for `o` in `P` and `q ∉ X`). -/
theorem cor4_i_of_i' (hgd : goods.Nodup) {o y : A} {X : G → Bool} {q : G} (hq : q ∈ goods) (hXq : X q = false)
    (hXs : SafeFor v agents goods base o X)
    (hi' : ∀ z ∈ agents, z ≠ o → z ≠ y → v z q = 0 ∧ ∃ h₀ ∈ goods, X h₀ = true ∧ v z h₀ = 0) :
    ∀ z ∈ agents, z ≠ o → z ≠ y → ∀ h ∈ goods.filter (fun g => X g || decide (g = q)),
      value v z ((goods.filter (fun g => X g || decide (g = q))).erase h) ≤ value v z (baseOf goods base z) := by
  intro z hz hzo hzy h _
  obtain ⟨hq0, h₀, hh₀, hX₀, hv₀⟩ := hi' z hz hzo hzy
  have h₀X : h₀ ∈ goods.filter X := List.mem_filter.mpr ⟨hh₀, hX₀⟩
  have h1 := value_sublist v z (List.erase_sublist (l := goods.filter (fun g => X g || decide (g = q))) (a := h))
  rw [value_perm (filter_insert_perm hgd hq hXq)] at h1
  have h2 := value_erase (v := v) (i := z) h₀X
  have h3 := hXs z hz hzo h₀ h₀X
  have h4 : value v z (q :: goods.filter X) = v z q + value v z (goods.filter X) := by simp [value]
  omega

/-- **Corollary 5 (unblocking)** (`k4/dl2.md` §4). Let `P` be min-frozen with `ω ≥ 1`, `X` an optimal bundle of a best
owner `o`, `C = J ∖ X`, `y ≠ o` free, and `P′` the re-base of `y` to `B′ ⊆ (B_y ∪ C) ∩ R_y` with `|B′| ≤ 2` and
`v_y(B′) ≥ v_y(B_y)`. Suppose some `c ∈ C ∖ B′` is such that `X ∪ {c}` threatens no listed `z ∉ {o, y}` holding `B_z`,
and `θ_y(X ∪ {c}) ≤ v_y(B′)`. Then `P′` is min-frozen and `def(P′) ≤ def(P) − 1`. (The text also assumes `def(P) > 0`
and `B′ ≠ B_y`, which the conclusion does not use.) -/
theorem cor5 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {o y : A} {X : G → Bool} (hX : OptimalBest v agents goods base o X)
    (hoy : o ≠ y) (hy : y ∈ agents) (hyF : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hnew : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ (base g = none ∧ X g = false)) ∧ 0 < v y g)
    (htwo : (baseOf goods base' y).length ≤ 2)
    (hv : value v y (baseOf goods base y) ≤ value v y (baseOf goods base' y))
    {c : G} (hc : c ∈ goods) (hcJ : base c = none) (hcX : X c = false) (hcB : base' c ≠ some y)
    (hi : ∀ z ∈ agents, z ≠ o → z ≠ y → ∀ h ∈ goods.filter (fun g => X g || decide (g = c)),
      value v z ((goods.filter (fun g => X g || decide (g = c))).erase h) ≤ value v z (baseOf goods base z))
    (hii : ∀ h ∈ goods.filter (fun g => X g || decide (g = c)),
      value v y ((goods.filter (fun g => X g || decide (g = c))).erase h) ≤ value v y (baseOf goods base' y)) :
    MinFrozen v agents goods base' ∧ DeficitDrop v agents goods base' base 1 := by
  classical
  have hXb := hX.2.2.1
  have hoB := hsame o hX.1 hoy
  have hnew' : ∀ g ∈ goods, base' g = some y → (base g = some y ∨ base g = none) ∧ 0 < v y g := fun g hg hb =>
    ⟨(hnew g hg hb).1.imp_right fun h => h.1, (hnew g hg hb).2⟩
  have hadm : ∀ g, vbNeeds v goods base' y g → NA agents (vbNeeds v goods base) g :=
    fun g hN => ⟨y, hy, vbNeeds_mono hv hN⟩
  have hc' : base' c = none := by
    cases hb : base' c with
    | none => rfl
    | some i =>
      have hiy : i ≠ y := fun e => hcB (by rw [hb, e])
      have := (base_eq_some_iff (hsame i (hmem' c hc i hb) hiy).symm hc).mp hb
      rw [hcJ] at this; cases this
  have hY := isBundle_insert hoB hsame hmem' hXb (fun g hg hx hb => by
    rcases (hnew g hg hb).1 with e | ⟨-, e⟩
    · rcases (hXb g hg).2 hx with e' | e' <;> rw [e] at e'
      · exact hoy (Option.some.inj e').symm
      · cases e'
    · rw [hx] at e; cases e) hc'
  have hS : SafeFor v agents goods base' o (fun g => X g || decide (g = c)) := by
    intro z hz hzo h hh
    by_cases hzy : z = y
    · subst hzy; exact hii h hh
    · rw [← hsame z hz hzy]; exact hi z hz hzo hzy h hh
  have hXY : ∀ g ∈ goods, X g = true → (X g || decide (g = c)) = true := fun g _ hx => by rw [hx]; rfl
  obtain ⟨hM', -, he⟩ := lemma2 hag hgd hM hω hy hyF hsame hmem' hnew' htwo hadm hX.1 hoy
    hX.2.1 hXY hY hS
  have hd := lemma2_drop hag hgd hM hω hy hyF hsame hmem' hnew' htwo hadm hoy hX hXY hY hS
  have hlen := (filter_insert_perm hgd hc hcX).length_eq
  simp only [List.length_cons] at hlen
  refine ⟨hM', fun d hd' => ?_⟩
  have := hd d hd'
  rw [hlen, he hv] at this
  exact deficitLE_mono this (by omega)

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
#print axioms EFX.C4min.otherSlots_roNeeds
#print axioms EFX.C4min.h1_core
#print axioms EFX.C4min.deficitLE_of_safe
#print axioms EFX.C4min.exists_safe_of_deficitLE
#print axioms EFX.C4min.lemmaH1
#print axioms EFX.C4min.lemmaH1_owner
#print axioms EFX.C4min.deficitLT_of_drop
#print axioms EFX.C4min.not_deficitLE_of_val_lt
#print axioms EFX.C4min.deficit_of_optimalBest
#print axioms EFX.C4min.setNeeds_mono
#print axioms EFX.C4min.isBundle_of_disjoint
#print axioms EFX.C4min.lemma2star
#print axioms EFX.C4min.lemma2star_drop
#print axioms EFX.C4min.lemma2star_lt
#print axioms EFX.C4min.lemma2
#print axioms EFX.C4min.lemma2_drop
#print axioms EFX.C4min.lemma2_lt
#print axioms EFX.C4min.W_rebase
#print axioms EFX.C4min.lemma3
#print axioms EFX.C4min.lemma3_val
#print axioms EFX.C4min.lemma3_lt
#print axioms EFX.C4min.lemma7
#print axioms EFX.C4min.lemma7_bigTop
#print axioms EFX.C4min.filter_insert_perm
#print axioms EFX.C4min.isBundle_insert
#print axioms EFX.C4min.cor4
#print axioms EFX.C4min.cor4_i_of_i'
#print axioms EFX.C4min.cor5
#print axioms EFX.C4min.moveT1_iff_code
#print axioms EFX.C4min.free_of_swap
#print axioms EFX.C4min.moveT3_iff_code
#print axioms EFX.C4min.lemma1c_rebase
#print axioms EFX.C4min.moveT1_rebase
