import EFX.DL2Moves

/-!
# Role swaps and frozen rotations: Lemmas 8–12 of `k4/dl13.md` §2

Ledger K4.DL13.SWAP.LEAN, K4.DL13.ROT.LEAN. The written proofs are those of `k4/dl13.md` §2.1, §2.2 (PR #75, refereed in
its review; rows K4.DL13.SWAP, K4.DL13.ROT). Everything is stated over the definitions of `EFX/C4min.lean`,
`EFX/PreAllocK.lean`, `EFX/C4minDescent.lean`, `EFX/DL13.lean` and `EFX/DL2Moves.lean` (bundles `IsBundle`, safety
`SafeFor`, `N_o(Z)` = `setNeeds`, `u_o` = `uCount`, optimal bundles of best owners `OptimalBest`, `DeficitDrop`), with the
conventions of `EFX/DL2Moves.lean`. Strictness is `EFX.Strict` (`EFX/K4Ties.lean`); `|R_x| ≤ 4` is
`(relevant v x goods).length ≤ 4` (both hold on every strict profile of a k = 4 core, the setting of `k4/dl13.md`).

**New definitions.**
- `RoleSwap v agents goods base base' x z g H`: the role swap of `k4/dl13.md` §2.1 (Lemma 6's hypotheses): `x` frozen
  with `B_x = {g}`, `z` free with `g ∈ R_z`, free helpers `H`; in `P′` `z` holds `{g}`, `x` and the helpers hold new bases
  inside `G = J ∪ B_z ∪ ⋃ B_h` (`SwapPool`) and their relevant sets, of at most two goods, with needs inside `𝒩`; the
  other listed agents keep their bases. `swapBase base x z g A` constructs the swap without helper
  (`roleSwap_swapBase`).
- `uBar` (`ū(Z)`), `iotaSwap` (`ι(Z)`) of Lemma 8; `eSwap` (`e`), `iotaNeed` (`ι`) of Lemma 9; `CountGood` (a good
  counted by `u_o(Z)`).
- `ParetoReassign v agents goods base base' π`: a Pareto reassignment of the frozen agents' goods (each frozen `x` takes
  `B_{π(x)}`, `π(x)` frozen, `v_x(B_{π(x)}) ≥ v_x(B_x)`; every frozen agent is some `π(x)`; free agents keep their bases);
  `IsParetoReassign`, `T4Optimal` (every Pareto reassignment is the identity), `ReassignChain` (finitely many in a row),
  `frozenWelfare` (`Σ_{x ∈ F} v_x(B_x)`).

**Results.**
- *Lemma 8* (the unfrozen agent as owner): `RoleSwap.junk_iff` (`J′ = G ∖ (A ∪ ⋃ B′_h)`), `RoleSwap.lemma8_bundle`
  (`x`'s bundles in `P′` are the `A ⊆ Z ⊆ G ∖ ⋃ B′_h`), `RoleSwap.lemma8_safe` (safety agent by agent),
  `RoleSwap.lemma8_u` (`u′_x(Z) = ū(Z) + ι(Z)`), `RoleSwap.lemma8` (`x` free in `P′`, `def(P′) ≤ ω + 2 − |Z| − ū − ι`),
  `RoleSwap.lemma8_val` (`Val_{P′}(x) = max (|Z| + ū(Z) + ι(Z))`); *Corollary 8.2*: `RoleSwap.cor8_2`.
- *Lemma 9* (the owner swap from a needer): `lemma9_admissible` (`Z` contains a base admissible for `x`),
  `RoleSwap.lemma9` (`def(P′) ≤ ω + 2 − |Z| − (u_o(X) − e) − ι`), `RoleSwap.eSwap_eq_zero` (`e = 0` when
  `v_o(X) < v_o(g)`), `RoleSwap.eSwap_le_one` (`e ≤ 1` when `g` is `o`'s top); *Corollaries 9.1, 9.2*: `cor9_1` (the S1
  repair: an admissible `A ⊆ X ∪ {c}` exists, and the constructed swap is a min-frozen (T3)-neighbour with
  `def(P′) ≤ def(P) − 1 − ι`), `cor9_2`.
- *Lemma 10* (the θ-dichotomy): `lemma10` (exactly one of (θ-a), (θ-b)), `lemma10_a` (under (θ-a), `Q` is an admissible
  re-base of `o` not needing `g`, and some other agent needs `g`).
- *Lemma 11* (an owner that does not move): `lemma11`; *Corollary 11.1* (the blocker swap): `cor11_1`, `cor11_1_auto`.
- *Lemma 12* (frozen rotations): `lemma12_move` (min-frozen, same `NA`, `F`, `J`, `ω`, free agents' bases and needs),
  `lemma12` (bundles unchanged, safety preserved, `u′_o ≥ u_o`, `def(P′) ≤ def(P)`), `lemma12_lt_iff` (the strict case,
  exactly), `lemma12_lt` (its two particular cases), `uCount_eq_goods` (`u_o(Z) = #{h ∈ 𝒩 : h ∉ N_o(Z) ∪ 𝒩₋ₒ}` on `𝒫`);
  *Corollary 12.1*: `cor12_1` (finitely many Pareto reassignments reach a T4-optimal `P*` with `def(P*) ≤ def(P)`).

**Faithfulness** (paper statement; Lean statement; why they agree). Each theorem's docstring restates the paper
statement. The Lean statements use the text's objects and conclusions with the same or weaker hypotheses. Where the
prose leaves room:
1. *The swap* is any base map meeting Lemma 6's conditions (`RoleSwap`); the text's `H = ∅` or `{h}` is a list `H`
   (Lemma 8 holds for any list of helpers). The text's "z needs g" is used only where the text uses it (Lemma 6's
   `N_z({g}) ⊆ 𝒩` is a field of `RoleSwap`; `roleSwap_swapBase` derives it from `g ∈ N_z`).
2. *Lemma 8*: `ū(Z)`'s set `N_z({g}) ∪ N_h(B′_h) ∪ 𝒩_{−{x,z,h}}` is the needed set of the listed agents other than `x`
   in `P′` (their needs there are `N_z({g})`, `N_h(B′_h)` and the unchanged `N_i`), and `ι`'s
   `g ∉ N_h(B′_h) ∪ 𝒩_{−{x,z,h}}` is "no listed agent other than `x, z` needs `g` in `P′`". The text's
   "`g ∉ N_x(Z)` iff `v_x(Z) > v_x(g)`, by strictness" is where `Strict` enters.
3. *Corollary 8.2* uses only: `z` the only needer of `g` in `P`, no helper needing `g` in `P′`, `x` strictly balanced on
   `g`, and `L_x ⊆ Z`; the text's "`x` big-top, `L_x ⊆ G`, `A ⊆ L_x`, `B′_h ∩ L_x = ∅`" say when such a `Z` exists. Its gain
   is stated with `|Z| + 1 + ū(Z) > Val*(P)`, which the text's `|Z| + 1 > Val*(P)` implies.
4. *Lemma 9*: the bound holds for every set `X` (the text takes a bundle of `o` in `P`; `eSwap_eq_zero` uses
   `X ⊆ W_o`); "`g` is `o`'s top" is `∀ r, v_o(r) ≤ v_o(g)`. *Corollary 11.1*: "X ∪ {c} threatens exactly one agent other
   than `o`, `z`" is used only as "threatens nobody outside `{o, z}`".
5. *Lemma 10*: (θ-b)'s "`o` big-top (`v_o(g) > v_o(b_o) + v_o(c_o)`)" is "every pair of `o`'s other goods is worth less
   than `g`" (the same, `b_o, c_o` being the best pair); "`Q` is a re-base admissible for `o`" is `N_o(Q) ⊆ 𝒩`,
   `Q ⊆ (B_o ∪ J) ∩ R_o`, `|Q| ≤ 2`, `Q ≠ B_o`.
6. *Lemma 11* is stated in the generality of Lemma 2* (any move keeping the needed set, with a newly frozen `z` on `g`):
   `κ = 1` is the text's condition, and `e*` counts the agents whose base actually changes, a subset of the text's
   `{x, z} ∪ H`, so it is at most the text's `e*` and the bound is at least as strong.
7. *Lemma 12*: "π a permutation of `F`" is "`π` maps `F` to `F` and onto `F`" (one-to-one follows, `P′` being a map);
   "`Val_{P′}(o) ≥ Val_P(o)`" is the three facts of `lemma12` together. Proposition 12.2 (DL₁₃^opt ⟹ TARGET₄) is not
   formalized: DL₁₃^opt is refuted (K4.DL13.OPT).

No statement of `k4/dl13.md` §2 turned out wrong or ambiguous; the differences above are weakenings of hypotheses or
choices of encoding.
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

/-! ## `k4/dl13.md` §2.1: the role swap, and Lemma 8 (the unfrozen agent as owner) -/

/-- The goods a role swap may use: `G = J ∪ B_z ∪ ⋃_{h ∈ H} B_h`. -/
def SwapPool (base : G → Option A) (z : A) (H : List A) (g : G) : Prop :=
  base g = none ∨ base g = some z ∨ ∃ h ∈ H, base g = some h

/-- **The role swap of `k4/dl13.md` §2.1** (the hypotheses of Lemma 6, `lemma6`): `x` frozen with `B_x = {g}`, `z` free
with `g ∈ R_z`, helpers `H` free and other than `x, z`; in `P′`, `z` holds `{g}`, `x` and the helpers hold new bases
inside `G` and their relevant sets, of at most two goods, with needs inside `𝒩` (as `z`'s); every other listed agent
keeps its base, and base goods go to listed agents. -/
structure RoleSwap (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) (x z : A) (g : G)
    (H : List A) : Prop where
  hx : x ∈ agents
  hxg : baseOf goods base x = [g]
  hgN : NA agents (vbNeeds v goods base) g
  hz : z ∈ agents
  hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z
  hzg : 0 < v z g
  hH : ∀ h ∈ H, h ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧ h ≠ x ∧ h ≠ z
  hsame : ∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ H → baseOf goods base i = baseOf goods base' i
  hmem' : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents
  hz' : baseOf goods base' z = [g]
  hnew : ∀ i, (i = x ∨ i ∈ H) → ∀ g' ∈ goods, base' g' = some i → SwapPool base z H g' ∧ 0 < v i g'
  htwo : ∀ i, (i = x ∨ i ∈ H) → (baseOf goods base' i).length ≤ 2
  hadm : ∀ i, (i = x ∨ i = z ∨ i ∈ H) → ∀ g', vbNeeds v goods base' i g' → NA agents (vbNeeds v goods base) g'

namespace RoleSwap

variable {x z : A} {g : G} {H : List A}

omit [DecidableEq G] in
/-- Lemma 6 for a `RoleSwap`. -/
theorem lemma6' (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (h : RoleSwap v agents goods base base' x z g H) :
    MinFrozen v agents goods base' ∧
      (∀ g', NA agents (vbNeeds v goods base') g' ↔ NA agents (vbNeeds v goods base) g') ∧
      (∀ i ∈ agents, Frozen agents goods base' (vbNeeds v goods base') i ↔
        (Frozen agents goods base (vbNeeds v goods base) i ∧ i ≠ x) ∨ i = z) ∧
      omegaP v agents goods base' = omegaP v agents goods base :=
  lemma6 hag hgd hM h.hx h.hxg h.hgN h.hz h.hzF h.hzg h.hH h.hsame h.hmem' h.hz' h.hnew h.htwo h.hadm

omit [DecidableEq G] in
theorem x_ne_z (h : RoleSwap v agents goods base base' x z g H) : x ≠ z := fun e =>
  h.hzF (e ▸ ⟨g, h.hxg, h.hgN⟩)

omit [DecidableEq G] in
theorem g_mem (h : RoleSwap v agents goods base base' x z g H) : g ∈ goods ∧ base g = some x :=
  mem_baseOf.mp (by rw [h.hxg]; exact List.mem_singleton_self g)

omit [DecidableEq G] in
theorem base'_g (h : RoleSwap v agents goods base base' x z g H) : base' g = some z :=
  (mem_baseOf.mp (by rw [h.hz']; exact List.mem_singleton_self g)).2

omit [DecidableEq G] in
/-- **The junk after a swap**: `J′ = G ∖ (A ∪ ⋃ B′_h)` (`k4/dl13.md` §2.1). -/
theorem junk_iff (hP : InP v agents goods base) (h : RoleSwap v agents goods base base' x z g H) {g' : G}
    (hg' : g' ∈ goods) :
    base' g' = none ↔ SwapPool base z H g' ∧ base' g' ≠ some x ∧ ∀ k ∈ H, base' g' ≠ some k := by
  constructor
  · intro hb'
    refine ⟨?_, by rw [hb']; simp, fun k _ => by rw [hb']; simp⟩
    cases hb : base g' with
    | none => exact Or.inl hb
    | some i =>
      by_cases hiz : i = z
      · exact Or.inr (Or.inl (by rw [hb, hiz]))
      by_cases hiH : i ∈ H
      · exact Or.inr (Or.inr ⟨i, hiH, hb⟩)
      by_cases hix : i = x
      · subst hix
        have : g' = g := by
          have hm : g' ∈ baseOf goods base i := mem_baseOf.mpr ⟨hg', hb⟩
          rw [h.hxg, List.mem_singleton] at hm; exact hm
        subst this; rw [h.base'_g] at hb'; cases hb'
      · have := (base_eq_some_iff (h.hsame i (hP.mem g' hg' i hb) hix hiz hiH).symm hg').mpr hb
        rw [hb'] at this; cases this
  · rintro ⟨hpool, hx', hH'⟩
    cases hb' : base' g' with
    | none => rfl
    | some i =>
      exfalso
      by_cases hix : i = x
      · exact hx' (by rw [hb', hix])
      by_cases hiH : i ∈ H
      · exact hH' i hiH hb'
      by_cases hiz : i = z
      · subst hiz
        have : g' = g := by
          have hm : g' ∈ baseOf goods base' i := mem_baseOf.mpr ⟨hg', hb'⟩
          rw [h.hz', List.mem_singleton] at hm; exact hm
        subst this
        rcases hpool with e | e | ⟨k, hk, e⟩ <;> rw [h.g_mem.2] at e
        · cases e
        · exact h.x_ne_z (Option.some.inj e)
        · exact (h.hH k hk).2.2.1 (Option.some.inj e).symm
      · have := (base_eq_some_iff (h.hsame i (h.hmem' g' hg' i hb') hix hiz hiH).symm hg').mp hb'
        rcases hpool with e | e | ⟨k, hk, e⟩ <;> rw [this] at e
        · cases e
        · exact hiz (Option.some.inj e)
        · exact hiH (Option.some.inj e ▸ hk)

omit [DecidableEq G] in
/-- **Lemma 8, the bundles** (`k4/dl13.md` §2.1): the bundles of `x` in `P′` are the `Z` with
`A ⊆ Z ⊆ G ∖ ⋃_{h ∈ H} B′_h` (`A = B′_x`). -/
theorem lemma8_bundle (hP : InP v agents goods base) (h : RoleSwap v agents goods base base' x z g H)
    (Z : G → Bool) :
    IsBundle goods base' x Z ↔ (∀ g' ∈ goods, base' g' = some x → Z g' = true) ∧
      (∀ g' ∈ goods, Z g' = true → SwapPool base z H g' ∧ ∀ k ∈ H, base' g' ≠ some k) := by
  constructor
  · intro hZ
    refine ⟨fun g' hg' hb => (hZ g' hg').1 hb, fun g' hg' hz => ?_⟩
    rcases (hZ g' hg').2 hz with hb | hb
    · refine ⟨(h.hnew x (Or.inl rfl) g' hg' hb).1, fun k hk e => ?_⟩
      rw [hb] at e; exact (h.hH k hk).2.2.1 (Option.some.inj e).symm
    · exact ⟨((h.junk_iff hP hg').mp hb).1, ((h.junk_iff hP hg').mp hb).2.2⟩
  · rintro ⟨h1, h2⟩ g' hg'
    refine ⟨h1 g' hg', fun hz => ?_⟩
    by_cases hb : base' g' = some x
    · exact Or.inl hb
    · exact Or.inr ((h.junk_iff hP hg').mpr ⟨(h2 g' hg' hz).1, hb, (h2 g' hg' hz).2⟩)

/-- **Lemma 8, safety** (`k4/dl13.md` §2.1): `Z` is safe for `x` in `P′` iff it threatens no agent outside the move
holding its base, does not threaten `z` holding `{g}`, and does not threaten a helper holding its new base. -/
theorem lemma8_safe (h : RoleSwap v agents goods base base' x z g H) (Z : G → Bool) :
    SafeFor v agents goods base' x Z ↔
      (∀ w ∈ agents, w ≠ x → w ≠ z → w ∉ H → ∀ k ∈ goods.filter Z,
        value v w ((goods.filter Z).erase k) ≤ value v w (baseOf goods base w)) ∧
      (∀ k ∈ goods.filter Z, value v z ((goods.filter Z).erase k) ≤ v z g) ∧
      (∀ w ∈ H, ∀ k ∈ goods.filter Z, value v w ((goods.filter Z).erase k) ≤ value v w (baseOf goods base' w)) := by
  have hzg : value v z (baseOf goods base' z) = v z g := by rw [h.hz']; simp [value]
  constructor
  · intro hS
    refine ⟨fun w hw hwx hwz hwH k hk => ?_, fun k hk => ?_, fun w hw k hk => hS w (h.hH w hw).1 (h.hH w hw).2.2.1 k hk⟩
    · rw [h.hsame w hw hwx hwz hwH]; exact hS w hw hwx k hk
    · rw [← hzg]; exact hS z h.hz (Ne.symm h.x_ne_z) k hk
  · rintro ⟨h1, h2, h3⟩ w hw hwx k hk
    by_cases hwz : w = z
    · subst hwz; rw [hzg]; exact h2 k hk
    by_cases hwH : w ∈ H
    · exact h3 w hwH k hk
    · rw [← h.hsame w hw hwx hwz hwH]; exact h1 w hw hwx hwz hwH k hk

end RoleSwap

open Classical in
/-- **`ū(Z)`** (Lemma 8): the frozen agents of `P` other than `x` whose base misses `N_x(Z) ∪ 𝒩′₋ₓ`, where
`𝒩′₋ₓ = N_z({g}) ∪ N_h(B′_h) ∪ 𝒩_{−{x,z,h}}` is the needed set of the listed agents other than `x` in `P′`. -/
noncomputable def uBar (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) (x : A)
    (Z : G → Bool) : Nat :=
  agents.countP (fun w => decide (Frozen agents goods base (vbNeeds v goods base) w ∧ w ≠ x ∧
    ∀ g' ∈ baseOf goods base w, ¬ setNeeds v goods x Z g' ∧ ∀ i ∈ agents, i ≠ x → ¬ vbNeeds v goods base' i g'))

open Classical in
/-- **`ι(Z)`** (Lemma 8): `1` if `v_x(Z) > v_x(g)` and no listed agent other than `x, z` needs `g` in `P′`
(`g ∉ N_h(B′_h) ∪ 𝒩_{−{x,z,h}}`), `0` otherwise. -/
noncomputable def iotaSwap (v : A → G → Nat) (agents : List A) (goods : List G) (base' : G → Option A) (x z : A)
    (g : G) (Z : G → Bool) : Nat :=
  if v x g < value v x (goods.filter Z) ∧ ∀ i ∈ agents, i ≠ x → i ≠ z → ¬ vbNeeds v goods base' i g then 1 else 0

namespace RoleSwap

variable {x z : A} {g : G} {H : List A}

/-- **Lemma 8, the count** (`k4/dl13.md` §2.1): for a bundle `Z` of `x` in `P′`, on a strict profile,
`u′_x(Z) = ū(Z) + ι(Z)`. -/
theorem lemma8_u (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hs : Strict v agents goods) (h : RoleSwap v agents goods base base' x z g H) {Z : G → Bool}
    (hZ : IsBundle goods base' x Z) :
    uCount v agents goods base' x Z = uBar v agents goods base base' x Z + iotaSwap v agents goods base' x z g Z := by
  classical
  obtain ⟨-, -, hF', -⟩ := h.lemma6' hag hgd hM
  obtain ⟨hgg, hbg⟩ := h.g_mem
  have hZg : Z g = false := by
    cases hz : Z g with
    | false => rfl
    | true =>
      rcases (hZ g hgg).2 hz with e | e <;> rw [h.base'_g] at e
      · exact absurd (Option.some.inj e) (Ne.symm h.x_ne_z)
      · cases e
  -- `g ∉ N_x(Z)` iff `v_x(Z) > v_x(g)` (strictness)
  have hgx : 0 < v x g := hM.1.rel g hgg x hbg
  have hneq : v x g ≠ value v x (goods.filter Z) := fun e => by
    have hdisj : ∀ a ∈ [g], a ∉ goods.filter Z := fun a ha hm => by
      rw [List.mem_singleton] at ha; subst ha
      rw [(List.mem_filter.mp hm).2] at hZg; cases hZg
    have := hs x h.hx [g] (goods.filter Z) (List.singleton_sublist.mpr hgg) List.filter_sublist hdisj
      (by simp [value]; exact e)
    simp [value] at this; omega
  have hset : ¬ setNeeds v goods x Z g ↔ v x g < value v x (goods.filter Z) := by
    unfold setNeeds
    constructor
    · intro hn; exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt fun hlt => hn ⟨hgg, hZg, hlt⟩) hneq
    · rintro hlt ⟨-, -, hlt'⟩; omega
  -- pointwise
  have hpt : ∀ w ∈ agents, (decide (Counted v agents goods base' x Z w) = true) ↔
      (decide (Frozen agents goods base (vbNeeds v goods base) w ∧ w ≠ x ∧
        ∀ g' ∈ baseOf goods base w, ¬ setNeeds v goods x Z g' ∧
          ∀ i ∈ agents, i ≠ x → ¬ vbNeeds v goods base' i g') ||
       (decide (w = z) && decide (v x g < value v x (goods.filter Z) ∧
          ∀ i ∈ agents, i ≠ x → i ≠ z → ¬ vbNeeds v goods base' i g))) = true := by
    intro w hw
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
    by_cases hwz : w = z
    · subst hwz
      have hnF : ¬ Frozen agents goods base (vbNeeds v goods base) w := h.hzF
      simp only [hnF, false_and, false_or, true_and]
      unfold Counted
      rw [h.hz']
      simp only [List.mem_singleton, forall_eq]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨hset.mp h1, fun i hi hix _ => h2 i hi hix⟩
      · rintro ⟨h1, h2⟩
        refine ⟨(hF' w hw).mpr (Or.inr rfl), hset.mpr h1, fun i hi hix hN => ?_⟩
        by_cases hiw : i = w
        · subst hiw; exact hN.2.1 h.base'_g
        · exact h2 i hi hix hiw hN
    · simp only [hwz, false_and, or_false]
      unfold Counted
      rw [hF' w hw]
      simp only [hwz, or_false]
      constructor
      · rintro ⟨⟨hF, hwx⟩, hc⟩
        have hwH : w ∉ H := fun hh => (h.hH w hh).2.1 hF
        rw [h.hsame w hw hwx hwz hwH]
        exact ⟨hF, hwx, hc⟩
      · rintro ⟨hF, hwx, hc⟩
        have hwH : w ∉ H := fun hh => (h.hH w hh).2.1 hF
        rw [← h.hsame w hw hwx hwz hwH]
        exact ⟨⟨hF, hwx⟩, hc⟩
  unfold uCount uBar iotaSwap
  rw [List.countP_congr hpt, ← countP_or_disj]
  · congr 1
    split
    · rename_i hc
      have : agents.countP (fun w => decide (w = z) && decide (v x g < value v x (goods.filter Z) ∧
          ∀ i ∈ agents, i ≠ x → i ≠ z → ¬ vbNeeds v goods base' i g)) =
          agents.countP (fun w => decide (some z = some w)) := by
        apply List.countP_congr; intro w _
        simp only [decide_eq_true_eq, Bool.and_eq_true, Option.some.injEq]
        exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, hc⟩⟩
      rw [this, countP_base agents hag (b := some z) (fun k hk => by cases hk; exact h.hz)]
      simp
    · rename_i hc
      exact List.countP_eq_zero.mpr fun w _ hw => hc (by simp at hw; exact hw.2)
  · intro w _ h1 h2
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h1 h2
    exact h.hzF (h2.1 ▸ h1.1)

/-- **Lemma 8, the deficit** (`k4/dl13.md` §2.1): `x` is free in `P′`, and for every bundle `Z` of `x` in `P′` that is
safe in `P′`, `def(P′) ≤ ω + 2 − |Z| − ū(Z) − ι(Z)` (so `Val_{P′}(x) = max (|Z| + ū(Z) + ι(Z))` over these `Z`). -/
theorem lemma8 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) (hs : Strict v agents goods) (h : RoleSwap v agents goods base base' x z g H) :
    ¬ Frozen agents goods base' (vbNeeds v goods base') x ∧
      ∀ Z, IsBundle goods base' x Z → SafeFor v agents goods base' x Z →
        DeficitLE v agents goods base'
          (omegaP v agents goods base + 2 - ((goods.filter Z).length : Int) -
            (uBar v agents goods base base' x Z : Int) - (iotaSwap v agents goods base' x z g Z : Int)) := by
  obtain ⟨hM', -, hF', hω'⟩ := h.lemma6' hag hgd hM
  have hxF : ¬ Frozen agents goods base' (vbNeeds v goods base') x := fun hF => by
    rcases (hF' x h.hx).mp hF with ⟨-, e⟩ | e
    · exact e rfl
    · exact h.x_ne_z e
  refine ⟨hxF, fun Z hZ hS => ?_⟩
  have hb := deficitLE_of_safe hag hM'.1 (by rw [hω']; exact hω) h.hx hxF hZ hS
  rw [hω', h.lemma8_u hag hgd hM hs hZ] at hb
  exact deficitLE_mono hb (by push_cast; omega)

/-- **Lemma 8, the value of `x` as owner** (`k4/dl13.md` §2.1): on a strict profile, `Val_{P′}(x) ≥ k` iff some `Z` with
`A ⊆ Z ⊆ G ∖ ⋃ B′_h` that threatens no agent outside the move holding its base, not `z` holding `{g}` and no helper
holding its new base, has `|Z| + ū(Z) + ι(Z) ≥ k`; that is, `Val_{P′}(x) = max (|Z| + ū(Z) + ι(Z))` over those `Z`. -/
theorem lemma8_val (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hs : Strict v agents goods) (h : RoleSwap v agents goods base base' x z g H) (k : Nat) :
    (∃ Z, IsBundle goods base' x Z ∧ SafeFor v agents goods base' x Z ∧
        k ≤ (goods.filter Z).length + uCount v agents goods base' x Z) ↔
      (∃ Z : G → Bool, ((∀ g' ∈ goods, base' g' = some x → Z g' = true) ∧
          (∀ g' ∈ goods, Z g' = true → SwapPool base z H g' ∧ ∀ w ∈ H, base' g' ≠ some w)) ∧
        ((∀ w ∈ agents, w ≠ x → w ≠ z → w ∉ H → ∀ r ∈ goods.filter Z,
          value v w ((goods.filter Z).erase r) ≤ value v w (baseOf goods base w)) ∧
         (∀ r ∈ goods.filter Z, value v z ((goods.filter Z).erase r) ≤ v z g) ∧
         (∀ w ∈ H, ∀ r ∈ goods.filter Z,
          value v w ((goods.filter Z).erase r) ≤ value v w (baseOf goods base' w))) ∧
        k ≤ (goods.filter Z).length + uBar v agents goods base base' x Z + iotaSwap v agents goods base' x z g Z) := by
  constructor
  · rintro ⟨Z, hZ, hS, hk⟩
    refine ⟨Z, (h.lemma8_bundle hM.1 Z).mp hZ, (h.lemma8_safe Z).mp hS, ?_⟩
    rw [h.lemma8_u hag hgd hM hs hZ] at hk; omega
  · rintro ⟨Z, hZ, hS, hk⟩
    have hZ' := (h.lemma8_bundle hM.1 Z).mpr hZ
    refine ⟨Z, hZ', (h.lemma8_safe Z).mpr hS, ?_⟩
    rw [h.lemma8_u hag hgd hM hs hZ']; omega

omit [DecidableEq A] in
/-- A good `x` values more than the rest: strict balance gives `v_x(g) < v_x(R_x ∖ {g})`, so `v_x(g) < v_x(Z)` for every
`Z` containing `R_x ∖ {g}`. -/
theorem lt_value_of_lower (hgd : goods.Nodup) {x : A} {g : G} (hg : g ∈ goods) (hbal : 2 * v x g < value v x goods)
    {Z : G → Bool} (hL : ∀ r ∈ goods, 0 < v x r → r ≠ g → Z r = true) : v x g < value v x (goods.filter Z) := by
  have h1 := value_erase (v := v) (i := x) hg
  have h2 := value_le_of_rel_sub (v := v) (i := x) (S := goods.erase g) (T := goods.filter Z) (hgd.erase g)
    (hgd.sublist List.filter_sublist) fun r hr hpos => by
      have hrg : r ≠ g := fun e => by subst e; exact (List.Nodup.not_mem_erase hgd) hr
      exact List.mem_filter.mpr ⟨List.mem_of_mem_erase hr, hL r (List.mem_of_mem_erase hr) hpos hrg⟩
  omega

/-- **Corollary 8.2 (the Lemma 7 swap)** (`k4/dl13.md` §2.1). In a role swap where no listed agent other than `z`
needs `g` in `P` and no helper needs `g` in `P′` (`g ∉ N_h(B′_h)`), with `x` strictly balanced (`2 v_x(g) < v_x(M)`),
every bundle `Z` of `x` in `P′` that is safe in `P′` and contains the lower goods `L_x = R_x ∖ {g}` has
`def(P′) ≤ ω + 1 − |Z| − ū(Z)`; so `def(P′) < def(P)` as soon as `|Z| + 1 + ū(Z) > Val*(P)` (in particular when
`|Z| + 1 > Val*(P)`). (The text's further hypotheses, `x` big-top, `L_x ⊆ G`, `A ⊆ L_x` and `B′_h ∩ L_x = ∅`, say when such
a `Z` exists; the bound does not use them.) -/
theorem cor8_2 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) (hs : Strict v agents goods) (h : RoleSwap v agents goods base base' x z g H)
    (hbal : 2 * v x g < value v x goods)
    (honly : ∀ i ∈ agents, i ≠ z → ¬ vbNeeds v goods base i g)
    (hhelp : ∀ k ∈ H, ¬ vbNeeds v goods base' k g)
    {Z : G → Bool} (hZ : IsBundle goods base' x Z) (hS : SafeFor v agents goods base' x Z)
    (hL : ∀ r ∈ goods, 0 < v x r → r ≠ g → Z r = true) :
    DeficitLE v agents goods base'
        (omegaP v agents goods base + 1 - ((goods.filter Z).length : Int) - (uBar v agents goods base base' x Z : Int)) ∧
      ((∀ o' ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o' → ∀ Z', IsBundle goods base o' Z' →
        SafeFor v agents goods base o' Z' →
          ((goods.filter Z').length : Int) + (uCount v agents goods base o' Z' : Int) <
            ((goods.filter Z).length : Int) + 1 + (uBar v agents goods base base' x Z : Int)) →
        DeficitLT v agents goods base' base) := by
  have hc : v x g < value v x (goods.filter Z) ∧ ∀ i ∈ agents, i ≠ x → i ≠ z → ¬ vbNeeds v goods base' i g := by
    refine ⟨lt_value_of_lower hgd h.g_mem.1 hbal hL, fun i hi hix hiz hN => ?_⟩
    by_cases hiH : i ∈ H
    · exact hhelp i hiH hN
    · exact honly i hi hiz ((vbNeeds_congr (h.hsame i hi hix hiz hiH).symm g).mp hN)
  have hι : iotaSwap v agents goods base' x z g Z = 1 := by
    unfold iotaSwap
    split
    · rfl
    · rename_i hn; exact absurd hc hn
  have hb := (h.lemma8 hag hgd hM hω hs).2 Z hZ hS
  rw [hι] at hb
  have hb' : DeficitLE v agents goods base'
      (omegaP v agents goods base + 1 - ((goods.filter Z).length : Int) - (uBar v agents goods base base' x Z : Int)) :=
    deficitLE_mono hb (by push_cast; omega)
  refine ⟨hb', fun hval => ?_⟩
  have hn := not_deficitLE_of_val_lt hag hM.1 hω hval
  exact ⟨_, hb', fun h' => hn (deficitLE_mono h' (by omega))⟩

end RoleSwap

/-! ## `k4/dl13.md` §2.1, Lemma 10 (the θ-dichotomy) -/

omit [DecidableEq A] in
/-- A duplicate-free list inside a duplicate-free list is at most as long. -/
theorem length_le_of_sub {S T : List G} (hS : S.Nodup) (hT : T.Nodup) (h : ∀ g ∈ S, g ∈ T) :
    S.length ≤ T.length := by
  have hp : S.Perm (T.filter (fun g => g ∈ S)) :=
    (List.perm_ext_iff_of_nodup hS (hT.sublist List.filter_sublist)).mpr fun g => by
      simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hg => ⟨h g hg, hg⟩, fun hg => hg.2⟩
  rw [hp.length_eq]; exact List.length_filter_le _ _

omit [DecidableEq A] in
/-- The goods of a duplicate-free list `L ⊆ goods`, as a test on `goods`, list `L` up to order. -/
theorem filter_mem_perm (hgd : goods.Nodup) {L : List G} (hL : L.Nodup) (hLg : ∀ g ∈ L, g ∈ goods) :
    (goods.filter (fun g => decide (g ∈ L))).Perm L :=
  (List.perm_ext_iff_of_nodup (hgd.sublist List.filter_sublist) hL).mpr fun g => by
    simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => h.2, fun h => ⟨hLg g h, h⟩⟩

omit [DecidableEq G] in
/-- **Lemma 10, (θ-a)** (`k4/dl13.md` §2.1). Let `P` be min-frozen, `o` free with `g ∈ N_o`, and `Q` a set of at most
two goods of `Z ∩ R_o` (`Z ⊆ W_o`) with `v_o(Q) > v_o(g)`. Then `Q ≠ B_o` is a base admissible for `o` inside `W_o`
(`N_o(Q) ⊆ 𝒩`) that does not need `g`, and some listed agent other than `o` needs `g`. -/
theorem lemma10_a (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base) {o : A} {g : G}
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (hog : vbNeeds v goods base o g)
    {Z : G → Bool} (hZ : ∀ r ∈ goods, Z r = true → base r = some o ∨ base r = none) {Q : G → Bool}
    (hQ : ∀ r ∈ goods, Q r = true → Z r = true ∧ 0 < v o r) (hQ2 : (goods.filter Q).length ≤ 2)
    (hQv : v o g < value v o (goods.filter Q)) :
    goods.filter Q ≠ baseOf goods base o ∧ (∀ r, setNeeds v goods o Q r → NA agents (vbNeeds v goods base) r) ∧
      ¬ setNeeds v goods o Q g ∧ ∃ i ∈ agents, i ≠ o ∧ vbNeeds v goods base i g := by
  have hBo := hog.2.2
  have hadm : ∀ r, setNeeds v goods o Q r → NA agents (vbNeeds v goods base) r := by
    rintro r ⟨hr, -, hlt⟩
    refine ⟨o, ho, hr, fun hb => ?_, by omega⟩
    have := le_value_of_mem v o (mem_baseOf.mpr ⟨hr, hb⟩ : r ∈ baseOf goods base o)
    omega
  have hng : ¬ setNeeds v goods o Q g := fun ⟨_, _, hlt⟩ => by omega
  obtain ⟨-, hNA, -, -, hsame, -⟩ := lemma1c_rebase hag hgd hM ho hoF
    (fun r hr hq => ⟨hZ r hr (hQ r hr hq).1, (hQ r hr hq).2⟩) hQ2 hadm
  obtain ⟨i, hi, hN⟩ := (hNA g).mpr ⟨o, ho, hog⟩
  have hio : i ≠ o := fun e => hng ((vbNeeds_rebase_self g).mp (e ▸ hN))
  refine ⟨fun e => by rw [e] at hQv; omega, hadm, hng, i, hi, hio,
    (vbNeeds_congr (hsame i hi hio).symm g).mp hN⟩

/-- **Lemma 10 (the θ-dichotomy)** (`k4/dl13.md` §2.1). Let `o` be free with `g ∈ N_o`, `|R_o| ≤ 4`, on a strict
profile, and `Z ⊆ W_o` with `θ_o(Z) > v_o(g)`. Then exactly one of:
- **(θ-a)** some set `Q` of at most two goods of `Z ∩ R_o` has `v_o(Q) > v_o(g)` (then `lemma10_a`);
- **(θ-b)** `|R_o| = 4`, `g` is `o`'s top, `o` is big-top on `g` (every pair of its other goods is worth less than `g`,
  i.e. `v_o(g) > v_o(b_o) + v_o(c_o)`), and `o`'s three lower goods lie in `Z`. -/
theorem lemma10 (hgd : goods.Nodup) (hP : InP v agents goods base) (hs : Strict v agents goods) {o : A} {g : G}
    (ho : o ∈ agents) (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (hog : vbNeeds v goods base o g)
    (hR4 : (relevant v o goods).length ≤ 4)
    {Z : G → Bool} (hZ : ∀ r ∈ goods, Z r = true → base r = some o ∨ base r = none)
    (hθ : ∃ h ∈ goods.filter Z, v o g < value v o ((goods.filter Z).erase h)) :
    let θa := ∃ Q : G → Bool, (∀ r ∈ goods, Q r = true → Z r = true ∧ 0 < v o r) ∧
      (goods.filter Q).length ≤ 2 ∧ v o g < value v o (goods.filter Q)
    let θb := (relevant v o goods).length = 4 ∧ (∀ r ∈ goods, 0 < v o r → r ≠ g → v o r < v o g) ∧
      (∀ r ∈ goods, ∀ s ∈ goods, 0 < v o r → 0 < v o s → r ≠ s → r ≠ g → s ≠ g → v o r + v o s < v o g) ∧
      (∀ r ∈ goods, 0 < v o r → r ≠ g → Z r = true)
    (θa ∨ θb) ∧ ¬ (θa ∧ θb) := by
  intro θa θb
  have hgg : g ∈ goods := hog.1
  have hgpos : 0 < v o g := by have := hog.2.2; omega
  -- `g ∉ Z`: `g` is needed, and `Z ⊆ W_o` misses `𝒩`
  have hgN : NA agents (vbNeeds v goods base) g := ⟨o, ho, hog⟩
  have hZg : Z g = false := by
    cases hz : Z g with
    | false => rfl
    | true =>
      rcases hZ g hgg hz with hb | hb
      · exact absurd hgN (not_NA_of_mem_free hP hoF (mem_baseOf.mpr ⟨hgg, hb⟩))
      · exact absurd hgN (not_NA_of_junk hP hgg hb)
  have hRnd : (relevant v o goods).Nodup := hgd.sublist List.filter_sublist
  have hgR : g ∈ relevant v o goods := mem_relevant.mpr ⟨hgg, hgpos⟩
  -- small sets of `Z ∩ R_o` as tests
  have hsingle : ∀ r ∈ goods, 0 < v o r → r ≠ g → Z r = true → ¬ θa → v o r < v o g := by
    intro r hr hpos hrg hz hna
    have hp := filter_mem_perm hgd (L := [r]) (by simp) (by simpa using hr)
    have hle : v o r ≤ v o g := Nat.le_of_not_lt fun hlt => hna ⟨fun t => decide (t ∈ [r]), fun t _ ht => by
      simp at ht; subst ht; exact ⟨hz, hpos⟩, by rw [hp.length_eq]; simp, by rw [value_perm hp]; simpa [value] using hlt⟩
    refine Nat.lt_of_le_of_ne hle fun e => ?_
    have := hs o ho [r] [g] (List.singleton_sublist.mpr hr) (List.singleton_sublist.mpr hgg)
      (by simpa using hrg) (by simp [value, e])
    simp [value] at this; omega
  have hpair : ∀ r ∈ goods, ∀ s ∈ goods, 0 < v o r → 0 < v o s → r ≠ s → r ≠ g → s ≠ g → Z r = true →
      Z s = true → ¬ θa → v o r + v o s < v o g := by
    intro r hr s hs' hpr hps hrs hrg hsg hzr hzs hna
    have hp := filter_mem_perm hgd (L := [r, s]) (by simpa using hrs) (by simp [hr, hs'])
    have hle : v o r + v o s ≤ v o g := Nat.le_of_not_lt fun hlt => hna ⟨fun t => decide (t ∈ [r, s]), fun t _ ht => by
      simp at ht; rcases ht with e | e <;> subst e
      · exact ⟨hzr, hpr⟩
      · exact ⟨hzs, hps⟩, by rw [hp.length_eq]; simp, by rw [value_perm hp]; simpa [value] using hlt⟩
    refine Nat.lt_of_le_of_ne hle fun e => ?_
    have hv := value_perm (v := v) (i := o) hp
    have := hs o ho (goods.filter (fun t => decide (t ∈ [r, s]))) [g] List.filter_sublist
      (List.singleton_sublist.mpr hgg) (fun t ht => by
        have := (List.mem_filter.mp ht).2; simp at this; simp; rcases this with e | e <;> subst e
        · exact hrg
        · exact hsg) (by rw [hv]; simp [value]; omega)
    rw [hv] at this
    simp [value] at this; omega
  refine ⟨?_, ?_⟩
  · by_cases ha : θa
    · exact Or.inl ha
    refine Or.inr ?_
    obtain ⟨h, hh, hlt⟩ := hθ
    -- `Q′`: the relevant goods of `Z ∖ h`
    let S := (goods.filter Z).erase h
    let Q' := S.filter (fun r => 0 < v o r)
    have hSnd : S.Nodup := (hgd.sublist List.filter_sublist).erase h
    have hQnd : Q'.Nodup := hSnd.sublist List.filter_sublist
    have hQmem : ∀ r ∈ Q', r ∈ goods ∧ Z r = true ∧ 0 < v o r ∧ r ≠ g := by
      intro r hr
      obtain ⟨hrS, hpos⟩ := List.mem_filter.mp hr
      obtain ⟨hrg, hz⟩ := List.mem_filter.mp (List.mem_of_mem_erase hrS)
      exact ⟨hrg, hz, by simpa using hpos, fun e => by rw [e, hZg] at hz; cases hz⟩
    have hQv : v o g < value v o Q' := by rw [← value_filter_pos]; exact hlt
    have h3 : 3 ≤ Q'.length := Nat.le_of_not_lt fun hlt2 => ha ⟨fun t => decide (t ∈ Q'), fun t _ ht => by
      have := hQmem t (by simpa using ht); exact ⟨this.2.1, this.2.2.1⟩,
      by rw [(filter_mem_perm hgd hQnd fun r hr => (hQmem r hr).1).length_eq]; omega,
      by rw [value_perm (filter_mem_perm hgd hQnd fun r hr => (hQmem r hr).1)]; exact hQv⟩
    have hgQ : (g :: Q').Nodup := List.nodup_cons.mpr ⟨fun hm => (hQmem g hm).2.2.2 rfl, hQnd⟩
    have hle4 := length_le_of_sub hgQ hRnd fun r hr => by
      rcases List.mem_cons.mp hr with e | e
      · subst e; exact hgR
      · exact mem_relevant.mpr ⟨(hQmem r e).1, (hQmem r e).2.2.1⟩
    simp only [List.length_cons] at hle4
    -- the relevant goods other than `g` are exactly `Q′`
    have hEnd : ((relevant v o goods).erase g).Nodup := hRnd.erase g
    have hElen : ((relevant v o goods).erase g).length = (relevant v o goods).length - 1 :=
      List.length_erase_of_mem hgR
    have hperm := perm_of_subset_length hQnd hEnd (fun r hr => by
      have := hQmem r hr
      exact (List.mem_erase_of_ne this.2.2.2).mpr (mem_relevant.mpr ⟨this.1, this.2.2.1⟩)) (by omega)
    have hlow : ∀ r ∈ goods, 0 < v o r → r ≠ g → r ∈ Q' := fun r hr hpos hrg =>
      hperm.symm.subset ((List.mem_erase_of_ne hrg).mpr (mem_relevant.mpr ⟨hr, hpos⟩))
    refine ⟨by omega, fun r hr hpos hrg => hsingle r hr hpos hrg (hQmem r (hlow r hr hpos hrg)).2.1 ha,
      fun r hr s hs' hpr hps hrs hrg hsg => hpair r hr s hs' hpr hps hrs hrg hsg (hQmem r (hlow r hr hpr hrg)).2.1
        (hQmem s (hlow s hs' hps hsg)).2.1 ha, fun r hr hpos hrg => (hQmem r (hlow r hr hpos hrg)).2.1⟩
  · rintro ⟨⟨Q, hQ, hQ2, hQv⟩, -, htop, hbt, -⟩
    have hnd : (goods.filter Q).Nodup := hgd.sublist List.filter_sublist
    have hmem : ∀ r ∈ goods.filter Q, r ∈ goods ∧ 0 < v o r ∧ r ≠ g := by
      intro r hr
      obtain ⟨hrg, hq⟩ := List.mem_filter.mp hr
      have := hQ r hrg hq
      exact ⟨hrg, this.2, fun e => by rw [e, hZg] at this; exact Bool.false_ne_true this.1⟩
    match hL : goods.filter Q, hQ2, hnd, hmem with
    | [], _, _, _ => rw [hL] at hQv; simp [value] at hQv
    | [r], _, _, hm =>
      rw [hL] at hQv
      have := hm r (by simp)
      have := htop r this.1 this.2.1 this.2.2
      simp [value] at hQv; omega
    | [r, t], _, hnd', hm =>
      rw [hL] at hQv
      have h1 := hm r (by simp)
      have h2 := hm t (by simp)
      have hrt : r ≠ t := by simpa using hnd'
      have := hbt r h1.1 t h2.1 h1.2.1 h2.2.1 hrt h1.2.2 h2.2.2
      simp [value] at hQv; omega
    | _ :: _ :: _ :: _, h2, _, _ => simp at h2

/-! ## `k4/dl13.md` §2.1, Lemma 9 (the owner swap from a needer) and Corollaries 9.1, 9.2 -/

/-- **The role swap without helper, constructed**: `z` takes `{g}`, `x` takes `A`, the goods of `B_z` not in `A` become
junk, every other good keeps its owner. -/
def swapBase (base : G → Option A) (x z : A) (g : G) (Ax : G → Bool) : G → Option A :=
  fun g' => if g' = g then some z else if Ax g' then some x else if base g' = some z then none else base g'

section swapBase
variable {x z : A} {g g' : G} {Ax : G → Bool}

theorem swapBase_g : swapBase base x z g Ax g = some z := by simp [swapBase]

theorem swapBase_A (h1 : g' ≠ g) (h2 : Ax g' = true) : swapBase base x z g Ax g' = some x := by
  simp [swapBase, h1, h2]

theorem swapBase_Bz (h1 : g' ≠ g) (h2 : Ax g' = false) (h3 : base g' = some z) :
    swapBase base x z g Ax g' = none := by
  simp [swapBase, h1, h2, h3]

theorem swapBase_other (h1 : g' ≠ g) (h2 : Ax g' = false) (h3 : base g' ≠ some z) :
    swapBase base x z g Ax g' = base g' := by
  simp [swapBase, h1, h2, h3]

end swapBase

/-- **The swap is a role swap** (Lemma 6's hypotheses): if `x` is frozen with `B_x = {g}`, `z` is free and needs `g`,
and `A ⊆ (J ∪ B_z) ∩ R_x` has at most two goods with `N_x(A) ⊆ 𝒩`, then `swapBase base x z g A` is a `RoleSwap` without
helper in which `x` holds `A`. -/
theorem roleSwap_swapBase (hgd : goods.Nodup) (hP : InP v agents goods base) {x z : A} {g : G} (hx : x ∈ agents)
    (hxg : baseOf goods base x = [g]) (hgN : NA agents (vbNeeds v goods base) g) (hz : z ∈ agents)
    (hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z) (hzN : vbNeeds v goods base z g) {Ax : G → Bool}
    (hA : ∀ r ∈ goods, Ax r = true → (base r = none ∨ base r = some z) ∧ 0 < v x r)
    (hA2 : (goods.filter Ax).length ≤ 2) (hAN : ∀ r, setNeeds v goods x Ax r → NA agents (vbNeeds v goods base) r) :
    RoleSwap v agents goods base (swapBase base x z g Ax) x z g [] ∧
      baseOf goods (swapBase base x z g Ax) x = goods.filter Ax := by
  have hxF : Frozen agents goods base (vbNeeds v goods base) x := ⟨g, hxg, hgN⟩
  have hxz : x ≠ z := fun e => hzF (e ▸ hxF)
  obtain ⟨hgg, hbg⟩ : g ∈ goods ∧ base g = some x := mem_baseOf.mp (by rw [hxg]; exact List.mem_singleton_self g)
  have hBx : ∀ g' ∈ goods, base g' = some x → g' = g := fun g' hg' hb => by
    have : g' ∈ baseOf goods base x := mem_baseOf.mpr ⟨hg', hb⟩
    rw [hxg, List.mem_singleton] at this; exact this
  have hApool : ∀ g' ∈ goods, Ax g' = true → ∀ i, base g' = some i → i = z := fun g' hg' h i hb => by
    rcases (hA g' hg' h).1 with e | e <;> rw [hb] at e
    · cases e
    · exact Option.some.inj e
  have hAg : Ax g = false := by
    cases h : Ax g with
    | false => rfl
    | true => exact absurd (hApool g hgg h x hbg) hxz
  -- `x` holds exactly `A`, `z` exactly `{g}`, the others their bases
  have hxiff : ∀ g' ∈ goods, swapBase base x z g Ax g' = some x ↔ Ax g' = true := by
    intro g' hg'
    by_cases h1 : g' = g
    · subst h1; rw [swapBase_g, hAg]; simp [Ne.symm hxz]
    cases h2 : Ax g'
    · by_cases h3 : base g' = some z
      · rw [swapBase_Bz h1 h2 h3]; simp
      · rw [swapBase_other h1 h2 h3]; simp only [Bool.false_eq_true, iff_false]
        exact fun hb => h1 (hBx g' hg' hb)
    · rw [swapBase_A h1 h2]; simp
  have hziff : ∀ g' ∈ goods, swapBase base x z g Ax g' = some z ↔ g' = g := by
    intro g' hg'
    by_cases h1 : g' = g
    · subst h1; simp [swapBase_g]
    cases h2 : Ax g'
    · by_cases h3 : base g' = some z
      · rw [swapBase_Bz h1 h2 h3]; simp [h1]
      · rw [swapBase_other h1 h2 h3]; simp [h1, h3]
    · rw [swapBase_A h1 h2]; simp [h1, hxz]
  have hoiff : ∀ i, i ≠ x → i ≠ z → ∀ g' ∈ goods, swapBase base x z g Ax g' = some i ↔ base g' = some i := by
    intro i hix hiz g' hg'
    by_cases h1 : g' = g
    · subst h1; rw [swapBase_g, hbg]
      exact ⟨fun e => absurd (Option.some.inj e).symm hiz, fun e => absurd (Option.some.inj e).symm hix⟩
    cases h2 : Ax g'
    · by_cases h3 : base g' = some z
      · rw [swapBase_Bz h1 h2 h3, h3]
        exact ⟨(fun e => by cases e), fun e => absurd (Option.some.inj e).symm hiz⟩
      · rw [swapBase_other h1 h2 h3]
    · rw [swapBase_A h1 h2]
      exact ⟨fun e => absurd (Option.some.inj e).symm hix, fun e => absurd (hApool g' hg' h2 i e) hiz⟩
  have hx' : baseOf goods (swapBase base x z g Ax) x = goods.filter Ax := by
    unfold baseOf
    apply List.filter_congr
    intro g' hg'
    by_cases h : Ax g' = true
    · simp [h, (hxiff g' hg').mpr h]
    · have : ¬ swapBase base x z g Ax g' = some x := fun e => h ((hxiff g' hg').mp e)
      simp [h, this]
  have hz' : baseOf goods (swapBase base x z g Ax) z = [g] := baseOf_single hgd hgg hziff
  refine ⟨⟨hx, hxg, hgN, hz, hzF, by have := hzN.2.2; omega, by simp,
    fun i _ hix hiz _ => (baseOf_congr (hoiff i hix hiz)).symm, fun g' hg' i hb => ?_, hz',
    fun i hi g' hg' hb => ?_, fun i hi => ?_, fun i hi => ?_⟩, hx'⟩
  · by_cases hix : i = x
    · rw [hix]; exact hx
    by_cases hiz : i = z
    · rw [hiz]; exact hz
    exact hP.mem g' hg' i ((hoiff i hix hiz g' hg').mp hb)
  · rcases hi with e | e
    · subst e
      obtain ⟨h1, h2⟩ := hA g' hg' ((hxiff g' hg').mp hb)
      refine ⟨?_, h2⟩
      rcases h1 with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · simp at e
  · rcases hi with e | e
    · subst e; rw [hx']; exact hA2
    · simp at e
  · rcases hi with e | e | e
    · subst e
      rintro g' ⟨hg', hne, hlt⟩
      refine hAN g' ⟨hg', ?_, by rw [hx'] at hlt; exact hlt⟩
      cases h : Ax g' with
      | false => rfl
      | true => exact absurd ((hxiff g' hg').mpr h) hne
    · subst e; exact needs_single_sub hz hzN hz'
    · simp at e

omit [DecidableEq A] [DecidableEq G] in
/-- A nonempty list has an element of least value. -/
theorem exists_min_value (f : G → Nat) : ∀ {L : List G}, L ≠ [] → ∃ m ∈ L, ∀ q ∈ L, f m ≤ f q
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun q hq => by simp at hq; subst hq; exact Nat.le_refl _⟩
  | a :: b :: t, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_value f (L := b :: t) (by simp)
    by_cases h : f a ≤ f m
    · exact ⟨a, by simp, fun q hq => by
        rcases List.mem_cons.mp hq with e | e
        · subst e; exact Nat.le_refl _
        · exact Nat.le_trans h (hmin q e)⟩
    · exact ⟨m, List.mem_cons_of_mem a hm, fun q hq => by
        rcases List.mem_cons.mp hq with e | e
        · rw [e]; omega
        · exact hmin q e⟩

/-- **Lemma 9, an admissible base for `x` in `Z`** (`k4/dl13.md` §2.1). Let `x` be frozen with `B_x = {g}`, `|R_x| ≤ 4`,
and `Z` a set missing `𝒩` that threatens `x` holding `{g}`. Then `Z` contains a set `A` admissible for `x`: `A ⊆ Z ∩ R_x`,
at most two goods, `N_x(A) ⊆ 𝒩`. -/
theorem lemma9_admissible (hgd : goods.Nodup) (hP : InP v agents goods base) {x : A} {g : G} (hx : x ∈ agents)
    (hxg : baseOf goods base x = [g]) (hgN : NA agents (vbNeeds v goods base) g)
    (hR4 : (relevant v x goods).length ≤ 4) {Z : G → Bool}
    (hZN : ∀ r ∈ goods, Z r = true → ¬ NA agents (vbNeeds v goods base) r)
    (hi : ∃ h ∈ goods.filter Z, v x g < value v x ((goods.filter Z).erase h)) :
    ∃ Ax : G → Bool, (∀ r ∈ goods, Ax r = true → Z r = true ∧ 0 < v x r) ∧ (goods.filter Ax).length ≤ 2 ∧
      ∀ r, setNeeds v goods x Ax r → NA agents (vbNeeds v goods base) r := by
  obtain ⟨hgg, hbg⟩ : g ∈ goods ∧ base g = some x := mem_baseOf.mp (by rw [hxg]; exact List.mem_singleton_self g)
  have hgx : 0 < v x g := hP.rel g hgg x hbg
  -- a good of `R_x` outside `𝒩` is worth at most `v_x(g)`
  have hlow : ∀ r ∈ goods, v x g < v x r → NA agents (vbNeeds v goods base) r := by
    intro r hr hlt
    refine ⟨x, hx, hr, fun hb => ?_, by rw [hxg]; simpa [value] using hlt⟩
    have : r ∈ baseOf goods base x := mem_baseOf.mpr ⟨hr, hb⟩
    rw [hxg, List.mem_singleton] at this; subst this; omega
  have hZg : Z g = false := by
    cases h : Z g with
    | false => rfl
    | true => exact absurd hgN (hZN g hgg h)
  obtain ⟨h, _, hlt⟩ := hi
  let S := (goods.filter Z).erase h
  let Q' := S.filter (fun r => 0 < v x r)
  have hQnd : Q'.Nodup := ((hgd.sublist List.filter_sublist).erase h).sublist List.filter_sublist
  have hQmem : ∀ r ∈ Q', r ∈ goods ∧ Z r = true ∧ 0 < v x r ∧ r ≠ g := by
    intro r hr
    obtain ⟨hrS, hpos⟩ := List.mem_filter.mp hr
    obtain ⟨hrg, hz⟩ := List.mem_filter.mp (List.mem_of_mem_erase hrS)
    exact ⟨hrg, hz, by simpa using hpos, fun e => by rw [e, hZg] at hz; cases hz⟩
  have hQv : v x g < value v x Q' := by rw [← value_filter_pos]; exact hlt
  have hp := filter_mem_perm hgd hQnd fun r hr => (hQmem r hr).1
  by_cases h2 : Q'.length ≤ 2
  · -- `A := Q′`
    refine ⟨fun t => decide (t ∈ Q'), fun r _ hr => ?_, by rw [hp.length_eq]; exact h2, fun r hN => ?_⟩
    · have := hQmem r (by simpa using hr); exact ⟨this.2.1, this.2.2.1⟩
    · obtain ⟨hr, -, hlt'⟩ := hN
      rw [value_perm hp] at hlt'
      exact hlow r hr (by omega)
  · -- `|Q′| = 3`: drop its least good
    have hRnd : (relevant v x goods).Nodup := hgd.sublist List.filter_sublist
    have hgR : g ∈ relevant v x goods := mem_relevant.mpr ⟨hgg, hgx⟩
    have hgQ : (g :: Q').Nodup := List.nodup_cons.mpr ⟨fun hm => (hQmem g hm).2.2.2 rfl, hQnd⟩
    have hle4 := length_le_of_sub hgQ hRnd fun r hr => by
      rcases List.mem_cons.mp hr with e | e
      · subst e; exact hgR
      · exact mem_relevant.mpr ⟨(hQmem r e).1, (hQmem r e).2.2.1⟩
    simp only [List.length_cons] at hle4
    have hperm := perm_of_subset_length hQnd (hRnd.erase g) (fun r hr => by
      have := hQmem r hr
      exact (List.mem_erase_of_ne this.2.2.2).mpr (mem_relevant.mpr ⟨this.1, this.2.2.1⟩))
      (by rw [List.length_erase_of_mem hgR]; omega)
    have hne : Q' ≠ [] := fun e => by rw [e] at h2; simp at h2
    obtain ⟨m, hm, hmin⟩ := exists_min_value (v x) hne
    have hAnd : (Q'.erase m).Nodup := hQnd.erase m
    have hpA := filter_mem_perm hgd hAnd fun r hr => (hQmem r (List.mem_of_mem_erase hr)).1
    have hAlen : (Q'.erase m).length = Q'.length - 1 := List.length_erase_of_mem hm
    refine ⟨fun t => decide (t ∈ Q'.erase m), fun r _ hr => ?_, by rw [hpA.length_eq]; omega, fun r hN => ?_⟩
    · have := hQmem r (List.mem_of_mem_erase (by simpa using hr)); exact ⟨this.2.1, this.2.2.1⟩
    · obtain ⟨hr, hrA, hlt'⟩ := hN
      rw [value_perm hpA] at hlt'
      by_cases hrg : r = g
      · subst hrg; exact hgN
      exfalso
      have hrpos : 0 < v x r := by omega
      have hrQ : r ∈ Q' := hperm.symm.subset ((List.mem_erase_of_ne hrg).mpr (mem_relevant.mpr ⟨hr, hrpos⟩))
      have hrm : r = m := by
        refine Classical.byContradiction fun hrm => ?_
        have : r ∈ Q'.erase m := (List.mem_erase_of_ne hrm).mpr hrQ
        simp [this] at hrA
      subst hrm
      -- `v_x(m) ≤ v_x(q) ≤ v_x(A)` for any `q ∈ A`
      obtain ⟨q, hq⟩ : ∃ q, q ∈ Q'.erase r := List.exists_mem_of_ne_nil _ (fun e => by
        rw [e] at hAlen; simp at hAlen; omega)
      have := hmin q (List.mem_of_mem_erase hq)
      have := le_value_of_mem v x hq
      omega

open Classical in
/-- **`e`** (Lemma 9): the listed agents counted in `u_o(X)` that are `x` or whose good lies in `N_o({g})` (`o`'s needs
in `P′`, where it holds `{g}`). -/
noncomputable def eSwap (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) (o x : A)
    (X : G → Bool) : Nat :=
  agents.countP (fun w => decide (Counted v agents goods base o X w ∧
    (w = x ∨ ∃ g' ∈ baseOf goods base w, vbNeeds v goods base' o g')))

open Classical in
/-- **`ι`** (Lemma 9): `1` if no listed agent outside `{o, x}` needs `g` in `P`, `0` otherwise. -/
noncomputable def iotaNeed (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o x : A)
    (g : G) : Nat :=
  if ∀ i ∈ agents, i ≠ o → i ≠ x → ¬ vbNeeds v goods base i g then 1 else 0

namespace RoleSwap

variable {x o : A} {g : G}

/-- **Lemma 9 (the owner swap from a needer)** (`k4/dl13.md` §2.1). Let the needer `o` of `g` take `{g}` and `x` take a
base `A ⊆ Z` (a `RoleSwap` without helper, `z = o`), where `Z ⊆ W_o` satisfies
(i) `Z` threatens `x` holding `{g}`; (ii) `Z` threatens no listed `w ∉ {o, x}` holding `B_w`; (iii) `θ_o(Z) ≤ v_o(g)`.
Then, on a strict profile with `ω ≥ 1`, for every set `X`, `def(P′) ≤ ω + 2 − |Z| − (u_o(X) − e) − ι`. -/
theorem lemma9 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) (hs : Strict v agents goods) (h : RoleSwap v agents goods base base' x o g [])
    {X Z : G → Bool} (hAZ : ∀ r ∈ goods, base' r = some x → Z r = true)
    (hZW : ∀ r ∈ goods, Z r = true → base r = some o ∨ base r = none)
    (hi : ∃ k ∈ goods.filter Z, v x g < value v x ((goods.filter Z).erase k))
    (hii : ∀ w ∈ agents, w ≠ o → w ≠ x → ∀ k ∈ goods.filter Z,
      value v w ((goods.filter Z).erase k) ≤ value v w (baseOf goods base w))
    (hiii : ∀ k ∈ goods.filter Z, value v o ((goods.filter Z).erase k) ≤ v o g) :
    DeficitLE v agents goods base'
      (omegaP v agents goods base + 2 - ((goods.filter Z).length : Int) -
        ((uCount v agents goods base o X : Int) - (eSwap v agents goods base base' o x X : Int)) -
        (iotaNeed v agents goods base o x g : Int)) := by
  classical
  have hxo := h.x_ne_z
  have hZ : IsBundle goods base' x Z := (h.lemma8_bundle hM.1 Z).mpr ⟨hAZ, fun r hr hz => ⟨by
    rcases hZW r hr hz with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inl e, by simp⟩⟩
  have hS : SafeFor v agents goods base' x Z := (h.lemma8_safe Z).mpr
    ⟨fun w hw hwx hwo _ => hii w hw hwo hwx, hiii, by simp⟩
  have hb := (h.lemma8 hag hgd hM hω hs).2 Z hZ hS
  have hvZ : v x g < value v x (goods.filter Z) := by
    obtain ⟨k, _, hlt⟩ := hi
    exact Nat.lt_of_lt_of_le hlt (value_sublist v x (List.erase_sublist))
  -- `ι ≤ ι(Z)`
  have hι : iotaNeed v agents goods base o x g ≤ iotaSwap v agents goods base' x o g Z := by
    unfold iotaNeed iotaSwap
    split
    · rename_i hn
      have : v x g < value v x (goods.filter Z) ∧ ∀ i ∈ agents, i ≠ x → i ≠ o → ¬ vbNeeds v goods base' i g :=
        ⟨hvZ, fun i hi hix hio hN => hn i hi hio hix
          ((vbNeeds_congr (h.hsame i hi hix hio (by simp)).symm g).mp hN)⟩
      split
      · exact Nat.le_refl _
      · rename_i hn'; exact absurd this hn'
    · exact Nat.zero_le _
  -- `u_o(X) ≤ ū(Z) + e`
  have hu : uCount v agents goods base o X ≤ uBar v agents goods base base' x Z + eSwap v agents goods base base' o x X := by
    unfold uCount uBar eSwap
    apply countP_le_add
    intro w hw hc
    have hc := of_decide_eq_true hc
    by_cases he : w = x ∨ ∃ g' ∈ baseOf goods base w, vbNeeds v goods base' o g'
    · exact Or.inr (decide_eq_true ⟨hc, he⟩)
    refine Or.inl (decide_eq_true ⟨hc.1, fun e => he (Or.inl e), fun g' hg' => ⟨fun hN => ?_, fun i hi hix hN => ?_⟩⟩)
    · -- `N_x(Z) ⊆ N_x({g}) ⊆ 𝒩₋ₒ`
      obtain ⟨hgg', -, hlt⟩ := hN
      have hwx : w ≠ x := fun e => he (Or.inl e)
      obtain ⟨-, hbw⟩ := mem_baseOf.mp hg'
      have hb' : base g' ≠ some x := fun e => by
        rw [hbw] at e; exact hwx (Option.some.inj e)
      exact (hc.2 g' hg').2 x h.hx hxo ⟨hgg', hb', by rw [h.hxg]; simp [value]; omega⟩
    · by_cases hio : i = o
      · subst hio; exact he (Or.inr ⟨g', hg', hN⟩)
      · exact (hc.2 g' hg').2 i hi hio ((vbNeeds_congr (h.hsame i hi hix hio (by simp)).symm g').mp hN)
  exact deficitLE_mono hb (by push_cast; omega)

/-- **Lemma 9, `e`** (`k4/dl13.md` §2.1): `e = 0` when `X ⊆ W_o` and `v_o(X) < v_o(g)`. -/
theorem eSwap_eq_zero (h : RoleSwap v agents goods base base' x o g []) {X : G → Bool}
    (hXW : ∀ r ∈ goods, X r = true → base r = some o ∨ base r = none)
    (hv : value v o (goods.filter X) < v o g) : eSwap v agents goods base base' o x X = 0 := by
  classical
  unfold eSwap
  apply List.countP_eq_zero.mpr
  intro w _ hw
  obtain ⟨hc, he⟩ := of_decide_eq_true hw
  obtain ⟨hgg, hbg⟩ := h.g_mem
  have hXg : X g = false := by
    cases hx : X g with
    | false => rfl
    | true =>
      rcases hXW g hgg hx with e | e <;> rw [hbg] at e
      · exact (h.x_ne_z (Option.some.inj e)).elim
      · cases e
  rcases he with e | ⟨g', hg', hN⟩
  · subst e
    exact (hc.2 g (by rw [h.hxg]; exact List.mem_singleton_self g)).1 ⟨hgg, hXg, hv⟩
  · obtain ⟨hg'g, -, hlt⟩ := hN
    rw [h.hz'] at hlt
    have hlt' : v o g < v o g' := by simpa [value] using hlt
    have hXg' : X g' = false := by
      cases hx : X g' with
      | false => rfl
      | true =>
        have hwo : w ≠ o := fun e => by subst e; exact h.hzF hc.1
        rcases hXW g' hg'g hx with e | e <;> rw [(mem_baseOf.mp hg').2] at e
        · exact (hwo (Option.some.inj e)).elim
        · cases e
    exact (hc.2 g' hg').1 ⟨hg'g, hXg', by omega⟩

/-- **Lemma 9, `e` when `g` is `o`'s top**: then `N_o({g}) = ∅` and `e ≤ 1` (only `x` can be counted). -/
theorem eSwap_le_one (hag : agents.Nodup) (h : RoleSwap v agents goods base base' x o g []) {X : G → Bool}
    (htop : ∀ r ∈ goods, v o r ≤ v o g) : eSwap v agents goods base base' o x X ≤ 1 := by
  classical
  unfold eSwap
  have : agents.countP (fun w => decide (Counted v agents goods base o X w ∧
      (w = x ∨ ∃ g' ∈ baseOf goods base w, vbNeeds v goods base' o g'))) ≤
      agents.countP (fun w => decide (some x = some w)) := by
    apply List.countP_mono_left
    intro w _ hw
    obtain ⟨-, he⟩ := of_decide_eq_true hw
    rcases he with e | ⟨g', -, hN⟩
    · simp [e]
    · obtain ⟨hg', -, hlt⟩ := hN
      rw [h.hz'] at hlt
      have := htop g' hg'
      simp [value] at hlt; omega
  rw [countP_base agents hag (b := some x) (fun k hk => by cases hk; exact h.hx)] at this
  simpa using this

end RoleSwap

/-- **Corollary 9.1 (the S1 repair)** (`k4/dl13.md` §2.1). Let `X` be an optimal bundle of a best owner `o`, `c` a junk
good outside `X`, and suppose `X ∪ {c}` threatens exactly one listed agent other than `o`: a frozen `x` with
`B_x = {g}` whose good `o` needs (the *S1 shape*); and `θ_o(X ∪ {c}) ≤ v_o(g)` (*θ-ok*). On a strict profile with
`ω ≥ 1` and `|R_x| ≤ 4`, some `A ⊆ X ∪ {c}` is admissible for `x`, and the swap (`o` takes `{g}`, `x` takes `A`;
`swapBase`) is a min-frozen (T3)-neighbour of `P` with `def(P′) ≤ def(P) − 1 − ι`. -/
theorem cor9_1 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) (hs : Strict v agents goods) {o x : A} {g : G} {X : G → Bool}
    (hX : OptimalBest v agents goods base o X) (hog : vbNeeds v goods base o g) (hx : x ∈ agents)
    (hxg : baseOf goods base x = [g]) (hR4 : (relevant v x goods).length ≤ 4) {c : G} (hc : c ∈ goods)
    (hcJ : base c = none) (hcX : X c = false)
    (hthr : ∃ k ∈ goods.filter (fun r => X r || decide (r = c)),
      v x g < value v x ((goods.filter (fun r => X r || decide (r = c))).erase k))
    (hnone : ∀ w ∈ agents, w ≠ o → w ≠ x → ∀ k ∈ goods.filter (fun r => X r || decide (r = c)),
      value v w ((goods.filter (fun r => X r || decide (r = c))).erase k) ≤ value v w (baseOf goods base w))
    (hθ : ∀ k ∈ goods.filter (fun r => X r || decide (r = c)),
      value v o ((goods.filter (fun r => X r || decide (r = c))).erase k) ≤ v o g) :
    ∃ Ax : G → Bool, (∀ r ∈ goods, Ax r = true → (X r || decide (r = c)) = true ∧ 0 < v x r) ∧
      (goods.filter Ax).length ≤ 2 ∧ (∀ r, setNeeds v goods x Ax r → NA agents (vbNeeds v goods base) r) ∧
      MinFrozen v agents goods (swapBase base x o g Ax) ∧ MoveT3 v agents goods base (swapBase base x o g Ax) ∧
      DeficitDrop v agents goods (swapBase base x o g Ax) base (1 + (iotaNeed v agents goods base o x g : Int)) := by
  classical
  obtain ⟨ho, hoF, hXb, hXs, hmax⟩ := hX
  have hP := hM.1
  have hgN : NA agents (vbNeeds v goods base) g := ⟨o, ho, hog⟩
  let Y : G → Bool := fun r => X r || decide (r = c)
  have hYW : ∀ r ∈ goods, Y r = true → base r = some o ∨ base r = none := by
    intro r hr hy
    rcases Bool.or_eq_true _ _ |>.mp hy with hx' | e
    · exact (hXb r hr).2 hx'
    · have : r = c := of_decide_eq_true e
      subst this; exact Or.inr hcJ
  have hYN : ∀ r ∈ goods, Y r = true → ¬ NA agents (vbNeeds v goods base) r := by
    intro r hr hy
    rcases hYW r hr hy with e | e
    · exact not_NA_of_mem_free hP hoF (mem_baseOf.mpr ⟨hr, e⟩)
    · exact not_NA_of_junk hP hr e
  obtain ⟨Ax, hA, hA2, hAN⟩ := lemma9_admissible hgd hP hx hxg hgN hR4 hYN hthr
  have hA' : ∀ r ∈ goods, Ax r = true → (base r = none ∨ base r = some o) ∧ 0 < v x r := by
    intro r hr ha
    refine ⟨?_, (hA r hr ha).2⟩
    rcases hYW r hr (hA r hr ha).1 with e | e
    · exact Or.inr e
    · exact Or.inl e
  obtain ⟨hRS, hx'⟩ := roleSwap_swapBase hgd hP hx hxg hgN ho hoF hog hA' hA2 hAN
  obtain ⟨hM', hNA, -, -⟩ := hRS.lemma6' hag hgd hM
  have hb := hRS.lemma9 hag hgd hM hω hs (X := X) (Z := Y)
    (fun r hr hb => by
      have : r ∈ baseOf goods (swapBase base x o g Ax) x := mem_baseOf.mpr ⟨hr, hb⟩
      rw [hx'] at this; exact (hA r hr (List.mem_filter.mp this).2).1)
    hYW hthr hnone hθ
  -- `e = 0`: `v_o(X) < v_o(g)` (drop `c` in θ-ok; strictness)
  have hperm := filter_insert_perm hgd hc hcX
  have hcY : c ∈ goods.filter Y := List.mem_filter.mpr ⟨hc, by simp [Y]⟩
  have hXv : value v o (goods.filter X) ≤ v o g := by
    have := hθ c hcY
    rwa [value_perm (hperm.erase c), List.erase_cons_head] at this
  have hXg : X g = false := by
    cases h : X g with
    | false => rfl
    | true => exact absurd hgN (hYN g hog.1 (by simp [Y, h]))
  have hXlt : value v o (goods.filter X) < v o g := by
    refine Nat.lt_of_le_of_ne hXv fun e => ?_
    have := hs o ho (goods.filter X) [g] List.filter_sublist (List.singleton_sublist.mpr hog.1)
      (fun r hr hrg => by
        rw [List.mem_singleton] at hrg; subst hrg; rw [(List.mem_filter.mp hr).2] at hXg; cases hXg)
      (by simp [value] at e ⊢; exact e)
    have := hog.2.2; omega
  have he := hRS.eSwap_eq_zero (fun r hr hx'' => (hXb r hr).2 hx'') hXlt
  rw [he] at hb
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  refine ⟨Ax, hA, hA2, hAN, hM', ⟨x, hx, o, ho, g, hxg, hgN, hoF, hog, hRS.hz', [], by simp, by simp,
    fun i hi hix hio _ => hRS.hsame i hi hix hio (by simp), fun g' => (hNA g').symm⟩, fun d hd => ?_⟩
  have := (deficit_of_optimalBest hag hP hω ⟨ho, hoF, hXb, hXs, hmax⟩).2 d hd
  exact deficitLE_mono hb (by rw [hlen]; push_cast; omega)

/-- **Corollary 9.2 (Lemma 9 at a best owner)** (`k4/dl13.md` §2.1). If `X` is an optimal bundle of a best owner `o`
that needs `g`, `e = 0`, and the swap (`o` takes `{g}`, `x` takes `A ⊆ Z`) uses a `Z ⊆ W_o` with (i)–(iii) of Lemma 9 and
`|Z| + ι > |X|`, then the swap lowers the deficit. -/
theorem cor9_2 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) (hs : Strict v agents goods) {o x : A} {g : G} {X Z : G → Bool}
    (hX : OptimalBest v agents goods base o X) (h : RoleSwap v agents goods base base' x o g [])
    (hAZ : ∀ r ∈ goods, base' r = some x → Z r = true)
    (hZW : ∀ r ∈ goods, Z r = true → base r = some o ∨ base r = none)
    (hi : ∃ k ∈ goods.filter Z, v x g < value v x ((goods.filter Z).erase k))
    (hii : ∀ w ∈ agents, w ≠ o → w ≠ x → ∀ k ∈ goods.filter Z,
      value v w ((goods.filter Z).erase k) ≤ value v w (baseOf goods base w))
    (hiii : ∀ k ∈ goods.filter Z, value v o ((goods.filter Z).erase k) ≤ v o g)
    (he : eSwap v agents goods base base' o x X = 0)
    (hlen : (goods.filter X).length < (goods.filter Z).length + iotaNeed v agents goods base o x g) :
    DeficitLT v agents goods base' base := by
  have hb := h.lemma9 hag hgd hM hω hs (X := X) hAZ hZW hi hii hiii
  rw [he] at hb
  obtain ⟨hd0, hleast⟩ := deficit_of_optimalBest hag hM.1 hω hX
  exact deficitLT_of_drop (k := 1) (Int.le_refl 1) (fun d hd => deficitLE_mono hb (by
    have := hleast d hd; push_cast at hlen ⊢; omega)) hd0

/-! ## `k4/dl13.md` §2.1, Corollary 11.1 (the blocker swap) -/

/-- **Corollary 11.1 (the blocker swap)** (`k4/dl13.md` §2.1). Let `X` be an optimal bundle of a best owner `o`, `c` a
junk good outside `X`, and suppose `X ∪ {c}` threatens no listed agent other than `o` and a free `z ≠ o` that needs the
good `g` of a frozen `x` (`B_x = {g}`), with `θ_z(X ∪ {c}) ≤ v_z(g)`. Let `A ⊆ (J ∪ B_z) ∖ (X ∪ {c})` be admissible for
`x` with `θ_x(X ∪ {c}) ≤ v_x(A)`, and let no agent counted in `u_o(X)` have its good in `N_x(A)` (`cor11_1_auto`: this
holds when `v_x(A) ≥ v_x(g)` or when `x` is the only frozen agent). Then the swap (`z` takes `{g}`, `x` takes `A`;
`swapBase`) is a min-frozen (T3)-neighbour of `P` with `def(P′) ≤ def(P) − 1`. -/
theorem cor11_1 (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hω : 0 < omegaP v agents goods base) {o x z : A} {g : G} {X : G → Bool}
    (hX : OptimalBest v agents goods base o X) {c : G} (hc : c ∈ goods) (hcJ : base c = none) (hcX : X c = false)
    (hx : x ∈ agents) (hxg : baseOf goods base x = [g]) (hz : z ∈ agents)
    (hzF : ¬ Frozen agents goods base (vbNeeds v goods base) z) (hzN : vbNeeds v goods base z g) (hzo : z ≠ o)
    (hnone : ∀ w ∈ agents, w ≠ o → w ≠ z → ∀ k ∈ goods.filter (fun r => X r || decide (r = c)),
      value v w ((goods.filter (fun r => X r || decide (r = c))).erase k) ≤ value v w (baseOf goods base w))
    (hθz : ∀ k ∈ goods.filter (fun r => X r || decide (r = c)),
      value v z ((goods.filter (fun r => X r || decide (r = c))).erase k) ≤ v z g)
    {Ax : G → Bool} (hA : ∀ r ∈ goods, Ax r = true → (base r = none ∨ base r = some z) ∧ 0 < v x r)
    (hAY : ∀ r ∈ goods, Ax r = true → (X r || decide (r = c)) = false)
    (hA2 : (goods.filter Ax).length ≤ 2) (hAN : ∀ r, setNeeds v goods x Ax r → NA agents (vbNeeds v goods base) r)
    (hθx : ∀ k ∈ goods.filter (fun r => X r || decide (r = c)),
      value v x ((goods.filter (fun r => X r || decide (r = c))).erase k) ≤ value v x (goods.filter Ax))
    (hcnt : ∀ w ∈ agents, Counted v agents goods base o X w → ∀ g' ∈ baseOf goods base w, ¬ setNeeds v goods x Ax g') :
    MinFrozen v agents goods (swapBase base x z g Ax) ∧ MoveT3 v agents goods base (swapBase base x z g Ax) ∧
      DeficitDrop v agents goods (swapBase base x z g Ax) base 1 := by
  classical
  obtain ⟨ho, hoF, hXb, hXs, hmax⟩ := hX
  have hP := hM.1
  have hgN : NA agents (vbNeeds v goods base) g := ⟨z, hz, hzN⟩
  have hxF : Frozen agents goods base (vbNeeds v goods base) x := ⟨g, hxg, hgN⟩
  have hxo : x ≠ o := fun e => hoF (e ▸ hxF)
  obtain ⟨hRS, hx'⟩ := roleSwap_swapBase hgd hP hx hxg hgN hz hzF hzN hA hA2 hAN
  obtain ⟨hM', hNA, -, -⟩ := hRS.lemma6' hag hgd hM
  have hoB : baseOf goods base o = baseOf goods (swapBase base x z g Ax) o := hRS.hsame o ho (Ne.symm hxo) (Ne.symm hzo) (by simp)
  let Y : G → Bool := fun r => X r || decide (r = c)
  have hXY : ∀ r ∈ goods, X r = true → Y r = true := fun r _ hr => by simp [Y, hr]
  -- `Y` is a bundle of `o` in `P′`
  have hY : IsBundle goods (swapBase base x z g Ax) o Y := by
    intro r hr
    refine ⟨fun hb => hXY r hr ((hXb r hr).1 ((base_eq_some_iff hoB.symm hr).mp hb)), fun hy => ?_⟩
    have hrW : base r = some o ∨ base r = none := by
      rcases Bool.or_eq_true _ _ |>.mp hy with h | e
      · exact (hXb r hr).2 h
      · have : r = c := of_decide_eq_true e
        subst this; exact Or.inr hcJ
    rcases hrW with e | e
    · exact Or.inl ((base_eq_some_iff hoB.symm hr).mpr e)
    · refine Or.inr ((hRS.junk_iff hP hr).mpr ⟨Or.inl e, fun hb => ?_, by simp⟩)
      have : r ∈ baseOf goods (swapBase base x z g Ax) x := mem_baseOf.mpr ⟨hr, hb⟩
      rw [hx'] at this
      have h2 := hAY r hr (List.mem_filter.mp this).2
      have hy' : (X r || decide (r = c)) = true := hy
      rw [hy'] at h2; cases h2
  -- `Y` is safe in `P′`
  have hS : SafeFor v agents goods (swapBase base x z g Ax) o Y := by
    intro w hw hwo k hk
    by_cases hwz : w = z
    · subst hwz; rw [hRS.hz']; have := hθz k hk; simpa [value] using this
    by_cases hwx : w = x
    · subst hwx; rw [hx']; exact hθx k hk
    · rw [← hRS.hsame w hw hwx hwz (by simp)]; exact hnone w hw hwo hwz k hk
  -- `e* = 0`
  have he : eStar v agents goods base (swapBase base x z g Ax) o X = 0 := by
    unfold eStar
    apply List.countP_eq_zero.mpr
    intro w hw hwp
    obtain ⟨hc', hch⟩ := of_decide_eq_true hwp
    -- `x` and `z` are not counted
    have hwx : w ≠ x := fun e => by
      subst e
      exact (hc'.2 g (by rw [hxg]; exact List.mem_singleton_self g)).2 z hz hzo hzN
    have hwz : w ≠ z := fun e => by subst e; exact hzF hc'.1
    rcases hch with hne | ⟨i, hi, hne, g', hg', hN⟩
    · exact hne (hRS.hsame w hw hwx hwz (by simp))
    · by_cases hix : i = x
      · subst hix
        refine hcnt w hw hc' g' hg' ⟨hN.1, ?_, by have h3 := hN.2.2; rw [hx'] at h3; exact h3⟩
        cases h : Ax g' with
        | false => rfl
        | true =>
          exfalso; apply hN.2.1
          have : g' ∈ baseOf goods (swapBase base i z g Ax) i := by rw [hx']; exact List.mem_filter.mpr ⟨hN.1, h⟩
          exact (mem_baseOf.mp this).2
      by_cases hiz : i = z
      · subst hiz
        -- `N_z({g}) ⊆ N_z`
        obtain ⟨hgg', -, hlt⟩ := hN
        rw [hRS.hz'] at hlt
        have hlt' : v i g < v i g' := by simpa [value] using hlt
        have hBz := hzN.2.2
        refine (hc'.2 g' hg').2 i hi hzo ⟨hgg', fun hb => ?_, by omega⟩
        have := le_value_of_mem v i (mem_baseOf.mpr ⟨hgg', hb⟩ : g' ∈ baseOf goods base i)
        omega
      · exact hne (hRS.hsame i hi hix hiz (by simp))
  have hd := lemma2star_drop hag hgd hP hM'.1 hNA hω ⟨ho, hoF, hXb, hXs, hmax⟩ hoB hXY hY hS
  rw [he] at hd
  have hlen := (filter_insert_perm hgd hc hcX).length_eq
  simp only [List.length_cons] at hlen
  refine ⟨hM', ⟨x, hx, z, hz, g, hxg, hgN, hzF, hzN, hRS.hz', [], by simp, by simp,
    fun i hi hix hiz _ => hRS.hsame i hi hix hiz (by simp), fun g' => (hNA g').symm⟩, fun d hdd => ?_⟩
  have := hd d hdd
  rw [hlen] at this
  exact deficitLE_mono this (by push_cast; omega)

omit [DecidableEq G] in
/-- **Corollary 11.1, the counted hypothesis is automatic** when `v_x(A) ≥ v_x(g)` (then `N_x(A) ⊆ N_x({g}) ⊆ 𝒩₋ₒ`) or
when `x` is the only frozen agent (`f = 1`: nobody is counted, since `x` is not). Here `z ≠ o` needs `g`. -/
theorem cor11_1_auto {o x z : A} {g : G} {X Ax : G → Bool} (hx : x ∈ agents) (hxg : baseOf goods base x = [g])
    (hxo : x ≠ o) (hz : z ∈ agents) (hzN : vbNeeds v goods base z g) (hzo : z ≠ o)
    (h : value v x [g] ≤ value v x (goods.filter Ax) ∨
      ∀ w ∈ agents, Frozen agents goods base (vbNeeds v goods base) w → w = x) :
    ∀ w ∈ agents, Counted v agents goods base o X w → ∀ g' ∈ baseOf goods base w, ¬ setNeeds v goods x Ax g' := by
  intro w hw hc g' hg' hN
  have hwx : w ≠ x := fun e => by
    subst e
    exact (hc.2 g (by rw [hxg]; exact List.mem_singleton_self g)).2 z hz hzo hzN
  rcases h with hv | hone
  · obtain ⟨hgg', -, hlt⟩ := hN
    have hb : base g' ≠ some x := fun e => by
      rw [(mem_baseOf.mp hg').2] at e; exact hwx (Option.some.inj e)
    exact (hc.2 g' hg').2 x hx hxo ⟨hgg', hb, by rw [hxg]; omega⟩
  · exact hwx (hone w hw hc.1)

/-! ## `k4/dl13.md` §2.2, Corollary 12.1 (normalization by frozen rotations) -/

/-- `P′` is a Pareto reassignment of `P` (for some `π`). -/
def IsParetoReassign (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) : Prop :=
  ∃ π : A → A, ParetoReassign v agents goods base base' π

/-- **T4-optimal** (`k4/dl13.md` §2.2): no Pareto reassignment other than the identity, i.e. every Pareto reassignment of
`P` leaves every listed agent's base unchanged (the frozen need digraph is acyclic). -/
def T4Optimal (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ∀ base', IsParetoReassign v agents goods base base' → ∀ i ∈ agents, baseOf goods base' i = baseOf goods base i

/-- Finitely many Pareto reassignments, one after the other. -/
inductive ReassignChain (v : A → G → Nat) (agents : List A) (goods : List G) :
    (G → Option A) → (G → Option A) → Prop
  | refl (base : G → Option A) : ReassignChain v agents goods base base
  | step {base base' base'' : G → Option A} : IsParetoReassign v agents goods base base' →
      ReassignChain v agents goods base' base'' → ReassignChain v agents goods base base''

open Classical in
/-- The potential of Corollary 12.1: `Σ_{x ∈ F} v_x(B_x)`. -/
noncomputable def frozenWelfare (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  (agents.map (fun x => if Frozen agents goods base (vbNeeds v goods base) x then value v x (baseOf goods base x)
    else 0)).sum

theorem sum_lt_sum_of_le_of_lt {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a) → (∃ a ∈ l, f a < g a) → (l.map f).sum < (l.map g).sum
  | [], _, ⟨_, ha, _⟩ => by simp at ha
  | b :: l, h, ⟨a, ha, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    have hb := h b (by simp)
    have hle := sum_le_sum_of_le f g l (fun c hc => h c (by simp [hc]))
    rcases List.mem_cons.mp ha with e | e
    · subst e; omega
    · have := sum_lt_sum_of_le_of_lt f g l (fun c hc => h c (by simp [hc])) ⟨a, e, hlt⟩
      omega

omit [DecidableEq G] in
open Classical in
theorem frozenWelfare_le : frozenWelfare v agents goods base ≤ (agents.map (fun x => value v x goods)).sum := by
  unfold frozenWelfare
  refine sum_le_sum_of_le _ _ agents fun x _ => ?_
  split
  · exact value_sublist v x List.filter_sublist
  · exact Nat.zero_le _

omit [DecidableEq G] in
/-- A Pareto reassignment that changes some base strictly raises `Σ_{x ∈ F} v_x(B_x)` on a strict profile (a frozen
agent that moves strictly prefers its new good). -/
theorem frozenWelfare_lt (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hs : Strict v agents goods) {π : A → A} (hR : ParetoReassign v agents goods base base' π) {i : A}
    (hi : i ∈ agents) (hne : baseOf goods base' i ≠ baseOf goods base i) :
    frozenWelfare v agents goods base < frozenWelfare v agents goods base' := by
  classical
  obtain ⟨-, -, hFF, -, -, -⟩ := lemma12_move hag hgd hM hR
  unfold frozenWelfare
  apply sum_lt_sum_of_le_of_lt
  · intro x hx
    by_cases hF : Frozen agents goods base (vbNeeds v goods base) x
    · obtain ⟨-, -, hB', hle⟩ := hR.frozen x hx hF
      simp only [hF, (hFF x hx).mpr hF, ↓reduceIte, hB']
      exact hle
    · have : ¬ Frozen agents goods base' (vbNeeds v goods base') x := fun h => hF ((hFF x hx).mp h)
      simp [hF, this]
  · refine ⟨i, hi, ?_⟩
    have hF : Frozen agents goods base (vbNeeds v goods base) i :=
      Classical.byContradiction fun hF => hne (hR.free i hi hF).symm
    obtain ⟨-, ⟨g', hBπ, -⟩, hB', hle⟩ := hR.frozen i hi hF
    obtain ⟨g, hB, -⟩ := id hF
    simp only [hF, (hFF i hi).mpr hF, ↓reduceIte, hB']
    rw [hB, hBπ] at hle ⊢
    rw [hB', hBπ, hB] at hne
    have hgg' : g ≠ g' := fun e => hne (by rw [e])
    have hg : g ∈ goods ∧ base g = some i := mem_baseOf.mp (by rw [hB]; exact List.mem_singleton_self g)
    have hg' : g' ∈ goods := (mem_baseOf.mp (by rw [hBπ]; exact List.mem_singleton_self g' :
      g' ∈ baseOf goods base (π i))).1
    have hpos := hM.1.rel g hg.1 i hg.2
    refine Nat.lt_of_le_of_ne hle fun e => ?_
    have := hs i hi [g] [g'] (List.singleton_sublist.mpr hg.1) (List.singleton_sublist.mpr hg')
      (by simpa using hgg') e
    simp [value] at this; omega

/-- **Corollary 12.1 (normalization)** (`k4/dl13.md` §2.2). On a strict profile, from every min-frozen `P` with `ω ≥ 1`,
finitely many Pareto reassignments (frozen rotations) reach a T4-optimal min-frozen `P*` with `def(P*) ≤ def(P)`. -/
theorem cor12_1 (hag : agents.Nodup) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hM : MinFrozen v agents goods base) (hω : 0 < omegaP v agents goods base) :
    ∃ base₁, ReassignChain v agents goods base base₁ ∧ MinFrozen v agents goods base₁ ∧
      T4Optimal v agents goods base₁ ∧ DeficitDrop v agents goods base₁ base 0 := by
  classical
  have key : ∀ n : Nat, ∀ b, MinFrozen v agents goods b → 0 < omegaP v agents goods b →
      (agents.map (fun x => value v x goods)).sum - frozenWelfare v agents goods b = n →
      ∃ b₁, ReassignChain v agents goods b b₁ ∧ MinFrozen v agents goods b₁ ∧ T4Optimal v agents goods b₁ ∧
        DeficitDrop v agents goods b₁ b 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro b hMb hωb hn
      by_cases hT : T4Optimal v agents goods b
      · exact ⟨b, ReassignChain.refl b, hMb, hT, fun d hd => by simpa using hd⟩
      · obtain ⟨b', ⟨π, hR⟩, hch⟩ : ∃ b', IsParetoReassign v agents goods b b' ∧
            ∃ i ∈ agents, baseOf goods b' i ≠ baseOf goods b i := by
          refine Classical.byContradiction fun hno => hT fun b' hb' i hi => ?_
          exact Classical.byContradiction fun hne => hno ⟨b', hb', i, hi, hne⟩
        obtain ⟨i, hi, hne⟩ := hch
        obtain ⟨hM', -, -, -, hω', -⟩ := lemma12_move hag hgd hMb hR
        obtain ⟨-, -, -, hdrop⟩ := lemma12 hag hgd hMb hωb hR
        have hlt := frozenWelfare_lt hag hgd hMb hs hR hi hne
        have hle := frozenWelfare_le (v := v) (agents := agents) (goods := goods) (base := b')
        obtain ⟨b₁, hch₁, hM₁, hT₁, hd₁⟩ := ih _ (by omega) b' hM' (by rw [hω']; exact hωb) rfl
        exact ⟨b₁, ReassignChain.step ⟨π, hR⟩ hch₁, hM₁, hT₁, fun d hd => by
          have := hd₁ (d - 0) (hdrop d hd); simpa using this⟩
  exact key _ base hM hω rfl

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
#print axioms EFX.C4min.RoleSwap.lemma6'
#print axioms EFX.C4min.RoleSwap.junk_iff
#print axioms EFX.C4min.RoleSwap.lemma8_bundle
#print axioms EFX.C4min.RoleSwap.lemma8_safe
#print axioms EFX.C4min.RoleSwap.lemma8_u
#print axioms EFX.C4min.RoleSwap.lemma8
#print axioms EFX.C4min.RoleSwap.lemma8_val
#print axioms EFX.C4min.RoleSwap.lt_value_of_lower
#print axioms EFX.C4min.RoleSwap.cor8_2
#print axioms EFX.C4min.length_le_of_sub
#print axioms EFX.C4min.filter_mem_perm
#print axioms EFX.C4min.lemma10_a
#print axioms EFX.C4min.lemma10
#print axioms EFX.C4min.roleSwap_swapBase
#print axioms EFX.C4min.exists_min_value
#print axioms EFX.C4min.lemma9_admissible
#print axioms EFX.C4min.RoleSwap.lemma9
#print axioms EFX.C4min.RoleSwap.eSwap_eq_zero
#print axioms EFX.C4min.RoleSwap.eSwap_le_one
#print axioms EFX.C4min.cor9_1
#print axioms EFX.C4min.cor9_2
#print axioms EFX.C4min.cor11_1
#print axioms EFX.C4min.cor11_1_auto
#print axioms EFX.C4min.sum_lt_sum_of_le_of_lt
#print axioms EFX.C4min.frozenWelfare_le
#print axioms EFX.C4min.frozenWelfare_lt
#print axioms EFX.C4min.cor12_1
