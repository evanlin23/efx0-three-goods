import EFX.KeyFrame

/-!
# The moves (T2), (T4), (T3⁺) and the relation R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4) (ledger K4.DL2.RC.LEAN)

The fixed relation R_T4 = (T1) ∪ (T2) ∪ (T3) ∪ (T4) of the conjecture DL_RT4 (K4.DL2.RT4E) fails at n = 5, f = 3
(compute/k4-rt4-n5b, compute/k4-rt4-n5c, `results/k4_rt4/n5*_FAILURES.md`): at those states every repair is a role swap
whose good passes through a frozen intermediary (frozen `x` frees `g`, frozen `y` moves from `h` to `g`, free `z` takes
`h`), which is neither a (T3) move (`z` does not take `x`'s good) nor a (T4) move (`x` and `z` change roles). The
coordinator's widened move is **(T3⁺), the frozen-chain role swap**; (T3) is its case `W = ∅`. This file writes the
moves (T2), (T4), (T3⁺) as relations on pre-allocations, in the style of `MoveT1`, `MoveT3` (`EFX/DL13.lean`), the
relation **R_C**, the conjecture **DL_RC**, and connects it to TARGET₄ and to the key frame of `EFX/KeyFrame.lean`. DL_RC
is a hypothesis of every theorem here, never an axiom; nothing of the model is redefined.

**Definitions** (P = `base`, P′ = `base'`; `B_i = baseOf goods base i`, `N_i(B_i) = vbNeeds v goods base i`,
`NA = NA agents (vbNeeds v goods base)`, frozen = `Frozen agents goods base (vbNeeds v goods base)`, the same with
`base'` in P′; a listed agent is *changed* if its base on `goods` differs, `B_i ≠ B′_i`).
- `MoveT2` (**(T2) rotation**, `k4/dl2.md` §3): a set `Y` of agents free in P (`|Y| ≥ 2`) takes new bases
  `B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y`, pairwise disjoint, everybody else unchanged, the needed set unchanged.
- `MoveT4` (**(T4)**, ledger K4.DL2.T134, K4.DL2.RT4E): every agent whose base changes is frozen in P and in P′, and
  NA(P′) = NA(P) (the frozen agents permute their singleton bases, every other base unchanged).
- `ChangedFrozen` (the set `W` of (T3⁺)): the changed listed agents frozen in P and in P′.
- `MoveT3plus` (**(T3⁺) the frozen-chain role swap**, the coordinator's definition): NA(P′) = NA(P); exactly one
  changed agent `x` is frozen in P and free in P′; exactly one changed agent `z` is free in P and frozen in P′, and `z`
  needs its new good in P; `W` = the changed agents frozen in both; `Y` = the changed agents free in both, with
  `|Y| ≤ 1`, each giving up a good; the bases of `W ∪ {z}` in P′ are exactly the bases of `W ∪ {x}` in P.
- `RC` (**R_C**) = `MoveT1 ∪ MoveT2 ∪ MoveT3plus ∪ MoveT4`; `RC34` = `MoveT3plus ∪ MoveT4`, the moves of R_C that may
  change the key; `RCZ` = every pair on a profile with `f = 0` (`FewestFrozenZero`), R_C otherwise (as `R13Z`).
- `DLRC` (**Conjecture DL_RC**): `DefLocalAt RC` on every strict profile of every connected k = 4 core whose fewest
  frozen agents is `f ≥ 1` (as `DL13`).

**Results.**
- `moveT3_moveT3plus`, `r13_rc`: on 𝒫, **(T3) ⊆ (T3⁺)** (with `W = ∅`, `Y = H`) and **R₁₃ ⊆ R_C**; `DLRC_of_DL13`.
- `moveT1_key`, `moveT2_key`: on 𝒫, **(T1) and (T2) keep the key** (`key_eq_of_free_changes`: if NA is unchanged and
  every changed agent is free in P, the key is unchanged). `rc_rKey`: hence R_C ⊆ `RKey RC34` on min-frozen pairs.
- `defLocal_RCZ_of_DLRC`, `dlrc_iff_defLocal_RCZ`, `C4minROConn_of_DLRC`, `target4_of_DLRC`: **DL_RC (with Theorem Z
  at f = 0) ⟺ DL for `RCZ` ⟹ TARGET₄**.
- `defLocal_rKey_of_DLRC`, `DLKey_of_DLRC`: **DL_RC ⟹ DefLocal (RKey (T3⁺ ∪ T4)) ⟹ DLKey (T3⁺ ∪ T4)**, so DL on the
  key graph for (T3⁺) ∪ (T4) is weaker than DL_RC; `dlKey_RC_iff`: DL on the key graph is the same for R_C and for
  (T3⁺) ∪ (T4) (a (T1) or (T2) move never leaves its key).
- Facts on 𝒫 used above, of independent use: `exists_frozen_of_NA` (every needed good is the whole base of a listed
  agent), `frozen'_shape` (an agent frozen in P′ holds the base of an agent frozen in P, if NA is unchanged),
  `not_frozen'_of_keep` (if NA is unchanged and the frozen agents keep their bases, the free agents stay free).

**Faithfulness** (paper statement / Lean statement / why they agree).
1. (T2): `k4/dl2.md` §3, "a set Y of agents free in P (|Y| ≥ 2) takes new bases B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y,
   pairwise disjoint, everybody else unchanged", with the needed set unchanged. Lean: a duplicate-free list `Y` of at
   least two listed agents free in P; every good of `B′_y` was junk or in a base of `Y` (`base g = none ∨ ∃ w ∈ Y,
   base g = some w`) and is relevant to `y`; every listed agent outside `Y` keeps its base; NA unchanged. Disjointness is
   automatic for a base map. "Takes new bases" is not read as "every base of `Y` changes" (the wider reading; the code
   `RTr` asks only that every changed agent be free in P and P′).
2. (T4): LEDGER K4.DL2.T134, "every agent whose base changes is frozen in P and in P′ and NA(P′) = NA(P)". Lean: the
   same, for listed agents, word for word.
3. (T3⁺): the coordinator's definition, clause by clause. "Exactly one changed agent `x` frozen in P and free in P′":
   `x` is listed, frozen in P and free in P′ (so changed, NA being unchanged), and every changed listed agent other
   than `x`, `z` and the agents of `Y` is frozen in P and in P′, so no other changed agent goes from frozen to free;
   likewise for `z`. "`z` needs its new good in P": `B′_z = [g]` with `g ∈ N_z(B_z)`. "`Y` = the changed agents free in
   both, `|Y| ≤ 1`, each giving up a good": a list `Y` of length ≤ 1 of listed agents free in P and P′, each with a good
   of `B_h` outside `B′_h`; with the previous clause it contains every changed agent free in both. "The bases of
   `W ∪ {z}` in P′ are exactly the bases of `W ∪ {x}` in P": for every list `B` of goods, `B` is the P′-base of `z` or of
   an agent of `W` iff it is the P-base of `x` or of an agent of `W` (equality of the two sets of bases).
4. (T3) ⊆ (T3⁺) and R₁₃ ⊆ R_C hold for P ∈ 𝒫 (P′ arbitrary), not for arbitrary base maps: that `x` and the helper are
   free in P′ uses (V1), (V2) of P (`exists_frozen_of_NA`). The relations matter only between min-frozen
   pre-allocations, so `DLRC_of_DL13` is unconditional.
5. "(T1) ∪ (T2) keep the key" (`k4/dl2.md` §3, "R_T is local only in the frozen agents") is proved in the direction
   used here (a (T1) or (T2) move between pre-allocations of 𝒫 keeps the key); the converse of the text (same key ⟹ a
   (T1) or (T2) move) is not formalized.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## The moves (T2), (T4), (T3⁺) and the relations R_C, `RC34`, `RCZ` -/

/-- **(T2) rotation** (`k4/dl2.md` §3): a set `Y` of at least two listed agents, free in `P`, takes new bases
`B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y` (pairwise disjoint, automatic for a base map); every other listed agent keeps its base
(on `goods`); the needed set `NA` is unchanged. -/
def MoveT2 : Nbhd A G := fun v agents goods base base' =>
  ∃ Y : List A, Y.Nodup ∧ 2 ≤ Y.length ∧
    (∀ y ∈ Y, y ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) y) ∧
    (∀ y ∈ Y, ∀ g ∈ baseOf goods base' y, (base g = none ∨ ∃ w ∈ Y, base g = some w) ∧ 0 < v y g) ∧
    (∀ i ∈ agents, i ∉ Y → baseOf goods base i = baseOf goods base' i) ∧
    (∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)

/-- **(T4)** (ledger K4.DL2.T134, K4.DL2.RT4E): every listed agent whose base changes is frozen in `P` and in `P′`, and
the needed set `NA` is unchanged (the frozen agents permute their singleton bases, every other base unchanged). -/
def MoveT4 : Nbhd A G := fun v agents goods base base' =>
  (∀ i ∈ agents, baseOf goods base i ≠ baseOf goods base' i →
    Frozen agents goods base (vbNeeds v goods base) i ∧ Frozen agents goods base' (vbNeeds v goods base') i) ∧
  (∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)

/-- The set `W` of (T3⁺): `w` is a listed agent whose base changes and that is frozen in `P` and in `P′`. -/
def ChangedFrozen (v : A → G → Nat) (agents : List A) (goods : List G) (base base' : G → Option A) (w : A) : Prop :=
  w ∈ agents ∧ baseOf goods base w ≠ baseOf goods base' w ∧
    Frozen agents goods base (vbNeeds v goods base) w ∧ Frozen agents goods base' (vbNeeds v goods base') w

/-- **(T3⁺) the frozen-chain role swap**: the needed set is unchanged; a listed agent `x` is frozen in `P` and free in
`P′`; a listed agent `z` is free in `P` and frozen in `P′`, and needs its new good in `P` (`B′_z = {g}`,
`g ∈ N_z(B_z)`); a list `Y` of at most one listed agent, free in `P` and in `P′`, each giving up a good of its base;
every other changed listed agent is frozen in `P` and in `P′` (the set `W`, `ChangedFrozen`); and the bases of
`W ∪ {z}` in `P′` are exactly the bases of `W ∪ {x}` in `P`. With `W = ∅` this is (T3). -/
def MoveT3plus : Nbhd A G := fun v agents goods base base' =>
  ∃ x ∈ agents, ∃ z ∈ agents,
    Frozen agents goods base (vbNeeds v goods base) x ∧ ¬ Frozen agents goods base' (vbNeeds v goods base') x ∧
    ¬ Frozen agents goods base (vbNeeds v goods base) z ∧ Frozen agents goods base' (vbNeeds v goods base') z ∧
    (∃ g, baseOf goods base' z = [g] ∧ vbNeeds v goods base z g) ∧
    ∃ Y : List A, Y.length ≤ 1 ∧
      (∀ h ∈ Y, h ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧
        ¬ Frozen agents goods base' (vbNeeds v goods base') h ∧
        ∃ g' ∈ baseOf goods base h, g' ∉ baseOf goods base' h) ∧
      (∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ Y → baseOf goods base i ≠ baseOf goods base' i →
        Frozen agents goods base (vbNeeds v goods base) i ∧ Frozen agents goods base' (vbNeeds v goods base') i) ∧
      (∀ B : List G,
        (baseOf goods base' z = B ∨ ∃ w, ChangedFrozen v agents goods base base' w ∧ baseOf goods base' w = B) ↔
        (baseOf goods base x = B ∨ ∃ w, ChangedFrozen v agents goods base base' w ∧ baseOf goods base w = B)) ∧
      (∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)

/-- **The relation R_C** = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4). -/
def RC : Nbhd A G := fun v agents goods base base' =>
  MoveT1 v agents goods base base' ∨ MoveT2 v agents goods base base' ∨
    MoveT3plus v agents goods base base' ∨ MoveT4 v agents goods base base'

/-- **(T3⁺) ∪ (T4)**: the moves of R_C that may change the key. -/
def RC34 : Nbhd A G := fun v agents goods base base' =>
  MoveT3plus v agents goods base base' ∨ MoveT4 v agents goods base base'

/-- Every pair of pre-allocations on a profile whose fewest frozen agents is 0, R_C on the others (as `R13Z`). -/
def RCZ : Nbhd A G := fun v agents goods base base' =>
  FewestFrozenZero v agents goods ∨ RC v agents goods base base'

/-- **Conjecture DL_RC**: on every strict profile of every connected k = 4 core whose fewest frozen agents is at least 1,
DL for R_C (`DefLocalAt RC`: if `ω ≥ 1`, every min-frozen `P` with `def(P) > 0`, `+∞` included, has a min-frozen `P′`
with `RC P P′` and `def(P′) < def(P)`). A hypothesis, never an axiom. -/
def DLRC (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods →
    (∀ base, InP v agents goods base → 1 ≤ nFrozen v agents goods base) →
      DefLocalAt (RC (A := A) (G := G)) v agents goods

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base base' : G → Option A}

/-! ## Frozen agents on 𝒫 -/

omit [DecidableEq A] [DecidableEq G] in
theorem eq_single_of_length_lt_two {l : List G} {g : G} (h : l.length < 2) (hg : g ∈ l) : l = [g] := by
  match l, h, hg with
  | [a], _, hg => rw [List.mem_singleton.mp hg]
  | _ :: _ :: _, h, _ => exact absurd h (by simp only [List.length_cons]; omega)

omit [DecidableEq G] in
/-- Two agents whose bases in `P′` share the good of a one-good base are the same agent. -/
theorem eq_of_mem_baseOf_single {i w : A} {g : G} (h1 : baseOf goods base' i = [g])
    (h2 : g ∈ baseOf goods base' w) : w = i := by
  have h3 : g ∈ baseOf goods base' i := by rw [h1]; exact List.mem_singleton_self g
  exact Option.some.inj ((mem_baseOf.mp h2).2.symm.trans (mem_baseOf.mp h3).2)

omit [DecidableEq G] in
/-- **On 𝒫, every needed good is the whole base of a listed agent** ((V1): it is not junk; (V2): its base has one
good). -/
theorem exists_frozen_of_NA (hP : InP v agents goods base) {g : G} (hg : NA agents (vbNeeds v goods base) g) :
    ∃ w ∈ agents, baseOf goods base w = [g] := by
  obtain ⟨-, -, hgg, -, -⟩ := id hg
  cases hb : base g with
  | none => exact absurd hg (hP.valid.v1 g (mem_junk.mpr ⟨hgg, hb⟩))
  | some w =>
    refine ⟨w, hP.mem g hgg w hb, ?_⟩
    have hmem : g ∈ baseOf goods base w := mem_baseOf.mpr ⟨hgg, hb⟩
    exact eq_single_of_length_lt_two (Nat.lt_of_not_le fun h2 => hP.valid.v2 w h2 g hmem hg) hmem

omit [DecidableEq G] in
/-- On 𝒫, a frozen agent is listed. -/
theorem mem_agents_of_frozen (hP : InP v agents goods base) {i : A}
    (hF : Frozen agents goods base (vbNeeds v goods base) i) : i ∈ agents := by
  obtain ⟨g, hb, -⟩ := hF
  have hg : g ∈ baseOf goods base i := by rw [hb]; exact List.mem_singleton_self g
  exact hP.mem g (mem_baseOf.mp hg).1 i (mem_baseOf.mp hg).2

omit [DecidableEq G] in
/-- **An agent frozen in `P′` holds the base of an agent frozen in `P`**, if `P ∈ 𝒫` and the needed set is unchanged:
`B′_i = {g}` and `B_w = {g}` for a listed `w` with `g ∈ NA(P)`. -/
theorem frozen'_shape (hP : InP v agents goods base)
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g) {i : A}
    (hi : Frozen agents goods base' (vbNeeds v goods base') i) :
    ∃ g w, w ∈ agents ∧ baseOf goods base' i = [g] ∧ baseOf goods base w = [g] ∧
      NA agents (vbNeeds v goods base) g := by
  obtain ⟨g, hb', hN'⟩ := hi
  have hN := (hNA g).mpr hN'
  obtain ⟨w, hw, hbw⟩ := exists_frozen_of_NA hP hN
  exact ⟨g, w, hw, hb', hbw, hN⟩

omit [DecidableEq G] in
/-- **The free agents stay free** if `P ∈ 𝒫`, the needed set is unchanged and every frozen agent keeps its base. -/
theorem not_frozen'_of_keep (hP : InP v agents goods base)
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)
    (hkeep : ∀ w ∈ agents, Frozen agents goods base (vbNeeds v goods base) w →
      baseOf goods base w = baseOf goods base' w)
    {i : A} (hi : ¬ Frozen agents goods base (vbNeeds v goods base) i) :
    ¬ Frozen agents goods base' (vbNeeds v goods base') i := by
  intro hF'
  obtain ⟨g, w, hw, hb'i, hbw, hN⟩ := frozen'_shape hP hNA hF'
  have hgw : g ∈ baseOf goods base' w := by
    rw [← hkeep w hw ⟨g, hbw, hN⟩, hbw]; exact List.mem_singleton_self g
  have hwi := eq_of_mem_baseOf_single hb'i hgw
  exact hi (hwi ▸ ⟨g, hbw, hN⟩)

omit [DecidableEq G] in
/-- **The key is unchanged** if `P ∈ 𝒫`, the needed set is unchanged and every changed listed agent is free in `P`
(then it is free in `P′` too, `not_frozen'_of_keep`). -/
theorem key_eq_of_free_changes (hP : InP v agents goods base)
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)
    (hch : ∀ i ∈ agents, baseOf goods base i ≠ baseOf goods base' i →
      ¬ Frozen agents goods base (vbNeeds v goods base) i) :
    key v agents goods base' = key v agents goods base := by
  have hkeep : ∀ w ∈ agents, Frozen agents goods base (vbNeeds v goods base) w →
      baseOf goods base w = baseOf goods base' w :=
    fun w hw hF => Classical.byContradiction fun hne => hch w hw hne hF
  have hb : ∀ i, Frozen agents goods base (vbNeeds v goods base) i → baseOf goods base i = baseOf goods base' i :=
    fun i hF => hkeep i (mem_agents_of_frozen hP hF) hF
  have hiff : ∀ i, Frozen agents goods base (vbNeeds v goods base) i ↔
      Frozen agents goods base' (vbNeeds v goods base') i := by
    intro i
    constructor
    · rintro ⟨g, hbi, hN⟩
      exact ⟨g, (hb i ⟨g, hbi, hN⟩).symm.trans hbi, (hNA g).mp hN⟩
    · intro hF'
      exact Classical.byContradiction fun hF => not_frozen'_of_keep hP hNA hkeep hF hF'
  refine key_eq_iff.mpr ⟨fun g => (hNA g).symm, fun i B => ⟨fun ⟨hF', hB⟩ => ?_, fun ⟨hF, hB⟩ => ?_⟩⟩
  · have hF := (hiff i).mpr hF'
    exact ⟨hF, (hb i hF).trans hB⟩
  · exact ⟨(hiff i).mp hF, (hb i hF).symm.trans hB⟩

/-! ## (T1) and (T2) keep the key -/

omit [DecidableEq G] in
/-- **A (T1) move keeps the key** (on 𝒫): only the free agent `y` changes, and NA is unchanged. -/
theorem moveT1_key (hP : InP v agents goods base) (h : MoveT1 v agents goods base base') :
    key v agents goods base' = key v agents goods base := by
  obtain ⟨y, -, hyf, -, -, hsame, hNA⟩ := h
  refine key_eq_of_free_changes hP hNA fun i hi hne => ?_
  by_cases hiy : i = y
  · exact hiy ▸ hyf
  · exact absurd (hsame i hi hiy) hne

omit [DecidableEq G] in
/-- **A (T2) move keeps the key** (on 𝒫): only agents of `Y`, free in `P`, change, and NA is unchanged. -/
theorem moveT2_key (hP : InP v agents goods base) (h : MoveT2 v agents goods base base') :
    key v agents goods base' = key v agents goods base := by
  obtain ⟨Y, -, -, hYf, -, hsame, hNA⟩ := h
  refine key_eq_of_free_changes hP hNA fun i hi hne => ?_
  by_cases hiY : i ∈ Y
  · exact (hYf i hiY).2
  · exact absurd (hsame i hi hiY) hne

/-! ## (T3) ⊆ (T3⁺), R₁₃ ⊆ R_C -/

omit [DecidableEq G] in
/-- **(T3) ⊆ (T3⁺)** on 𝒫: a (T3) move from `P ∈ 𝒫` is a (T3⁺) move with `W = ∅` and `Y` the helper list. That `x` and
the helper are free in `P′` uses (V1), (V2) of `P`. -/
theorem moveT3_moveT3plus (hP : InP v agents goods base) (h : MoveT3 v agents goods base base') :
    MoveT3plus v agents goods base base' := by
  obtain ⟨x, hx, z, hz, g, hbx, hNAg, hzf, hzg, hbz', H, hH, hHp, hsame, hNA⟩ := h
  have hxF : Frozen agents goods base (vbNeeds v goods base) x := ⟨g, hbx, hNAg⟩
  have hgz : g ∈ baseOf goods base' z := by rw [hbz']; exact List.mem_singleton_self g
  have hxz : x ≠ z := fun e => hzf (e ▸ hxF)
  -- an agent `i ≠ z` frozen in `P′` holds, in `P′`, the base of an agent `w` frozen in `P`; `w = x` would force
  -- `i = z`, so `w` did not move, and `w = i`: `i` is neither `x` nor a helper
  have hfr : ∀ i, i ≠ z → Frozen agents goods base' (vbNeeds v goods base') i → i ≠ x ∧ i ∉ H := by
    intro i hiz hF'
    obtain ⟨g'', w, hw, hb'i, hbw, hN⟩ := frozen'_shape hP hNA hF'
    have hwF : Frozen agents goods base (vbNeeds v goods base) w := ⟨g'', hbw, hN⟩
    by_cases hwx : w = x
    · subst hwx
      have : g = g'' := (List.cons.inj (hbx.symm.trans hbw)).1
      subst this
      exact absurd (eq_of_mem_baseOf_single hb'i hgz).symm hiz
    · have hwz : w ≠ z := fun e => hzf (e ▸ hwF)
      have hwH : w ∉ H := fun hm => (hHp w hm).2.2.2.1 hwF
      have hgw : g'' ∈ baseOf goods base' w := by
        rw [← hsame w hw hwx hwz hwH, hbw]; exact List.mem_singleton_self g''
      have hwi : w = i := eq_of_mem_baseOf_single hb'i hgw
      subst hwi
      exact ⟨hwx, hwH⟩
  have hx' : ¬ Frozen agents goods base' (vbNeeds v goods base') x := fun hF' => (hfr x hxz hF').1 rfl
  -- `W` is empty: a changed agent is `x` (free in `P′`), `z` (free in `P`) or a helper (free in `P`)
  have hW : ∀ w, ¬ ChangedFrozen v agents goods base base' w := by
    rintro w ⟨hw, hne, hF, hF'⟩
    by_cases hwx : w = x
    · exact hx' (hwx ▸ hF')
    by_cases hwz : w = z
    · exact hzf (hwz ▸ hF)
    by_cases hwH : w ∈ H
    · exact (hHp w hwH).2.2.2.1 hF
    exact hne (hsame w hw hwx hwz hwH)
  refine ⟨x, hx, z, hz, hxF, hx', hzf, ⟨g, hbz', (hNA g).mp hNAg⟩, ⟨g, hbz', hzg⟩, H, hH, fun h hhH => ?_,
    fun i hi hix hiz hiH hne => absurd (hsame i hi hix hiz hiH) hne, fun B => ?_, hNA⟩
  · obtain ⟨hha, -, hhz, hhf, hgive⟩ := hHp h hhH
    exact ⟨hha, hhf, fun hF' => (hfr h hhz hF').2 hhH, hgive⟩
  · constructor
    · rintro (e | ⟨w, hw, -⟩)
      · exact Or.inl (hbx.trans (hbz'.symm.trans e))
      · exact absurd hw (hW w)
    · rintro (e | ⟨w, hw, -⟩)
      · exact Or.inl (hbz'.trans (hbx.symm.trans e))
      · exact absurd hw (hW w)

omit [DecidableEq G] in
/-- **R₁₃ ⊆ R_C** on 𝒫. -/
theorem r13_rc (hP : InP v agents goods base) (h : R13 v agents goods base base') : RC v agents goods base base' := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl (moveT3_moveT3plus hP h)))

omit [DecidableEq G] in
/-- **(T3⁺) ∪ (T4) ⊆ R_C.** -/
theorem rc34_rc (h : RC34 v agents goods base base') : RC v agents goods base base' :=
  Or.inr (Or.inr h)

omit [DecidableEq G] in
/-- **R_C ⊆ `RKey ((T3⁺) ∪ (T4))` on min-frozen pairs**: a (T1) or (T2) move keeps the key, a (T3⁺) or (T4) move reaches
a neighbouring key. -/
theorem rc_rKey (hM : MinFrozen v agents goods base) (hM' : MinFrozen v agents goods base')
    (h : RC v agents goods base base') : RKey (RC34 (A := A) (G := G)) v agents goods base base' := by
  rcases h with h | h | h | h
  · exact rKey_of_key_eq (moveT1_key hM.1 h)
  · exact rKey_of_key_eq (moveT2_key hM.1 h)
  · exact rKey_of_move hM hM' (Or.inl h)
  · exact rKey_of_move hM hM' (Or.inr h)

/-! ## DL_RC ⟹ TARGET₄ -/

/-- **At f = 0, DL holds for `RCZ`** (every pair is an `RCZ`-pair there; Theorem Z). -/
theorem defLocalAt_RCZ_of_f0 (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods)
    (hf0 : FewestFrozenZero v agents goods) : DefLocalAt (RCZ (A := A) (G := G)) v agents goods :=
  (defLocalAt_top_of_f0 hag hgd hc hf0).mono fun _ _ _ => Or.inl hf0

/-- **DL_RC (at f ≥ 1) and Theorem Z (at f = 0) give DL for `RCZ`** on every strict profile of every connected k = 4
core. -/
theorem defLocal_RCZ_of_DLRC (h : DLRC A G) : DefLocal (RCZ (A := A) (G := G)) := by
  intro agents goods v hag hgd hc hconn hs
  by_cases hf0 : FewestFrozenZero v agents goods
  · exact defLocalAt_RCZ_of_f0 hag hgd hc hf0
  · refine (h agents goods v hag hgd hc hconn hs fun base hP => ?_).mono fun _ _ hr => Or.inr hr
    exact Nat.pos_of_ne_zero fun h0 => hf0 ⟨base, hP, h0⟩

/-- **The converse**: DL for `RCZ` gives DL_RC (on a profile with `f ≥ 1`, `RCZ` is `RC`). -/
theorem DLRC_of_defLocal_RCZ (h : DefLocal (RCZ (A := A) (G := G))) : DLRC A G := by
  intro agents goods v hag hgd hc hconn hs hf
  refine (h agents goods v hag hgd hc hconn hs).mono fun _ _ hr => hr.resolve_left ?_
  rintro ⟨base, hP, h0⟩
  have := hf base hP
  omega

/-- **DL_RC is exactly DL for `RCZ`.** -/
theorem dlrc_iff_defLocal_RCZ : DLRC A G ↔ DefLocal (RCZ (A := A) (G := G)) :=
  ⟨defLocal_RCZ_of_DLRC, DLRC_of_defLocal_RCZ⟩

/-- **DL_RC ⟹ C₄ᵐⁱⁿ (removal-only) on connected cores with a 4-good agent.** -/
theorem C4minROConn_of_DLRC (h : DLRC A G) : C4minROConn A G :=
  C4minROConn_of_defLocal (defLocal_RCZ_of_DLRC h)

/-- **DL_RC ⟹ TARGET₄**: with Theorem Z at f = 0, every instance with at least one agent and at most four relevant goods
per agent has an EFX₀ allocation (`target4_of_defLocal` for `RCZ`). DL_RC is a hypothesis, not an axiom. -/
theorem target4_of_DLRC (I : Inst) (hn : 0 < I.n) (hDL : DLRC (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_defLocal I hn (defLocal_RCZ_of_DLRC hDL) h

/-- **DL₁₃ ⟹ DL_RC** (R₁₃ ⊆ R_C on 𝒫, and DL only looks at min-frozen pairs). DL₁₃ is refuted (K4.DL2.T13); this
records that R_C extends R₁₃. -/
theorem DLRC_of_DL13 (h : DL13 A G) : DLRC A G :=
  fun agents goods v hag hgd hc hconn hs hf =>
    (h agents goods v hag hgd hc hconn hs hf).mono_minFrozen fun _ _ hM _ hr => r13_rc hM.1 hr

/-! ## DL_RC ⟹ DL on the key graph for (T3⁺) ∪ (T4) -/

/-- **DL for R_C ⟹ DL for `RKey ((T3⁺) ∪ (T4))`**, on one instance (`rc_rKey`). -/
theorem defLocalAt_rKey_of_defLocalAt_RC (h : DefLocalAt (RC (A := A) (G := G)) v agents goods) :
    DefLocalAt (RKey (RC34 (A := A) (G := G))) v agents goods :=
  h.mono_minFrozen fun _ _ hM hM' hr => rc_rKey hM hM' hr

/-- **DL_RC ⟹ DefLocal (RKey ((T3⁺) ∪ (T4)))**: at `f = 0` by Theorem Z, at `f ≥ 1` by `rc_rKey`. -/
theorem defLocal_rKey_of_DLRC (h : DLRC A G) : DefLocal (RKey (RC34 (A := A) (G := G))) := by
  intro agents goods v hag hgd hc hconn hs
  by_cases hf0 : FewestFrozenZero v agents goods
  · exact (defLocalAt_top_of_f0 hag hgd hc hf0).mono fun _ _ _ => Or.inl hf0
  · refine defLocalAt_rKey_of_defLocalAt_RC (h agents goods v hag hgd hc hconn hs fun base hP => ?_)
    exact Nat.pos_of_ne_zero fun h0 => hf0 ⟨base, hP, h0⟩

/-- **DL_RC ⟹ DLKey ((T3⁺) ∪ (T4))**: DL on the key graph for the moves that change the key is weaker than DL_RC (through
`DefLocal (RKey …)` and `DLKey_of_defLocal_rKey`). -/
theorem DLKey_of_DLRC (h : DLRC A G) : DLKey (RC34 (A := A) (G := G)) :=
  DLKey_of_defLocal_rKey (defLocal_rKey_of_DLRC h)

/-- A neighbouring key of R_C with a smaller least deficit is a neighbouring key of (T3⁺) ∪ (T4): a (T1) or (T2) move
stays in its key, and `def*(κ) < def*(κ)` is impossible. -/
theorem keyNbr_RC34_of_RC {κ κ' : Key A G} (h : KeyNbr (RC (A := A) (G := G)) v agents goods κ κ')
    (hlt : KeyDeficitLT v agents goods κ' κ) : KeyNbr (RC34 (A := A) (G := G)) v agents goods κ κ' := by
  obtain ⟨b, b', hM, hk, hM', hk', hr⟩ := h
  have hne : κ' ≠ κ := by
    rintro rfl
    obtain ⟨d, hd, hnd⟩ := hlt
    exact hnd hd
  rcases hr with hr | hr | hr
  · exact absurd (hk' ▸ hk ▸ moveT1_key hM.1 hr) hne
  · exact absurd (hk' ▸ hk ▸ moveT2_key hM.1 hr) hne
  · exact ⟨b, b', hM, hk, hM', hk', hr⟩

/-- **DL on the key graph is the same for R_C and for (T3⁺) ∪ (T4).** -/
theorem dlKey_RC_iff : DLKey (RC (A := A) (G := G)) ↔ DLKey (RC34 (A := A) (G := G)) := by
  constructor
  · intro h agents goods v hag hgd hc hconn hs hf κ hκ hpos
    obtain ⟨κ', hN, hlt⟩ := h agents goods v hag hgd hc hconn hs hf κ hκ hpos
    exact ⟨κ', keyNbr_RC34_of_RC hN hlt, hlt⟩
  · exact DLKey.mono fun _ _ _ _ _ _ _ hr => rc34_rc hr

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.eq_single_of_length_lt_two
#print axioms EFX.C4min.eq_of_mem_baseOf_single
#print axioms EFX.C4min.exists_frozen_of_NA
#print axioms EFX.C4min.mem_agents_of_frozen
#print axioms EFX.C4min.frozen'_shape
#print axioms EFX.C4min.not_frozen'_of_keep
#print axioms EFX.C4min.key_eq_of_free_changes
#print axioms EFX.C4min.moveT1_key
#print axioms EFX.C4min.moveT2_key
#print axioms EFX.C4min.moveT3_moveT3plus
#print axioms EFX.C4min.r13_rc
#print axioms EFX.C4min.rc34_rc
#print axioms EFX.C4min.rc_rKey
#print axioms EFX.C4min.defLocalAt_RCZ_of_f0
#print axioms EFX.C4min.defLocal_RCZ_of_DLRC
#print axioms EFX.C4min.DLRC_of_defLocal_RCZ
#print axioms EFX.C4min.dlrc_iff_defLocal_RCZ
#print axioms EFX.C4min.C4minROConn_of_DLRC
#print axioms EFX.C4min.target4_of_DLRC
#print axioms EFX.C4min.DLRC_of_DL13
#print axioms EFX.C4min.defLocalAt_rKey_of_defLocalAt_RC
#print axioms EFX.C4min.defLocal_rKey_of_DLRC
#print axioms EFX.C4min.DLKey_of_DLRC
#print axioms EFX.C4min.keyNbr_RC34_of_RC
#print axioms EFX.C4min.dlKey_RC_iff
