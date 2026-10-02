import EFX.KeyFrame

/-!
# The moves (T2), (T4), (T3⁺) and the relation R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4) (ledger K4.DL2.RC.LEAN)

The conjecture DL_RT4, DL for the fixed relation R_T4 = (T1) ∪ (T2) ∪ (T3) ∪ (T4) (ledger K4.DL2.RT4, REFUTED; data
K4.DL2.RT4E), fails at n = 5, f = 3 (`results/k4_rt4/n5b_FAILURES.md`, `results/k4_rt4/n5c_FAILURES.md`, merged with
PR #86), and so does its key-graph form with single (T3)/(T4) edges (ledger K4.DL13.KEY, REFUTED): at those states every
repair is a role swap whose good passes through a frozen intermediary (frozen `x` frees `g`, frozen `y` moves from `h`
to `g`, free `z` takes `h`), which is neither a (T3) move (`z` does not take `x`'s good) nor a (T4) move (`x` and `z`
change roles). Ledger K4.DL2.RC (CONJECTURE) widens (T3) to **(T3⁺), the frozen-chain role swap**; (T3) is its case
`W = ∅`. This file writes the moves (T2), (T4), (T3⁺) as relations on pre-allocations, in the style of `MoveT1`,
`MoveT3` (`EFX/DL13.lean`), the relations **R_T4** and **R_C**, the conjecture **DL_RC**, and connects it to TARGET₄
and to the key frame of `EFX/KeyFrame.lean`. DL_RC is a hypothesis of every theorem here, never an axiom; nothing of
the model is redefined.

**Definitions** (P = `base`, P′ = `base'`; `B_i = baseOf goods base i`, `N_i(B_i) = vbNeeds v goods base i`,
`NA = NA agents (vbNeeds v goods base)`, frozen = `Frozen agents goods base (vbNeeds v goods base)`, the same with
`base'` in P′; a listed agent is *changed* if its base on `goods` differs, `B_i ≠ B′_i`).
- `MoveT2` (**(T2) rotation**, `k4/dl2.md` §3): a set `Y` of agents free in P (`|Y| ≥ 2`) takes new bases
  `B′_y ⊆ (J ∪ ⋃_{w ∈ Y} B_w) ∩ R_y`, pairwise disjoint, everybody else unchanged, the needed set unchanged.
- `MoveT4` (**(T4)**, ledger K4.DL2.T134, K4.DL2.RT4E): every agent whose base changes is frozen in P and in P′, and
  NA(P′) = NA(P). It contains the identity (`moveT4_refl`); on 𝒫 it reads "the frozen agents permute their singleton
  bases, every other base unchanged".
- `ChangedFrozen` (the set `W` of (T3⁺)): the changed listed agents frozen in P and in P′.
- `MoveT3plus` (**(T3⁺) the frozen-chain role swap**, as defined in ledger K4.DL2.RC): NA(P′) = NA(P); exactly one
  changed agent `x` is frozen in P and free in P′; exactly one changed agent `z` is free in P and frozen in P′, and `z`
  needs its new good in P; `W` = the changed agents frozen in both; `Y` = the changed agents free in both, with
  `|Y| ≤ 1`, each giving up a good; the bases of `W ∪ {z}` in P′ are exactly the bases of `W ∪ {x}` in P.
- `RT4` (**R_T4**, ledger K4.DL2.RT4) = `MoveT1 ∪ MoveT2 ∪ MoveT3 ∪ MoveT4`, and `DLRT4` (**Conjecture DL_RT4**,
  REFUTED at n = 5): `DefLocalAt RT4` at `f ≥ 1`, as `DLRC`.
- `RC` (**R_C**, ledger K4.DL2.RC) = `MoveT1 ∪ MoveT2 ∪ MoveT3plus ∪ MoveT4`; `RC34` = `MoveT3plus ∪ MoveT4`, the moves
  of R_C that may change the key; `RCZ` = every pair on a profile with `f = 0` (`FewestFrozenZero`), R_C otherwise
  (as `R13Z`).
- `DLRC` (**Conjecture DL_RC**, ledger K4.DL2.RC): `DefLocalAt RC` on every strict profile of every connected k = 4
  core whose fewest frozen agents is `f ≥ 1` (as `DL13`).

**Results.**
- `moveT3_moveT3plus`, `r13_rc`, `rt4_rc`: on 𝒫, **(T3) ⊆ (T3⁺)** (with `W = ∅`, `Y = H`), **R₁₃ ⊆ R_C** and
  **R_T4 ⊆ R_C** (the inclusion K4.DL2.RC claims); `DLRC_of_DL13`, `DLRC_of_DLRT4`. DL₁₃ and DL_RT4 are refuted
  (K4.DL2.T13, K4.DL2.RT4), so these two implications are vacuous; the inclusions are the content.
  `moveT3_of_moveT3plus`, `moveT3_iff`: (T3⁺) with `W = ∅` is (T3), so on 𝒫 (T3) is exactly the case `W = ∅` of (T3⁺).
- `minFrozen_of_NA_eq`: on 𝒫, a pre-allocation with the needed set of a min-frozen one is min-frozen (every move of R_C
  keeps NA, so an R_C move from a min-frozen P to a Q ∈ 𝒫 lands on a min-frozen Q). `moveT3plus_of_inP` builds a (T3⁺)
  move from `P ∈ 𝒫` and NA(P′) = NA(P), deriving the four frozen-status clauses of `x` and `z` from the needed goods in
  their bases (`frozen_of_mem_NA`, `not_frozen_of_forall`), as `moveT1_of_inP` does for (T1).
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
   `RTr` asks only that every changed agent be free in P and P′). The two readings give the same R_C up to pairs with
   the same bases on `goods` (if two or more agents of `Y` change, they form a (T2) move of the strict reading; if one
   does, a (T1) move), and such a pair never lowers the deficit, so DL_RC is the same (an argument, not formalized).
2. (T4): LEDGER K4.DL2.T134, "every agent whose base changes is frozen in P and in P′ and NA(P′) = NA(P)". Lean: the
   same, for listed agents, word for word. The pair (P, P) is a (T4) move (`moveT4_refl`); it never lowers the deficit.
   The ledger's gloss "the frozen agents permute their singleton bases" holds on 𝒫 (an argument, not formalized): there
   every needed good is the one-good base of exactly one listed agent (`exists_frozen_of_NA`), and a changed agent has a
   one-good base of a needed good in P and in P′.
3. (T3⁺): ledger K4.DL2.RC's definition, clause by clause. "Exactly one changed agent `x` frozen in P and free in P′":
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
   used here (a (T1) or (T2) move from a pre-allocation of 𝒫 keeps the key); the converse of the text (same key ⟹ a
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
the needed set `NA` is unchanged. (T4) contains the identity (`moveT4_refl`: no base changes). The gloss "the frozen
agents permute their singleton bases, every other base unchanged" holds on 𝒫, where every needed good is the one-good
base of exactly one listed agent; for arbitrary base maps (T4) is only the condition above. -/
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

/-- **The relation R_T4** = (T1) ∪ (T2) ∪ (T3) ∪ (T4) of the conjecture DL_RT4 (ledger K4.DL2.RT4). -/
def RT4 : Nbhd A G := fun v agents goods base base' =>
  MoveT1 v agents goods base base' ∨ MoveT2 v agents goods base base' ∨
    MoveT3 v agents goods base base' ∨ MoveT4 v agents goods base base'

/-- **Conjecture DL_RT4** (ledger K4.DL2.RT4, **REFUTED** at n = 5, f = 3, `results/k4_rt4/n5b_FAILURES.md`): on every
strict profile of every connected k = 4 core whose fewest frozen agents is at least 1, DL for R_T4 (`DefLocalAt RT4`).
Stated only to record `DLRC_of_DLRT4`; never an axiom, never a hypothesis of a result used elsewhere. -/
def DLRT4 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods →
    (∀ base, InP v agents goods base → 1 ≤ nFrozen v agents goods base) →
      DefLocalAt (RT4 (A := A) (G := G)) v agents goods

/-- **The relation R_C** = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4) (ledger K4.DL2.RC). -/
def RC : Nbhd A G := fun v agents goods base base' =>
  MoveT1 v agents goods base base' ∨ MoveT2 v agents goods base base' ∨
    MoveT3plus v agents goods base base' ∨ MoveT4 v agents goods base base'

/-- **(T3⁺) ∪ (T4)**: the moves of R_C that may change the key. -/
def RC34 : Nbhd A G := fun v agents goods base base' =>
  MoveT3plus v agents goods base base' ∨ MoveT4 v agents goods base base'

/-- Every pair of pre-allocations on a profile whose fewest frozen agents is 0, R_C on the others (as `R13Z`). -/
def RCZ : Nbhd A G := fun v agents goods base base' =>
  FewestFrozenZero v agents goods ∨ RC v agents goods base base'

/-- **Conjecture DL_RC** (ledger K4.DL2.RC, open): on every strict profile of every connected k = 4 core whose fewest
frozen agents is at least 1, DL for R_C (`DefLocalAt RC`: if `ω ≥ 1`, every min-frozen `P` with `def(P) > 0`, `+∞`
included, has a min-frozen `P′` with `RC P P′` and `def(P′) < def(P)`). A hypothesis, never an axiom. -/
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

omit [DecidableEq G] in
/-- **A pre-allocation of 𝒫 with the needed set of a min-frozen one is min-frozen.** On 𝒫 the number of frozen agents
is `|NA|` (`numFrozen_eq`), so it depends only on the needed set. Every move of R_C keeps NA, so an R_C move from a
min-frozen `P` to a `P′ ∈ 𝒫` reaches a min-frozen `P′`. -/
theorem minFrozen_of_NA_eq (hag : agents.Nodup) (hgd : goods.Nodup) (hM : MinFrozen v agents goods base)
    (hP' : InP v agents goods base')
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g) :
    MinFrozen v agents goods base' := by
  have e : nFrozen v agents goods base' = nFrozen v agents goods base := by
    unfold nFrozen
    rw [numFrozen_eq hP'.valid hag hgd hP'.mem, numFrozen_eq hM.1.valid hag hgd hM.1.mem]
    unfold numNA
    congr 1
    funext g
    exact decide_eq_decide.mpr (hNA g).symm
  exact ⟨hP', fun b hb => e ▸ hM.2 b hb⟩

omit [DecidableEq G] in
/-- **On 𝒫, an agent whose base holds a needed good is frozen** (its base is that good alone, `exists_frozen_of_NA`). -/
theorem frozen_of_mem_NA (hP : InP v agents goods base) {i : A} {g : G} (hg : g ∈ baseOf goods base i)
    (hN : NA agents (vbNeeds v goods base) g) : Frozen agents goods base (vbNeeds v goods base) i := by
  obtain ⟨w, -, hw⟩ := exists_frozen_of_NA hP hN
  have hwi : i = w := eq_of_mem_baseOf_single hw hg
  exact ⟨g, hwi ▸ hw, hN⟩

omit [DecidableEq G] in
/-- An agent whose base holds no good of `NA(P)` is free in `P`, and in `P′` if `NA(P′) = NA(P)` (for any base maps). -/
theorem not_frozen_of_forall
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g) {i : A}
    (h : ∀ g ∈ baseOf goods base' i, ¬ NA agents (vbNeeds v goods base) g) :
    ¬ Frozen agents goods base' (vbNeeds v goods base') i := by
  rintro ⟨y, hb, hN⟩
  exact h y (by rw [hb]; exact List.mem_singleton_self y) ((hNA y).mpr hN)

omit [DecidableEq G] in
/-- **Building a (T3⁺) move on 𝒫** (in the style of `moveT1_of_inP`): from `P ∈ 𝒫` and `NA(P′) = NA(P)`, the four
frozen-status clauses of `x` and `z` follow from the needed goods in their bases: `x` holds a needed good in `P` and
none in `P′`; `z` holds none in `P` and has `B′_z = {g}` with `g ∈ N_z(B_z)`. The clauses on `Y`, on the other changed
agents and on the bases of `W` are those of `MoveT3plus`. -/
theorem moveT3plus_of_inP (hP : InP v agents goods base)
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)
    {x z : A} (hx : x ∈ agents) (hz : z ∈ agents)
    (hxN : ∃ g ∈ baseOf goods base x, NA agents (vbNeeds v goods base) g)
    (hxN' : ∀ g ∈ baseOf goods base' x, ¬ NA agents (vbNeeds v goods base) g)
    (hzN : ∀ g ∈ baseOf goods base z, ¬ NA agents (vbNeeds v goods base) g)
    {g : G} (hbz' : baseOf goods base' z = [g]) (hzg : vbNeeds v goods base z g)
    {Y : List A} (hY : Y.length ≤ 1)
    (hYp : ∀ h ∈ Y, h ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧
      ¬ Frozen agents goods base' (vbNeeds v goods base') h ∧ ∃ g' ∈ baseOf goods base h, g' ∉ baseOf goods base' h)
    (hcl : ∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ Y → baseOf goods base i ≠ baseOf goods base' i →
      Frozen agents goods base (vbNeeds v goods base) i ∧ Frozen agents goods base' (vbNeeds v goods base') i)
    (hB : ∀ B : List G,
      (baseOf goods base' z = B ∨ ∃ w, ChangedFrozen v agents goods base base' w ∧ baseOf goods base' w = B) ↔
      (baseOf goods base x = B ∨ ∃ w, ChangedFrozen v agents goods base base' w ∧ baseOf goods base w = B)) :
    MoveT3plus v agents goods base base' := by
  obtain ⟨gx, hgx, hNx⟩ := hxN
  have hNg : NA agents (vbNeeds v goods base) g := ⟨z, hz, hzg⟩
  exact ⟨x, hx, z, hz, frozen_of_mem_NA hP hgx hNx, not_frozen_of_forall hNA hxN',
    not_frozen_of_forall (fun _ => Iff.rfl) hzN, ⟨g, hbz', (hNA g).mp hNg⟩, ⟨g, hbz', hzg⟩, Y, hY, hYp, hcl, hB, hNA⟩

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
/-- A (T3) move from `P ∈ 𝒫` is a (T3⁺) move with `W = ∅` and `Y` the helper list. That `x` and the helper are free in
`P′` uses (V1), (V2) of `P`. -/
theorem moveT3_moveT3plus_W (hP : InP v agents goods base) (h : MoveT3 v agents goods base base') :
    MoveT3plus v agents goods base base' ∧ ∀ w, ¬ ChangedFrozen v agents goods base base' w := by
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
  refine ⟨⟨x, hx, z, hz, hxF, hx', hzf, ⟨g, hbz', (hNA g).mp hNAg⟩, ⟨g, hbz', hzg⟩, H, hH, fun h hhH => ?_,
    fun i hi hix hiz hiH hne => absurd (hsame i hi hix hiz hiH) hne, fun B => ?_, hNA⟩, hW⟩
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
/-- **(T3) ⊆ (T3⁺)** on 𝒫 (with `W = ∅` and `Y` the helper list). -/
theorem moveT3_moveT3plus (hP : InP v agents goods base) (h : MoveT3 v agents goods base base') :
    MoveT3plus v agents goods base base' :=
  (moveT3_moveT3plus_W hP h).1

omit [DecidableEq G] in
/-- **(T3⁺) with `W = ∅` is (T3)** (for any base maps): then `B′_z = B_x = {g}`, the agents of `Y` are the helpers,
and every other agent keeps its base. With `moveT3_moveT3plus`, (T3) is exactly the case `W = ∅` of (T3⁺) on 𝒫
(`moveT3_iff`). -/
theorem moveT3_of_moveT3plus (h : MoveT3plus v agents goods base base')
    (hW : ∀ w, ¬ ChangedFrozen v agents goods base base' w) : MoveT3 v agents goods base base' := by
  obtain ⟨x, hx, z, hz, hxF, hx', hzf, hzF', ⟨g, hbz', hzg⟩, Y, hY, hYp, hcl, hB, hNA⟩ := h
  have hzx : baseOf goods base' z = baseOf goods base x := by
    rcases (hB (baseOf goods base x)).mpr (Or.inl rfl) with e | ⟨w, hw, -⟩
    · exact e
    · exact absurd hw (hW w)
  have hbx : baseOf goods base x = [g] := hzx.symm.trans hbz'
  obtain ⟨g', hbx', hN'⟩ := hxF
  have hgg : g' = g := (List.cons.inj (hbx'.symm.trans hbx)).1
  subst hgg
  refine ⟨x, hx, z, hz, g', hbx, hN', hzf, hzg, hbz', Y, hY, fun h hhY => ?_, fun i hi hix hiz hiY => ?_, hNA⟩
  · obtain ⟨hha, hhf, hhf', hgive⟩ := hYp h hhY
    exact ⟨hha, fun e => hhf (e ▸ ⟨g', hbx', hN'⟩), fun e => hhf' (e ▸ hzF'), hhf, hgive⟩
  · refine Classical.byContradiction fun hne => ?_
    obtain ⟨hF, hF'⟩ := hcl i hi hix hiz hiY hne
    exact hW i ⟨hi, hne, hF, hF'⟩

omit [DecidableEq G] in
/-- **On 𝒫, (T3) is exactly (T3⁺) with `W = ∅`.** -/
theorem moveT3_iff (hP : InP v agents goods base) :
    MoveT3 v agents goods base base' ↔
      MoveT3plus v agents goods base base' ∧ ∀ w, ¬ ChangedFrozen v agents goods base base' w :=
  ⟨moveT3_moveT3plus_W hP, fun h => moveT3_of_moveT3plus h.1 h.2⟩

omit [DecidableEq G] in
/-- **R₁₃ ⊆ R_C** on 𝒫. -/
theorem r13_rc (hP : InP v agents goods base) (h : R13 v agents goods base base') : RC v agents goods base base' := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl (moveT3_moveT3plus hP h)))

omit [DecidableEq G] in
/-- **R_T4 ⊆ R_C** on 𝒫 (the inclusion ledger K4.DL2.RC claims): (T1), (T2), (T4) are moves of both, and a (T3) move
from `P ∈ 𝒫` is a (T3⁺) move (`moveT3_moveT3plus`). -/
theorem rt4_rc (hP : InP v agents goods base) (h : RT4 v agents goods base base') : RC v agents goods base base' := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (moveT3_moveT3plus hP h)))
  · exact Or.inr (Or.inr (Or.inr h))

omit [DecidableEq G] in
/-- **(T4) contains the identity**: no base changes, NA is the same. -/
theorem moveT4_refl : MoveT4 v agents goods base base :=
  ⟨fun _ _ h => absurd rfl h, fun _ => Iff.rfl⟩

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

/-- **DL_RT4 ⟹ DL_RC** (R_T4 ⊆ R_C on 𝒫, `rt4_rc`, and DL only looks at min-frozen pairs). DL_RT4 is refuted
(ledger K4.DL2.RT4, at n = 5, f = 3), so this implication is vacuous; the inclusion `rt4_rc` is the content: every
repair DL_RT4 finds is a repair of DL_RC. -/
theorem DLRC_of_DLRT4 (h : DLRT4 A G) : DLRC A G :=
  fun agents goods v hag hgd hc hconn hs hf =>
    (h agents goods v hag hgd hc hconn hs hf).mono_minFrozen fun _ _ hM _ hr => rt4_rc hM.1 hr

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
#print axioms EFX.C4min.minFrozen_of_NA_eq
#print axioms EFX.C4min.frozen_of_mem_NA
#print axioms EFX.C4min.not_frozen_of_forall
#print axioms EFX.C4min.moveT3plus_of_inP
#print axioms EFX.C4min.moveT1_key
#print axioms EFX.C4min.moveT2_key
#print axioms EFX.C4min.moveT3_moveT3plus_W
#print axioms EFX.C4min.moveT3_moveT3plus
#print axioms EFX.C4min.moveT3_of_moveT3plus
#print axioms EFX.C4min.moveT3_iff
#print axioms EFX.C4min.r13_rc
#print axioms EFX.C4min.rt4_rc
#print axioms EFX.C4min.moveT4_refl
#print axioms EFX.C4min.rc34_rc
#print axioms EFX.C4min.rc_rKey
#print axioms EFX.C4min.defLocalAt_RCZ_of_f0
#print axioms EFX.C4min.defLocal_RCZ_of_DLRC
#print axioms EFX.C4min.DLRC_of_defLocal_RCZ
#print axioms EFX.C4min.dlrc_iff_defLocal_RCZ
#print axioms EFX.C4min.C4minROConn_of_DLRC
#print axioms EFX.C4min.target4_of_DLRC
#print axioms EFX.C4min.DLRC_of_DL13
#print axioms EFX.C4min.DLRC_of_DLRT4
#print axioms EFX.C4min.defLocalAt_rKey_of_defLocalAt_RC
#print axioms EFX.C4min.defLocal_rKey_of_DLRC
#print axioms EFX.C4min.DLKey_of_DLRC
#print axioms EFX.C4min.keyNbr_RC34_of_RC
#print axioms EFX.C4min.dlKey_RC_iff
