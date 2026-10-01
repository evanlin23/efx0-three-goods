import EFX.DL13

/-!
# The key frame: DL on the key graph ⟹ TARGET₄, for any move relation (`k4/dl13.md` §2.3; ledger K4.DL2.KEY.LEAN)

The Remark "DL on the key graph" of `k4/dl13.md` §2.3 (merged in PR #75) says that a descent for TARGET₄
needs only the least deficits of the *keys*: if every key with a positive least deficit has a neighbouring key with a
smaller one, the deficit descends. This file writes that frame for an **arbitrary** move relation `M` on
pre-allocations (`M : Nbhd A G`, as in `EFX/C4minDescent.lean`), so that the proof workstreams can plug in any set of
moves. `DLKey M` is a hypothesis of every theorem here, never an axiom. Everything is stated with the definitions of
`EFX/C4min.lean`, `EFX/C4minDescent.lean` and `EFX/DL13.lean` (`InP`, `MinFrozen`, `nFrozen`, `NA`, `Frozen`,
`vbNeeds`, `DeficitLE`, `DefLocalAt`, `DefLocal`, `FewestFrozenZero`); nothing of the model is redefined.

**Definitions** (P = `base`; NA, frozen agents and bases with the value-based needs `vbNeeds`, as in `EFX/DL13.lean`).
- `Key A G` and `key P` (**the key κ(P)**): the needed set `NA(P)` (a predicate on goods) and the frozen agents with
  their bases (the predicate "`i` is frozen in P and `B_i = B`" on pairs `(i, B)`). Two pre-allocations have the same
  key iff they have the same needed set, the same frozen agents, and every frozen agent the same base (`key_eq_iff`).
- `KeyDeficitLE κ d` (**def\*(κ) ≤ d**): some min-frozen P with `κ(P) = κ` has `def(P) ≤ d`. So def\*(κ) is the least
  deficit of a min-frozen P of key κ, in `ℤ ∪ {+∞}` (`+∞` if every such P has `def = +∞`, or if no min-frozen P has key
  κ). `KeyDeficitLT κ′ κ` (**def\*(κ′) < def\*(κ)**): some integer `d` has `def*(κ′) ≤ d` and not `def*(κ) ≤ d`, the
  order of `DeficitLT` (`EFX/C4minDescent.lean`).
- `KeyNbr M κ κ′` (**κ′ ∈ N_M(κ)**): some min-frozen P of key κ and some min-frozen Q of key κ′ have `M P Q`.
- `RKey M` (**R_key**): `RKey M P P′` iff the profile has `f = 0` (`FewestFrozenZero`, the clause of `R13Z`), or
  `κ(P′) ∈ N_M(κ(P))`, or `κ(P′) = κ(P)`.
- `DLKeyAt M` (one instance) and `DLKey M` (**DL on the key graph**): on every strict profile of every connected k = 4
  core whose fewest frozen agents is `f ≥ 1` (every pre-allocation of 𝒫 has a frozen agent, as in `DL13`), every key κ
  of a min-frozen P with `ω ≥ 1` and with `def*(κ) > 0` (`¬ def*(κ) ≤ 0`, `+∞` included) has a key `κ′ ∈ N_M(κ)` with
  `def*(κ′) < def*(κ)`.

**Results.**
- (i) `defLocalAt_rKey_of_dlKeyAt`, `defLocal_rKey_of_DLKey`: **DLKey M ⟹ DefLocal (RKey M)**. If
  `def(P) > def*(κ(P))`, a min-frozen state of the same key is better; otherwise `def*(κ(P)) > 0` and a better state
  lies in a neighbouring key. At `f = 0` Theorem Z gives DL for every pair (`defLocalAt_top_of_f0`).
- (ii) `C4minROConn_of_DLKey`, `target4_of_DLKey`: **DLKey M ⟹ TARGET₄**, for every `M` (`target4_of_defLocal`).
- (iii) `KeyNbr.mono`, `DLKey.mono`: **M ⊆ M′ ⟹ (DLKey M ⟹ DLKey M′)**; it suffices that `M ⊆ M′` on pairs of
  min-frozen pre-allocations (`N_M` only looks at those).
- The converse of (i): `dlKeyAt_of_defLocalAt_rKey`, `DLKey_of_defLocal_rKey`, `dlKey_iff_defLocal_rKey`:
  **DLKey M ⟺ DefLocal (RKey M)** (at `f ≥ 1` on one instance; on all profiles with the `f = 0` clause), so the key
  frame loses nothing against DL for `RKey M`.
- Plugging in a move relation: `rKey_of_move` (`M ⊆ RKey M` on min-frozen pairs), `DefLocalAt.mono_minFrozen` (DL for
  `R` ⟹ DL for `R′` if `R ⊆ R′` on min-frozen pairs), and `dlKeyAt_of_defLocalAt_keep`: if `K` keeps the key on
  min-frozen pairs, DL for `K ∪ M` at `f ≥ 1` gives `DLKeyAt M` (`EFX/MovesC.lean` does this with `K = (T1) ∪ (T2)`,
  through `rc_rKey`).
- `exists_least_keyDeficit`, `exists_keyMin`: def\*(κ) is attained (a min-frozen P of key κ with
  `def(P) = def*(κ)`), from `deficitLE_lower`.

**Faithfulness** (paper statement / Lean statement / why they agree).
- *Paper* (`k4/dl13.md` §2.3, Remark): "Write κ(P) for the key of P (needed set, frozen agents, their goods), def\*(κ)
  for the least deficit of a min-frozen P with key κ, and N(κ) for the keys reached by one (T3) or (T4) move from some
  state of κ. Let R_key(P, P′) hold iff κ(P′) ∈ N(κ(P)) ∪ {κ(P)} (and every pair at f = 0). Then … DL_{R_key} is
  equivalent to DL on the key graph: every key κ with def\*(κ) > 0 has a neighbour κ′ ∈ N(κ) with def\*(κ′) < def\*(κ).
  (If def(P) > def\*(κ(P)), a state of the same key is better; otherwise a better state lies in a neighbouring key.)"
- *Lean*: `RKey M` is R_key with the moves `M` in place of (T3) ∪ (T4) (a parameter; `EFX/MovesC.lean` instantiates it
  with (T3⁺) ∪ (T4)); `DLKey M` is DL on the key graph, at `f ≥ 1`; `dlKey_iff_defLocal_rKey` is the equivalence, and
  `target4_of_DLKey` the consequence for TARGET₄.
- *Why they agree*: the key is the paper's (𝒩, F, φ): `needed` is 𝒩 = NA(P), and the frozen part records F with each
  frozen agent's base, which is `{φ(x)}`. On 𝒫 the needed set is the set of the frozen agents' goods ((V1), (V2)), so
  the first component is determined by the second; it is kept because the paper lists it. def\*, N and R_key are
  word for word, with the min-frozen class as the states (the paper's "state" is a min-frozen P).

**Choices where the prose leaves room.**
1. *Which keys.* "Every key κ" is read as every key of a min-frozen P (a key of no min-frozen P has `def* = +∞` and
   no neighbours, so the statement would be false for it). The premise `ω ≥ 1` of `DefLocalAt` is kept; it is
   automatic (`def*(κ) > 0` forces `ω ≥ 1`, `omegaP_pos`), so it does not strengthen `DLKey`.
2. *f ≥ 1.* As in `DL13`: every pre-allocation of 𝒫 has a frozen agent (the negation of `FewestFrozenZero`). At
   `f = 0` the key is empty and Theorem Z answers; `RKey`'s `f = 0` clause is `R13Z`'s.
3. *Deficits in `ℤ ∪ {+∞}`* are read through `DeficitLE` as in `EFX/C4minDescent.lean`: `def*(κ) ≤ d` is a predicate,
   and `def*(κ′) < def*(κ)` says that some integer `d` bounds `def*(κ′)` and not `def*(κ)`.
4. *The key as a value*: `Key A G` has a predicate on goods and a predicate on (agent, base) pairs, so key equality is
   equality of predicates (`propext`, `funext`); `key_eq_iff` restates it pointwise.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Keys, least deficits of keys, the key graph -/

/-- A **key**: a needed set (a predicate on goods) and the frozen agents with their bases (a predicate on pairs of an
agent and a base). -/
structure Key (A G : Type) where
  needed : G → Prop
  frozen : A → List G → Prop

/-- **The key κ(P)** of a pre-allocation: its needed set `NA(P)` and its frozen agents with their bases (`(i, B)` is in the
frozen part iff `i` is frozen in `P` and `B_i = B`). -/
def key (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Key A G where
  needed := fun g => NA agents (vbNeeds v goods base) g
  frozen := fun i B => Frozen agents goods base (vbNeeds v goods base) i ∧ baseOf goods base i = B

/-- **def\*(κ) ≤ d**: some min-frozen pre-allocation of key κ has `def ≤ d`. -/
def KeyDeficitLE (v : A → G → Nat) (agents : List A) (goods : List G) (κ : Key A G) (d : Int) : Prop :=
  ∃ base, MinFrozen v agents goods base ∧ key v agents goods base = κ ∧ DeficitLE v agents goods base d

/-- **def\*(κ′) < def\*(κ)**, in `ℤ ∪ {+∞}`: some integer `d` has `def*(κ′) ≤ d` and not `def*(κ) ≤ d`. -/
def KeyDeficitLT (v : A → G → Nat) (agents : List A) (goods : List G) (κ' κ : Key A G) : Prop :=
  ∃ d : Int, KeyDeficitLE v agents goods κ' d ∧ ¬ KeyDeficitLE v agents goods κ d

/-- **κ′ ∈ N_M(κ)**: some min-frozen `P` of key κ and some min-frozen `Q` of key κ′ have `M P Q`. -/
def KeyNbr (M : Nbhd A G) (v : A → G → Nat) (agents : List A) (goods : List G) (κ κ' : Key A G) : Prop :=
  ∃ base base', MinFrozen v agents goods base ∧ key v agents goods base = κ ∧
    MinFrozen v agents goods base' ∧ key v agents goods base' = κ' ∧ M v agents goods base base'

/-- **R_key for the moves `M`**: every pair on a profile whose fewest frozen agents is 0 (the clause of `R13Z`);
otherwise `κ(P′) ∈ N_M(κ(P)) ∪ {κ(P)}`. -/
def RKey (M : Nbhd A G) : Nbhd A G := fun v agents goods base base' =>
  FewestFrozenZero v agents goods ∨
    KeyNbr M v agents goods (key v agents goods base) (key v agents goods base') ∨
    key v agents goods base' = key v agents goods base

/-- **DL on the key graph, on one instance**: every key κ of a min-frozen `P` with `ω ≥ 1` and with `def*(κ) > 0`
(`+∞` included) has a key `κ′ ∈ N_M(κ)` with `def*(κ′) < def*(κ)`. -/
def DLKeyAt (M : Nbhd A G) (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ κ : Key A G,
    (∃ base, MinFrozen v agents goods base ∧ key v agents goods base = κ ∧
      1 ≤ (nFrozen v agents goods base : Int) - (2 * (agents.length : Int) - (goods.length : Int))) →
    ¬ KeyDeficitLE v agents goods κ 0 →
      ∃ κ', KeyNbr M v agents goods κ κ' ∧ KeyDeficitLT v agents goods κ' κ

/-- **DL on the key graph for the moves `M`** (`k4/dl13.md` §2.3, Remark): `DLKeyAt M` on every strict profile of every
connected k = 4 core whose fewest frozen agents is at least 1. A hypothesis, never an axiom. -/
def DLKey (M : Nbhd A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods →
    (∀ base, InP v agents goods base → 1 ≤ nFrozen v agents goods base) →
      DLKeyAt M v agents goods

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base base' : G → Option A}

/-! ## Keys -/

omit [DecidableEq G] in
/-- **Two pre-allocations have the same key** iff they have the same needed set and the same frozen agents with the
same bases. -/
theorem key_eq_iff :
    key v agents goods base = key v agents goods base' ↔
      (∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g) ∧
      ∀ i B, (Frozen agents goods base (vbNeeds v goods base) i ∧ baseOf goods base i = B) ↔
        (Frozen agents goods base' (vbNeeds v goods base') i ∧ baseOf goods base' i = B) := by
  constructor
  · intro h
    have h1 := congrArg Key.needed h
    have h2 := congrArg Key.frozen h
    simp only [key] at h1 h2
    exact ⟨fun g => Iff.of_eq (congrFun h1 g), fun i B => Iff.of_eq (congrFun (congrFun h2 i) B)⟩
  · rintro ⟨h1, h2⟩
    simp only [key, Key.mk.injEq]
    exact ⟨funext fun g => propext (h1 g), funext fun i => funext fun B => propext (h2 i B)⟩

/-! ## Least deficits of keys -/

/-- `def*(κ) ≤ d` is upward closed in `d`. -/
theorem keyDeficitLE_mono {κ : Key A G} {d d' : Int} (h : KeyDeficitLE v agents goods κ d) (hd : d ≤ d') :
    KeyDeficitLE v agents goods κ d' := by
  obtain ⟨b, hM, hk, hD⟩ := h
  exact ⟨b, hM, hk, deficitLE_mono hD hd⟩

/-- A min-frozen pre-allocation of key κ bounds `def*(κ)`: `def(P) ≤ d ⟹ def*(κ(P)) ≤ d`. -/
theorem keyDeficitLE_of (hM : MinFrozen v agents goods base) {d : Int} (h : DeficitLE v agents goods base d) :
    KeyDeficitLE v agents goods (key v agents goods base) d :=
  ⟨base, hM, rfl, h⟩

/-- **A finite def\*(κ) is attained as an integer**: if `def*(κ) ≤ d` for some integer `d`, there is a least such
integer. -/
theorem exists_least_keyDeficit {κ : Key A G} {d : Int} (h : KeyDeficitLE v agents goods κ d) :
    ∃ d₀, KeyDeficitLE v agents goods κ d₀ ∧ ∀ d', KeyDeficitLE v agents goods κ d' → d₀ ≤ d' := by
  have hlow : ∀ d', KeyDeficitLE v agents goods κ d' → -(2 * (agents.length : Int)) ≤ d' := by
    rintro d' ⟨b, -, -, hD⟩
    exact deficitLE_lower hD
  have key' : ∀ n : Nat, ∀ d : Int, d + 2 * (agents.length : Int) ≤ n → KeyDeficitLE v agents goods κ d →
      ∃ d₀, KeyDeficitLE v agents goods κ d₀ ∧ ∀ d', KeyDeficitLE v agents goods κ d' → d₀ ≤ d' := by
    intro n
    induction n with
    | zero =>
      intro d hn hd
      exact ⟨d, hd, fun d' hd' => by have := hlow d' hd'; omega⟩
    | succ n ih =>
      intro d hn hd
      by_cases h1 : KeyDeficitLE v agents goods κ (d - 1)
      · exact ih (d - 1) (by omega) h1
      · refine ⟨d, hd, fun d' hd' => Classical.byContradiction fun hlt => h1 (keyDeficitLE_mono hd' ?_)⟩
        omega
  exact key' (d + 2 * (agents.length : Int)).toNat d (Int.self_le_toNat _) h

/-- **def\*(κ) is attained**: if some min-frozen pre-allocation has key κ, one of them has `def(P) = def*(κ)`, i.e.
`def*(κ) ≤ d ⟹ def(P) ≤ d` for every `d` (the converse holds since `P` has key κ). -/
theorem exists_keyMin {κ : Key A G} (h : ∃ base, MinFrozen v agents goods base ∧ key v agents goods base = κ) :
    ∃ base, MinFrozen v agents goods base ∧ key v agents goods base = κ ∧
      ∀ d, KeyDeficitLE v agents goods κ d → DeficitLE v agents goods base d := by
  by_cases hfin : ∃ d, KeyDeficitLE v agents goods κ d
  · obtain ⟨d, hd⟩ := hfin
    obtain ⟨d₀, ⟨b, hM, hk, hD⟩, hleast⟩ := exists_least_keyDeficit hd
    exact ⟨b, hM, hk, fun d' hd' => deficitLE_mono hD (hleast d' hd')⟩
  · obtain ⟨b, hM, hk⟩ := h
    exact ⟨b, hM, hk, fun d hd => absurd ⟨d, hd⟩ hfin⟩

/-! ## (iii) Monotonicity -/

omit [DecidableEq G] in
/-- `N_M(κ) ⊆ N_M′(κ)` when `M ⊆ M′` on pairs of min-frozen pre-allocations. -/
theorem KeyNbr.mono {M M' : Nbhd A G}
    (hM : ∀ b b', MinFrozen v agents goods b → MinFrozen v agents goods b' → M v agents goods b b' →
      M' v agents goods b b')
    {κ κ' : Key A G} (h : KeyNbr M v agents goods κ κ') : KeyNbr M' v agents goods κ κ' := by
  obtain ⟨b, b', hM1, hk, hM2, hk', hm⟩ := h
  exact ⟨b, b', hM1, hk, hM2, hk', hM b b' hM1 hM2 hm⟩

/-- Widening the moves weakens DL on the key graph, on one instance. -/
theorem DLKeyAt.mono {M M' : Nbhd A G}
    (hM : ∀ b b', MinFrozen v agents goods b → MinFrozen v agents goods b' → M v agents goods b b' →
      M' v agents goods b b')
    (h : DLKeyAt M v agents goods) : DLKeyAt M' v agents goods := fun κ hκ hpos => by
  obtain ⟨κ', hN, hlt⟩ := h κ hκ hpos
  exact ⟨κ', KeyNbr.mono hM hN, hlt⟩

/-- **(iii) `M ⊆ M′ ⟹ (DLKey M ⟹ DLKey M′)`**; `M ⊆ M′` is needed only on pairs of min-frozen pre-allocations. -/
theorem DLKey.mono {M M' : Nbhd A G}
    (hM : ∀ v agents goods b b', MinFrozen v agents goods b → MinFrozen v agents goods b' →
      M v agents goods b b' → M' v agents goods b b')
    (h : DLKey M) : DLKey M' :=
  fun agents goods v hag hgd hc hconn hs hf =>
    (h agents goods v hag hgd hc hconn hs hf).mono (hM v agents goods)

/-! ## Plugging in moves -/

/-- **DL is monotone in the relation on min-frozen pairs**: `DefLocalAt` only looks at pairs of min-frozen
pre-allocations. -/
theorem DefLocalAt.mono_minFrozen {R R' : Nbhd A G}
    (hR : ∀ b b', MinFrozen v agents goods b → MinFrozen v agents goods b' → R v agents goods b b' →
      R' v agents goods b b')
    (h : DefLocalAt R v agents goods) : DefLocalAt R' v agents goods := fun b hM hω hpos => by
  obtain ⟨b', hM', hr, hlt⟩ := h b hM hω hpos
  exact ⟨b', hM', hR b b' hM hM' hr, hlt⟩

omit [DecidableEq G] in
/-- **`M ⊆ RKey M` on min-frozen pairs**: a move between min-frozen pre-allocations reaches a neighbouring key. -/
theorem rKey_of_move {M : Nbhd A G} (hM : MinFrozen v agents goods base) (hM' : MinFrozen v agents goods base')
    (h : M v agents goods base base') : RKey M v agents goods base base' :=
  Or.inr (Or.inl ⟨base, base', hM, rfl, hM', rfl, h⟩)

omit [DecidableEq G] in
/-- **Moves that keep the key are `RKey`-moves.** -/
theorem rKey_of_key_eq {M : Nbhd A G} (h : key v agents goods base' = key v agents goods base) :
    RKey M v agents goods base base' :=
  Or.inr (Or.inr h)

/-! ## (i) DL on the key graph ⟹ DL for `RKey M` -/

/-- **(i), on one instance: `DLKeyAt M ⟹ DefLocalAt (RKey M)`.** If some min-frozen state of the key of `P` has a
deficit below `def(P)`, it is an `RKey`-neighbour (same key); otherwise `def*(κ(P)) > 0`, and DL on the key graph gives
a neighbouring key with a smaller least deficit, whose best state is below `def(P)`. -/
theorem defLocalAt_rKey_of_dlKeyAt {M : Nbhd A G} (h : DLKeyAt M v agents goods) :
    DefLocalAt (RKey M) v agents goods := by
  intro b hM hω hpos
  by_cases hsame : ∃ d, KeyDeficitLE v agents goods (key v agents goods b) d ∧ ¬ DeficitLE v agents goods b d
  · -- a state of the same key is better
    obtain ⟨d, ⟨b', hM', hk', hD'⟩, hnd⟩ := hsame
    exact ⟨b', hM', rKey_of_key_eq hk', d, hD', hnd⟩
  · -- `def(P) = def*(κ(P)) > 0`: a better state lies in a neighbouring key
    have hle : ∀ d, KeyDeficitLE v agents goods (key v agents goods b) d → DeficitLE v agents goods b d :=
      fun d hd => Classical.byContradiction fun hnd => hsame ⟨d, hd, hnd⟩
    obtain ⟨κ', hN, d, ⟨b', hM', hk', hD'⟩, hnd⟩ :=
      h (key v agents goods b) ⟨b, hM, rfl, hω⟩ fun h0 => hpos (hle 0 h0)
    refine ⟨b', hM', Or.inr (Or.inl (hk' ▸ hN)), d, hD', fun hD => hnd (keyDeficitLE_of hM hD)⟩

/-- **(i) `DLKey M ⟹ DefLocal (RKey M)`**: at `f = 0` by Theorem Z (every pair is an `RKey`-pair there), at `f ≥ 1` by
`defLocalAt_rKey_of_dlKeyAt`. -/
theorem defLocal_rKey_of_DLKey {M : Nbhd A G} (h : DLKey M) : DefLocal (RKey M) := by
  intro agents goods v hag hgd hc hconn hs
  by_cases hf0 : FewestFrozenZero v agents goods
  · exact (defLocalAt_top_of_f0 hag hgd hc hf0).mono fun _ _ _ => Or.inl hf0
  · refine defLocalAt_rKey_of_dlKeyAt (h agents goods v hag hgd hc hconn hs fun base hP => ?_)
    exact Nat.pos_of_ne_zero fun h0 => hf0 ⟨base, hP, h0⟩

/-! ## The converse: DL for `RKey M` ⟹ DL on the key graph -/

/-- **The converse of (i), on one instance with `f ≥ 1`: `DefLocalAt (RKey M) ⟹ DLKeyAt M`.** Take a min-frozen `P` of
key κ with `def(P) = def*(κ)` (`exists_keyMin`); DL for `RKey M` gives a better min-frozen `P′`; it cannot have key κ,
so its key is in `N_M(κ)` and has a smaller least deficit. -/
theorem dlKeyAt_of_defLocalAt_rKey {M : Nbhd A G} (hag : agents.Nodup) (hgd : goods.Nodup)
    (hf : ¬ FewestFrozenZero v agents goods) (h : DefLocalAt (RKey M) v agents goods) : DLKeyAt M v agents goods := by
  rintro κ ⟨b₀, hM₀, hk₀, -⟩ hpos
  obtain ⟨b, hM, hk, hle⟩ := exists_keyMin ⟨b₀, hM₀, hk₀⟩
  have hb0 : ¬ DeficitLE v agents goods b 0 := fun h0 => hpos (hk ▸ keyDeficitLE_of hM h0)
  have hω := omegaP_pos hb0
  rw [omegaP_eq hag hgd hM.1] at hω
  obtain ⟨b', hM', hr, d, hD', hnd⟩ := h b hM (by omega) hb0
  rcases hr with hz | hN | hsame
  · exact absurd hz hf
  · refine ⟨key v agents goods b', hk ▸ hN, d, keyDeficitLE_of hM' hD', fun hd => hnd (hle d hd)⟩
  · exact absurd (hle d (hk ▸ hsame ▸ keyDeficitLE_of hM' hD')) hnd

/-- **The converse of (i): `DefLocal (RKey M) ⟹ DLKey M`.** -/
theorem DLKey_of_defLocal_rKey {M : Nbhd A G} (h : DefLocal (RKey M)) : DLKey M := by
  intro agents goods v hag hgd hc hconn hs hf
  refine dlKeyAt_of_defLocalAt_rKey hag hgd ?_ (h agents goods v hag hgd hc hconn hs)
  rintro ⟨base, hP, h0⟩
  have := hf base hP
  omega

/-- **DL on the key graph is exactly DL for `RKey M`**: the key frame loses nothing. -/
theorem dlKey_iff_defLocal_rKey {M : Nbhd A G} : DLKey M ↔ DefLocal (RKey M) :=
  ⟨defLocal_rKey_of_DLKey, DLKey_of_defLocal_rKey⟩

/-- **From DL for a relation `K ∪ M` whose part `K` keeps the key, to DL on the key graph for `M`**, on one instance with
`f ≥ 1`: `K ∪ M ⊆ RKey M` on min-frozen pairs. -/
theorem dlKeyAt_of_defLocalAt_keep {K M : Nbhd A G} (hag : agents.Nodup) (hgd : goods.Nodup)
    (hf : ¬ FewestFrozenZero v agents goods)
    (hK : ∀ b b', MinFrozen v agents goods b → MinFrozen v agents goods b' → K v agents goods b b' →
      key v agents goods b' = key v agents goods b)
    (h : DefLocalAt (fun v agents goods b b' => K v agents goods b b' ∨ M v agents goods b b') v agents goods) :
    DLKeyAt M v agents goods := by
  refine dlKeyAt_of_defLocalAt_rKey hag hgd hf (h.mono_minFrozen fun b b' hM hM' hr => ?_)
  rcases hr with hr | hr
  · exact rKey_of_key_eq (hK b b' hM hM' hr)
  · exact rKey_of_move hM hM' hr

/-- **DL for `M` at `f ≥ 1` implies DL on the key graph for `M`**, on one instance (the case `K = ∅` of
`dlKeyAt_of_defLocalAt_keep`). -/
theorem dlKeyAt_of_defLocalAt {M : Nbhd A G} (hag : agents.Nodup) (hgd : goods.Nodup)
    (hf : ¬ FewestFrozenZero v agents goods) (h : DefLocalAt M v agents goods) : DLKeyAt M v agents goods :=
  dlKeyAt_of_defLocalAt_rKey hag hgd hf (h.mono_minFrozen fun _ _ hM hM' hr => rKey_of_move hM hM' hr)

/-! ## (ii) DL on the key graph ⟹ TARGET₄ -/

/-- **DLKey M ⟹ C₄ᵐⁱⁿ (removal-only) on connected cores with a 4-good agent**, for every `M`. -/
theorem C4minROConn_of_DLKey {M : Nbhd A G} (h : DLKey M) : C4minROConn A G :=
  C4minROConn_of_defLocal (defLocal_rKey_of_DLKey h)

/-- **(ii) DLKey M ⟹ TARGET₄**, for every move relation `M`: with Theorem Z at `f = 0`, every instance with at least one
agent and at most four relevant goods per agent has an EFX₀ allocation. `DLKey M` is a hypothesis, not an axiom. -/
theorem target4_of_DLKey (I : Inst) (hn : 0 < I.n) {M : Nbhd (Fin I.n) (Fin I.m)} (hDL : DLKey M)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_defLocal I hn (defLocal_rKey_of_DLKey hDL) h

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.key_eq_iff
#print axioms EFX.C4min.keyDeficitLE_mono
#print axioms EFX.C4min.keyDeficitLE_of
#print axioms EFX.C4min.exists_least_keyDeficit
#print axioms EFX.C4min.exists_keyMin
#print axioms EFX.C4min.KeyNbr.mono
#print axioms EFX.C4min.DLKeyAt.mono
#print axioms EFX.C4min.DLKey.mono
#print axioms EFX.C4min.DefLocalAt.mono_minFrozen
#print axioms EFX.C4min.rKey_of_move
#print axioms EFX.C4min.rKey_of_key_eq
#print axioms EFX.C4min.defLocalAt_rKey_of_dlKeyAt
#print axioms EFX.C4min.defLocal_rKey_of_DLKey
#print axioms EFX.C4min.dlKeyAt_of_defLocalAt_rKey
#print axioms EFX.C4min.DLKey_of_defLocal_rKey
#print axioms EFX.C4min.dlKey_iff_defLocal_rKey
#print axioms EFX.C4min.dlKeyAt_of_defLocalAt_keep
#print axioms EFX.C4min.dlKeyAt_of_defLocalAt
#print axioms EFX.C4min.C4minROConn_of_DLKey
#print axioms EFX.C4min.target4_of_DLKey
