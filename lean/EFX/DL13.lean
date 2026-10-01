import EFX.C4minDescent
import EFX.ThmZ

/-!
# DL₁₃ at f ≥ 1 and Theorem Z at f = 0 ⟹ TARGET₄ (`k4/dl2.md` §3; ledger K4.DL2.T13.LEAN)

Conjecture DL₁₃ of `k4/dl2.md` §3 (K4.DL2.T13, PR #69) is DL_R for the relation R₁₃ = (T1) ∪ (T3) (re-bases and role
swaps, no rotations), stated only on the profiles whose fewest frozen agents is `f ≥ 1`. At `f = 0` DL for R₁₃ fails
(K4.DL2.RX: `induct-g-r1`, `dl2-rot-n3m7`, where free agents must rotate), but there Theorem Z
(`EFX.C4min.theoremZ_RO`, K4.C4MIN.Z) gives C₄ᵐⁱⁿ's removal-only conclusion, which is DL for the full relation
(`EFX.C4min.defLocalAt_top_iff`). This file writes the combination of `k4/dl2.md` §3: for the relation `R13Z` = "every
pair on a profile with `f = 0`, R₁₃ otherwise", DL₁₃ gives DL_{R13Z} (`DefLocal R13Z`), hence TARGET₄ by
`EFX.C4min.target4_of_defLocal`. DL₁₃ is a hypothesis of every theorem here, never an axiom. Everything is stated with
the definitions of `EFX/C4min.lean`, `EFX/PreAllocK.lean` and `EFX/C4minDescent.lean`; nothing of the model is
redefined.

**Definitions** (P = `base`, P′ = `base'`; `B_i = baseOf goods base i`, `N_i(B_i) = vbNeeds v goods base i`,
`NA = NA agents (vbNeeds v goods base)`, frozen = `Frozen agents goods base (vbNeeds v goods base)`; "keeps its base"
compares `baseOf goods`, as `BasesDiffer` does).
- `MoveT1` (**(T1) re-base**): a listed agent `y`, free in P, replaces its base by another base
  `B′_y ⊆ (B_y ∪ J) ∩ R_y`; every other listed agent keeps its base; the needed set is unchanged.
- `MoveT3` (**(T3) role swap with at most one helper**): a listed agent `x`, frozen in P with base `{g}`, and a listed
  agent `z`, free in P, with `g ∈ N_z(B_z)`: `z` takes `{g}` (`B′_z = [g]`), `x` takes a new base; a list `H` of at
  most one further listed agent (the helper `h ≠ x, z`), free in P, whose new base misses at least one good of `B_h`;
  every other listed agent keeps its base; the needed set is unchanged.
- `R13`: `MoveT1 ∨ MoveT3`, the relation R₁₃ of `k4/dl2.md` §3.
- `FewestFrozenZero`: some pre-allocation of 𝒫 has no frozen agent (`f = 0`; Theorem Z's hypothesis).
- `R13Z`: `FewestFrozenZero ∨ R13`: every pair of pre-allocations on a profile with `f = 0`, R₁₃ otherwise (the
  relation R* of `k4/dl2.md` §3).
- `DL13` (**Conjecture DL₁₃**, K4.DL2.T13): `DefLocalAt R13` on every strict profile of every connected k = 4 core whose
  fewest frozen agents is `f ≥ 1` (every pre-allocation of 𝒫 has a frozen agent). As in `DefLocal`, `DefLocalAt`
  carries `ω ≥ 1` and asks, for every min-frozen P with `def(P) > 0` (`+∞` included), a min-frozen P′ with `R13 P P′`
  and `def(P′) < def(P)`.

**Results.**
- `defLocalAt_top_of_f0`, `defLocalAt_R13Z_of_f0` (f = 0): on every k = 4 core with `f = 0`, DL holds for the full
  relation (Theorem Z with `defLocalAt_top_iff`), hence for `R13Z`.
- `defLocal_R13Z_of_DL13`: DL₁₃ ⟹ `DefLocal R13Z` (Theorem Z at `f = 0`, DL₁₃ at `f ≥ 1`); `DL13_of_defLocal_R13Z`
  and `dl13_iff_defLocal_R13Z`: the converse, so `DefLocal R13Z` is exactly DL₁₃ and the frame loses nothing.
- `C4minROConn_of_DL13`, `target4_of_DL13`: DL₁₃ ⟹ `C4minROConn` ⟹ TARGET₄ (`target4_of_defLocal`).
- `moveT1_of_inP`: for P, P′ ∈ 𝒫 the clause `B′_y ⊆ (B_y ∪ J) ∩ R_y` of (T1) is automatic, so `MoveT1` is exactly "one
  free agent's base changes, the other bases and the needed set do not" there; `moveT3_new_base`: in (T3) the new base
  of `x` differs from `{g}` (it is automatic that `x` takes a *new* base).
- `moveT1_basesDiffer`, `moveT3_basesDiffer`, `r13_basesDiffer`: a (T1) move changes at most one base, a (T3) move at
  most three (`BasesDiffer 3`).

**Where the Lean statement differs from the prose, and from the code.**
1. The moves are those of `k4/dl2.md` §3 ((T1), (T3), each with "the needed set NA staying the same"), written as
   predicates on two base maps. The clauses that the text derives rather than requires are left out of `MoveT3`: that
   `x` takes a new base (`moveT3_new_base`), that `x ≠ z` (`x` is frozen, `z` free), and where the new bases lie
   (`J ∪ B_z ∪ B_h`, from the unchanged bases). The (T1) clause `B′_y ⊆ (B_y ∪ J) ∩ R_y` is kept as written and is
   automatic on 𝒫 (`moveT1_of_inP`).
2. The code `R13` of `k4/dl2_relations.py` (`_one(s, nt_ok=False) or _swap(s, 1, gives=True)`) phrases the moves by
   frozen-status changes rather than by NA: (T1) is "exactly one base changes and no agent with an unchanged base
   changes its frozen status"; (T3) is "x frozen in P and free in P′, z free in P and frozen in P′ with B′_z = B_x and
   z needing x's good, at most one further changed agent, free in P and P′, giving up a good, no agent with an unchanged
   base changing its frozen status". The text requires NA(P′) = NA(P) instead. On pairs of min-frozen pre-allocations
   the two agree (for (T1) by Lemma 1(a), (b) of `k4/dl2.md` §4; for (T3) because NA is the set of frozen agents'
   goods on 𝒫, and F(P′) = F(P) − x + z); this agreement is the text's argument, not formalized here. The Lean
   relation follows the text.
3. "At most one helper" is a list `H` of length ≤ 1, the set `H` of Lemma 6 of `k4/dl2.md` §4 (`H = []`: a role swap
   without helper).
4. "f ≥ 1" in `DL13` is "every pre-allocation of 𝒫 has a frozen agent" (`1 ≤ nFrozen`), the negation of Theorem Z's
   hypothesis `FewestFrozenZero`. Theorem Z's Lean statement (`theoremZ_RO`) needs only `IsCore4` and `f = 0`, so it
   covers the f = 0 profiles of `DefLocal` (connected, strict) with no gap.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## The moves (T1), (T3) and the relations R₁₃, `R13Z` -/

/-- **(T1) re-base** (`k4/dl2.md` §3): a listed agent `y`, free in `P`, replaces its base by another base
`B′_y ⊆ (B_y ∪ J) ∩ R_y`; every other listed agent keeps its base (on `goods`); the needed set `NA` is unchanged. -/
def MoveT1 : Nbhd A G := fun v agents goods base base' =>
  ∃ y ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) y ∧
    baseOf goods base y ≠ baseOf goods base' y ∧
    (∀ g ∈ baseOf goods base' y, (base g = some y ∨ base g = none) ∧ 0 < v y g) ∧
    (∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i) ∧
    (∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g)

/-- **(T3) role swap with at most one helper** (`k4/dl2.md` §3): a listed agent `x`, frozen in `P` with base `{g}`
(`g ∈ NA`), and a listed agent `z`, free in `P`, with `g ∈ N_z(B_z)`: `z` takes `{g}` and `x` takes a new base; at most
one further listed agent `h ≠ x, z` (the list `H`), free in `P`, replaces its base by one that misses at least one good
of `B_h`; every other listed agent keeps its base (on `goods`); the needed set `NA` is unchanged. -/
def MoveT3 : Nbhd A G := fun v agents goods base base' =>
  ∃ x ∈ agents, ∃ z ∈ agents, ∃ g : G,
    baseOf goods base x = [g] ∧ NA agents (vbNeeds v goods base) g ∧
    ¬ Frozen agents goods base (vbNeeds v goods base) z ∧ vbNeeds v goods base z g ∧
    baseOf goods base' z = [g] ∧
    ∃ H : List A, H.length ≤ 1 ∧
      (∀ h ∈ H, h ∈ agents ∧ h ≠ x ∧ h ≠ z ∧ ¬ Frozen agents goods base (vbNeeds v goods base) h ∧
        ∃ g' ∈ baseOf goods base h, g' ∉ baseOf goods base' h) ∧
      (∀ i ∈ agents, i ≠ x → i ≠ z → i ∉ H → baseOf goods base i = baseOf goods base' i) ∧
      (∀ g', NA agents (vbNeeds v goods base) g' ↔ NA agents (vbNeeds v goods base') g')

/-- **The relation R₁₃** (`k4/dl2.md` §3, code `R13`): a (T1) or a (T3) move; no rotations. -/
def R13 : Nbhd A G := fun v agents goods base base' =>
  MoveT1 v agents goods base base' ∨ MoveT3 v agents goods base base'

/-- **The fewest frozen agents is 0**: some pre-allocation of 𝒫 has no frozen agent (Theorem Z's hypothesis). -/
def FewestFrozenZero (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∃ base, InP v agents goods base ∧ nFrozen v agents goods base = 0

/-- **The relation R\*** of `k4/dl2.md` §3: every pair of pre-allocations on a profile whose fewest frozen agents is 0,
R₁₃ on the others. -/
def R13Z : Nbhd A G := fun v agents goods base base' =>
  FewestFrozenZero v agents goods ∨ R13 v agents goods base base'

/-- **Conjecture DL₁₃** (`k4/dl2.md` §3, K4.DL2.T13): on every strict profile of every connected k = 4 core whose fewest
frozen agents is at least 1, DL for R₁₃ (`DefLocalAt R13`: if `ω ≥ 1`, every min-frozen `P` with `def(P) > 0`, `+∞`
included, has a min-frozen `P′` with `R13 P P′` and `def(P′) < def(P)`). A hypothesis, never an axiom. -/
def DL13 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods →
    (∀ base, InP v agents goods base → 1 ≤ nFrozen v agents goods base) →
      DefLocalAt (R13 (A := A) (G := G)) v agents goods

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base base' : G → Option A}

/-! ## The moves -/

omit [DecidableEq G] in
/-- **On 𝒫, (T1) is "one free agent's base changes, nothing else does"**: for `P, P′ ∈ 𝒫` the clause
`B′_y ⊆ (B_y ∪ J) ∩ R_y` follows from the other bases being unchanged. -/
theorem moveT1_of_inP (hP : InP v agents goods base) (hP' : InP v agents goods base') {y : A} (hy : y ∈ agents)
    (hfree : ¬ Frozen agents goods base (vbNeeds v goods base) y)
    (hne : baseOf goods base y ≠ baseOf goods base' y)
    (hsame : ∀ i ∈ agents, i ≠ y → baseOf goods base i = baseOf goods base' i)
    (hNA : ∀ g, NA agents (vbNeeds v goods base) g ↔ NA agents (vbNeeds v goods base') g) :
    MoveT1 v agents goods base base' := by
  refine ⟨y, hy, hfree, hne, fun g hg => ?_, hsame, hNA⟩
  obtain ⟨hgg, hb'⟩ := mem_baseOf.mp hg
  refine ⟨?_, hP'.rel g hgg y hb'⟩
  cases hb : base g with
  | none => exact Or.inr rfl
  | some i =>
    refine Or.inl ?_
    by_cases hiy : i = y
    · rw [hiy]
    · have hi := hP.mem g hgg i hb
      have : g ∈ baseOf goods base' i := hsame i hi hiy ▸ mem_baseOf.mpr ⟨hgg, hb⟩
      rw [(mem_baseOf.mp this).2] at hb'
      exact absurd (Option.some.inj hb') hiy

omit [DecidableEq G] in
/-- In a (T3) move, `x` takes a new base: `B′_x ≠ {g}` (`g` is now `z`'s, and `x ≠ z` since `x` is frozen, `z` free). -/
theorem moveT3_new_base (h : MoveT3 v agents goods base base') :
    ∃ x ∈ agents, Frozen agents goods base (vbNeeds v goods base) x ∧
      baseOf goods base x ≠ baseOf goods base' x := by
  obtain ⟨x, hx, z, -, g, hbx, hNA, hzf, -, hbz', -⟩ := h
  refine ⟨x, hx, ⟨g, hbx, hNA⟩, fun e => ?_⟩
  have hg' : g ∈ baseOf goods base' x := by rw [← e, hbx]; exact List.mem_singleton_self g
  have hgz : g ∈ baseOf goods base' z := by rw [hbz']; exact List.mem_singleton_self g
  have hxz : x = z := Option.some.inj ((mem_baseOf.mp hg').2.symm.trans (mem_baseOf.mp hgz).2)
  exact hzf (hxz ▸ ⟨g, hbx, hNA⟩)

omit [DecidableEq G] in
/-- A (T1) move changes the base of one agent. -/
theorem moveT1_basesDiffer (h : MoveT1 v agents goods base base') : BasesDiffer 1 v agents goods base base' := by
  obtain ⟨y, -, -, -, -, hsame, -⟩ := h
  exact ⟨[y], Nat.le_refl _, fun i hi hni => hsame i hi fun e => hni (e ▸ List.mem_singleton_self i)⟩

omit [DecidableEq G] in
/-- A (T3) move changes the bases of at most three agents. -/
theorem moveT3_basesDiffer (h : MoveT3 v agents goods base base') : BasesDiffer 3 v agents goods base base' := by
  obtain ⟨x, -, z, -, g, -, -, -, -, -, H, hH, -, hsame, -⟩ := h
  refine ⟨x :: z :: H, by simp only [List.length_cons]; omega, fun i hi hni => ?_⟩
  simp only [List.mem_cons, not_or] at hni
  exact hsame i hi hni.1 hni.2.1 hni.2.2

omit [DecidableEq G] in
/-- **R₁₃ changes the bases of at most three agents** (`R13 ⊆ BasesDiffer 3`). -/
theorem r13_basesDiffer (h : R13 v agents goods base base') : BasesDiffer 3 v agents goods base base' := by
  rcases h with h | h
  · exact basesDiffer_mono (by decide) (moveT1_basesDiffer h)
  · exact moveT3_basesDiffer h

/-! ## f = 0: Theorem Z -/

/-- **At f = 0, DL holds for the full relation**: on every k = 4 core whose fewest frozen agents is 0, Theorem Z
(`theoremZ_RO`) gives a min-frozen `P` with `def(P) ≤ 0`, which is C₄ᵐⁱⁿ's removal-only conclusion, i.e. DL for the
full relation (`defLocalAt_top_iff`). -/
theorem defLocalAt_top_of_f0 (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods)
    (hf0 : FewestFrozenZero v agents goods) : DefLocalAt (fun _ _ _ _ _ => True) v agents goods :=
  (defLocalAt_top_iff hag hgd).mpr (theoremZ_RO hag hgd hc hf0)

/-- **At f = 0, DL holds for `R13Z`** (every pair is an `R13Z`-pair there). -/
theorem defLocalAt_R13Z_of_f0 (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods)
    (hf0 : FewestFrozenZero v agents goods) : DefLocalAt (R13Z (A := A) (G := G)) v agents goods :=
  (defLocalAt_top_of_f0 hag hgd hc hf0).mono fun _ _ _ => Or.inl hf0

/-! ## DL₁₃ ⟹ DL_{R13Z} ⟹ TARGET₄ -/

/-- **DL₁₃ (at f ≥ 1) and Theorem Z (at f = 0) give DL for `R13Z`** on every strict profile of every connected k = 4
core. -/
theorem defLocal_R13Z_of_DL13 (h : DL13 A G) : DefLocal (R13Z (A := A) (G := G)) := by
  intro agents goods v hag hgd hc hconn hs
  by_cases hf0 : FewestFrozenZero v agents goods
  · exact defLocalAt_R13Z_of_f0 hag hgd hc hf0
  · refine (h agents goods v hag hgd hc hconn hs fun base hP => ?_).mono fun _ _ hr => Or.inr hr
    exact Nat.pos_of_ne_zero fun h0 => hf0 ⟨base, hP, h0⟩

/-- **The converse**: DL for `R13Z` gives DL₁₃ (on a profile with `f ≥ 1`, `R13Z` is `R13`). -/
theorem DL13_of_defLocal_R13Z (h : DefLocal (R13Z (A := A) (G := G))) : DL13 A G := by
  intro agents goods v hag hgd hc hconn hs hf
  refine (h agents goods v hag hgd hc hconn hs).mono fun _ _ hr => hr.resolve_left ?_
  rintro ⟨base, hP, h0⟩
  have := hf base hP
  omega

/-- **DL₁₃ is exactly DL for `R13Z`**: the frame loses nothing. -/
theorem dl13_iff_defLocal_R13Z : DL13 A G ↔ DefLocal (R13Z (A := A) (G := G)) :=
  ⟨defLocal_R13Z_of_DL13, DL13_of_defLocal_R13Z⟩

/-- **DL₁₃ ⟹ C₄ᵐⁱⁿ (removal-only) on connected cores with a 4-good agent.** -/
theorem C4minROConn_of_DL13 (h : DL13 A G) : C4minROConn A G :=
  C4minROConn_of_defLocal (defLocal_R13Z_of_DL13 h)

/-- **DL₁₃ ⟹ TARGET₄** (`k4/dl2.md` §3): with Theorem Z at f = 0, every instance with at least one agent and at most
four relevant goods per agent has an EFX₀ allocation (`target4_of_defLocal` for `R13Z`). DL₁₃ is a hypothesis, not an
axiom. -/
theorem target4_of_DL13 (I : Inst) (hn : 0 < I.n) (hDL : DL13 (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_defLocal I hn (defLocal_R13Z_of_DL13 hDL) h

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.moveT1_of_inP
#print axioms EFX.C4min.moveT3_new_base
#print axioms EFX.C4min.moveT1_basesDiffer
#print axioms EFX.C4min.moveT3_basesDiffer
#print axioms EFX.C4min.r13_basesDiffer
#print axioms EFX.C4min.defLocalAt_top_of_f0
#print axioms EFX.C4min.defLocalAt_R13Z_of_f0
#print axioms EFX.C4min.defLocal_R13Z_of_DL13
#print axioms EFX.C4min.DL13_of_defLocal_R13Z
#print axioms EFX.C4min.dl13_iff_defLocal_R13Z
#print axioms EFX.C4min.C4minROConn_of_DL13
#print axioms EFX.C4min.target4_of_DL13
