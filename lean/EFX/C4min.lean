import EFX.LB4R

/-!
# The space 𝒫, completability and Conjecture C₄ᵐⁱⁿ (`k4/c4x.md` §1, §5; ledger K4.C4MIN.FRAME)

The frame for conjecture C₄ᵐⁱⁿ of `k4/c4x.md` (PR #36, branch `proof/k4-c4x`, read at commit efef349): its definitions over the pre-allocations
of `EFX/PreAllocK.lean`, the statement as a `Prop`, and the reductions "C₄ᵐⁱⁿ ⟹ C₄∃ ⟹ TARGET₄". C₄ᵐⁱⁿ is a hypothesis of
every theorem here, never an axiom.

**Definitions** (`k4/c4x.md` §1), for agents `agents`, goods `goods`, values `v` (over lists, as in `PreAllocK`):
- `vbNeeds`: the value-based needs `N_i = {g ∈ goods ∖ B_i : v_i(g) > v_i(B_i)}` (such a `g` is relevant to `i`). These
  are the needs of `EFX.LB4.Needs.valueBased`.
- `InP`: a pre-allocation of 𝒫, given by its base map alone (the needs are `vbNeeds`): every base good goes to a
  listed agent that values it (`B_i ⊆ R_i`), every base has at most two goods, and (V1), (V2) hold
  (`EFX.LB4.Valid` with the value-based needs).
- `nFrozen`: the number of frozen agents, `EFX.LB4.numFrozen` with the value-based needs (by `EFX.LB4.numFrozen_eq`,
  `|F| = |NA|`); `MinFrozen`: a pre-allocation of 𝒫 with the fewest frozen agents among all of 𝒫.
- `Completable`: some completion is an `EFX.LB4.SoundCompletion` of `(base, vbNeeds)`: an owner (a free agent) or none,
  frozen non-owners get no junk, free non-owners at most `2 − |B_i|` junk goods, the owner's needs taken from its
  bundle, and (OC₄). By Theorem 1′₄ (`EFX.LB4.SoundCompletion.efx0_d2`) it is EFX₀ with at most one bundle of more than
  two goods.
- `ownerBundle`, `roNeeds`, `Unthreatened`, `DeficitLE`, `RemovalOnly`: removal-only completability and the deficit,
  below.

**Statements.**
- `TheoremC4min`: every strict profile of every k = 4 core has a completable pre-allocation of 𝒫 with the fewest
  frozen agents (the task's form, "some P ∈ 𝒫 with the fewest frozen agents is completable").
- `TheoremC4minRO`: the same with "removal-only completable" (deficit ≤ 0), the form of `k4/c4x.md` §5. It implies
  `TheoremC4min` (`C4min_of_C4minRO`), since a removal-only completable pre-allocation is completable
  (`completable_of_removalOnly`, the text's "then C can go into those slots in any way").
- `C4minConn`, `C4minROConn`: the same on connected cores with a 4-good agent, the class `EFX.LB4.target4_of_completions`
  needs.

**Results.**
- `completable_of_removalOnly`: removal-only completability implies completability. The completion puts the junk
  goods of `C` into the other agents' slots with `EFX.LB.fill` (the construction of `EFX.LB4.complete_none_exists`).
- `C4exists_of_C4min`, `target4_of_C4min`, `k4D_of_C4min`: C₄ᵐⁱⁿ ⟹ C₄∃ (`EFX.LB4R.TheoremC4exists`) ⟹ K4.D, TARGET₄.
- `C4existsConn_of_C4minConn`, `target4_of_C4minConn`: the connected variant, through
  `EFX.LB4R.target4_of_C4existsConn`; `C4minConn_of_C4min`, and the removal-only versions.
- `inP_phase1`: the picks of Phase 1 (`EFX.LB4R.phase1State`, any τ) form a pre-allocation of 𝒫, so 𝒫 is never empty
  (`k4/c4x.md` §1, second remark); `exists_minFrozen`: hence a pre-allocation with the fewest frozen agents exists on
  every instance.

**Choices where the prose leaves room.**
1. `k4/c4x.md` §1 says `B_i ⊆ R_i`; `InP.rel` asks `0 < v_i(g)` for every base good, and `InP.mem` that its agent is
   listed (a completion must give base goods to listed agents).
2. A pre-allocation of 𝒫 is its base map: the needs are always `vbNeeds`, so two base maps that agree on `goods` are the
   same pre-allocation for every definition here.
3. The set `C ⊆ J` of the removal-only condition is a test `C : G → Bool`; only its values on the junk matter
   (`|C|` is `((LB4.junk goods base).filter C).length`).
4. `S_o(C)` is `EFX.LB4.otherSlots` with `roNeeds` (frozen status recomputed with the owner's needs from
   `X_o = B_o ∪ (J ∖ C)`), the definition Lemma 3₄ uses.
5. The deficit is stated as a predicate `DeficitLE P d` ("def(P) ≤ d") instead of a number, exactly as the text defines
   it: `|J| − S` if that is ≤ 0, otherwise the least `|C| − S_o(C)` over the free owners `o` and the sets `C` that leave
   nobody threatened (no such pair: `+∞`). `RemovalOnly` is `DeficitLE P 0`.
6. "Threatened while holding its base alone": `max_h v_x(X_o ∖ h) > v_x(B_x)` for some `h ∈ X_o` (`Unthreatened`).
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## The space 𝒫 -/

/-- The value-based needs of `k4/c4x.md` §1: `N_i = {g ∈ goods ∖ B_i : v_i(g) > v_i(B_i)}`. -/
def vbNeeds (v : A → G → Nat) (goods : List G) (base : G → Option A) (i : A) (g : G) : Prop :=
  g ∈ goods ∧ base g ≠ some i ∧ value v i (baseOf goods base i) < v i g

instance (v : A → G → Nat) (goods : List G) (base : G → Option A) (i : A) (g : G) :
    Decidable (vbNeeds v goods base i g) := by
  unfold vbNeeds; infer_instance

/-- **The space 𝒫** (`k4/c4x.md` §1, Definition): the base map `base` is a pre-allocation of 𝒫 if every base good goes
to a listed agent that values it, every base has at most two goods, and (V1), (V2) hold with the value-based needs. -/
structure InP (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop where
  mem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents
  rel : ∀ g ∈ goods, ∀ i, base g = some i → 0 < v i g
  two : ∀ i, (baseOf goods base i).length ≤ 2
  valid : Valid agents goods base (vbNeeds v goods base)

/-- `|F|`: the number of frozen agents of a pre-allocation (with the value-based needs). -/
noncomputable def nFrozen (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  numFrozen agents goods base (vbNeeds v goods base)

/-- A pre-allocation of 𝒫 with the fewest frozen agents. -/
def MinFrozen (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  InP v agents goods base ∧ ∀ base', InP v agents goods base' → nFrozen v agents goods base ≤ nFrozen v agents goods base'

/-- **Completable** (`k4/c4x.md` §1): some completion with an owner (or none) is a sound completion of the
pre-allocation with its value-based needs (the owner's needs from its bundle). -/
def Completable (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ∃ (o : Option A) (X : G → A), SoundCompletion v agents goods base (vbNeeds v goods base) o X

/-! ## Removal-only completability and the deficit -/

/-- The owner's bundle `X_o = B_o ∪ (J ∖ C)`. -/
def ownerBundle (goods : List G) (base : G → Option A) (o : A) (C : G → Bool) : List G :=
  goods.filter (fun g => base g = some o ∨ (base g = none ∧ C g = false))

/-- The needs with the owner's taken from `X_o = B_o ∪ (J ∖ C)`:
`N_o^X = {g ∈ goods ∖ X_o : v_o(g) > v_o(X_o)}`. -/
def roNeeds (v : A → G → Nat) (goods : List G) (base : G → Option A) (o : A) (C : G → Bool) (i : A) (g : G) :
    Prop :=
  if i = o then g ∈ goods ∧ g ∉ ownerBundle goods base o C ∧ value v o (ownerBundle goods base o C) < v o g
  else vbNeeds v goods base i g

/-- `B_o ∪ (J ∖ C)` threatens no listed agent `x ≠ o` holding its base alone:
`v_x(X_o ∖ h) ≤ v_x(B_x)` for every `h ∈ X_o`. -/
def Unthreatened (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A)
    (C : G → Bool) : Prop :=
  ∀ x ∈ agents, x ≠ o → ∀ h ∈ ownerBundle goods base o C,
    value v x ((ownerBundle goods base o C).erase h) ≤ value v x (baseOf goods base x)

/-- `ω = |J| − S` with the value-based needs (the caps counted with their sign). -/
noncomputable def omegaP (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Int :=
  ((LB4.junk goods base).length : Int) - capSum agents goods base (vbNeeds v goods base)

/-- **`def(P) ≤ d`** (`k4/c4x.md` §1): `def(P) = |J| − S` if that is ≤ 0; otherwise `def(P)` is the least value of
`|C| − S_o(C)` over the free owners `o` and the sets `C ⊆ J` such that `B_o ∪ (J ∖ C)` threatens nobody holding its base
alone (`S_o(C)`: the slots of the agents other than `o`, frozen status computed with the owner's needs from its
bundle). -/
def DeficitLE (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (d : Int) : Prop :=
  (omegaP v agents goods base ≤ 0 ∧ omegaP v agents goods base ≤ d) ∨
  (0 < omegaP v agents goods base ∧ ∃ o ∈ agents, ¬ Frozen agents goods base (vbNeeds v goods base) o ∧
    ∃ C : G → Bool, Unthreatened v agents goods base o C ∧
      (((LB4.junk goods base).filter C).length : Int) -
        (otherSlots agents goods base (roNeeds v goods base o C) o : Int) ≤ d)

/-- **Removal-only completable**: `def(P) ≤ 0`. -/
def RemovalOnly (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  DeficitLE v agents goods base 0

/-! ## The statements -/

/-- **Conjecture C₄ᵐⁱⁿ** (`k4/c4x.md` §5, K4.C4X.MIN), completable form: every strict profile of every k = 4 core has a
completable pre-allocation of 𝒫 with the fewest frozen agents. A hypothesis of the theorems below, never an axiom. -/
def TheoremC4min (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → ∃ base : G → Option A, MinFrozen v agents goods base ∧ Completable v agents goods base

/-- **Conjecture C₄ᵐⁱⁿ, removal-only form** (the text's statement): some pre-allocation of 𝒫 with the fewest frozen
agents has deficit ≤ 0. -/
def TheoremC4minRO (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → ∃ base : G → Option A, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base

/-- C₄ᵐⁱⁿ on connected cores with a 4-good agent (the class `EFX.LB4.target4_of_completions` needs). -/
def C4minConn (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → (∃ i ∈ agents, (relevant v i goods).length = 4) →
      ∃ base : G → Option A, MinFrozen v agents goods base ∧ Completable v agents goods base

/-- The removal-only form on connected cores with a 4-good agent. -/
def C4minROConn (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → (∃ i ∈ agents, (relevant v i goods).length = 4) →
      ∃ base : G → Option A, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base


/-! ## Removal-only ⟹ completable -/

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}

omit [DecidableEq G] in
/-- The value-based needs are needs in the Definition's sense (`EFX.LB4.Needs.valueBased`). -/
theorem needs_vb (i : A) : Needs v goods base (vbNeeds v goods base) i :=
  ⟨fun g hg hb hlt => ⟨hg, hb, hlt⟩, fun g ⟨hg, hb, hlt⟩ => ⟨hg, by omega, hb⟩⟩

open Classical in
/-- The slots of the removal-only completion: none for the owner and for agents frozen with `roNeeds`, `2 − |B_j|`
for the others (the summands of `EFX.LB4.otherSlots`). -/
noncomputable def roSlots (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A)
    (C : G → Bool) (j : A) : Nat :=
  if j = o ∨ Frozen agents goods base (roNeeds v goods base o C) j then 0 else 2 - (baseOf goods base j).length

/-- The removal-only completion: base goods to their base's agent, the junk goods of `C` into the slots of the agents
other than `o` (`EFX.LB.fill`, in the order of `agents`), every other junk good to the owner `o`. -/
noncomputable def roCompletion (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (o : A)
    (C : G → Bool) (g : G) : A :=
  match base g with
  | some i => i
  | none => if C g then (LB.fill (roSlots v agents goods base o C) agents ((LB4.junk goods base).filter C) g).getD o
      else o

omit [DecidableEq G] in
theorem sum_roSlots (o : A) (C : G → Bool) :
    (agents.map (roSlots v agents goods base o C)).sum = otherSlots agents goods base (roNeeds v goods base o C) o := by
  unfold otherSlots roSlots
  congr

/-- **Removal-only completable ⟹ completable** (`k4/c4x.md` §1: "then C can go into those slots in any way"). If
`def(P) ≤ 0`, a completion without owner (`ω ≤ 0`, `EFX.LB4.complete_none_exists`) or the removal-only completion
with owner `o` (`roCompletion`) is a sound completion. -/
theorem completable_of_removalOnly (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (hP : InP v agents goods base) (hR : RemovalOnly v agents goods base) : Completable v agents goods base := by
  classical
  have hNd : ∀ i ∈ agents, Needs v goods base (vbNeeds v goods base) i := fun i _ => needs_vb i
  rcases hR with ⟨hω, -⟩ | ⟨-, o, ho, hoF, C, hU, hle⟩
  · -- `ω ≤ 0`: the completion without owner
    obtain ⟨d, -⟩ := List.exists_mem_of_ne_nil agents hne
    have hC := complete_none_exists (N := vbNeeds v goods base) hag hgd hP.mem (fun j _ => hP.two j) hω d
    exact ⟨none, _, SoundCompletion.of_baseNeeds hNd hP.valid hC (fun w hw => by cases hw)⟩
  -- the removal-only completion with owner `o`
  obtain ⟨s, hs⟩ : ∃ s, s = roSlots v agents goods base o C := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = roCompletion v agents goods base o C := ⟨_, rfl⟩
  have hfit : ((LB4.junk goods base).filter C).length ≤ (agents.map s).sum := by
    rw [hs, sum_roSlots]; omega
  have hso : s o = 0 := by simp [hs, roSlots]
  -- every junk good of `C` is placed with an agent other than `o`
  have hplace : ∀ g ∈ goods, base g = none → C g = true →
      ∃ j, LB.fill s agents ((LB4.junk goods base).filter C) g = some j ∧ X g = j ∧ j ∈ agents ∧ 0 < s j := by
    intro g hg hb hCg
    obtain ⟨j, hj⟩ := LB.fill_cover (List.mem_filter.mpr ⟨mem_junk.mpr ⟨hg, hb⟩, hCg⟩) hfit
    have := LB.fill_some hj
    refine ⟨j, hj, ?_, this.1, this.2.2⟩
    rw [hX]; simp only [roCompletion, hb, hCg, ↓reduceIte]; rw [← hs, hj]; rfl
  have hXb : ∀ g ∈ goods, ∀ i, base g = some i → X g = i := fun g _ i hb => by simp [hX, roCompletion, hb]
  have hXo : ∀ g ∈ goods, base g = none → C g = false → X g = o := fun g _ hb hCg => by
    simp [hX, roCompletion, hb, hCg]
  -- the owner's bundle is `B_o ∪ (J ∖ C)`
  have hbundle : bundle goods X o = ownerBundle goods base o C := by
    unfold bundle ownerBundle
    apply List.filter_congr
    intro g hg
    cases hb : base g with
    | some i => simp [hXb g hg i hb]
    | none =>
      cases hCg : C g with
      | false => simp [hXo g hg hb hCg]
      | true =>
        obtain ⟨j, -, hXj, -, hpos⟩ := hplace g hg hb hCg
        have hjo : j ≠ o := fun e => by rw [e, hso] at hpos; omega
        simp [hXj, hjo]
  have hON : ownerNeeds v goods X (vbNeeds v goods base) (some o) = roNeeds v goods base o C := by
    funext i g
    unfold ownerNeeds roNeeds
    by_cases hio : i = o
    · subst hio
      simp only [↓reduceIte]
      rw [← hbundle]
      apply propext
      constructor
      · rintro ⟨hg, hXg, hlt⟩; exact ⟨hg, fun h => hXg (LB.mem_bundle.mp h).2, hlt⟩
      · rintro ⟨hg, hXg, hlt⟩; exact ⟨hg, fun h => hXg (LB.mem_bundle.mpr ⟨hg, h⟩), hlt⟩
    · simp [hio, Ne.symm hio]
  -- the junk goods of `j ≠ o` are placed with `j` by `fill`
  have hjunk : ∀ j, j ≠ o → ∀ g ∈ junkOf goods base X j,
      LB.fill s agents ((LB4.junk goods base).filter C) g = some j ∧ 0 < s j := by
    intro j hjo g hgJ
    obtain ⟨hg, hXg, hb⟩ := mem_junkOf.mp hgJ
    cases hCg : C g with
    | false => exact absurd ((hXo g hg hb hCg).symm.trans hXg) (Ne.symm hjo)
    | true =>
      obtain ⟨k, hk, hXk, -, hpos⟩ := hplace g hg hb hCg
      rw [hXk] at hXg; subst hXg; exact ⟨hk, hpos⟩
  have hFo : ¬ Frozen agents goods base (ownerNeeds v goods X (vbNeeds v goods base) (some o)) o :=
    fun ⟨y, hy, i, hi, hN⟩ => hoF ⟨y, hy, i, hi, ownerNeeds_le hXb hNd i hi y hN⟩
  refine ⟨some o, X, fun i _ _ => needs_vb i, hP.valid.toOwnerNeeds hXb hNd, ⟨fun g hg => ?_, hXb,
    fun w hw => ?_, fun j _ hjo hF => ?_, fun j _ hjo hF => ?_⟩, ?_⟩
  · cases hb : base g with
    | some i => rw [hXb g hg i hb]; exact hP.mem g hg i hb
    | none =>
      cases hCg : C g with
      | false => rw [hXo g hg hb hCg]; exact ho
      | true => obtain ⟨j, -, hXj, hj, -⟩ := hplace g hg hb hCg; rw [hXj]; exact hj
  · cases hw; exact ⟨ho, hFo⟩
  · -- a frozen agent has no slot
    have hjo' : j ≠ o := fun e => hjo (by rw [e])
    rw [hON] at hF
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro g hgJ
    have := (hjunk j hjo' g hgJ).2
    simp [hs, roSlots, hF] at this
  · have hjo' : j ≠ o := fun e => hjo (by rw [e])
    rw [hON] at hF
    have hc := LB.fill_count hag ((LB.nodup_bundle hgd _ j).sublist List.filter_sublist) (fun g hg => (hjunk j hjo' g hg).1)
    have h2 := hP.two j
    simp only [hs, roSlots, hjo', hF, or_self, ↓reduceIte] at hc
    unfold junkOf
    omega
  · intro w hw j hj hjw h hh
    cases hw
    rw [hbundle] at hh ⊢
    exact Nat.le_trans (hU j hj hjw h hh) (value_baseOf_le hXb j)

/-! ## 𝒫 is not empty, and a pre-allocation with the fewest frozen agents exists -/

/-- **The picks of Phase 1 form a pre-allocation of 𝒫** (`k4/c4x.md` §1, second remark), for every insertion sequence
τ: bases are single picks the pickers value, and the pick needs of Phase 1 (`EFX.LB4R.needsOf`) are the value-based
needs, so (V1), (V2) are those of `EFX.LB4R.phase1State_inv`. -/
theorem inP_phase1 (hag : agents.Nodup) (hgd : goods.Nodup) (τ : List Nat) :
    InP v agents goods (LB4R.phase1State v agents goods τ).base := by
  have hR := LB4R.phase1_spec v agents goods agents.length agents goods τ hag hgd
  have hI := LB4R.phase1State_inv (v := v) (τ := τ) hag hgd
  have hbo := LB4R.phase1State_baseOf hR hgd (τ := τ)
  -- the value-based needs are Phase 1's needs
  have hNA : ∀ g, NA agents (vbNeeds v goods (LB4R.phase1State v agents goods τ).base) g →
      NA agents (LB4R.needsOf v goods (LB4R.phase1State v agents goods τ)) g := by
    rintro g ⟨i, hi, hg, -, hlt⟩
    refine ⟨i, hi, Or.inr ⟨fun h => h, hg, by omega, fun y hy => ?_⟩⟩
    rw [hbo i, hy] at hlt; simpa using hlt
  refine ⟨fun g _ i hb => ?_, fun g _ i hb => ?_, fun i => ?_,
    ⟨fun g hg h => hI.valid.v1 g hg (hNA g h), fun i h2 g hg h => hI.valid.v2 i h2 g hg (hNA g h)⟩⟩
  · obtain ⟨p, hp, rfl, -⟩ := (LB4R.phase1State_base hR).mp hb
    exact hR.mem p hp
  · obtain ⟨p, hp, rfl, hpg⟩ := (LB4R.phase1State_base hR).mp hb
    exact (hR.pickMem p hp g hpg).2
  · rw [hbo i]
    cases (LB4R.phase1State v agents goods τ).pick i <;> simp

/-- **A pre-allocation with the fewest frozen agents exists** on every instance (𝒫 is not empty, `inP_phase1`). -/
theorem exists_minFrozen (hag : agents.Nodup) (hgd : goods.Nodup) : ∃ base, MinFrozen v agents goods base := by
  refine Classical.byContradiction fun hno => ?_
  have key : ∀ n, ∀ base, InP v agents goods base → nFrozen v agents goods base = n → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro base hP hn
      refine hno ⟨base, hP, fun base' hP' => Nat.le_of_not_lt fun hlt => ?_⟩
      exact ih _ (hn ▸ hlt) base' hP' rfl
  exact key _ _ (inP_phase1 hag hgd []) rfl

/-! ## C₄ᵐⁱⁿ ⟹ C₄∃ ⟹ K4.D, TARGET₄ -/

/-- **C₄ᵐⁱⁿ ⟹ C₄∃**: a completable pre-allocation gives a sound completion. -/
theorem C4exists_of_C4min (h : TheoremC4min A G) : LB4R.TheoremC4exists A G :=
  fun agents goods v hag hgd hc hs => by
    obtain ⟨base, -, o, X, hS⟩ := h agents goods v hag hgd hc hs
    exact ⟨base, vbNeeds v goods base, o, X, hS⟩

/-- **The removal-only form implies the completable form.** -/
theorem C4min_of_C4minRO (h : TheoremC4minRO A G) : TheoremC4min A G :=
  fun agents goods v hag hgd hc hs => by
    obtain ⟨base, hmin, hR⟩ := h agents goods v hag hgd hc hs
    have hne : agents ≠ [] := fun e => by have := hc.1; rw [e] at this; simp at this
    exact ⟨base, hmin, completable_of_removalOnly hag hgd hne hmin.1 hR⟩

/-- **C₄ᵐⁱⁿ ⟹ K4.D**: every k = 4 core (strict or not, through K4.TIE) has an EFX₀ allocation with at most one bundle
of more than two goods (`EFX.LB4R.k4D_of_C4exists`). -/
theorem k4D_of_C4min (hC : TheoremC4min A G) {agents : List A} {goods : List G} {v : A → G → Nat}
    (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ w ∈ agents, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 :=
  LB4R.k4D_of_C4exists (C4exists_of_C4min hC) hag hgd hc

/-- **C₄ᵐⁱⁿ ⟹ TARGET₄** (`EFX.LB4R.target4_of_C4exists`): every instance with at least one agent and at most four
relevant goods per agent has an EFX₀ allocation. C₄ᵐⁱⁿ is a hypothesis, not an axiom. -/
theorem target4_of_C4min (I : Inst) (hn : 0 < I.n) (hC : TheoremC4min (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  LB4R.target4_of_C4exists I hn (C4exists_of_C4min hC) h

/-- **C₄ᵐⁱⁿ (removal-only form) ⟹ TARGET₄.** -/
theorem target4_of_C4minRO (I : Inst) (hn : 0 < I.n) (hC : TheoremC4minRO (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4min I hn (C4min_of_C4minRO hC) h

/-- C₄ᵐⁱⁿ implies its connected variant. -/
theorem C4minConn_of_C4min (h : TheoremC4min A G) : C4minConn A G :=
  fun agents goods v hag hgd hc _ hs _ => h agents goods v hag hgd hc hs

/-- The removal-only form implies its connected variant. -/
theorem C4minROConn_of_C4minRO (h : TheoremC4minRO A G) : C4minROConn A G :=
  fun agents goods v hag hgd hc _ hs _ => h agents goods v hag hgd hc hs

/-- The connected removal-only form implies the connected completable form. -/
theorem C4minConn_of_C4minROConn (h : C4minROConn A G) : C4minConn A G :=
  fun agents goods v hag hgd hc hconn hs h4 => by
    obtain ⟨base, hmin, hR⟩ := h agents goods v hag hgd hc hconn hs h4
    have hne : agents ≠ [] := fun e => by have := hc.1; rw [e] at this; simp at this
    exact ⟨base, hmin, completable_of_removalOnly hag hgd hne hmin.1 hR⟩

/-- **C₄ᵐⁱⁿ on connected cores with a 4-good agent ⟹ C₄∃ there** (`EFX.LB4R.C4existsConn`). -/
theorem C4existsConn_of_C4minConn (h : C4minConn A G) : LB4R.C4existsConn A G :=
  fun agents goods v hag hgd hc hconn hs h4 => by
    obtain ⟨base, -, o, X, hS⟩ := h agents goods v hag hgd hc hconn hs h4
    exact ⟨base, vbNeeds v goods base, o, X, hS⟩

/-- **C₄ᵐⁱⁿ on connected cores with a 4-good agent ⟹ TARGET₄** (`EFX.LB4R.target4_of_C4existsConn`). -/
theorem target4_of_C4minConn (I : Inst) (hn : 0 < I.n) (hC : C4minConn (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  LB4R.target4_of_C4existsConn I hn (C4existsConn_of_C4minConn hC) h

/-- **C₄ᵐⁱⁿ (removal-only form) on connected cores with a 4-good agent ⟹ TARGET₄.** -/
theorem target4_of_C4minROConn (I : Inst) (hn : 0 < I.n) (hC : C4minROConn (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4minConn I hn (C4minConn_of_C4minROConn hC) h

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.completable_of_removalOnly
#print axioms EFX.C4min.inP_phase1
#print axioms EFX.C4min.exists_minFrozen
#print axioms EFX.C4min.C4exists_of_C4min
#print axioms EFX.C4min.C4min_of_C4minRO
#print axioms EFX.C4min.k4D_of_C4min
#print axioms EFX.C4min.target4_of_C4min
#print axioms EFX.C4min.target4_of_C4minRO
#print axioms EFX.C4min.C4minConn_of_C4min
#print axioms EFX.C4min.C4minROConn_of_C4minRO
#print axioms EFX.C4min.C4minConn_of_C4minROConn
#print axioms EFX.C4min.C4existsConn_of_C4minConn
#print axioms EFX.C4min.target4_of_C4minConn
#print axioms EFX.C4min.target4_of_C4minROConn
