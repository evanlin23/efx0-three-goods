import EFX.ThmZ

/-!
# Theorem F: C₄ᵐⁱⁿ when some configuration has only robust frozen agents (`k4/c4min.md` §3.6; PR #41)

Theorem F of `k4/c4min.md` (PR #41, branch `proof/k4-c4min`): on every k = 4 core, if some configuration at the fewest
frozen agents has only robust frozen agents, some pre-allocation of 𝒫 with the fewest frozen agents has `def(P) ≤ 0` and
is completable. With no frozen agent it is Theorem Z (`EFX/ThmZ.lean`).

**Definitions** (`k4/c4min.md` §1, §3.6), over the lists of `EFX/C4min.lean` and the APAs of `EFX/ThmZ.lean`.
- `IsCfg`: a configuration with frozen agents `fr : A → Bool`, as a holding map `hold : G → Option A` (`none` for the
  pool). Every frozen agent holds one good, relevant to it. Every free agent holds a pair. No agent has a need outside
  `𝒩`, the goods of the frozen agents (`frG`): a good outside its holding and `𝒩` is worth at most its holding.
  `M′ = M ∖ 𝒩` is `outN`, and the free agents are `freeA`.
- "At the fewest frozen agents" is the hypothesis `hmin`: no pre-allocation of 𝒫 has fewer frozen agents than `fr` has
  agents. Then the configuration's pre-allocation (the relevant goods of the holdings, `apaBase`) is in 𝒫 (`inP_cfg`)
  and has the fewest frozen agents (`minFrozen_cfg`). Its frozen agents are exactly those of `fr`, so every good of `𝒩` is
  needed (`fr_of_frozen`, `frozen_of_min`).
- `FRobust`: every frozen agent `x` has `v_x(M′) ≤ v_x(φ(x))` (the text's `v_x(U_x) ≤ v_x(φ(x))`). A free agent is
  robust when it is robust over `M′` (`ZRobust` over `outN`), i.e. against `U_y = R_y ∖ 𝒩`.

**Results.**
- `rigid_NA` (Lemma 1, rigidity): at the fewest frozen agents, `NA(P′) ⊆ NA(P)` gives `NA(P′) = NA(P)`, and `P′` has
  the fewest frozen agents too.
- `removalOnly_of_cfg` (Lemma 1(a) with `C = ∅`): a free agent that threatens nobody gives `def(P) ≤ 0`.
- `isAPA_sub`, `zthreat_outN`, `not_threat_frozen`: the free agents form an APA over `M′` (Theorem Z's setting, with
  `U_y` in place of `R_y`), threats among them are the same there, and a robust frozen agent is threatened by no free
  agent.
- `isCfg_joinH`, `fRobust_joinH`, `nRobust_joinH`: any APA of the free agents over `M′`, joined with the frozen goods, is
  again a frozen-robust configuration.
- `fmax_poolOpt`, `fmax_nRobust` (Lemma Z1 among the free agents): a frozen-robust configuration with the largest
  potential (`fPot`: robust free agents, then welfare) is pool-optimal over `M′`, and has the most robust free agents
  among all APAs of the free agents over `M′`.
- `frozen_cycle` (the last step): at such a maximum, if some agent is frozen, not every free agent can have four relevant
  goods outside `𝒩`. Otherwise every frozen good would be needed by another frozen agent, the needs would contain a cycle
  (`exists_cycle`), and rotating it would raise the welfare.
- `theoremF_min`, `theoremF`, `c4minRO_of_frobust` (**Theorem F**). With no frozen agent it is `theoremZ_min`.
  Otherwise, at a maximum, Lemmas P and R on the free agents over `M′` (`zvalid_or_all4`) give a free agent that
  threatens no free agent. It threatens no frozen agent either, and Lemma 1(a) applies.

**Choices where the prose leaves room** (the text is `k4/c4min.md` §3.6 on branch `proof/k4-c4min`, PR #41, read at
commit b9ff629).
1. A configuration is given by its holdings and its frozen agents. "At the fewest frozen agents" is the hypothesis
   `hmin`, and the configuration's frozen goods are then needed (rigidity), as in §1.
2. The potential is (robust free agents, welfare `Σ_i v_i(H_i)`) over the frozen-robust configurations with the given
   frozen agents, instead of the text's `(r, Λ)`. `r` counts only free agents, since every frozen agent is robust. The
   theorem holds at every maximum.
3. The free agents' part of the proof (pool-optimality, Lemmas Z2, P and R) is not redone. It is Theorem Z's, applied to
   the free agents over `M′` (`zvalid_or_all4`). For this, Theorem Z's lemmas assume only `|R_i| ≤ 4`: a free agent may
   have fewer than three relevant goods outside `𝒩`, and then it is robust (`robust_of_rel_le2`). The text's kinds
   (T3), (T4), (D) and (R) are covered this way.
4. The frozen cycle is a set of frozen agents that the needing map sends injectively into itself (`exists_cycle`); all of
   it is rotated.
5. Hypotheses used (`theoremF_min`): at least one agent, `|R_i| ≤ 4`, a frozen-robust configuration, and `hmin`. With no
   frozen agent (Theorem Z), every good must also be relevant to some agent. Strict values, balance, the private-goods
   rule, connectivity and the text's `ω ≥ 1` are not used.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-! ## Configurations -/

/-- `g` is a good of the needed set `𝒩`: it is held by a frozen agent. -/
def frG (fr : A → Bool) (hold : G → Option A) (g : G) : Bool :=
  match hold g with
  | some z => fr z
  | none => false

/-- `M′ = M ∖ 𝒩`: the goods not held by a frozen agent. -/
def outN (goods : List G) (fr : A → Bool) (hold : G → Option A) : List G :=
  goods.filter (fun g => !frG fr hold g)

/-- The free agents. -/
def freeA (agents : List A) (fr : A → Bool) : List A := agents.filter (fun i => !fr i)

/-- **A configuration** (`k4/c4min.md` §1) with frozen agents `fr`, as a holding map (`none` for the pool): every frozen
agent holds one good, relevant to it (its good of `𝒩`); every free agent holds a pair; and no agent has a need outside
`𝒩` (no good outside its holding and `𝒩` is worth more to it than its holding). The pool is `M′` minus the pairs. -/
structure IsCfg (v : A → G → Nat) (agents : List A) (goods : List G) (fr : A → Bool) (hold : G → Option A) :
    Prop where
  mem : ∀ g ∈ goods, ∀ i, hold g = some i → i ∈ agents
  frz : ∀ x ∈ agents, fr x = true → ∃ y, baseOf goods hold x = [y] ∧ 0 < v x y
  pair : ∀ i ∈ agents, fr i = false → (baseOf goods hold i).length = 2
  adm : ∀ i ∈ agents, ∀ g ∈ goods, hold g ≠ some i → value v i (baseOf goods hold i) < v i g →
    frG fr hold g = true

/-- **Frozen-robust** (`k4/c4min.md` §3.6): every frozen agent values its good at least as much as all goods of `M′`
together, `v_x(U_x) ≤ v_x(φ(x))`. -/
def FRobust (v : A → G → Nat) (agents : List A) (goods : List G) (fr : A → Bool) (hold : G → Option A) : Prop :=
  ∀ x ∈ agents, fr x = true → value v x (outN goods fr hold) ≤ value v x (baseOf goods hold x)

omit [DecidableEq A] [DecidableEq G] in
theorem frG_eq_true {fr : A → Bool} {hold : G → Option A} {g : G} :
    frG fr hold g = true ↔ ∃ z, hold g = some z ∧ fr z = true := by
  unfold frG
  cases hold g with
  | none => simp
  | some z => simp

omit [DecidableEq A] [DecidableEq G] in
theorem mem_outN {fr : A → Bool} {hold : G → Option A} {g : G} :
    g ∈ outN goods fr hold ↔ g ∈ goods ∧ frG fr hold g = false := by
  unfold outN; simp

omit [DecidableEq A] [DecidableEq G] in
theorem mem_freeA {fr : A → Bool} {i : A} : i ∈ freeA agents fr ↔ i ∈ agents ∧ fr i = false := by
  unfold freeA; simp

section cfg
variable {fr : A → Bool} {hold : G → Option A}

omit [DecidableEq G] in
/-- For a free agent, `Q_i` is the same over `M′`. -/
theorem baseOf_outN {i : A} (hi : fr i = false) : baseOf (outN goods fr hold) hold i = baseOf goods hold i := by
  unfold baseOf outN
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  by_cases h : hold g = some i
  · simp [h, frG, hi]
  · simp [h]

omit [DecidableEq G] in
/-- For a free agent, `Q_o ∪ L` is the same over `M′`. -/
theorem W_outN {o : A} (ho : fr o = false) : W (outN goods fr hold) hold o = W goods hold o := by
  unfold W outN
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  by_cases h : hold g = some o
  · simp [h, frG, ho]
  · by_cases h' : hold g = none
    · simp [h', frG]
    · simp [h, h']

omit [DecidableEq G] in
/-- **The free agents form an APA over `M′`** (the sub-instance of `k4/c4min.md` §3.6: Theorem Z's argument runs among
the free agents, with `U_y = R_y ∖ 𝒩` in place of `R_y`). -/
theorem isAPA_sub (hC : IsCfg v agents goods fr hold) : IsAPA v (freeA agents fr) (outN goods fr hold) hold := by
  refine ⟨fun g hg i hi => ?_, fun i hi => ?_, fun i hi g ⟨hg, hgi, hlt⟩ => ?_⟩
  · obtain ⟨hgg, hf⟩ := mem_outN.mp hg
    refine mem_freeA.mpr ⟨hC.mem g hgg i hi, ?_⟩
    cases h : fr i
    · rfl
    · simp [frG, hi, h] at hf
  · obtain ⟨hia, hf⟩ := mem_freeA.mp hi
    rw [baseOf_outN hf]; exact hC.pair i hia hf
  · obtain ⟨hia, hf⟩ := mem_freeA.mp hi
    obtain ⟨hgg, hgf⟩ := mem_outN.mp hg
    rw [baseOf_outN hf] at hlt
    have := hC.adm i hia g hgg hgi hlt
    rw [hgf] at this; cases this

/-- Threats among free agents are the same over `M′`. -/
theorem zthreat_outN {o j : A} (ho : fr o = false) (hj : fr j = false) :
    ZThreat v (outN goods fr hold) hold o j ↔ ZThreat v goods hold o j := by
  unfold ZThreat; rw [W_outN ho, baseOf_outN hj]

/-- A robust frozen agent is threatened by no free agent: `Q_o ∪ L ⊆ M′`. -/
theorem not_threat_frozen (hR : FRobust v agents goods fr hold) {o x : A} (ho : fr o = false) (hx : x ∈ agents)
    (hfx : fr x = true) : ¬ ZThreat v goods hold o x := by
  rintro ⟨h, _, hlt⟩
  have hsub : ((W goods hold o).erase h).Sublist (outN goods fr hold) := by
    refine List.erase_sublist.trans ?_
    unfold W outN
    refine LB4.filter_sublist_of_imp fun g _ hg => ?_
    simp only [decide_eq_true_eq] at hg
    rcases hg with hg | hg <;> simp [frG, hg, ho]
  have := value_sublist v x hsub
  have := hR x hx hfx
  omega

omit [DecidableEq G] in
/-- In a configuration, every need (of the relevant goods of the holdings) is a good of `𝒩`. -/
theorem needs_cfg (hC : IsCfg v agents goods fr hold) {i : A} (hi : i ∈ agents) {g : G}
    (hN : vbNeeds v goods (apaBase v hold) i g) : frG fr hold g = true := by
  obtain ⟨hg, hgb, hlt⟩ := hN
  rw [value_apaBase] at hlt
  exact hC.adm i hi g hg (fun hh => hgb (apaBase_eq_some.mpr ⟨hh, by omega⟩)) hlt

omit [DecidableEq G] in
/-- A good of `𝒩` is the base of its frozen holder. -/
theorem apaBase_frozen (hC : IsCfg v agents goods fr hold) {g : G} (hg : g ∈ goods) {x : A}
    (hx : hold g = some x) (hfx : fr x = true) : apaBase v hold g = some x := by
  obtain ⟨y, hy, hpos⟩ := hC.frz x (hC.mem g hg x hx) hfx
  have : g ∈ baseOf goods hold x := mem_baseOf.mpr ⟨hg, hx⟩
  rw [hy, List.mem_singleton] at this
  subst this
  exact apaBase_eq_some.mpr ⟨hx, hpos⟩

omit [DecidableEq G] in
/-- **A configuration is a pre-allocation of 𝒫** (the bases are the relevant goods of the holdings). -/
theorem inP_cfg (hC : IsCfg v agents goods fr hold) : InP v agents goods (apaBase v hold) := by
  have hNA : ∀ g, NA agents (vbNeeds v goods (apaBase v hold)) g →
      ∃ x, fr x = true ∧ apaBase v hold g = some x := fun g ⟨i, hi, hN⟩ => by
    obtain ⟨x, hx, hfx⟩ := frG_eq_true.mp (needs_cfg hC hi hN)
    exact ⟨x, hfx, apaBase_frozen hC hN.1 hx hfx⟩
  have hlen : ∀ i, (baseOf goods hold i).length ≤ 2 := fun i => by
    by_cases hi : i ∈ agents
    · cases hf : fr i
      · rw [hC.pair i hi hf]; exact Nat.le_refl _
      · obtain ⟨y, hy, -⟩ := hC.frz i hi hf; rw [hy]; simp
    · have : baseOf goods hold i = [] := List.eq_nil_iff_forall_not_mem.mpr fun g hg =>
        hi (hC.mem g (mem_baseOf.mp hg).1 i (mem_baseOf.mp hg).2)
      rw [this]; simp
  refine ⟨fun g hg i hb => hC.mem g hg i (apaBase_eq_some.mp hb).1,
    fun g _ i hb => (apaBase_eq_some.mp hb).2, fun i => ?_, ⟨fun g hg hN => ?_, fun i h2 g hg hN => ?_⟩⟩
  · rw [baseOf_apaBase]
    exact Nat.le_trans (List.length_filter_le _ _) (hlen i)
  · obtain ⟨x, -, hb⟩ := hNA g hN
    rw [(mem_junk.mp hg).2] at hb; cases hb
  · obtain ⟨x, hfx, hb⟩ := hNA g hN
    obtain ⟨hgg, hgi⟩ := mem_baseOf.mp hg
    rw [hgi] at hb; cases hb
    have hia : i ∈ agents := hC.mem g hgg i (apaBase_eq_some.mp hgi).1
    obtain ⟨y, hy, -⟩ := hC.frz i hia hfx
    rw [baseOf_apaBase, hy] at h2
    have := List.length_filter_le (fun g => decide (0 < v i g)) [y]
    simp only [List.length_singleton] at this
    omega

omit [DecidableEq G] in
/-- Only agents of `fr` are frozen in a configuration. -/
theorem fr_of_frozen (hC : IsCfg v agents goods fr hold) {j : A}
    (hF : Frozen agents goods (apaBase v hold) (vbNeeds v goods (apaBase v hold)) j) : fr j = true := by
  obtain ⟨y, hy, i, hi, hN⟩ := hF
  obtain ⟨x, hx, hfx⟩ := frG_eq_true.mp (needs_cfg hC hi hN)
  have : y ∈ baseOf goods (apaBase v hold) j := by rw [hy]; simp
  obtain ⟨hyg, hyb⟩ := mem_baseOf.mp this
  rw [apaBase_frozen hC hyg hx hfx] at hyb
  cases hyb; exact hfx

omit [DecidableEq G] in
theorem nFrozen_cfg_le (hC : IsCfg v agents goods fr hold) :
    nFrozen v agents goods (apaBase v hold) ≤ agents.countP fr := by
  classical
  unfold nFrozen numFrozen
  apply List.countP_mono_left
  intro j _ h
  exact fr_of_frozen hC (of_decide_eq_true h)

end cfg

/-! ## The fewest frozen agents, and the owner step -/

/-- If `p → q` on `l` and `q` holds at most as often as `p`, then `q → p` on `l`. -/
theorem countP_imp_eq {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
    l.countP q ≤ l.countP p → ∀ x ∈ l, q x = true → p x = true
  | [], _, _, x, hx, _ => by simp at hx
  | a :: l, himp, hle, x, hx, hq => by
    have himp' : ∀ x ∈ l, p x = true → q x = true := fun x hx => himp x (by simp [hx])
    have hmono : l.countP p ≤ l.countP q := List.countP_mono_left himp'
    have ha := himp a (by simp)
    rw [List.countP_cons, List.countP_cons] at hle
    rcases List.mem_cons.mp hx with rfl | hx
    · cases hpx : p x
      · rw [hq, hpx] at hle; simp at hle; omega
      · rfl
    · refine countP_imp_eq himp' ?_ x hx hq
      cases hpa : p a
      · cases hqa : q a <;> simp [hpa, hqa] at hle <;> omega
      · rw [ha hpa, hpa] at hle; simp at hle; omega

omit [DecidableEq G] in
/-- **Lemma 1, rigidity of the needed set** (`k4/c4min.md` §1): if `P` has the fewest frozen agents and `P′ ∈ 𝒫` has
`NA(P′) ⊆ NA(P)`, then `NA(P′) = NA(P)` and `P′` has the fewest frozen agents too, since `|F(P′)| = |NA(P′)|` in a
valid pre-allocation (`EFX.LB4.numFrozen_eq`). -/
theorem rigid_NA (hag : agents.Nodup) (hgd : goods.Nodup) {base base' : G → Option A}
    (hM : MinFrozen v agents goods base) (hP' : InP v agents goods base')
    (hsub : ∀ g ∈ goods, NA agents (vbNeeds v goods base') g → NA agents (vbNeeds v goods base) g) :
    (∀ g ∈ goods, NA agents (vbNeeds v goods base) g → NA agents (vbNeeds v goods base') g) ∧
      MinFrozen v agents goods base' := by
  classical
  have e1 : nFrozen v agents goods base = numNA agents goods (vbNeeds v goods base) :=
    numFrozen_eq hM.1.valid hag hgd hM.1.mem
  have e2 : nFrozen v agents goods base' = numNA agents goods (vbNeeds v goods base') :=
    numFrozen_eq hP'.valid hag hgd hP'.mem
  have himp : ∀ g ∈ goods, decide (NA agents (vbNeeds v goods base') g) = true →
      decide (NA agents (vbNeeds v goods base) g) = true :=
    fun g hg h => decide_eq_true (hsub g hg (of_decide_eq_true h))
  have hle : numNA agents goods (vbNeeds v goods base') ≤ numNA agents goods (vbNeeds v goods base) := by
    unfold numNA; exact List.countP_mono_left himp
  have hmin := hM.2 base' hP'
  refine ⟨fun g hg h => of_decide_eq_true (countP_imp_eq himp ?_ g hg (decide_eq_true h)), hP', fun b hb => ?_⟩
  · have : numNA agents goods (vbNeeds v goods base) ≤ numNA agents goods (vbNeeds v goods base') := by omega
    unfold numNA at this; exact this
  · have := hM.2 b hb; omega

section cfg
variable {fr : A → Bool} {hold : G → Option A}

omit [DecidableEq G] in
/-- **Rigidity at the fewest frozen agents** (`k4/c4min.md` §1): if no pre-allocation of 𝒫 has fewer frozen agents than
`fr` has agents, every agent of `fr` is frozen in the configuration, i.e. its good is needed. -/
theorem frozen_of_min (hC : IsCfg v agents goods fr hold)
    (hmin : ∀ base, InP v agents goods base → agents.countP fr ≤ nFrozen v agents goods base)
    {x : A} (hx : x ∈ agents) (hfx : fr x = true) :
    Frozen agents goods (apaBase v hold) (vbNeeds v goods (apaBase v hold)) x := by
  classical
  have h := hmin _ (inP_cfg hC)
  unfold nFrozen numFrozen at h
  exact of_decide_eq_true (countP_imp_eq (fun j _ hj => fr_of_frozen hC (of_decide_eq_true hj)) h x hx hfx)

omit [DecidableEq G] in
/-- At the fewest frozen agents, the configuration's pre-allocation has the fewest frozen agents. -/
theorem minFrozen_cfg (hC : IsCfg v agents goods fr hold)
    (hmin : ∀ base, InP v agents goods base → agents.countP fr ≤ nFrozen v agents goods base) :
    MinFrozen v agents goods (apaBase v hold) :=
  ⟨inP_cfg hC, fun b hb => Nat.le_trans (nFrozen_cfg_le hC) (hmin b hb)⟩

/-- **Lemma 1(a) with `C = ∅`** (`k4/c4min.md` §1): if a free agent `o` of a configuration threatens nobody, the
configuration's pre-allocation has `def(P) ≤ 0`: owner `o`, and the removed goods are the other free agents' pairs,
whose irrelevant goods fill exactly those agents' slots; the owner keeps `Q_o ∪ L`. -/
theorem removalOnly_of_cfg (hC : IsCfg v agents goods fr hold) {o : A} (ho : o ∈ agents) (hfo : fr o = false)
    (hV : ∀ x ∈ agents, x ≠ o → ¬ ZThreat v goods hold o x) : RemovalOnly v agents goods (apaBase v hold) := by
  classical
  by_cases hω : omegaP v agents goods (apaBase v hold) ≤ 0
  · exact Or.inl ⟨hω, hω⟩
  have hNF : ∀ j, fr j = false → ¬ Frozen agents goods (apaBase v hold) (vbNeeds v goods (apaBase v hold)) j :=
    fun j hj hF => by rw [fr_of_frozen hC hF] at hj; cases hj
  let C : G → Bool := fun g => match hold g with
    | some j => decide (j ≠ o)
    | none => false
  have hOB : ownerBundle goods (apaBase v hold) o C = W goods hold o := by
    unfold ownerBundle W
    apply List.filter_congr
    intro g _
    unfold apaBase
    cases h : hold g with
    | none => simp [C, h]
    | some j =>
      by_cases hj : j = o
      · subst hj; by_cases hp : 0 < v j g <;> simp [C, h, hp]
      · by_cases hp : 0 < v j g <;> simp [C, h, hp, hj]
  refine removalOnly_of_owner (by omega) ho (hNF o hfo) C ?_ ?_
  · intro x hx hxo h hh
    rw [hOB] at hh ⊢
    rw [value_apaBase]
    exact Nat.le_of_not_lt fun hlt => hV x hx hxo ⟨h, hh, hlt⟩
  · let p : A → G → Bool := fun j g => decide (j ≠ o ∧ hold g = some j ∧ ¬ 0 < v j g)
    have h1 : ((LB4.junk goods (apaBase v hold)).filter C).length ≤
        (goods.map (fun g => agents.countP (fun j => p j g))).sum := by
      unfold LB4.junk
      rw [List.filter_filter, ← List.countP_eq_length_filter]
      apply countP_le_sum_of
      intro g hg hpg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpg
      obtain ⟨hCg, hb⟩ := hpg
      cases h : hold g with
      | none => simp [C, h] at hCg
      | some j =>
        have hjo : j ≠ o := by simpa [C, h] using hCg
        have hnp : ¬ 0 < v j g := fun hp => by rw [apaBase_eq_some.mpr ⟨h, hp⟩] at hb; cases hb
        exact List.countP_pos_iff.mpr ⟨j, hC.mem g hg j h, by simp [p, hjo, h]; omega⟩
    have h2 := LB4.sum_countP_comm p agents goods
    have h3 : (agents.map (fun j => goods.countP (p j))).sum ≤
        otherSlots agents goods (apaBase v hold) (vbNeeds v goods (apaBase v hold)) o := by
      unfold otherSlots
      apply LB4.sum_le_sum_of_le
      intro j hj
      by_cases hjo : j = o
      · have : goods.countP (p j) = 0 := List.countP_eq_zero.mpr fun g _ h => by simp [p, hjo] at h
        rw [this]; exact Nat.zero_le _
      · cases hfj : fr j
        · have hif : ¬ (j = o ∨ Frozen agents goods (apaBase v hold) (vbNeeds v goods (apaBase v hold)) j) :=
            fun h => h.elim hjo (hNF j hfj)
          simp only [hif, ↓reduceIte]
          rw [baseOf_apaBase]
          have e : goods.countP (p j) = (baseOf goods hold j).countP (fun g => decide (¬ 0 < v j g)) := by
            unfold baseOf
            rw [List.countP_filter]
            apply List.countP_congr
            intro g _
            simp only [p, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨-, hh, hn⟩; exact ⟨hn, hh⟩
            · rintro ⟨hn, hh⟩; exact ⟨hjo, hh, hn⟩
          rw [e, ← List.countP_eq_length_filter]
          have hl := List.length_eq_countP_add_countP (fun g => decide (0 < v j g)) (l := baseOf goods hold j)
          simp only [decide_eq_true_eq] at hl
          rw [hC.pair j hj hfj] at hl
          omega
        · -- a frozen agent's one good is relevant: it holds no junk
          have : goods.countP (p j) = 0 := List.countP_eq_zero.mpr fun g hg h => by
            simp only [p, decide_eq_true_eq] at h
            obtain ⟨-, hh, hn⟩ := h
            obtain ⟨y, hy, hpos⟩ := hC.frz j hj hfj
            have : g ∈ baseOf goods hold j := mem_baseOf.mpr ⟨hg, hh⟩
            rw [hy, List.mem_singleton] at this
            subst this; exact hn hpos
          rw [this]; exact Nat.zero_le _
    omega

/-! ## Joining the frozen goods of one configuration with an APA of the free agents -/

/-- The goods of `𝒩` as in `hold`, the other goods as in `hold'`. -/
def joinH (fr : A → Bool) (hold hold' : G → Option A) (g : G) : Option A :=
  if frG fr hold g = true then hold g else hold' g

section join
variable {hold' : G → Option A}

omit [DecidableEq A] [DecidableEq G] in
theorem joinH_of_out {g : G} (hg : frG fr hold g = false) : joinH fr hold hold' g = hold' g := by
  simp [joinH, hg]

omit [DecidableEq A] [DecidableEq G] in
theorem joinH_of_in {g : G} (hg : frG fr hold g = true) : joinH fr hold hold' g = hold g := by
  simp [joinH, hg]

omit [DecidableEq G] in
theorem frG_joinH (hA' : IsAPA v (freeA agents fr) (outN goods fr hold) hold') {g : G} (hg : g ∈ goods) :
    frG fr (joinH fr hold hold') g = frG fr hold g := by
  cases h : frG fr hold g
  · unfold frG
    rw [joinH_of_out h]
    cases h' : hold' g with
    | none => rfl
    | some i => exact (mem_freeA.mp (hA'.mem g (mem_outN.mpr ⟨hg, h⟩) i h')).2
  · unfold frG
    rw [joinH_of_in h]
    exact h

omit [DecidableEq G] in
theorem outN_joinH (hA' : IsAPA v (freeA agents fr) (outN goods fr hold) hold') :
    outN goods fr (joinH fr hold hold') = outN goods fr hold := by
  unfold outN
  apply List.filter_congr
  intro g hg
  rw [frG_joinH hA' hg]

omit [DecidableEq G] in
/-- Over `M′`, the join is `hold'`. -/
theorem baseOf_joinH_out (i : A) :
    baseOf (outN goods fr hold) (joinH fr hold hold') i = baseOf (outN goods fr hold) hold' i := by
  apply baseOf_congr
  intro g hg
  rw [joinH_of_out (mem_outN.mp hg).2]

omit [DecidableEq G] in
theorem baseOf_joinH_free {i : A} (hi : fr i = false) :
    baseOf goods (joinH fr hold hold') i = baseOf (outN goods fr hold) hold' i := by
  unfold baseOf outN
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  cases h : frG fr hold g
  · rw [joinH_of_out h]; simp
  · rw [joinH_of_in h]
    obtain ⟨z, hz, hfz⟩ := frG_eq_true.mp h
    have : z ≠ i := fun e => by rw [e, hi] at hfz; cases hfz
    simp [hz, this]

omit [DecidableEq G] in
theorem baseOf_joinH_frozen (hA' : IsAPA v (freeA agents fr) (outN goods fr hold) hold') {x : A}
    (hx : fr x = true) : baseOf goods (joinH fr hold hold') x = baseOf goods hold x := by
  apply baseOf_congr
  intro g hg
  cases h : frG fr hold g
  · rw [joinH_of_out h]
    constructor
    · intro h'
      have := (mem_freeA.mp (hA'.mem g (mem_outN.mpr ⟨hg, h⟩) x h')).2
      rw [hx] at this; cases this
    · intro h'
      simp [frG, h', hx] at h
  · rw [joinH_of_in h]

omit [DecidableEq G] in
/-- **The join is a configuration**, frozen-robust if the first one is. -/
theorem isCfg_joinH (hC : IsCfg v agents goods fr hold) (hA' : IsAPA v (freeA agents fr) (outN goods fr hold) hold') :
    IsCfg v agents goods fr (joinH fr hold hold') := by
  refine ⟨fun g hg i hi => ?_, fun x hx hfx => ?_, fun i hi hfi => ?_, fun i hi g hg hgi hlt => ?_⟩
  · cases h : frG fr hold g
    · rw [joinH_of_out h] at hi
      exact (mem_freeA.mp (hA'.mem g (mem_outN.mpr ⟨hg, h⟩) i hi)).1
    · rw [joinH_of_in h] at hi
      exact hC.mem g hg i hi
  · rw [baseOf_joinH_frozen hA' hfx]; exact hC.frz x hx hfx
  · rw [baseOf_joinH_free hfi]; exact hA'.pair i (mem_freeA.mpr ⟨hi, hfi⟩)
  · rw [frG_joinH hA' hg]
    cases hfi : fr i
    · rw [baseOf_joinH_free hfi] at hlt
      cases h : frG fr hold g
      · rw [joinH_of_out h] at hgi
        exact absurd ⟨mem_outN.mpr ⟨hg, h⟩, hgi, hlt⟩ (hA'.adm i (mem_freeA.mpr ⟨hi, hfi⟩) g)
      · rfl
    · rw [baseOf_joinH_frozen hA' hfi] at hlt
      refine hC.adm i hi g hg (fun hh => hgi ?_) hlt
      have : frG fr hold g = true := by simp [frG, hh, hfi]
      rw [joinH_of_in this, hh]

omit [DecidableEq G] in
theorem fRobust_joinH (hR : FRobust v agents goods fr hold)
    (hA' : IsAPA v (freeA agents fr) (outN goods fr hold) hold') : FRobust v agents goods fr (joinH fr hold hold') := by
  intro x hx hfx
  rw [outN_joinH hA', baseOf_joinH_frozen hA' hfx]
  exact hR x hx hfx

omit [DecidableEq G] in
/-- The robust free agents of the join are those of `hold'` over `M′`. -/
theorem nRobust_joinH (hA' : IsAPA v (freeA agents fr) (outN goods fr hold) hold') :
    nRobust v (freeA agents fr) (outN goods fr (joinH fr hold hold')) (joinH fr hold hold') =
      nRobust v (freeA agents fr) (outN goods fr hold) hold' := by
  unfold nRobust ZRobust
  rw [outN_joinH hA']
  apply List.countP_congr
  intro i _
  rw [baseOf_joinH_out]

end join

end cfg

/-! ## The potential: robust free agents, then welfare -/

/-- The potential of a configuration, `r · (B + 1) + Σ_i v_i(H_i)`: `r` counts the robust free agents over `M′` (against
`U_y = R_y ∖ 𝒩`) and `B = Σ_i v_i(M)` bounds the welfare, as `zPot` of Theorem Z (the text's `(r, Λ)`; see the module
doc). -/
noncomputable def fPot (v : A → G → Nat) (agents : List A) (goods : List G) (fr : A → Bool) (hold : G → Option A) :
    Nat :=
  nRobust v (freeA agents fr) (outN goods fr hold) hold * ((agents.map (fun i => value v i goods)).sum + 1) +
    welfare v agents goods hold

/-- A function bounded on a nonempty set has a maximum there. -/
theorem exists_max_of_bdd {α : Type} (P : α → Prop) (f : α → Nat) (B : Nat) (hB : ∀ a, P a → f a ≤ B)
    (h : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  have key : ∀ d, ∀ a, P a → B - f a = d → ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a ha hd
      by_cases hm : ∀ b, P b → f b ≤ f a
      · exact ⟨a, ha, hm⟩
      · obtain ⟨b, hb, hlt⟩ : ∃ b, P b ∧ f a < f b := Classical.byContradiction fun hno =>
          hm fun b hb => Nat.le_of_not_lt fun hl => hno ⟨b, hb, hl⟩
        exact ih _ (by have := hB b hb; omega) b hb rfl
  obtain ⟨a, ha⟩ := h
  exact key _ a ha rfl

section fmax
variable {fr : A → Bool} {hold : G → Option A}

omit [DecidableEq G] in
theorem fPot_le (hold : G → Option A) :
    fPot v agents goods fr hold ≤ agents.length * ((agents.map (fun i => value v i goods)).sum + 1) +
      (agents.map (fun i => value v i goods)).sum := by
  unfold fPot
  have h1 := nRobust_le (v := v) (agents := freeA agents fr) (goods := outN goods fr hold) hold
  have h2 : (freeA agents fr).length ≤ agents.length := List.length_filter_le _ _
  have h3 := zWelfare_le (v := v) (agents := agents) (goods := goods) hold
  have := Nat.mul_le_mul_right ((agents.map (fun i => value v i goods)).sum + 1) (Nat.le_trans h1 h2)
  unfold zWelfare at h3
  omega

omit [DecidableEq G] in
/-- More robust free agents, or as many and more welfare, is a larger potential. -/
theorem fPot_lt {h1 h2 : G → Option A}
    (h : nRobust v (freeA agents fr) (outN goods fr h1) h1 < nRobust v (freeA agents fr) (outN goods fr h2) h2 ∨
      (nRobust v (freeA agents fr) (outN goods fr h1) h1 ≤ nRobust v (freeA agents fr) (outN goods fr h2) h2 ∧
        welfare v agents goods h1 < welfare v agents goods h2)) :
    fPot v agents goods fr h1 < fPot v agents goods fr h2 := by
  unfold fPot
  obtain ⟨B, hB⟩ : ∃ B, B = (agents.map (fun i => value v i goods)).sum := ⟨_, rfl⟩
  rw [← hB]
  have hw1 := zWelfare_le (v := v) (agents := agents) (goods := goods) h1
  unfold zWelfare at hw1
  rw [← hB] at hw1
  rcases h with hr | ⟨hr, hw⟩
  · have := Nat.mul_le_mul_right (B + 1) hr
    rw [Nat.succ_mul] at this
    omega
  · have := Nat.mul_le_mul_right (B + 1) hr
    omega

/-- **Lemma Z1 among the free agents**: a frozen-robust configuration with the largest potential is pool-optimal over
`M′` (a pool improvement of a free agent keeps `𝒩` and the frozen agents, keeps the robust agents, and raises the
welfare). -/
theorem fmax_poolOpt (hgd : goods.Nodup) (hC : IsCfg v agents goods fr hold) (hR : FRobust v agents goods fr hold)
    (hmax : ∀ h, IsCfg v agents goods fr h → FRobust v agents goods fr h →
      fPot v agents goods fr h ≤ fPot v agents goods fr hold) :
    PoolOpt v (freeA agents fr) (outN goods fr hold) hold := by
  classical
  intro i hi S hS hS2 hSW
  refine Nat.le_of_not_lt fun hlt => ?_
  have hgd' : (outN goods fr hold).Nodup := hgd.sublist List.filter_sublist
  have hA := isAPA_sub hC
  have hA' := isAPA_poolImprove hgd' hA hi hS hS2 hSW hlt
  have hSg : ∀ g ∈ S, g ∈ outN goods fr hold := fun g hg => (mem_W.mp (hSW g hg)).1
  obtain ⟨hia, hfi⟩ := mem_freeA.mp hi
  have hval : ∀ j, value v j (baseOf (outN goods fr hold) hold j) ≤
      value v j (baseOf (outN goods fr hold) (poolImprove hold i S) j) := by
    intro j
    by_cases hji : j = i
    · subst hji; rw [value_poolImprove_self hgd' hS hSg]; omega
    · rw [baseOf_poolImprove_other hSW hji]; exact Nat.le_refl _
  have := hmax _ (isCfg_joinH hC hA') (fRobust_joinH hR hA')
  refine absurd this (Nat.not_le.mpr (fPot_lt (Or.inr ⟨?_, ?_⟩)))
  · rw [nRobust_joinH hA']
    unfold nRobust
    apply List.countP_mono_left
    intro j _ hjr
    have hj' : ZRobust v (outN goods fr hold) hold j := of_decide_eq_true hjr
    unfold ZRobust at hj'
    have := hval j
    exact decide_eq_true (by unfold ZRobust; omega)
  · unfold welfare
    apply sum_lt_of_le_of_lt
    · intro j _
      cases hfj : fr j
      · rw [baseOf_joinH_free hfj, ← baseOf_outN (goods := goods) (hold := hold) hfj]
        exact hval j
      · rw [baseOf_joinH_frozen hA' hfj]; exact Nat.le_refl _
    · refine ⟨i, hia, ?_⟩
      rw [baseOf_joinH_free hfi, value_poolImprove_self hgd' hS hSg, ← baseOf_outN (goods := goods) (hold := hold) hfi]
      exact hlt

omit [DecidableEq G] in
/-- A frozen-robust configuration with the largest potential has the most robust free agents among all APAs of the
free agents over `M′` (join them with its frozen goods). -/
theorem fmax_nRobust (hC : IsCfg v agents goods fr hold) (hR : FRobust v agents goods fr hold)
    (hmax : ∀ h, IsCfg v agents goods fr h → FRobust v agents goods fr h →
      fPot v agents goods fr h ≤ fPot v agents goods fr hold) :
    ∀ hold', IsAPA v (freeA agents fr) (outN goods fr hold) hold' →
      nRobust v (freeA agents fr) (outN goods fr hold) hold' ≤ nRobust v (freeA agents fr) (outN goods fr hold) hold := by
  intro hold' hA'
  refine Nat.le_of_not_lt fun hlt => ?_
  have := hmax _ (isCfg_joinH hC hA') (fRobust_joinH hR hA')
  refine absurd this (Nat.not_le.mpr (fPot_lt (Or.inl ?_)))
  rw [nRobust_joinH hA']; exact hlt

end fmax

/-! ## Cycles of frozen agents -/

theorem inj_on_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hxa | hxl <;> rcases List.mem_cons.mp hy with hya | hyl
    · rw [hxa, hya]
    · subst hxa; exact absurd (List.mem_map.mpr ⟨y, hyl, e.symm⟩) h.1
    · subst hya; exact absurd (List.mem_map.mpr ⟨x, hxl, e⟩) h.1
    · exact inj_on_of_nodup_map h.2 x hxl y hyl e

theorem exists_dup_erase {α : Type} [DecidableEq α] : ∀ {l : List α}, ¬ l.Nodup → ∃ a ∈ l, a ∈ l.erase a
  | [], h => absurd List.nodup_nil h
  | a :: l, h => by
    rw [List.nodup_cons] at h
    by_cases ha : a ∈ l
    · exact ⟨a, by simp, by simpa using ha⟩
    · obtain ⟨b, hb, hb'⟩ := exists_dup_erase fun hl => h ⟨ha, hl⟩
      have hab : b ≠ a := fun e => ha (e ▸ hb)
      refine ⟨b, by simp [hb], ?_⟩
      have hne' : (a == b) = false := by simp [Ne.symm hab]
      rw [List.erase_cons, hne']
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact List.mem_cons_of_mem _ hb'

/-- **A cycle of a self-map**: if `τ` maps a nonempty duplicate-free list `F` into itself, it maps some nonempty
duplicate-free sublist `S` of `F` into itself injectively (drop an element outside the image until none is). -/
theorem exists_cycle {α : Type} [DecidableEq α] (τ : α → α) : ∀ (n : Nat) (F : List α), F.length = n → F.Nodup →
    F ≠ [] → (∀ x ∈ F, τ x ∈ F) → ∃ S : List α, S ≠ [] ∧ S.Nodup ∧ (∀ x ∈ S, x ∈ F) ∧ (∀ x ∈ S, τ x ∈ S) ∧
      ∀ x ∈ S, ∀ y ∈ S, τ x = τ y → x = y := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F hn hF hne hτ
    by_cases hinj : ∀ x ∈ F, ∀ y ∈ F, τ x = τ y → x = y
    · exact ⟨F, hne, hF, fun x hx => hx, hτ, hinj⟩
    · obtain ⟨z, hzF, hz⟩ : ∃ z ∈ F, ∀ x ∈ F, τ x ≠ z := by
        refine Classical.byContradiction fun hno => hinj ?_
        have hcov : ∀ z ∈ F, z ∈ F.map τ := fun z hz => Classical.byContradiction fun hzm =>
          hno ⟨z, hz, fun x hx e => hzm (List.mem_map.mpr ⟨x, hx, e⟩)⟩
        have hnd : (F.map τ).Nodup := by
          refine Classical.byContradiction fun hnd => ?_
          obtain ⟨a, ha, ha'⟩ := exists_dup_erase hnd
          have := LB.length_le_of_subset hF (T := (F.map τ).erase a) fun z hz => by
            by_cases hza : z = a
            · subst hza; exact ha'
            · exact (List.mem_erase_of_ne hza).mpr (hcov z hz)
          rw [List.length_erase_of_mem ha, List.length_map] at this
          have := List.length_pos_iff.mpr hne
          omega
        exact inj_on_of_nodup_map hnd
      have hlen : (F.erase z).length = n - 1 := by rw [List.length_erase_of_mem hzF, hn]
      have hpos := List.length_pos_iff.mpr hne
      obtain ⟨S, hS, hSnd, hSF, hSτ, hSi⟩ := ih (n - 1) (by omega) (F.erase z) hlen (hF.erase z)
        (List.ne_nil_of_mem ((List.mem_erase_of_ne (hz z hzF)).mpr (hτ z hzF)))
        (fun x hx => (List.mem_erase_of_ne (hz x (List.mem_of_mem_erase hx))).mpr (hτ x (List.mem_of_mem_erase hx)))
      exact ⟨S, hS, hSnd, fun x hx => List.mem_of_mem_erase (hSF x hx), hSτ, hSi⟩

/-! ## The last step: a cycle of frozen agents -/

section last
variable {fr : A → Bool} {hold : G → Option A}

omit [DecidableEq G] in
/-- **The last step of Theorem F** (`k4/c4min.md` §3.6). At the fewest frozen agents, if some agent is frozen and every
free agent has four relevant goods, none of them in `𝒩`, then no frozen-robust configuration has the largest potential:
every frozen good is needed (rigidity), only by frozen agents, so the needs contain a cycle of frozen agents, and
rotating it (`x_{i+1}` takes `φ(x_i)`) gives every agent on it a better good of `𝒩`, keeps the configuration
frozen-robust and the free agents as they are, and raises the welfare. -/
theorem frozen_cycle (hag : agents.Nodup) (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hC : IsCfg v agents goods fr hold) (hR : FRobust v agents goods fr hold)
    (hmin : ∀ base, InP v agents goods base → agents.countP fr ≤ nFrozen v agents goods base)
    (hmax : ∀ h, IsCfg v agents goods fr h → FRobust v agents goods fr h →
      fPot v agents goods fr h ≤ fPot v agents goods fr hold)
    (hall : ∀ j ∈ freeA agents fr, (relevant v j (outN goods fr hold)).length = 4)
    (hf : ∃ x ∈ agents, fr x = true) : False := by
  classical
  -- every frozen agent's good is needed by another frozen agent
  have hneed : ∀ x ∈ agents, fr x = true → ∃ z, z ∈ agents ∧ fr z = true ∧ z ≠ x ∧
      ∃ y, baseOf goods hold x = [y] ∧ value v z (baseOf goods hold z) < v z y := by
    intro x hx hfx
    obtain ⟨y, hy, hpos⟩ := hC.frz x hx hfx
    obtain ⟨y', hy', z, hz, hN⟩ := frozen_of_min hC hmin hx hfx
    have hyy : y' = y := by
      rw [baseOf_apaBase, hy] at hy'
      simp only [List.filter_cons, decide_eq_true_eq, hpos, ↓reduceIte, List.filter_nil, List.cons.injEq,
        and_true] at hy'
      exact hy'.symm
    subst hyy
    obtain ⟨hyg, hyb, hlt⟩ := hN
    rw [value_apaBase] at hlt
    have hyx : hold y' = some x := (mem_baseOf.mp (by rw [hy]; simp : y' ∈ baseOf goods hold x)).2
    have hfy : frG fr hold y' = true := by simp [frG, hyx, hfx]
    refine ⟨z, hz, ?_, ?_, y', hy, hlt⟩
    · -- a free agent values no good of `𝒩`
      cases hfz : fr z
      · exfalso
        have h4z := hall z (mem_freeA.mpr ⟨hz, hfz⟩)
        have hsub : (relevant v z (outN goods fr hold)).Sublist (relevant v z goods) :=
          List.Sublist.filter _ List.filter_sublist
        have heq := hsub.eq_of_length (by have := h4 z hz; have := hsub.length_le; omega)
        have hyr : y' ∈ relevant v z goods := mem_relevant.mpr ⟨hyg, by omega⟩
        rw [← heq] at hyr
        have := (mem_outN.mp (mem_relevant.mp hyr).1).2
        rw [hfy] at this; cases this
      · rfl
    · rintro rfl
      exact hyb (apaBase_eq_some.mpr ⟨hyx, hpos⟩)
  -- the map to a needing frozen agent, and a cycle of it
  let τ : A → A := fun x => if h : x ∈ agents ∧ fr x = true then Classical.choose (hneed x h.1 h.2) else x
  have hτ : ∀ x ∈ agents, fr x = true → τ x ∈ agents ∧ fr (τ x) = true ∧ τ x ≠ x ∧
      ∃ y, baseOf goods hold x = [y] ∧ value v (τ x) (baseOf goods hold (τ x)) < v (τ x) y := fun x hx hfx => by
    have e : τ x = Classical.choose (hneed x hx hfx) := by simp [τ, hx, hfx]
    rw [e]; exact Classical.choose_spec (hneed x hx hfx)
  have hF : ∀ x, x ∈ agents.filter fr ↔ x ∈ agents ∧ fr x = true := fun x => by simp
  obtain ⟨x₀, hx₀, hfx₀⟩ := hf
  obtain ⟨S, hSne, hSnd, hSF, hSτ, hSinj⟩ := exists_cycle τ _ (agents.filter fr) rfl
    (hag.sublist List.filter_sublist) (List.ne_nil_of_mem ((hF x₀).mpr ⟨hx₀, hfx₀⟩))
    fun x hx => (hF _).mpr ⟨(hτ x ((hF x).mp hx).1 ((hF x).mp hx).2).1, (hτ x ((hF x).mp hx).1 ((hF x).mp hx).2).2.1⟩
  have hSa : ∀ x ∈ S, x ∈ agents ∧ fr x = true := fun x hx => (hF x).mp (hSF x hx)
  -- the rotation along the cycle
  let σ : A → A := fun y => if y ∈ S then τ y else y
  have hσS : ∀ y ∈ S, σ y = τ y := fun y hy => by simp [σ, hy]
  have hσn : ∀ y, y ∉ S → σ y = y := fun y hy => by simp [σ, hy]
  have hσfr : ∀ o ∈ agents, fr (σ o) = fr o := fun o _ => by
    by_cases hoS : o ∈ S
    · rw [hσS o hoS, (hSa _ (hSτ o hoS)).2, (hSa o hoS).2]
    · rw [hσn o hoS]
  have hinj : ∀ o ∈ agents, ∀ o' ∈ agents, σ o = σ o' → o = o' := fun o _ o' _ e => by
    by_cases hoS : o ∈ S <;> by_cases ho'S : o' ∈ S
    · rw [hσS o hoS, hσS o' ho'S] at e; exact hSinj o hoS o' ho'S e
    · rw [hσS o hoS, hσn o' ho'S] at e; exact absurd (e ▸ hSτ o hoS) ho'S
    · rw [hσn o hoS, hσS o' ho'S] at e; exact absurd (e.symm ▸ hSτ o' ho'S) hoS
    · rw [hσn o hoS, hσn o' ho'S] at e; exact e
  have hsurj : ∀ j ∈ agents, ∃ o ∈ agents, σ o = j := fun j hj => by
    by_cases hjS : j ∈ S
    · have hnd := LB.nodup_map_of_inj hSnd hSinj
      have hperm := perm_of_subset_length hnd hSnd (fun y hy => by
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy; exact hSτ o ho) (by simp)
      obtain ⟨o, ho, e⟩ := List.mem_map.mp (hperm.mem_iff.mpr hjS)
      exact ⟨o, (hSa o ho).1, by rw [hσS o ho, e]⟩
    · exact ⟨j, hj, hσn j hjS⟩
  let h2 := rotateH hold σ
  have hb : ∀ o ∈ agents, baseOf goods h2 (σ o) = baseOf goods hold o := fun o ho =>
    baseOf_rotateH hC.mem hinj ho
  have hfrG : ∀ g ∈ goods, frG fr h2 g = frG fr hold g := fun g hg => by
    unfold frG
    simp only [h2, rotateH]
    cases h : hold g with
    | none => rfl
    | some z => exact hσfr z (hC.mem g hg z h)
  have houtN : outN goods fr h2 = outN goods fr hold := by
    unfold outN
    apply List.filter_congr
    intro g hg
    rw [hfrG g hg]
  -- off the cycle nothing moves
  have hoff : ∀ i, i ∉ S → ∀ g, (h2 g = some i ↔ hold g = some i) := fun i hiS g => by
    simp only [h2, rotateH]
    cases h : hold g with
    | none => simp
    | some z =>
      simp only [Option.map_some, Option.some.injEq]
      by_cases hzS : z ∈ S
      · rw [hσS z hzS]
        constructor
        · intro e; exact absurd (e ▸ hSτ z hzS) hiS
        · intro e; subst e; exact absurd hzS hiS
      · rw [hσn z hzS]
  have hfreeS : ∀ i ∈ agents, fr i = false → i ∉ S := fun i _ hfi hiS => by
    rw [(hSa i hiS).2] at hfi; cases hfi
  -- the agents on the cycle gain
  have hgain : ∀ o ∈ S, value v (τ o) (baseOf goods hold (τ o)) < value v (τ o) (baseOf goods hold o) := by
    intro o hoS
    obtain ⟨-, -, -, y, hy, hlt⟩ := hτ o (hSa o hoS).1 (hSa o hoS).2
    rw [hy]; simp only [value_cons, value_nil, Nat.add_zero]; exact hlt
  have hle : ∀ o ∈ agents, value v (σ o) (baseOf goods hold (σ o)) ≤ value v (σ o) (baseOf goods hold o) :=
    fun o _ => by
      by_cases hoS : o ∈ S
      · rw [hσS o hoS]; exact Nat.le_of_lt (hgain o hoS)
      · rw [hσn o hoS]; exact Nat.le_refl _
  -- the rotated holding is a frozen-robust configuration
  have hC2 : IsCfg v agents goods fr h2 := by
    refine ⟨fun g hg i hi => ?_, fun x hx hfx => ?_, fun i hi hfi => ?_, fun i hi g hg hgi hlt => ?_⟩
    · simp only [h2, rotateH] at hi
      cases h : hold g with
      | none => rw [h] at hi; cases hi
      | some z =>
        rw [h] at hi
        simp only [Option.map_some, Option.some.injEq] at hi
        rw [← hi]
        by_cases hzS : z ∈ S
        · rw [hσS z hzS]; exact (hSa _ (hSτ z hzS)).1
        · rw [hσn z hzS]; exact hC.mem g hg z h
    · obtain ⟨o, ho, rfl⟩ := hsurj x hx
      rw [hσfr o ho] at hfx
      rw [hb o ho]
      obtain ⟨y, hy, hpos⟩ := hC.frz o ho hfx
      refine ⟨y, hy, ?_⟩
      by_cases hoS : o ∈ S
      · obtain ⟨-, -, -, y', hy', hlt⟩ := hτ o ho hfx
        rw [hy] at hy'
        simp only [List.cons.injEq, and_true] at hy'
        subst hy'
        rw [hσS o hoS]; omega
      · rw [hσn o hoS]; exact hpos
    · rw [baseOf_congr fun g _ => hoff i (hfreeS i hi hfi) g]
      exact hC.pair i hi hfi
    · rw [hfrG g hg]
      obtain ⟨o, ho, rfl⟩ := hsurj i hi
      rw [hb o ho] at hlt
      by_cases hoS : o ∈ S
      · rw [hσS o hoS] at hgi hlt
        have hτo := (hSa _ (hSτ o hoS)).1
        have hg1 := hgain o hoS
        refine hC.adm (τ o) hτo g hg (fun hh => ?_) (by omega)
        have := EFX.le_value_of_mem (v := v) (τ o) (mem_baseOf.mpr ⟨hg, hh⟩)
        omega
      · rw [hσn o hoS] at hgi hlt
        refine hC.adm o ho g hg (fun hh => hgi ?_) hlt
        simp only [h2, rotateH, hh, Option.map_some, hσn o hoS]
  have hR2 : FRobust v agents goods fr h2 := by
    intro x hx hfx
    obtain ⟨o, ho, rfl⟩ := hsurj x hx
    rw [houtN, hb o ho]
    have := hR (σ o) (by
      by_cases hoS : o ∈ S
      · rw [hσS o hoS]; exact (hSa _ (hSτ o hoS)).1
      · rw [hσn o hoS]; exact ho) hfx
    have := hle o ho
    omega
  -- its potential is larger
  have hr : nRobust v (freeA agents fr) (outN goods fr h2) h2 = nRobust v (freeA agents fr) (outN goods fr hold) hold := by
    unfold nRobust ZRobust
    rw [houtN]
    apply List.countP_congr
    intro i hi
    obtain ⟨hia, hfi⟩ := mem_freeA.mp hi
    rw [baseOf_congr fun g _ => hoff i (hfreeS i hia hfi) g]
  have hw : welfare v agents goods hold < welfare v agents goods h2 := by
    unfold welfare
    apply sum_lt_of_le_of_lt
    · intro j hj
      obtain ⟨o, ho, rfl⟩ := hsurj j hj
      rw [hb o ho]; exact hle o ho
    · obtain ⟨o, hoS⟩ := List.exists_mem_of_ne_nil S hSne
      refine ⟨σ o, ?_, ?_⟩
      · rw [hσS o hoS]; exact (hSa _ (hSτ o hoS)).1
      · rw [hb o (hSa o hoS).1, hσS o hoS]; exact hgain o hoS
  have := hmax h2 hC2 hR2
  exact absurd this (Nat.not_le.mpr (fPot_lt (Or.inr ⟨Nat.le_of_eq hr.symm, hw⟩)))

end last

/-! ## Theorem F -/

/-- **Theorem F with the hypotheses it uses** (`k4/c4min.md` §3.6): let there be at least one agent, every agent have at
most four relevant goods and every good be relevant to some agent. If some configuration with frozen agents `fr` is
frozen-robust and no pre-allocation of 𝒫 has fewer frozen agents than `fr` has, then some pre-allocation of 𝒫 with the
fewest frozen agents has `def(P) ≤ 0` and is completable.

With no frozen agent this is Theorem Z (`theoremZ_min`). Otherwise take a frozen-robust configuration with the largest
potential: it is pool-optimal over `M′` with the most robust free agents (`fmax_poolOpt`, `fmax_nRobust`), so the free
agents have a valid owner or all hold four goods outside `𝒩` (`zvalid_or_all4` on the free agents over `M′`); the
latter is impossible (`frozen_cycle`), and a robust frozen agent is never threatened (`not_threat_frozen`), so the owner
threatens nobody and Lemma 1(a) applies (`removalOnly_of_cfg`). -/
theorem theoremF_min (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) (hrel : ∀ g ∈ goods, ∃ i ∈ agents, 0 < v i g)
    {fr : A → Bool} {hold : G → Option A} (hC : IsCfg v agents goods fr hold) (hR : FRobust v agents goods fr hold)
    (hmin : ∀ base, InP v agents goods base → agents.countP fr ≤ nFrozen v agents goods base) :
    ∃ base, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base ∧ Completable v agents goods base := by
  by_cases hf : ∃ x ∈ agents, fr x = true
  · obtain ⟨h, ⟨hCh, hRh⟩, hmax⟩ := exists_max_of_bdd
      (fun h => IsCfg v agents goods fr h ∧ FRobust v agents goods fr h) (fPot v agents goods fr) _
      (fun h _ => fPot_le h) ⟨hold, hC, hR⟩
    have hmax' : ∀ h', IsCfg v agents goods fr h' → FRobust v agents goods fr h' →
        fPot v agents goods fr h' ≤ fPot v agents goods fr h := fun h' a b => hmax h' ⟨a, b⟩
    have h4' : ∀ i ∈ freeA agents fr, (relevant v i (outN goods fr h)).length ≤ 4 := fun i hi =>
      Nat.le_trans (List.Sublist.filter _ List.filter_sublist).length_le (h4 i (mem_freeA.mp hi).1)
    rcases zvalid_or_all4 (hag.sublist List.filter_sublist) (hgd.sublist List.filter_sublist) (isAPA_sub hCh)
      (fmax_poolOpt hgd hCh hRh hmax') (fmax_nRobust hCh hRh hmax') h4' with ⟨o, ho, hV⟩ | hall
    · obtain ⟨hoa, hfo⟩ := mem_freeA.mp ho
      have hRO := removalOnly_of_cfg hCh hoa hfo fun x hx hxo => by
        cases hfx : fr x
        · exact fun hT => hV x (mem_freeA.mpr ⟨hx, hfx⟩) hxo ((zthreat_outN hfo hfx).mpr hT)
        · exact not_threat_frozen hRh hfo hx hfx
      exact ⟨apaBase v h, minFrozen_cfg hCh hmin, hRO, completable_of_removalOnly hag hgd hne (inP_cfg hCh) hRO⟩
    · exact (frozen_cycle hag h4 hCh hRh hmin hmax' (fun j hj => (hall j hj).1) hf).elim
  · have h0 : nFrozen v agents goods (apaBase v hold) = 0 := by
      have h1 := nFrozen_cfg_le hC
      have h2 : agents.countP fr = 0 := List.countP_eq_zero.mpr fun x hx h => hf ⟨x, hx, h⟩
      omega
    exact theoremZ_min hag hgd hne h4 hrel ⟨apaBase v hold, inP_cfg hC, h0⟩

/-- **Theorem F** (`k4/c4min.md` §3.6): on every k = 4 core, if some configuration at the fewest frozen agents is
frozen-robust, then some pre-allocation of 𝒫 with the fewest frozen agents has `def(P) ≤ 0` and is completable
(C₄ᵐⁱⁿ's conclusion in both forms). -/
theorem theoremF (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods) {fr : A → Bool}
    {hold : G → Option A} (hC : IsCfg v agents goods fr hold) (hR : FRobust v agents goods fr hold)
    (hmin : ∀ base, InP v agents goods base → agents.countP fr ≤ nFrozen v agents goods base) :
    ∃ base, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base ∧ Completable v agents goods base :=
  theoremF_min hag hgd (fun e => by have := hc.1; rw [e] at this; simp at this) (fun i hi => (hc.2.1 i hi).2)
    hc.2.2.2.2.2 hC hR hmin

/-- **Theorem F in C₄ᵐⁱⁿ's removal-only form** (`TheoremC4minRO`'s conclusion on the profiles with a frozen-robust
configuration at the fewest frozen agents; the strictness hypothesis is carried but not used). -/
theorem c4minRO_of_frobust (A G : Type) [DecidableEq A] [DecidableEq G] :
    ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
      Strict v agents goods → (∃ (fr : A → Bool) (hold : G → Option A), IsCfg v agents goods fr hold ∧
        FRobust v agents goods fr hold ∧
        ∀ base, InP v agents goods base → agents.countP fr ≤ nFrozen v agents goods base) →
      ∃ base : G → Option A, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base :=
  fun _ _ _ hag hgd hc _ ⟨_, _, hC, hR, hmin⟩ =>
    let ⟨base, hM, hRO, _⟩ := theoremF hag hgd hc hC hR hmin
    ⟨base, hM, hRO⟩

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.rigid_NA
#print axioms EFX.C4min.inP_cfg
#print axioms EFX.C4min.frozen_of_min
#print axioms EFX.C4min.minFrozen_cfg
#print axioms EFX.C4min.removalOnly_of_cfg
#print axioms EFX.C4min.isAPA_sub
#print axioms EFX.C4min.not_threat_frozen
#print axioms EFX.C4min.isCfg_joinH
#print axioms EFX.C4min.fmax_poolOpt
#print axioms EFX.C4min.fmax_nRobust
#print axioms EFX.C4min.exists_cycle
#print axioms EFX.C4min.frozen_cycle
#print axioms EFX.C4min.theoremF_min
#print axioms EFX.C4min.theoremF
#print axioms EFX.C4min.c4minRO_of_frobust
