import EFX.K3Theorem

/-!
# Theorem Z: C₄ᵐⁱⁿ when the fewest frozen agents is 0 (`k4/c4min.md` §3; PR #41)

Theorem Z of `k4/c4min.md` (PR #41, branch `proof/k4-c4min`): on every strict profile of a k = 4 core whose fewest
frozen agents is 0, some pre-allocation of 𝒫 with the fewest frozen agents is completable. The proof works with
*all-pairs allocations* (APAs): every agent holds a pair of goods whose relevant part is admissible (needs nothing),
and the other goods form the pool.

**Definitions** (`k4/c4min.md` §3.1), over the lists of `EFX/C4min.lean`; an APA is a holding map
`hold : G → Option A` (`hold g = some i` iff `g ∈ Q_i`; `none` for the pool `L`), so `Q_i = baseOf goods hold i`,
`L = junk goods hold` and `Q_o ∪ L = W goods hold o` (`EFX/K3Pareto.lean`).
- `IsAPA`: pairs of exactly two goods held by listed agents, each needing nothing (`vbNeeds` empty: admissible).
- `ZThreat o i`: `max_{h ∈ Q_o ∪ L} v_i((Q_o ∪ L) ∖ h) > v_i(Q_i)`; `ZValid o`: `o` threatens nobody.
- `ZRobust i`: `v_i(Q_i) ≥ v_i(R_i ∖ Q_i)`, i.e. `v_i(M) ≤ 2 v_i(Q_i)`; `nRobust`: their number.
- `PoolOpt`: no agent prefers a pair of `Q_i ∪ L`.

**Results so far.**
- `completable_of_zvalid` (Lemma Z0): a valid owner of an APA gives a pre-allocation of 𝒫 with no frozen agent (the
  relevant goods of the pairs, `apaBase`) that is completable, hence C₄ᵐⁱⁿ's conclusion (`c4min_of_zvalid`).
- `removalOnly_of_f0_small`: with no frozen agent and `m ≤ 2n`, `ω ≤ 0` and there is nothing to prove.
- `exists_apa` (Lemma Z1, existence): a pre-allocation of 𝒫 with no frozen agent and `m ≥ 2n` extends to an APA (its
  bases filled up with junk goods, `EFX.LB.fill`).
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-! ## All-pairs allocations -/

/-- **An all-pairs allocation** (`k4/c4min.md` §3.1): every listed agent holds exactly two goods, and its holding needs
nothing (its relevant part is admissible); the goods held by nobody form the pool. -/
structure IsAPA (v : A → G → Nat) (agents : List A) (goods : List G) (hold : G → Option A) : Prop where
  mem : ∀ g ∈ goods, ∀ i, hold g = some i → i ∈ agents
  pair : ∀ i ∈ agents, (baseOf goods hold i).length = 2
  adm : ∀ i ∈ agents, ∀ g, ¬ vbNeeds v goods hold i g

/-- `o` threatens `i`: `v_i((Q_o ∪ L) ∖ h) > v_i(Q_i)` for some `h ∈ Q_o ∪ L`. -/
def ZThreat (v : A → G → Nat) (goods : List G) (hold : G → Option A) (o i : A) : Prop :=
  ∃ h ∈ W goods hold o, value v i (baseOf goods hold i) < value v i ((W goods hold o).erase h)

/-- A valid owner: a listed agent that threatens no other listed agent. -/
def ZValid (v : A → G → Nat) (agents : List A) (goods : List G) (hold : G → Option A) (o : A) : Prop :=
  o ∈ agents ∧ ∀ i ∈ agents, i ≠ o → ¬ ZThreat v goods hold o i

/-- A robust agent: its pair is worth at least the rest of its goods. -/
def ZRobust (v : A → G → Nat) (goods : List G) (hold : G → Option A) (i : A) : Prop :=
  value v i goods ≤ 2 * value v i (baseOf goods hold i)

/-- Pool-optimal: no agent prefers a pair of goods from its pair and the pool. -/
def PoolOpt (v : A → G → Nat) (agents : List A) (goods : List G) (hold : G → Option A) : Prop :=
  ∀ i ∈ agents, ∀ S : List G, S.Nodup → S.length = 2 → (∀ g ∈ S, g ∈ W goods hold i) →
    value v i S ≤ value v i (baseOf goods hold i)

open Classical in
/-- The number of robust agents. -/
noncomputable def nRobust (v : A → G → Nat) (agents : List A) (goods : List G) (hold : G → Option A) : Nat :=
  agents.countP (fun i => decide (ZRobust v goods hold i))

/-! ## Lemma Z0: a valid owner gives a completable pre-allocation with no frozen agent -/

/-- The bases of an APA: the relevant goods of every pair. -/
def apaBase (v : A → G → Nat) (hold : G → Option A) (g : G) : Option A :=
  match hold g with
  | some i => if 0 < v i g then some i else none
  | none => none

omit [DecidableEq A] [DecidableEq G] in
theorem apaBase_eq_some {hold : G → Option A} {g : G} {i : A} :
    apaBase v hold g = some i ↔ hold g = some i ∧ 0 < v i g := by
  unfold apaBase
  cases hold g with
  | none => simp
  | some j =>
    by_cases hp : 0 < v j g
    · simp only [hp, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hp⟩
      · exact And.left
    · simp only [hp, ↓reduceIte, reduceCtorEq, Option.some.injEq, false_iff, not_and]
      rintro rfl; exact hp

omit [DecidableEq G] in
theorem baseOf_apaBase {hold : G → Option A} (i : A) :
    baseOf goods (apaBase v hold) i = (baseOf goods hold i).filter (fun g => 0 < v i g) := by
  unfold baseOf
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  simp only [apaBase_eq_some]
  by_cases h1 : hold g = some i <;> by_cases h2 : 0 < v i g <;> simp [h1, h2]

omit [DecidableEq G] in
theorem value_apaBase {hold : G → Option A} (i : A) :
    value v i (baseOf goods (apaBase v hold) i) = value v i (baseOf goods hold i) := by
  rw [baseOf_apaBase, ← LB4.value_filter_pos]

omit [DecidableEq G] in
/-- The bases of an APA have no needs. -/
theorem noNeeds_apaBase {hold : G → Option A} (hA : IsAPA v agents goods hold) :
    ∀ i ∈ agents, ∀ g, ¬ vbNeeds v goods (apaBase v hold) i g := by
  intro i hi g ⟨hg, hgb, hlt⟩
  rw [value_apaBase] at hlt
  by_cases hh : hold g = some i
  · exact hgb (apaBase_eq_some.mpr ⟨hh, by omega⟩)
  · exact hA.adm i hi g ⟨hg, hh, hlt⟩

omit [DecidableEq G] in
theorem inP_apaBase {hold : G → Option A} (hA : IsAPA v agents goods hold) :
    InP v agents goods (apaBase v hold) := by
  have hNA : ∀ g, ¬ NA agents (vbNeeds v goods (apaBase v hold)) g :=
    fun g ⟨i, hi, hN⟩ => noNeeds_apaBase hA i hi g hN
  refine ⟨fun g hg i hb => hA.mem g hg i (apaBase_eq_some.mp hb).1,
    fun g _ i hb => (apaBase_eq_some.mp hb).2, fun i => ?_, ⟨fun g _ => hNA g, fun _ _ g _ => hNA g⟩⟩
  rw [baseOf_apaBase]
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  by_cases hi : i ∈ agents
  · rw [hA.pair i hi]; exact Nat.le_refl _
  · have : baseOf goods hold i = [] := List.eq_nil_iff_forall_not_mem.mpr fun g hg =>
      hi (hA.mem g (mem_baseOf.mp hg).1 i (mem_baseOf.mp hg).2)
    rw [this]; simp

omit [DecidableEq G] in
theorem nFrozen_apaBase {hold : G → Option A} (hA : IsAPA v agents goods hold) :
    nFrozen v agents goods (apaBase v hold) = 0 := by
  unfold nFrozen numFrozen
  rw [List.countP_eq_zero]
  intro j _ h
  simp only [decide_eq_true_eq] at h
  obtain ⟨y, -, i, hi, hN⟩ := h
  exact noNeeds_apaBase hA i hi y hN

/-- The completion of an APA with owner `o`: every agent keeps its pair, the owner also takes the pool. -/
def apaX (hold : G → Option A) (o : A) (g : G) : A :=
  match hold g with
  | some j => j
  | none => o

omit [DecidableEq G] in
theorem bundle_apaX_ne {hold : G → Option A} {o j : A} (hjo : j ≠ o) :
    bundle goods (apaX hold o) j = baseOf goods hold j := by
  unfold bundle baseOf apaX
  apply List.filter_congr
  intro g _
  cases hold g with
  | none => simp [Ne.symm hjo]
  | some k => simp

omit [DecidableEq G] in
theorem bundle_apaX_owner {hold : G → Option A} (o : A) :
    bundle goods (apaX hold o) o = W goods hold o := by
  unfold bundle W apaX
  apply List.filter_congr
  intro g _
  cases hold g with
  | none => simp
  | some k => simp [eq_comm]

/-- **Lemma Z0** (`k4/c4min.md` §3.1). If `o` is a valid owner of an APA, then the pre-allocation of the relevant goods of
the pairs is completable: every agent keeps its pair, the owner also takes the pool, and this is a sound completion. -/
theorem completable_of_zvalid {hold : G → Option A} (hA : IsAPA v agents goods hold) {o : A}
    (hV : ZValid v agents goods hold o) : Completable v agents goods (apaBase v hold) := by
  have hP := inP_apaBase hA
  have hNF : ∀ j, ¬ Frozen agents goods (apaBase v hold) (vbNeeds v goods (apaBase v hold)) j :=
    fun _ ⟨y, _, i, hi, hN⟩ => noNeeds_apaBase hA i hi y hN
  refine ⟨some o, apaX hold o, SoundCompletion.of_baseNeeds (fun i _ => needs_vb i) hP.valid
    ⟨fun g hg => ?_, fun g _ i hb => ?_, fun w hw => ?_, fun j _ _ hF => absurd hF (hNF j),
      fun j hj hjo _ => ?_⟩ ?_⟩
  · unfold apaX
    cases h : hold g with
    | none => exact hV.1
    | some j => exact hA.mem g hg j h
  · unfold apaX; rw [(apaBase_eq_some.mp hb).1]
  · cases hw; exact ⟨hV.1, hNF o⟩
  · have hjo' : j ≠ o := fun e => hjo (by rw [e])
    unfold junkOf
    rw [bundle_apaX_ne hjo', baseOf_apaBase]
    have : ((baseOf goods hold j).filter (fun g => apaBase v hold g = none)).length =
        ((baseOf goods hold j).filter (fun g => ¬ (0 < v j g))).length := by
      congr 1
      apply List.filter_congr
      intro g hg
      have hh := (mem_baseOf.mp hg).2
      cases e : apaBase v hold g with
      | none =>
        have : ¬ 0 < v j g := fun hp => by rw [apaBase_eq_some.mpr ⟨hh, hp⟩] at e; cases e
        simp [this]
      | some k =>
        obtain ⟨hk, hp⟩ := apaBase_eq_some.mp e
        rw [hh] at hk; cases hk
        simp [hp]
    rw [this, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter, Nat.add_comm]
    have h := List.length_eq_countP_add_countP (fun g => decide (0 < v j g)) (l := baseOf goods hold j)
    simp only [decide_eq_true_eq] at h
    rw [hA.pair j hj] at h
    omega
  · intro w hw j hj hjw h hh
    cases hw
    rw [bundle_apaX_owner] at hh ⊢
    rw [bundle_apaX_ne hjw]
    exact Nat.le_of_not_lt fun hlt => hV.2 j hj hjw ⟨h, hh, hlt⟩

/-- **C₄ᵐⁱⁿ's conclusion from a valid owner**: a pre-allocation of 𝒫 with no frozen agent (so the fewest) that is
completable. -/
theorem c4min_of_zvalid {hold : G → Option A} (hA : IsAPA v agents goods hold) {o : A}
    (hV : ZValid v agents goods hold o) :
    ∃ base, MinFrozen v agents goods base ∧ Completable v agents goods base :=
  ⟨apaBase v hold, ⟨inP_apaBase hA, fun _ _ => by rw [nFrozen_apaBase hA]; exact Nat.zero_le _⟩,
    completable_of_zvalid hA hV⟩

/-- With no frozen agent and `m ≤ 2n`, `ω = −σ ≤ 0`: removal-only completable without owner. -/
theorem removalOnly_of_f0_small (hag : agents.Nodup) (hgd : goods.Nodup) {base : G → Option A}
    (hP : InP v agents goods base) (h0 : nFrozen v agents goods base = 0) (hm : goods.length ≤ 2 * agents.length) :
    RemovalOnly v agents goods base := by
  have he := omega_eq hP.valid hag hgd hP.mem
  have hF := numFrozen_eq hP.valid hag hgd hP.mem
  unfold nFrozen at h0
  rw [h0] at hF
  have : omegaP v agents goods base ≤ 0 := by unfold omegaP; rw [he, ← hF]; omega
  exact Or.inl ⟨this, this⟩

/-! ## Lemma Z1: an APA exists -/

/-- Counting a disjunction of exclusive tests. -/
theorem countP_or_disj {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = true → q a = true → False) →
    l.countP p + l.countP q = l.countP (fun a => p a || q a)
  | [], _ => by simp
  | a :: l, h => by
    have ih := countP_or_disj (l := l) fun b hb => h b (by simp [hb])
    have ha := h a (by simp)
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- `fill` gives every agent exactly its slots when the goods suffice. -/
theorem fill_countP_eq {s : A → Nat} : ∀ {ks : List A} {rest : List G}, ks.Nodup → rest.Nodup →
    (ks.map s).sum ≤ rest.length → ∀ j ∈ ks, rest.countP (fun g => LB.fill s ks rest g = some j) = s j
  | [], _, _, _, _, j, hj => by simp at hj
  | k :: ks, rest, hks, hr, hsum, j, hj => by
    simp only [List.map_cons, List.sum_cons] at hsum
    have hnd : (rest.take (s k) ++ rest.drop (s k)).Nodup := by rw [List.take_append_drop]; exact hr
    have hdisj : ∀ g ∈ rest.drop (s k), g ∉ rest.take (s k) := fun g hd ht =>
      (List.nodup_append.mp hnd).2.2 g ht g hd rfl
    have hfill : ∀ g, LB.fill s (k :: ks) rest g =
        if g ∈ rest.take (s k) then some k else LB.fill s ks (rest.drop (s k)) g := fun g => rfl
    have hsplitc : ∀ p : G → Bool, rest.countP p = (rest.take (s k)).countP p + (rest.drop (s k)).countP p :=
      fun p => by rw [← List.countP_append, List.take_append_drop]
    rw [hsplitc]
    have htk : (rest.take (s k)).length = s k := by rw [List.length_take]; omega
    have hk' : k ∉ ks := (List.nodup_cons.mp hks).1
    by_cases hjk : j = k
    · subst hjk
      have h1 : (rest.take (s j)).countP (fun g => decide (LB.fill s (j :: ks) rest g = some j)) =
          (rest.take (s j)).length := by
        rw [List.countP_eq_length]
        intro g hg
        rw [hfill]; simp [hg]
      have h2 : (rest.drop (s j)).countP (fun g => decide (LB.fill s (j :: ks) rest g = some j)) = 0 := by
        rw [List.countP_eq_zero]
        intro g hg h
        rw [hfill] at h
        simp only [hdisj g hg, ↓reduceIte, decide_eq_true_eq] at h
        exact hk' (LB.fill_some h).1
      rw [h1, h2, htk]; rfl
    · have hj' : j ∈ ks := (List.mem_cons.mp hj).resolve_left hjk
      have h1 : (rest.take (s k)).countP (fun g => decide (LB.fill s (k :: ks) rest g = some j)) = 0 := by
        rw [List.countP_eq_zero]
        intro g hg h
        rw [hfill] at h
        simp only [hg, ↓reduceIte, decide_eq_true_eq, Option.some.injEq] at h
        exact hjk h.symm
      have h2 : (rest.drop (s k)).countP (fun g => decide (LB.fill s (k :: ks) rest g = some j)) =
          (rest.drop (s k)).countP (fun g => decide (LB.fill s ks (rest.drop (s k)) g = some j)) := by
        apply List.countP_congr
        intro g hg
        rw [hfill]
        simp [hdisj g hg]
      rw [h1, h2, Nat.zero_add]
      exact fill_countP_eq (List.nodup_cons.mp hks).2 (List.nodup_append.mp hnd).2.1
        (by rw [List.length_drop]; omega) j hj'

open Classical in
/-- **Lemma Z1, existence** (`k4/c4min.md` §3.1). A pre-allocation of 𝒫 with no frozen agent extends to an APA when
`m ≥ 2n`: its bases need nothing, and filling every agent's slots with junk goods keeps that. -/
theorem exists_apa (hag : agents.Nodup) (hgd : goods.Nodup) {base : G → Option A} (hP : InP v agents goods base)
    (h0 : nFrozen v agents goods base = 0) (hm : 2 * agents.length ≤ goods.length) :
    ∃ hold, IsAPA v agents goods hold := by
  -- no agent needs anything
  have hF := numFrozen_eq hP.valid hag hgd hP.mem
  unfold nFrozen at h0
  rw [h0] at hF
  have hNA : ∀ i ∈ agents, ∀ g, ¬ vbNeeds v goods base i g := by
    intro i hi g hN
    have : 0 < numNA agents goods (vbNeeds v goods base) :=
      List.countP_pos_iff.mpr ⟨g, hN.1, decide_eq_true ⟨i, hi, hN⟩⟩
    omega
  let s : A → Nat := fun j => 2 - (baseOf goods base j).length
  have hlen := length_goods (base := base) hag hP.mem
  have hsum : (agents.map s).sum ≤ (LB4.junk goods base).length := by
    have : ∀ l : List A, (∀ j ∈ l, (baseOf goods base j).length ≤ 2) →
        (l.map s).sum + (l.map (fun i => (baseOf goods base i).length)).sum = 2 * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        have ha := hl a (by simp)
        have hih := ih fun j hj => hl j (by simp [hj])
        simp only [List.map_cons, List.sum_cons, List.length_cons, s] at hih ⊢
        omega
    have := this agents fun j _ => hP.two j
    omega
  let hold : G → Option A := fun g => match base g with
    | some i => some i
    | none => LB.fill s agents (LB4.junk goods base) g
  have hjnd : (LB4.junk goods base).Nodup := hgd.sublist List.filter_sublist
  refine ⟨hold, fun g hg i hh => ?_, fun i hi => ?_, fun i hi g ⟨hg, hgh, hlt⟩ => ?_⟩
  · simp only [hold] at hh
    cases hb : base g with
    | some j => rw [hb] at hh; cases hh; exact hP.mem g hg _ hb
    | none => rw [hb] at hh; exact (LB.fill_some hh).1
  · -- `Q_i` is `B_i` plus the junk goods `fill` gives `i`
    have hc := fill_countP_eq hag hjnd hsum i hi
    have e : (baseOf goods hold i).length = (baseOf goods base i).length +
        (LB4.junk goods base).countP (fun g => LB.fill s agents (LB4.junk goods base) g = some i) := by
      unfold baseOf LB4.junk
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, List.countP_filter]
      rw [countP_or_disj (fun g _ h1 h2 => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2; rw [h2.2] at h1; cases h1)]
      apply List.countP_congr
      intro g _
      cases hb : base g <;> simp [hold, hb, LB4.junk]
    rw [e, hc]
    have := hP.two i
    simp only [s]; omega
  · -- `Q_i ⊇ B_i` is worth at least `B_i`, which needs nothing
    have hsub : value v i (baseOf goods base i) ≤ value v i (baseOf goods hold i) :=
      value_sublist v i (LB4.filter_sublist_of_imp fun g _ hb => by
        simp only [decide_eq_true_eq] at hb ⊢; simp [hold, hb])
    refine hNA i hi g ⟨hg, fun hb => hgh (by simp [hold, hb]), by omega⟩


/-! ## Lemma Z1: pool improvements; a pool-optimal APA with the most robust agents -/

/-- A pool improvement: `i` takes the pair `S ⊆ Q_i ∪ L`, the rest of `Q_i` goes to the pool. -/
def poolImprove (hold : G → Option A) (i : A) (S : List G) (g : G) : Option A :=
  if g ∈ S then some i else if hold g = some i then none else hold g

section improve
variable {hold : G → Option A} {i : A} {S : List G}

theorem baseOf_poolImprove_self (hgd : goods.Nodup) (hS : S.Nodup) (hSg : ∀ g ∈ S, g ∈ goods) :
    (baseOf goods (poolImprove hold i S) i).Perm S := by
  apply baseOf_perm hgd hS
  intro g
  unfold poolImprove
  by_cases hg : g ∈ S
  · simp [hg, hSg g hg]
  · simp only [hg, ↓reduceIte, false_iff, not_and]
    intro _
    split
    · simp
    · rename_i h; exact h

theorem baseOf_poolImprove_other (hSW : ∀ g ∈ S, g ∈ W goods hold i) {j : A} (hji : j ≠ i) :
    baseOf goods (poolImprove hold i S) j = baseOf goods hold j := by
  apply baseOf_congr
  intro g hg
  unfold poolImprove
  by_cases hgS : g ∈ S
  · simp only [hgS, ↓reduceIte, Option.some.injEq]
    have := (mem_W.mp (hSW g hgS)).2
    constructor
    · intro e; exact absurd e.symm hji
    · intro e; rcases this with e' | e' <;> rw [e] at e'
      · exact absurd (Option.some.inj e') hji
      · cases e'
  · simp only [hgS, ↓reduceIte]
    split
    · rename_i h; rw [h]; simp [Ne.symm hji]
    · rfl

theorem value_poolImprove_self (hgd : goods.Nodup) (hS : S.Nodup) (hSg : ∀ g ∈ S, g ∈ goods) :
    value v i (baseOf goods (poolImprove hold i S) i) = value v i S :=
  value_perm (baseOf_poolImprove_self hgd hS hSg)

/-- **A pool improvement is an APA** in which `i` gains and nobody else changes. -/
theorem isAPA_poolImprove (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) (hi : i ∈ agents) (hS : S.Nodup)
    (hS2 : S.length = 2) (hSW : ∀ g ∈ S, g ∈ W goods hold i)
    (hlt : value v i (baseOf goods hold i) < value v i S) : IsAPA v agents goods (poolImprove hold i S) := by
  have hSg : ∀ g ∈ S, g ∈ goods := fun g hg => (mem_W.mp (hSW g hg)).1
  refine ⟨fun g hg j hj => ?_, fun j hj => ?_, fun j hj g ⟨hg, hgb, hvl⟩ => ?_⟩
  · unfold poolImprove at hj
    by_cases hgS : g ∈ S
    · simp only [hgS, ↓reduceIte, Option.some.injEq] at hj; rw [← hj]; exact hi
    · simp only [hgS, ↓reduceIte] at hj
      split at hj
      · cases hj
      · exact hA.mem g hg j hj
  · by_cases hji : j = i
    · subst hji; rw [(baseOf_poolImprove_self hgd hS hSg).length_eq, hS2]
    · rw [baseOf_poolImprove_other hSW hji]; exact hA.pair j hj
  · by_cases hji : j = i
    · subst hji
      rw [value_poolImprove_self hgd hS hSg] at hvl
      have hgS : g ∉ S := fun h => hgb (by simp [poolImprove, h])
      by_cases hh : hold g = some j
      · have := le_value_of_mem v j (mem_baseOf.mpr ⟨hg, hh⟩ : g ∈ baseOf goods hold j)
        omega
      · exact hA.adm j hj g ⟨hg, hh, by omega⟩
    · rw [baseOf_poolImprove_other hSW hji] at hvl
      refine hA.adm j hj g ⟨hg, fun hh => hgb ?_, hvl⟩
      have : g ∉ S := fun h => by
        rcases (mem_W.mp (hSW g h)).2 with e | e <;> rw [hh] at e
        · exact hji (Option.some.inj e)
        · cases e
      simp [poolImprove, this, hh, hji]

end improve

/-- The welfare of an APA, `Σ_i v_i(Q_i)` (`welfare` of `EFX/K3Theorem.lean`). -/
abbrev zWelfare (v : A → G → Nat) (agents : List A) (goods : List G) (hold : G → Option A) : Nat :=
  welfare v agents goods hold

/-- The potential `r · (B + 1) + Σ_i v_i(Q_i)`, with `B = Σ_i v_i(M)` a bound on the welfare: maximizing it maximizes
the number of robust agents first, then the welfare (in place of the text's level sum Λ; see the module doc). -/
noncomputable def zPot (v : A → G → Nat) (agents : List A) (goods : List G) (hold : G → Option A) : Nat :=
  nRobust v agents goods hold * ((agents.map (fun i => value v i goods)).sum + 1) + zWelfare v agents goods hold

omit [DecidableEq G] in
theorem zWelfare_le (hold : G → Option A) :
    zWelfare v agents goods hold ≤ (agents.map (fun i => value v i goods)).sum :=
  LB4.sum_le_sum_of_le _ _ agents fun i _ => value_sublist v i List.filter_sublist

omit [DecidableEq G] in
theorem nRobust_le (hold : G → Option A) : nRobust v agents goods hold ≤ agents.length := by
  unfold nRobust; exact List.countP_le_length

/-- **Lemma Z1** (`k4/c4min.md` §3.1): if an APA exists, some APA is pool-optimal and has the most robust agents among
all APAs (take a maximum of `zPot`; a pool improvement raises it, and so does any APA with more robust agents). -/
theorem exists_zmax (hgd : goods.Nodup) (h : ∃ hold, IsAPA v agents goods hold) :
    ∃ hold, IsAPA v agents goods hold ∧ PoolOpt v agents goods hold ∧
      ∀ hold', IsAPA v agents goods hold' → nRobust v agents goods hold' ≤ nRobust v agents goods hold := by
  classical
  obtain ⟨B, hB⟩ : ∃ B, B = (agents.map (fun i => value v i goods)).sum := ⟨_, rfl⟩
  have hpot : ∀ hold, zPot v agents goods hold = nRobust v agents goods hold * (B + 1) + zWelfare v agents goods hold :=
    fun hold => by rw [hB]; rfl
  have htop : ∀ hold, zPot v agents goods hold ≤ agents.length * (B + 1) + B := fun hold => by
    rw [hpot]
    have := nRobust_le (v := v) (agents := agents) (goods := goods) hold
    have := zWelfare_le (v := v) (agents := agents) (goods := goods) hold
    rw [← hB] at this
    have := Nat.mul_le_mul_right (B + 1) (nRobust_le (v := v) (agents := agents) (goods := goods) hold)
    omega
  have key : ∀ d, ∀ hold, IsAPA v agents goods hold → agents.length * (B + 1) + B - zPot v agents goods hold = d →
      ∃ hold, IsAPA v agents goods hold ∧ PoolOpt v agents goods hold ∧
        ∀ hold', IsAPA v agents goods hold' → nRobust v agents goods hold' ≤ nRobust v agents goods hold := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro hold hA hd
      -- a better APA would contradict the induction
      have better : ∀ hold', IsAPA v agents goods hold' → zPot v agents goods hold < zPot v agents goods hold' →
          ∃ hold, IsAPA v agents goods hold ∧ PoolOpt v agents goods hold ∧
            ∀ hold'', IsAPA v agents goods hold'' → nRobust v agents goods hold'' ≤ nRobust v agents goods hold :=
        fun hold' hA' hlt => ih _ (by have := htop hold'; omega) hold' hA' rfl
      by_cases hpo : PoolOpt v agents goods hold
      · by_cases hmax : ∀ hold', IsAPA v agents goods hold' → nRobust v agents goods hold' ≤ nRobust v agents goods hold
        · exact ⟨hold, hA, hpo, hmax⟩
        · obtain ⟨hold', hA', hlt⟩ : ∃ hold', IsAPA v agents goods hold' ∧
              nRobust v agents goods hold < nRobust v agents goods hold' :=
            Classical.byContradiction fun hno => hmax fun h' hA' => Nat.le_of_not_lt fun hl => hno ⟨h', hA', hl⟩
          refine better hold' hA' ?_
          rw [hpot, hpot]
          have := zWelfare_le (v := v) (agents := agents) (goods := goods) hold
          rw [← hB] at this
          have := Nat.mul_le_mul_right (B + 1) hlt
          rw [Nat.succ_mul] at this
          omega
      · obtain ⟨i, hi, S, hS, hS2, hSW, hlt⟩ : ∃ i ∈ agents, ∃ S : List G, S.Nodup ∧ S.length = 2 ∧
            (∀ g ∈ S, g ∈ W goods hold i) ∧ value v i (baseOf goods hold i) < value v i S :=
          Classical.byContradiction fun hno => hpo fun i hi S hS hS2 hSW =>
            Nat.le_of_not_lt fun hl => hno ⟨i, hi, S, hS, hS2, hSW, hl⟩
        have hSg : ∀ g ∈ S, g ∈ goods := fun g hg => (mem_W.mp (hSW g hg)).1
        have hA' := isAPA_poolImprove hgd hA hi hS hS2 hSW hlt
        refine better _ hA' ?_
        rw [hpot, hpot]
        -- the robust agents stay robust, and the welfare rises
        have hval : ∀ j, value v j (baseOf goods hold j) ≤ value v j (baseOf goods (poolImprove hold i S) j) := by
          intro j
          by_cases hji : j = i
          · subst hji; rw [value_poolImprove_self hgd hS hSg]; omega
          · rw [baseOf_poolImprove_other hSW hji] <;> exact Nat.le_refl _
        have hr : nRobust v agents goods hold ≤ nRobust v agents goods (poolImprove hold i S) := by
          unfold nRobust
          apply List.countP_mono_left
          intro j _ hj
          have hj' : ZRobust v goods hold j := of_decide_eq_true hj
          have := hval j
          unfold ZRobust at hj'
          exact decide_eq_true (by unfold ZRobust; omega)
        have hw : zWelfare v agents goods hold < zWelfare v agents goods (poolImprove hold i S) :=
          sum_lt_of_le_of_lt _ _ agents (fun j _ => hval j)
            ⟨i, hi, by rw [value_poolImprove_self hgd hS hSg]; exact hlt⟩
        have := Nat.mul_le_mul_right (B + 1) hr
        omega
  obtain ⟨hold, hA⟩ := h
  exact key _ hold hA rfl


/-! ## Lemma Z2: who can be threatened -/

omit [DecidableEq A] in
/-- A set's value is at most that of any duplicate-free set containing its relevant goods. -/
theorem value_le_of_rel_sub {i : A} {S T : List G} (hS : S.Nodup) (hT : T.Nodup)
    (h : ∀ g ∈ S, 0 < v i g → g ∈ T) : value v i S ≤ value v i T := by
  rw [LB4.value_filter_pos i S]
  exact value_le_of_subset (hS.sublist List.filter_sublist) hT (fun g hg => by
    obtain ⟨hgS, hp⟩ := List.mem_filter.mp hg
    exact h g hgS (of_decide_eq_true hp)) i

omit [DecidableEq G] in
/-- `v_i(M) = v_i(Q_i) + v_i(M ∖ Q_i)`. -/
theorem value_split (hold : G → Option A) (i : A) :
    value v i goods = value v i (baseOf goods hold i) + value v i (goods.filter (fun g => hold g ≠ some i)) := by
  have hp := List.filter_append_perm (fun g => decide (hold g = some i)) goods
  rw [← value_perm hp, value_append]
  congr 2
  apply List.filter_congr
  intro g _
  simp

omit [DecidableEq G] in
/-- The relevant goods of `W_o` (for `o ≠ i`) lie outside `Q_i`. -/
theorem W_out {hold : G → Option A} {o i : A} (hoi : o ≠ i) {g : G} (hg : g ∈ W goods hold o) :
    hold g ≠ some i := by
  intro h
  rcases (mem_W.mp hg).2 with e | e <;> rw [h] at e
  · exact hoi (Option.some.inj e).symm
  · cases e

/-- **Lemma Z2(a)**: a robust agent is threatened by nobody. -/
theorem not_threat_of_robust (hgd : goods.Nodup) {hold : G → Option A} {o i : A} (hoi : o ≠ i)
    (hR : ZRobust v goods hold i) : ¬ ZThreat v goods hold o i := by
  rintro ⟨h, _, hlt⟩
  have hW : (W goods hold o).Nodup := hgd.sublist List.filter_sublist
  have := value_le_of_rel_sub (v := v) (i := i) (T := goods.filter (fun g => hold g ≠ some i)) (hW.erase h)
    (hgd.sublist List.filter_sublist) fun g hg _ => by
      have hgW := List.mem_of_mem_erase hg
      exact List.mem_filter.mpr ⟨(mem_W.mp hgW).1, decide_eq_true (W_out hoi hgW)⟩
  have := value_split (v := v) (goods := goods) hold i
  unfold ZRobust at hR
  omega

/-- A list of length two. -/
theorem eq_pair_of_length {α : Type} {l : List α} (h : l.length = 2) : ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩


section cases
variable {hold : G → Option A}

/-- Admissibility, as a bound: a good outside `Q_i` is worth at most `v_i(Q_i)`. -/
theorem adm_le (hA : IsAPA v agents goods hold) {i : A} (hi : i ∈ agents) {g : G} (hg : g ∈ goods)
    (hgi : hold g ≠ some i) : v i g ≤ value v i (baseOf goods hold i) :=
  Nat.le_of_not_lt fun hlt => hA.adm i hi g ⟨hg, hgi, hlt⟩

omit [DecidableEq A] [DecidableEq G] in
theorem ne_of_hold {x y : G} {j k : A} (hx : hold x = some j) (hy : hold y = some k) (hjk : j ≠ k) : x ≠ y :=
  fun e => hjk (Option.some.inj (hx.symm.trans (e ▸ hy)))

omit [DecidableEq G] in
theorem mem_pair_iff {i : A} {a y : G} (h : (baseOf goods hold i).Perm [a, y]) {g : G} :
    g ∈ goods ∧ hold g = some i ↔ g = a ∨ g = y := by
  rw [← mem_baseOf, h.mem_iff]; simp

/-- The value of a pair. -/
theorem value_pair {i : A} {a y : G} (h : (baseOf goods hold i).Perm [a, y]) (j : A) :
    value v j (baseOf goods hold i) = v j a + v j y := by
  rw [value_perm h]; simp [value]

/-- An agent's pair, as two distinct goods. -/
theorem exists_pair (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) {i : A} (hi : i ∈ agents) :
    ∃ a y, a ≠ y ∧ (baseOf goods hold i).Perm [a, y] := by
  obtain ⟨a, y, h⟩ := eq_pair_of_length (hA.pair i hi)
  have hnd : (baseOf goods hold i).Nodup := hgd.sublist List.filter_sublist
  rw [h] at hnd
  exact ⟨a, y, by simpa using hnd, by rw [h]⟩

/-- **Case A** (`k4/c4min.md` §3.2, kind (T)): `Q_i = {a, y}` with `a` relevant and `y` not. At a pool-optimal APA the
pool is worthless to `i`, and a threat by `o` needs both goods of `Q_o` relevant to `i` and worth more than `a`. -/
theorem caseA_pool (hpo : PoolOpt v agents goods hold) {i : A} (hi : i ∈ agents)
    {a y : G} (hay : a ≠ y) (hQ : (baseOf goods hold i).Perm [a, y]) (hy : v i y = 0) :
    ∀ g ∈ goods, hold g = none → v i g = 0 := by
  intro g hg hgn
  have ha := (mem_pair_iff hQ).mpr (Or.inl rfl)
  have hag : a ≠ g := fun e => by rw [e, hgn] at ha; cases ha.2
  have := hpo i hi [a, g] (by simp [hag]) rfl fun x hx => by
    simp at hx
    rcases hx with rfl | rfl
    · exact mem_W.mpr ⟨ha.1, Or.inl ha.2⟩
    · exact mem_W.mpr ⟨hg, Or.inr hgn⟩
  rw [value_pair hQ] at this
  simp [value] at this
  omega

theorem caseA_threat (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) (hpo : PoolOpt v agents goods hold)
    {i : A} (hi : i ∈ agents) {a y : G} (hay : a ≠ y) (hQ : (baseOf goods hold i).Perm [a, y]) (hy : v i y = 0)
    {o : A} (ho : o ∈ agents) (hoi : o ≠ i) (hT : ZThreat v goods hold o i) :
    ∃ c d, c ≠ d ∧ (baseOf goods hold o).Perm [c, d] ∧ 0 < v i c ∧ 0 < v i d ∧ v i a < v i c + v i d := by
  obtain ⟨h, _, hlt⟩ := hT
  obtain ⟨c, d, hcd, hQo⟩ := exists_pair hgd hA ho
  have hW : (W goods hold o).Nodup := hgd.sublist List.filter_sublist
  have hpool := caseA_pool hpo hi hay hQ hy
  -- the relevant goods of `W_o` are in `Q_o`
  have hle := value_le_of_rel_sub (v := v) (i := i) (T := baseOf goods hold o) (hW.erase h)
    (hgd.sublist List.filter_sublist) fun g hg hp => by
      obtain ⟨hgg, hb⟩ := mem_W.mp (List.mem_of_mem_erase hg)
      rcases hb with hb | hb
      · exact mem_baseOf.mpr ⟨hgg, hb⟩
      · exact absurd (hpool g hgg hb) (by omega)
  rw [value_pair hQ, hy] at hlt
  rw [value_pair hQo] at hle
  have hc := (mem_pair_iff hQo).mpr (Or.inl rfl)
  have hd := (mem_pair_iff hQo).mpr (Or.inr rfl)
  have hci := adm_le hA hi hc.1 (fun e => hoi (Option.some.inj (hc.2.symm.trans e)))
  have hdi := adm_le hA hi hd.1 (fun e => hoi (Option.some.inj (hd.2.symm.trans e)))
  rw [value_pair hQ, hy] at hci hdi
  refine ⟨c, d, hcd, hQo, ?_, ?_, by omega⟩
  · refine Nat.pos_of_ne_zero fun h0 => ?_; omega
  · refine Nat.pos_of_ne_zero fun h0 => ?_; omega

/-- Case A: the threatening pair is admissible for `i`. -/
theorem caseA_adm (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) (hpo : PoolOpt v agents goods hold)
    {i : A} (hi : i ∈ agents) {a y : G} (hay : a ≠ y) (hQ : (baseOf goods hold i).Perm [a, y]) (hy : v i y = 0)
    {o : A} (ho : o ∈ agents) (hoi : o ≠ i) (hT : ZThreat v goods hold o i) :
    ∀ g ∈ goods, hold g ≠ some o → v i g ≤ value v i (baseOf goods hold o) := by
  obtain ⟨c, d, -, hQo, -, -, hlt⟩ := caseA_threat hgd hA hpo hi hay hQ hy ho hoi hT
  intro g hg hgo
  rw [value_pair hQo]
  by_cases hgi : hold g = some i
  · rcases (mem_pair_iff hQ).mp ⟨hg, hgi⟩ with rfl | rfl
    · omega
    · rw [hy]; exact Nat.zero_le _
  · have := adm_le hA hi hg hgi
    rw [value_pair hQ, hy] at this
    omega

/-- Case A with three relevant goods: after taking the threatening pair, `i` is robust. -/
theorem caseA_robust3 (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) (hpo : PoolOpt v agents goods hold)
    {i : A} (hi : i ∈ agents) {a y : G} (hay : a ≠ y) (hQ : (baseOf goods hold i).Perm [a, y]) (hy : v i y = 0)
    (ha : 0 < v i a) {o : A} (ho : o ∈ agents) (hoi : o ≠ i) (hT : ZThreat v goods hold o i)
    (h3 : (relevant v i goods).length = 3) : value v i goods ≤ 2 * value v i (baseOf goods hold o) := by
  obtain ⟨c, d, hcd, hQo, hc, hd, hlt⟩ := caseA_threat hgd hA hpo hi hay hQ hy ho hoi hT
  have hcm := (mem_pair_iff hQo).mpr (Or.inl rfl)
  have hdm := (mem_pair_iff hQo).mpr (Or.inr rfl)
  have ham := (mem_pair_iff hQ).mpr (Or.inl rfl)
  have hac : a ≠ c := ne_of_hold ham.2 hcm.2 (Ne.symm hoi)
  have had : a ≠ d := ne_of_hold ham.2 hdm.2 (Ne.symm hoi)
  have hperm := perm_of_subset_length (T := relevant v i goods) (S := [a, c, d]) (by simp [hac, had, hcd])
    (hgd.sublist List.filter_sublist) (fun g hg => by
      simp at hg
      rcases hg with rfl | rfl | rfl
      · exact mem_relevant.mpr ⟨ham.1, ha⟩
      · exact mem_relevant.mpr ⟨hcm.1, hc⟩
      · exact mem_relevant.mpr ⟨hdm.1, hd⟩) (by rw [h3]; simp)
  rw [value_relevant, ← value_perm hperm, value_pair hQo]
  simp [value]; omega

/-- Case A: at most one agent threatens `i` (their pairs would be four goods of `R_i ∖ {a}`). -/
theorem caseA_unique (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) (hpo : PoolOpt v agents goods hold)
    {i : A} (hi : i ∈ agents) {a y : G} (hay : a ≠ y) (hQ : (baseOf goods hold i).Perm [a, y]) (hy : v i y = 0)
    (ha : 0 < v i a) (h4 : (relevant v i goods).length ≤ 4) {o o' : A} (ho : o ∈ agents) (ho' : o' ∈ agents)
    (hoi : o ≠ i) (hoi' : o' ≠ i) (hT : ZThreat v goods hold o i) (hT' : ZThreat v goods hold o' i) : o = o' := by
  refine Classical.byContradiction fun hoo => ?_
  obtain ⟨c, d, hcd, hQo, hc, hd, -⟩ := caseA_threat hgd hA hpo hi hay hQ hy ho hoi hT
  obtain ⟨c', d', hcd', hQo', hc', hd', -⟩ := caseA_threat hgd hA hpo hi hay hQ hy ho' hoi' hT'
  have hcm := (mem_pair_iff hQo).mpr (Or.inl rfl)
  have hdm := (mem_pair_iff hQo).mpr (Or.inr rfl)
  have hcm' := (mem_pair_iff hQo').mpr (Or.inl rfl)
  have hdm' := (mem_pair_iff hQo').mpr (Or.inr rfl)
  have ham := (mem_pair_iff hQ).mpr (Or.inl rfl)
  have hnd : [a, c, d, c', d'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨ne_of_hold ham.2 hcm.2 (Ne.symm hoi), ne_of_hold ham.2 hdm.2 (Ne.symm hoi),
      ne_of_hold ham.2 hcm'.2 (Ne.symm hoi'), ne_of_hold ham.2 hdm'.2 (Ne.symm hoi')⟩,
      ⟨hcd, ne_of_hold hcm.2 hcm'.2 hoo, ne_of_hold hcm.2 hdm'.2 hoo⟩,
      ⟨ne_of_hold hdm.2 hcm'.2 hoo, ne_of_hold hdm.2 hdm'.2 hoo⟩, hcd', not_false⟩
  have := LB.length_le_of_subset hnd (T := relevant v i goods) fun g hg => by
    simp at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact mem_relevant.mpr ⟨ham.1, ha⟩
    · exact mem_relevant.mpr ⟨hcm.1, hc⟩
    · exact mem_relevant.mpr ⟨hdm.1, hd⟩
    · exact mem_relevant.mpr ⟨hcm'.1, hc'⟩
    · exact mem_relevant.mpr ⟨hdm'.1, hd'⟩
  simp at this; omega


/-- The relevant goods of `i` are its relevant goods in `Q_i` and those outside. -/
theorem relevant_perm_split {i : A} {p q : G} (hgd : goods.Nodup) (hQ : (baseOf goods hold i).Perm [p, q])
    (hp : 0 < v i p) (hq : 0 < v i q) :
    (relevant v i goods).Perm ([p, q] ++ (relevant v i goods).filter (fun g => hold g ≠ some i)) := by
  have hsplit := List.filter_append_perm (fun g => decide (hold g = some i)) (relevant v i goods)
  have hpq : p ≠ q := by
    have hn := hQ.nodup_iff.mp (hgd.sublist List.filter_sublist); simpa using hn
  refine hsplit.symm.trans (List.Perm.append ?_ ?_)
  · apply (List.perm_ext_iff_of_nodup ((hgd.sublist List.filter_sublist).sublist List.filter_sublist)
      (by simp [hpq])).mpr
    intro g
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false]
    rw [← mem_pair_iff hQ]
    constructor
    · rintro ⟨⟨hg, -⟩, hh⟩; exact ⟨hg, hh⟩
    · rintro ⟨hg, hh⟩
      refine ⟨⟨hg, ?_⟩, hh⟩
      rcases (mem_pair_iff hQ).mp ⟨hg, hh⟩ with rfl | rfl
      · exact hp
      · exact hq
  · apply List.Perm.of_eq
    apply List.filter_congr
    intro g _
    simp

/-- **Case B, three goods**: `Q_i ⊆ R_i` and `|R_i| = 3` make `i` robust. -/
theorem caseB_robust3 (hgd : goods.Nodup) (hA : IsAPA v agents goods hold) {i : A} (hi : i ∈ agents) {p q : G}
    (hQ : (baseOf goods hold i).Perm [p, q]) (hp : 0 < v i p) (hq : 0 < v i q)
    (h3 : (relevant v i goods).length = 3) : ZRobust v goods hold i := by
  have hs := relevant_perm_split hgd hQ hp hq
  have hl := hs.length_eq
  rw [h3] at hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  obtain ⟨z, hz⟩ : ∃ z, (relevant v i goods).filter (fun g => hold g ≠ some i) = [z] := by
    match h : (relevant v i goods).filter (fun g => hold g ≠ some i), hl with
    | [z], _ => exact ⟨z, rfl⟩
    | [], hl => exact absurd hl (by simp only [List.length_nil]; omega)
    | _ :: _ :: _, hl => exact absurd hl (by simp only [List.length_cons]; omega)
  have hzm : z ∈ (relevant v i goods).filter (fun g => hold g ≠ some i) := by rw [hz]; simp
  obtain ⟨hzr, hzh⟩ := List.mem_filter.mp hzm
  have hzle := adm_le hA hi (mem_relevant.mp hzr).1 (of_decide_eq_true hzh)
  unfold ZRobust
  rw [value_relevant, value_perm hs, hz, value_append, value_pair hQ]
  rw [value_pair hQ] at hzle
  simp [value]; omega

/-- **Case B, four goods** (`k4/c4min.md` §3.2, kinds (D) and (R)): `Q_i = {p, q} ⊆ R_i`, the other two goods `u, w`
of `R_i`, and `i` not robust: `v(p) + v(q) < v(u) + v(w)`. -/
structure CaseB4 (v : A → G → Nat) (goods : List G) (hold : G → Option A) (i : A) (p q u w : G) : Prop where
  hQ : (baseOf goods hold i).Perm [p, q]
  pp : 0 < v i p
  pq : 0 < v i q
  hu : u ∈ goods ∧ hold u ≠ some i ∧ 0 < v i u
  hw : w ∈ goods ∧ hold w ≠ some i ∧ 0 < v i w
  huw : u ≠ w
  rel : ∀ g ∈ goods, 0 < v i g → g = p ∨ g = q ∨ g = u ∨ g = w
  total : value v i goods = v i p + v i q + v i u + v i w
  nonrob : v i p + v i q < v i u + v i w

theorem caseB4_of (hgd : goods.Nodup) {i : A} {p q : G} (hQ : (baseOf goods hold i).Perm [p, q])
    (hp : 0 < v i p) (hq : 0 < v i q) (h4 : (relevant v i goods).length = 4) (hnr : ¬ ZRobust v goods hold i) :
    ∃ u w, CaseB4 v goods hold i p q u w := by
  have hs := relevant_perm_split hgd hQ hp hq
  have hl := hs.length_eq
  rw [h4] at hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  obtain ⟨u, w, huw⟩ := eq_pair_of_length (l := (relevant v i goods).filter (fun g => hold g ≠ some i)) (by omega)
  have hnd : ((relevant v i goods).filter (fun g => hold g ≠ some i)).Nodup :=
    (hgd.sublist List.filter_sublist).sublist List.filter_sublist
  rw [huw] at hnd
  have hmem : ∀ g, g ∈ [u, w] → g ∈ goods ∧ hold g ≠ some i ∧ 0 < v i g := fun g hg => by
    rw [← huw] at hg
    obtain ⟨hgr, hgh⟩ := List.mem_filter.mp hg
    exact ⟨(mem_relevant.mp hgr).1, of_decide_eq_true hgh, (mem_relevant.mp hgr).2⟩
  have htot : value v i goods = v i p + v i q + v i u + v i w := by
    rw [value_relevant, value_perm hs, huw]; simp [value]; omega
  refine ⟨u, w, hQ, hp, hq, hmem u (by simp), hmem w (by simp), by simpa using hnd, fun g hg hpos => ?_, htot, ?_⟩
  · have := hs.mem_iff.mp (mem_relevant.mpr ⟨hg, hpos⟩)
    rw [huw] at this; simp at this; exact this
  · unfold ZRobust at hnr
    rw [htot, value_pair hQ] at hnr
    omega

section B4
variable {i : A} {p q u w : G}

theorem CaseB4.pool_le (hB : CaseB4 v goods hold i p q u w)
    (hpo : PoolOpt v agents goods hold) (hi : i ∈ agents) {z : G} (hz : z ∈ goods) (hzn : hold z = none) :
    v i z ≤ v i p ∧ v i z ≤ v i q := by
  have hpm := (mem_pair_iff hB.hQ).mpr (Or.inl rfl)
  have hqm := (mem_pair_iff hB.hQ).mpr (Or.inr rfl)
  have hzp : z ≠ p := fun e => by rw [e, hpm.2] at hzn; cases hzn
  have hzq : z ≠ q := fun e => by rw [e, hqm.2] at hzn; cases hzn
  have hW : ∀ x, x = z ∨ x = p ∨ x = q → x ∈ W goods hold i := by
    rintro x (rfl | rfl | rfl)
    · exact mem_W.mpr ⟨hz, Or.inr hzn⟩
    · exact mem_W.mpr ⟨hpm.1, Or.inl hpm.2⟩
    · exact mem_W.mpr ⟨hqm.1, Or.inl hqm.2⟩
  have h1 := hpo i hi [z, p] (by simp [hzp]) rfl fun x hx => hW x (by
    simp at hx; rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have h2 := hpo i hi [z, q] (by simp [hzq]) rfl fun x hx => hW x (by
    simp at hx; rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h))
  rw [value_pair hB.hQ] at h1 h2
  simp [value] at h1 h2
  omega

theorem CaseB4.not_both_pool (hB : CaseB4 v goods hold i p q u w) (hA : IsAPA v agents goods hold)
    (hpo : PoolOpt v agents goods hold) (hi : i ∈ agents) : ¬ (hold u = none ∧ hold w = none) := by
  rintro ⟨hu, hw⟩
  have := hB.pool_le hpo hi hB.hu.1 hu
  have := hB.pool_le hpo hi hB.hw.1 hw
  have := hB.nonrob
  omega

theorem CaseB4.threat_W (hB : CaseB4 v goods hold i p q u w) (hgd : goods.Nodup) (hA : IsAPA v agents goods hold)
    (hi : i ∈ agents) {o : A} (hoi : o ≠ i) (hT : ZThreat v goods hold o i) :
    u ∈ W goods hold o ∧ w ∈ W goods hold o := by
  obtain ⟨h, _, hlt⟩ := hT
  have hW : (W goods hold o).Nodup := hgd.sublist List.filter_sublist
  have hpm := (mem_pair_iff hB.hQ).mpr (Or.inl rfl)
  have hqm := (mem_pair_iff hB.hQ).mpr (Or.inr rfl)
  -- the relevant goods of `W_o` are among `u, w`
  have hin : ∀ g ∈ W goods hold o, 0 < v i g → g = u ∨ g = w := by
    intro g hg hpos
    have hgi := W_out hoi hg
    rcases hB.rel g (mem_W.mp hg).1 hpos with rfl | rfl | h | h
    · exact absurd hpm.2 hgi
    · exact absurd hqm.2 hgi
    · exact Or.inl h
    · exact Or.inr h
  have one : ∀ x, x = u ∨ x = w → x ∉ W goods hold o → False := by
    intro x hx hxn
    obtain ⟨y, hy, hxy⟩ : ∃ y, (y = u ∨ y = w) ∧ ∀ g ∈ W goods hold o, 0 < v i g → g = y := by
      rcases hx with rfl | rfl
      · exact ⟨w, Or.inr rfl, fun g hg hpos => (hin g hg hpos).resolve_left (fun e => hxn (e ▸ hg))⟩
      · exact ⟨u, Or.inl rfl, fun g hg hpos => (hin g hg hpos).resolve_right (fun e => hxn (e ▸ hg))⟩
    have hle := value_le_of_rel_sub (v := v) (i := i) (T := [y]) (hW.erase h) (by simp) fun g hg hpos => by
      simp [hxy g (List.mem_of_mem_erase hg) hpos]
    have hy' : y ∈ goods ∧ hold y ≠ some i := by
      rcases hy with rfl | rfl
      · exact ⟨hB.hu.1, hB.hu.2.1⟩
      · exact ⟨hB.hw.1, hB.hw.2.1⟩
    have := adm_le hA hi hy'.1 hy'.2
    simp only [value_cons, value_nil, Nat.add_zero] at hle
    omega
  exact ⟨Classical.byContradiction (one u (Or.inl rfl)), Classical.byContradiction (one w (Or.inr rfl))⟩

/-- Case B4: at most one agent threatens `i` (it holds whichever of `u, w` is not in the pool). -/
theorem CaseB4.unique (hB : CaseB4 v goods hold i p q u w) (hgd : goods.Nodup) (hA : IsAPA v agents goods hold)
    (hpo : PoolOpt v agents goods hold) (hi : i ∈ agents) {o o' : A} (hoi : o ≠ i) (hoi' : o' ≠ i)
    (hT : ZThreat v goods hold o i) (hT' : ZThreat v goods hold o' i) : o = o' := by
  obtain ⟨hu, hw⟩ := hB.threat_W hgd hA hi hoi hT
  obtain ⟨hu', hw'⟩ := hB.threat_W hgd hA hi hoi' hT'
  have key : ∀ x, x ∈ W goods hold o → x ∈ W goods hold o' → hold x ≠ none → o = o' := by
    intro x hx hx' hn
    rcases (mem_W.mp hx).2 with e | e
    · rcases (mem_W.mp hx').2 with e' | e'
      · exact Option.some.inj (e.symm.trans e')
      · exact absurd e' hn
    · exact absurd e hn
  by_cases h : hold u = none
  · exact key w hw hw' fun hwn => hB.not_both_pool hA hpo hi ⟨h, hwn⟩
  · exact key u hu hu' h

/-- Case B4: the threatening pair is admissible for `i` (it holds `u` or `w`, and then beats every other good of `i`). -/
theorem CaseB4.adm (hB : CaseB4 v goods hold i p q u w) (hgd : goods.Nodup) (hA : IsAPA v agents goods hold)
    (hpo : PoolOpt v agents goods hold) (hi : i ∈ agents) {o : A} (hoi : o ≠ i) (hT : ZThreat v goods hold o i) :
    ∀ g ∈ goods, hold g ≠ some o → v i g ≤ value v i (baseOf goods hold o) := by
  obtain ⟨hu, hw⟩ := hB.threat_W hgd hA hi hoi hT
  have hnb := hB.not_both_pool hA hpo hi
  have hnr := hB.nonrob
  have hpm := (mem_pair_iff hB.hQ).mpr (Or.inl rfl)
  have hqm := (mem_pair_iff hB.hQ).mpr (Or.inr rfl)
  have hval : ∀ x, hold x = some o → x ∈ goods → v i x ≤ value v i (baseOf goods hold o) := fun x hx hxg =>
    le_value_of_mem v i (mem_baseOf.mpr ⟨hxg, hx⟩)
  intro g hg hgo
  by_cases hpos : 0 < v i g
  · rcases (mem_W.mp hu).2 with eu | eu <;> rcases (mem_W.mp hw).2 with ew | ew
    · -- `Q_o = {u, w}`
      have hsum : v i u + v i w ≤ value v i (baseOf goods hold o) := by
        have := value_le_of_subset (v := v) (S := [u, w]) (T := baseOf goods hold o) (by simp [hB.huw])
          (hgd.sublist List.filter_sublist) (fun x hx => by
            simp at hx
            rcases hx with rfl | rfl
            · exact mem_baseOf.mpr ⟨hB.hu.1, eu⟩
            · exact mem_baseOf.mpr ⟨hB.hw.1, ew⟩) i
        simp only [value_cons, value_nil, Nat.add_zero] at this
        omega
      rcases hB.rel g hg hpos with rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact absurd eu hgo
      · exact absurd ew hgo
    · -- `u ∈ Q_o`, `w` in the pool
      have := hB.pool_le hpo hi hB.hw.1 ew
      have := hval u eu hB.hu.1
      rcases hB.rel g hg hpos with rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact absurd eu hgo
      · omega
    · have := hB.pool_le hpo hi hB.hu.1 eu
      have := hval w ew hB.hw.1
      rcases hB.rel g hg hpos with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · exact absurd ew hgo
    · exact absurd ⟨eu, ew⟩ hnb
  · omega

end B4

end cases

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.completable_of_zvalid
#print axioms EFX.C4min.c4min_of_zvalid
#print axioms EFX.C4min.removalOnly_of_f0_small
#print axioms EFX.C4min.exists_apa
#print axioms EFX.C4min.isAPA_poolImprove
#print axioms EFX.C4min.exists_zmax
