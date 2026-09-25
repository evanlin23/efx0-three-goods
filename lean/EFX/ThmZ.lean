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

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.completable_of_zvalid
#print axioms EFX.C4min.c4min_of_zvalid
#print axioms EFX.C4min.removalOnly_of_f0_small
#print axioms EFX.C4min.exists_apa
