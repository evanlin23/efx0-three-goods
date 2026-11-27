import EFX.OC1MaxMoves

/-!
# Lemma M: the S\* completion as a matching condition (`k4/matching.md` §1)

Lemma M (K4.MATCH.M, `proof/k4-matching`; refereed CORRECT, `k4/referee/matching.md`) reads the S\* completion of a
state as a bipartite matching condition. This file proves the completability equivalence (no dummy slots, d = 0),
both directions.

**Definitions** (`k4/matching.md` §0–§1, `k4/sdc.md` §30), for a state `B` (each agent's base, a list of goods):
- `Threat v i S w`: the set `S` *threatens* `i` at value `w`: removing some good of `S` leaves a set worth more than
  `w` to `i` (so an agent of value `w` would strongly envy `S`). EFX₀ says no bundle threatens anybody at its own
  value (`efx0L_iff`).
- `Frozen`: some other agent values a good of `j`'s base above its own base; `Holder`: unfrozen, at most one base good.
- `SStar v agents goods B o`: an **S\* completion with owner `o`**: a complete EFX₀ allocation keeping every base, in
  which every junk good goes to `o` or to a holder other than `o`, and every agent other than `o` receives at most one
  junk good. It is a one-absorber completion (`oneAbsorber_of_sStar`).
- Lemma 2\*'s hypotheses: `G1` (no base of a non-holder other than `o` threatens anybody at base values) and `G2` (no
  junk good is wanted).
- For `H` a list of junk goods: `ownerSet` = X(H) = `B o` ∪ (J ∖ H); `H1` = (H1)(H), X(H) threatens no non-holder other
  than `o` at its base value; `Exposed` = E(H), the holders other than `o` that X(H) threatens at their base value;
  `Edge h u` = h ~ u in Γ(H): `u` is not exposed, or `u` values `h` and X(H) does not threaten `u` at
  `v_u(B_u) + v_u(h)`; `SlotMatching`: a matching of all of `H` into the holders other than `o` along edges of Γ(H),
  covering every exposed holder.

**Results.**
- `sStar_of_slotMatching` (**Lemma M, ⇐**): under (G1) and (G2), if some `H ⊆ J` satisfies (H1) and has a slot
  matching, then `o` gives each matched holder its good, takes the rest of the junk, and the result is an S\*
  completion.
- `slotMatching_of_sStar` (**Lemma M, ⇒**): every S\* completion with owner `o` gives such an `H` (the junk given to
  the holders) and matching (the allocation itself). This direction needs neither (G1) nor (G2).
- `lemmaM`: the equivalence.

Not formalized: the deficiency formula with `d` dummy slots (the Mendelsohn–Dulmage and König–Ore steps of §1).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Threats -/

section threat
variable (v : A → G → Nat)

/-- The list `S` threatens `i` at value `w`: removing some good of `S` leaves a set worth more than `w` to `i`. -/
def Threat (i : A) (S : List G) (w : Nat) : Prop := ∃ x ∈ S, w < value v i (S.erase x)

variable {v}

omit [DecidableEq A] in
theorem not_threat_iff {i : A} {S : List G} {w : Nat} :
    ¬ Threat v i S w ↔ ∀ x ∈ S, value v i (S.erase x) ≤ w := by
  unfold Threat
  constructor
  · intro h x hx; exact Nat.le_of_not_lt fun hl => h ⟨x, hx, hl⟩
  · rintro h ⟨x, hx, hl⟩; have := h x hx; omega

omit [DecidableEq A] in
theorem not_threat_mono {i : A} {S : List G} {w w' : Nat} (h : ¬ Threat v i S w) (hw : w ≤ w') :
    ¬ Threat v i S w' := by
  rw [not_threat_iff] at h ⊢
  exact fun x hx => Nat.le_trans (h x hx) hw

/-- **EFX₀ in threat form**: no bundle threatens another listed agent at its own value. -/
theorem efx0L_iff {agents : List A} {goods : List G} {X : G → A} :
    EFX0L v agents goods X ↔ ∀ i ∈ agents, ∀ j ∈ agents, i ≠ j →
      ¬ Threat v i (bundle goods X j) (value v i (bundle goods X i)) := by
  unfold EFX0L
  constructor
  · intro h i hi j hj hij
    exact not_threat_iff.mpr fun x hx => h i hi j hj hij x hx
  · intro h i hi j hj hij x hx
    exact not_threat_iff.mp (h i hi j hj hij) x hx

omit [DecidableEq A] in
/-- Lists without repetitions and with the same goods have the same value. -/
theorem value_eq_of_mem_iff {i : A} {L M : List G} (hL : L.Nodup) (hM : M.Nodup) (h : ∀ g, g ∈ L ↔ g ∈ M) :
    value v i L = value v i M :=
  Nat.le_antisymm (value_le_of_nodup_sub i hL fun g hg => (h g).mp hg)
    (value_le_of_nodup_sub i hM fun g hg => (h g).mpr hg)

omit [DecidableEq A] in
/-- Threats only depend on the goods of a list without repetitions. -/
theorem threat_congr {i : A} {L M : List G} {w : Nat} (hL : L.Nodup) (hM : M.Nodup) (h : ∀ g, g ∈ L ↔ g ∈ M) :
    Threat v i L w ↔ Threat v i M w := by
  have key : ∀ {L M : List G}, L.Nodup → M.Nodup → (∀ g, g ∈ L ↔ g ∈ M) → Threat v i L w → Threat v i M w := by
    intro L M hL hM h ⟨x, hx, hlt⟩
    refine ⟨x, (h x).mp hx, ?_⟩
    rwa [value_eq_of_mem_iff (hL.erase x) (hM.erase x) fun g => by
      rw [hL.mem_erase_iff, hM.mem_erase_iff, h g]] at hlt
  exact ⟨key hL hM h, key hM hL fun g => (h g).symm⟩

omit [DecidableEq A] [DecidableEq G] in
theorem value_le_of_length_le_one {i : A} {L : List G} {w : Nat} (hlen : L.length ≤ 1) (hw : ∀ y ∈ L, v i y ≤ w) :
    value v i L ≤ w := by
  match L, hlen with
  | [], _ => simp
  | [a], _ => simpa using hw a (by simp)

omit [DecidableEq A] in
/-- **A set of at most two goods, each worth at most `w` to `i`, does not threaten `i` at value `w`.** -/
theorem not_threat_small {i : A} {S T : List G} {w : Nat} (hS : S.Nodup) (hST : ∀ y ∈ S, y ∈ T)
    (hT : T.length ≤ 2) (hw : ∀ y ∈ S, v i y ≤ w) : ¬ Threat v i S w := by
  refine not_threat_iff.mpr fun x hx => value_le_of_length_le_one ?_ fun y hy => hw y (List.mem_of_mem_erase hy)
  have := hS.length_le_of_subset hST
  rw [List.length_erase_of_mem hx]; omega

omit [DecidableEq A] [DecidableEq G] in
theorem length_le_one_of_eq {L : List G} (hL : L.Nodup) (h : ∀ a ∈ L, ∀ b ∈ L, a = b) : L.length ≤ 1 := by
  match L, hL with
  | [], _ => simp
  | a :: l, hL =>
    have : l = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb => by
      have := h a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
      subst this; exact (List.nodup_cons.mp hL).1 hb
    simp [this]

end threat

/-! ## States, holders and the S\* completion -/

section states
variable (v : A → G → Nat) (agents : List A) (goods : List G)

/-- `j` is frozen at `B`: another listed agent values a good of `j`'s base more than its own base. -/
def Frozen (B : A → List G) (j : A) : Prop := ∃ g ∈ B j, ∃ i ∈ agents, i ≠ j ∧ value v i (B i) < v i g

/-- `j` is a holder at `B`: unfrozen, with at most one base good (an empty base included). -/
def Holder (B : A → List G) (j : A) : Prop := ¬ Frozen v agents B j ∧ (B j).length ≤ 1

/-- A valid state: bases inside the goods, without repetitions, pairwise disjoint. -/
def ValidState (B : A → List G) : Prop :=
  (∀ i ∈ agents, (B i).Nodup ∧ ∀ g ∈ B i, g ∈ goods) ∧ (∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → ∀ g ∈ B i, g ∉ B j)

/-- An **S\* completion with owner `o`** (`k4/matching.md` §0): a complete EFX₀ allocation that keeps every base and
gives every junk good to `o` or to a holder other than `o`, each agent other than `o` receiving at most one junk
good. -/
def SStar (B : A → List G) (o : A) : Prop :=
  ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧ (∀ i ∈ agents, ∀ g ∈ B i, X g = i) ∧
    (∀ g ∈ junkOf agents goods B, X g = o ∨ (X g ≠ o ∧ X g ∈ agents ∧ Holder v agents B (X g))) ∧
    (∀ i ∈ agents, i ≠ o → ((junkOf agents goods B).filter (fun g => X g = i)).length ≤ 1)

/-- (G1): no base of a non-holder other than the owner threatens anybody at base values. -/
def G1 (B : A → List G) (o : A) : Prop :=
  ∀ j ∈ agents, j ≠ o → ¬ Holder v agents B j → ∀ i ∈ agents, i ≠ j → ¬ Threat v i (B j) (value v i (B i))

/-- (G2): no junk good is wanted. -/
def G2 (B : A → List G) : Prop := ∀ g ∈ junkOf agents goods B, ∀ i ∈ agents, v i g ≤ value v i (B i)

/-- The owner's set X(H) = `B o` ∪ (J ∖ H). -/
def ownerSet (B : A → List G) (o : A) (H : List G) : List G :=
  B o ++ (junkOf agents goods B).filter (fun g => decide (g ∉ H))

/-- (H1)(H): X(H) threatens no non-holder other than the owner at its base value. -/
def H1 (B : A → List G) (o : A) (H : List G) : Prop :=
  ∀ q ∈ agents, q ≠ o → ¬ Holder v agents B q → ¬ Threat v q (ownerSet agents goods B o H) (value v q (B q))

/-- E(H): `u` is exposed, threatened by X(H) at its base value. -/
def Exposed (B : A → List G) (o : A) (H : List G) (u : A) : Prop :=
  Threat v u (ownerSet agents goods B o H) (value v u (B u))

/-- The edge `h ~ u` of the slot graph Γ(H) (Lemma 2\*'s admissibility). -/
def Edge (B : A → List G) (o : A) (H : List G) (h : G) (u : A) : Prop :=
  ¬ Exposed v agents goods B o H u ∨
    (0 < v u h ∧ ¬ Threat v u (ownerSet agents goods B o H) (value v u (B u) + v u h))

/-- A matching `m` of all of `H` into the holders other than `o`, along edges of Γ(H), covering E(H). -/
def SlotMatching (B : A → List G) (o : A) (H : List G) (m : G → A) : Prop :=
  (∀ h ∈ H, m h ∈ agents ∧ m h ≠ o ∧ Holder v agents B (m h) ∧ Edge v agents goods B o H h (m h)) ∧
  (∀ h ∈ H, ∀ h' ∈ H, m h = m h' → h = h') ∧
  (∀ u ∈ agents, u ≠ o → Holder v agents B u → Exposed v agents goods B o H u → ∃ h ∈ H, m h = u)

end states

section lemmaM
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq G] in
theorem mem_bundle {X : G → A} {j : A} {g : G} : g ∈ bundle goods X j ↔ g ∈ goods ∧ X g = j := by
  simp [bundle]

omit [DecidableEq G] in
theorem nodup_bundle (hgd : goods.Nodup) (X : G → A) (j : A) : (bundle goods X j).Nodup :=
  hgd.sublist List.filter_sublist

omit [DecidableEq A] in
theorem nodup_ownerSet {B : A → List G} {o : A} (ho : o ∈ agents) (hst : ValidState agents goods B) (hgd : goods.Nodup)
    (H : List G) : (ownerSet agents goods B o H).Nodup := by
  refine List.nodup_append.mpr ⟨(hst.1 o ho).1, (hgd.sublist List.filter_sublist).sublist List.filter_sublist,
    fun a ha b hb e => ?_⟩
  have := (mem_junkOf.mp (List.mem_filter.mp hb).1).2 o ho
  exact this (e ▸ ha)

omit [DecidableEq A] in
theorem mem_ownerSet {B : A → List G} {o : A} {H : List G} {g : G} :
    g ∈ ownerSet agents goods B o H ↔ g ∈ B o ∨ (g ∈ junkOf agents goods B ∧ g ∉ H) := by
  simp [ownerSet]

omit [DecidableEq A] in
/-- A good of `goods` is in some listed agent's base or in the junk. -/
theorem base_or_junk {B : A → List G} {g : G} (hg : g ∈ goods) :
    (∃ i ∈ agents, g ∈ B i) ∨ g ∈ junkOf agents goods B := by
  by_cases h : ∃ i ∈ agents, g ∈ B i
  · exact Or.inl h
  · exact Or.inr (mem_junkOf.mpr ⟨hg, fun i hi hgi => h ⟨i, hi, hgi⟩⟩)

/-- **Lemma M, ⇐** (`k4/matching.md` §1). Under (G1) and (G2), if a set `H` of junk goods satisfies (H1) and has a
slot matching `m`, then the allocation in which each good of `H` goes to its matched holder, the other junk goods to
`o`, and every base stays, is an S\* completion with owner `o`. -/
theorem sStar_of_slotMatching {B : A → List G} {o : A} (hgd : goods.Nodup) (hst : ValidState agents goods B)
    (ho : o ∈ agents) (hG1 : G1 v agents B o) (hG2 : G2 v agents goods B) {H : List G}
    (hHJ : ∀ h ∈ H, h ∈ junkOf agents goods B) (hH1 : H1 v agents goods B o H) {m : G → A}
    (hm : SlotMatching v agents goods B o H m) : SStar v agents goods B o := by
  classical
  obtain ⟨hmH, hinj, hcov⟩ := hm
  let X : G → A := fun g => match agents.find? (fun i => decide (g ∈ B i)) with
    | some i => i
    | none => if g ∈ H then m g else o
  -- the allocation on bases and on junk
  have hXbase : ∀ i ∈ agents, ∀ g ∈ B i, X g = i := by
    intro i hi g hg
    cases hq : agents.find? (fun i => decide (g ∈ B i)) with
    | none => exact absurd (List.find?_eq_none.mp hq i hi) (by simpa using hg)
    | some j =>
      have hj := List.mem_of_find?_eq_some hq
      have hgj : g ∈ B j := by simpa using List.find?_some hq
      have : j = i := Classical.byContradiction fun hji => hst.2 j hj i hi hji g hgj hg
      simp only [X, hq, this]
  have hXjunk : ∀ g ∈ junkOf agents goods B, X g = if g ∈ H then m g else o := by
    intro g hg
    have hq : agents.find? (fun i => decide (g ∈ B i)) = none :=
      List.find?_eq_none.mpr fun i hi => by simpa using (mem_junkOf.mp hg).2 i hi
    simp only [X, hq]
  -- the goods of each bundle
  have hmemB : ∀ j ∈ agents, ∀ g, g ∈ bundle goods X j ↔ g ∈ B j ∨ (g ∈ junkOf agents goods B ∧ X g = j) := by
    intro j hj g
    rw [mem_bundle]
    constructor
    · rintro ⟨hg, hXg⟩
      rcases base_or_junk (B := B) hg with ⟨i, hi, hgi⟩ | hJ
      · rw [hXbase i hi g hgi] at hXg; subst hXg; exact Or.inl hgi
      · exact Or.inr ⟨hJ, hXg⟩
    · rintro (hgj | ⟨hJ, hXg⟩)
      · exact ⟨(hst.1 j hj).2 g hgj, hXbase j hj g hgj⟩
      · exact ⟨(mem_junkOf.mp hJ).1, hXg⟩
  -- the owner's bundle is X(H)
  have hown : ∀ g, g ∈ bundle goods X o ↔ g ∈ ownerSet agents goods B o H := by
    intro g
    rw [hmemB o ho, mem_ownerSet]
    refine or_congr_right ⟨fun ⟨hJ, hXg⟩ => ⟨hJ, fun hgH => ?_⟩, fun ⟨hJ, hgH⟩ => ⟨hJ, ?_⟩⟩
    · rw [hXjunk g hJ, ite_eq_left hgH] at hXg
      exact (hmH g hgH).2.1 hXg
    · rw [hXjunk g hJ, ite_eq_right hgH]
  -- junk received by an agent other than `o` is a good of `H` matched to it
  have hrecv : ∀ j, j ≠ o → ∀ g ∈ junkOf agents goods B, X g = j → g ∈ H ∧ m g = j := by
    intro j hjo g hJ hXg
    rw [hXjunk g hJ] at hXg
    by_cases hgH : g ∈ H
    · rw [ite_eq_left hgH] at hXg; exact ⟨hgH, hXg⟩
    · rw [ite_eq_right hgH] at hXg; exact absurd hXg.symm hjo
  have hbase_le : ∀ i ∈ agents, value v i (B i) ≤ value v i (bundle goods X i) := fun i hi =>
    value_le_of_nodup_sub i (hst.1 i hi).1 fun g hg => (hmemB i hi g).mpr (Or.inl hg)
  refine ⟨X, fun g hg => ?_, ?_, hXbase, fun g hJ => ?_, fun i hi hio => ?_⟩
  · -- `X` is an allocation
    rcases base_or_junk (B := B) hg with ⟨i, hi, hgi⟩ | hJ
    · rw [hXbase i hi g hgi]; exact hi
    · rw [hXjunk g hJ]
      by_cases hgH : g ∈ H
      · rw [ite_eq_left hgH]; exact (hmH g hgH).1
      · rw [ite_eq_right hgH]; exact ho
  · -- EFX₀
    refine efx0L_iff.mpr fun i hi j hj hij => ?_
    by_cases hjo : j = o
    · -- the owner's bundle
      subst hjo
      rw [threat_congr (nodup_bundle hgd X j) (nodup_ownerSet hj hst hgd H) hown]
      by_cases hhold : Holder v agents B i
      · by_cases hexp : Exposed v agents goods B j H i
        · obtain ⟨h, hh, hmh⟩ := hcov i hi hij hhold hexp
          have hedge := (hmH h hh).2.2.2
          rw [hmh] at hedge
          rcases hedge with hne | ⟨-, hnt⟩
          · exact absurd hexp hne
          · refine not_threat_mono hnt ?_
            have hhJ := hHJ h hh
            have hle := value_le_of_nodup_sub (v := v) i
              (List.nodup_append.mpr ⟨(hst.1 i hi).1, (by simp : [h].Nodup), fun a ha b hb e => by
                rw [List.mem_singleton] at hb; subst hb; exact (mem_junkOf.mp hhJ).2 i hi (e ▸ ha)⟩)
              (M := bundle goods X i) fun g hg => by
                rcases List.mem_append.mp hg with hg | hg
                · exact (hmemB i hi g).mpr (Or.inl hg)
                · rw [List.mem_singleton] at hg; subst hg
                  exact (hmemB i hi g).mpr (Or.inr ⟨hhJ, by rw [hXjunk g hhJ, ite_eq_left hh, hmh]⟩)
            rw [value_append_eq] at hle
            simpa using hle
        · exact not_threat_mono hexp (hbase_le i hi)
      · exact not_threat_mono (hH1 i hi hij hhold) (hbase_le i hi)
    · by_cases hhold : Holder v agents B j
      · -- a holder's bundle: at most two goods, each unwanted by `i`
        have hsmall : ∃ T : List G, (∀ g ∈ bundle goods X j, g ∈ T) ∧ T.length ≤ 2 := by
          by_cases hex : ∃ h ∈ H, m h = j
          · obtain ⟨h, hh, hmh⟩ := hex
            refine ⟨B j ++ [h], fun g hg => ?_, by simp; exact hhold.2⟩
            rcases (hmemB j hj g).mp hg with hg | ⟨hJ, hXg⟩
            · exact List.mem_append_left _ hg
            · obtain ⟨hgH, hmg⟩ := hrecv j hjo g hJ hXg
              rw [hinj g hgH h hh (hmg.trans hmh.symm)]; simp
          · refine ⟨B j, fun g hg => ?_, by have := hhold.2; omega⟩
            rcases (hmemB j hj g).mp hg with hg | ⟨hJ, hXg⟩
            · exact hg
            · obtain ⟨hgH, hmg⟩ := hrecv j hjo g hJ hXg
              exact absurd ⟨g, hgH, hmg⟩ hex
        obtain ⟨T, hT, hTlen⟩ := hsmall
        refine not_threat_mono (not_threat_small (nodup_bundle hgd X j) hT hTlen fun g hg => ?_) (hbase_le i hi)
        rcases (hmemB j hj g).mp hg with hg | ⟨hJ, -⟩
        · exact Nat.le_of_not_lt fun hlt => hhold.1 ⟨g, hg, i, hi, hij, hlt⟩
        · exact hG2 g hJ i hi
      · -- a non-holder's bundle is its base
        have hb : ∀ g, g ∈ bundle goods X j ↔ g ∈ B j := fun g => by
          rw [hmemB j hj g]
          refine ⟨fun h => h.elim id fun ⟨hJ, hXg⟩ => ?_, Or.inl⟩
          obtain ⟨hgH, hmg⟩ := hrecv j hjo g hJ hXg
          exact absurd (hmg ▸ (hmH g hgH).2.2.1) hhold
        rw [threat_congr (nodup_bundle hgd X j) (hst.1 j hj).1 hb]
        exact not_threat_mono (hG1 j hj hjo hhold i hi hij) (hbase_le i hi)
  · -- the shape: junk to `o` or to a matched holder
    rw [hXjunk g hJ]
    by_cases hgH : g ∈ H
    · rw [ite_eq_left hgH]; exact Or.inr ⟨(hmH g hgH).2.1, (hmH g hgH).1, (hmH g hgH).2.2.1⟩
    · rw [ite_eq_right hgH]; exact Or.inl rfl
  · -- at most one junk good to each agent other than `o`
    refine length_le_one_of_eq ((hgd.sublist List.filter_sublist).sublist List.filter_sublist) fun a ha b hb => ?_
    obtain ⟨haJ, hXa⟩ := List.mem_filter.mp ha
    obtain ⟨hbJ, hXb⟩ := List.mem_filter.mp hb
    obtain ⟨haH, hma⟩ := hrecv i hio a haJ (by simpa using hXa)
    obtain ⟨hbH, hmb⟩ := hrecv i hio b hbJ (by simpa using hXb)
    exact hinj a haH b hbH (hma.trans hmb.symm)

/-- **Lemma M, ⇒** (`k4/matching.md` §1): every S\* completion with owner `o` gives a set `H` of junk goods (those
given to the holders) satisfying (H1), with a slot matching (the completion itself). -/
theorem slotMatching_of_sStar {B : A → List G} {o : A} (hgd : goods.Nodup) (hst : ValidState agents goods B)
    (ho : o ∈ agents) (h : SStar v agents goods B o) :
    ∃ (H : List G) (m : G → A), (∀ h ∈ H, h ∈ junkOf agents goods B) ∧ H1 v agents goods B o H ∧
      SlotMatching v agents goods B o H m := by
  classical
  obtain ⟨X, -, hE, hXbase, hshape, hone⟩ := h
  let H := (junkOf agents goods B).filter (fun g => decide (X g ≠ o))
  have hmemH : ∀ g, g ∈ H ↔ g ∈ junkOf agents goods B ∧ X g ≠ o := fun g => by simp [H]
  have hmemB : ∀ j ∈ agents, ∀ g, g ∈ bundle goods X j ↔ g ∈ B j ∨ (g ∈ junkOf agents goods B ∧ X g = j) := by
    intro j hj g
    rw [mem_bundle]
    constructor
    · rintro ⟨hg, hXg⟩
      rcases base_or_junk (B := B) hg with ⟨i, hi, hgi⟩ | hJ
      · rw [hXbase i hi g hgi] at hXg; subst hXg; exact Or.inl hgi
      · exact Or.inr ⟨hJ, hXg⟩
    · rintro (hgj | ⟨hJ, hXg⟩)
      · exact ⟨(hst.1 j hj).2 g hgj, hXbase j hj g hgj⟩
      · exact ⟨(mem_junkOf.mp hJ).1, hXg⟩
  have hown : ∀ g, g ∈ bundle goods X o ↔ g ∈ ownerSet agents goods B o H := by
    intro g
    rw [hmemB o ho, mem_ownerSet]
    refine or_congr_right ⟨fun ⟨hJ, hXg⟩ => ⟨hJ, fun hgH => ((hmemH g).mp hgH).2 hXg⟩,
      fun ⟨hJ, hgH⟩ => ⟨hJ, Classical.byContradiction fun hne => hgH ((hmemH g).mpr ⟨hJ, hne⟩)⟩⟩
  have hthreat : ∀ i ∈ agents, i ≠ o →
      ¬ Threat v i (ownerSet agents goods B o H) (value v i (bundle goods X i)) := fun i hi hio => by
    have := efx0L_iff.mp hE i hi o ho hio
    rwa [threat_congr (nodup_bundle hgd X o) (nodup_ownerSet ho hst hgd H) hown] at this
  -- an agent that receives no junk has its base as bundle
  have hnojunk : ∀ i ∈ agents, (∀ g ∈ junkOf agents goods B, X g ≠ i) →
      value v i (bundle goods X i) = value v i (B i) := fun i hi hno =>
    value_eq_of_mem_iff (nodup_bundle hgd X i) (hst.1 i hi).1 fun g => by
      rw [hmemB i hi g]
      exact ⟨fun h => h.elim id fun ⟨hJ, hXg⟩ => absurd hXg (hno g hJ), Or.inl⟩
  -- two junk goods of the same agent other than `o` are equal
  have hsame : ∀ i ∈ agents, i ≠ o → ∀ a ∈ junkOf agents goods B, ∀ b ∈ junkOf agents goods B,
      X a = i → X b = i → a = b := by
    intro i hi hio a ha b hb hXa hXb
    refine Classical.byContradiction fun hab => ?_
    have h2 := (List.nodup_cons.mpr ⟨by simpa using hab, by simp⟩ : [a, b].Nodup).length_le_of_subset
      (l₂ := (junkOf agents goods B).filter (fun g => X g = i)) (fun g hg => by
        simp at hg; rcases hg with rfl | rfl
        · exact List.mem_filter.mpr ⟨ha, by simpa using hXa⟩
        · exact List.mem_filter.mpr ⟨hb, by simpa using hXb⟩)
    have := hone i hi hio
    simp at h2; omega
  refine ⟨H, X, fun g hg => ((hmemH g).mp hg).1, fun q hq hqo hqh => ?_, fun h hh => ?_, fun h hh h' hh' e => ?_,
    fun u hu huo _ hexp => ?_⟩
  · -- (H1): a non-holder other than `o` receives no junk
    have := hthreat q hq hqo
    rwa [hnojunk q hq fun g hJ hXg => by
      rcases hshape g hJ with h1 | ⟨-, -, h2⟩
      · exact hqo (hXg.symm.trans h1)
      · exact hqh (hXg ▸ h2)] at this
  · -- each good of `H` goes to a holder other than `o`, along an edge
    obtain ⟨hJ, hXo⟩ := (hmemH h).mp hh
    rcases hshape h hJ with h1 | ⟨h1, h2, h3⟩
    · exact absurd h1 hXo
    refine ⟨h2, h1, h3, ?_⟩
    by_cases hexp : Exposed v agents goods B o H (X h)
    · -- the bundle of `X h` is its base and `h`
      have hval : value v (X h) (bundle goods X (X h)) = value v (X h) (B (X h)) + v (X h) h := by
        have hnd2 : (B (X h) ++ [h]).Nodup := List.nodup_append.mpr ⟨(hst.1 _ h2).1, by simp,
          fun a ha b hb e => by
            rw [List.mem_singleton] at hb; subst hb; exact (mem_junkOf.mp hJ).2 _ h2 (e ▸ ha)⟩
        have hmem2 : ∀ g, g ∈ bundle goods X (X h) ↔ g ∈ B (X h) ++ [h] := fun g => by
          rw [hmemB _ h2 g, List.mem_append, List.mem_singleton]
          refine or_congr_right ⟨fun ⟨hgJ, hXg⟩ => hsame _ h2 h1 g hgJ h hJ hXg rfl, fun e => ?_⟩
          subst e; exact ⟨hJ, rfl⟩
        rw [value_eq_of_mem_iff (nodup_bundle hgd X _) hnd2 hmem2, value_append_eq]
        simp
      have hnt := hthreat (X h) h2 h1
      rw [hval] at hnt
      refine Or.inr ⟨Nat.pos_of_ne_zero fun h0 => ?_, hnt⟩
      rw [h0, Nat.add_zero] at hnt
      exact hnt hexp
    · exact Or.inl hexp
  · -- injectivity
    exact hsame (X h) ((hshape h ((hmemH h).mp hh).1).resolve_left ((hmemH h).mp hh).2).2.1
      ((hmemH h).mp hh).2 h ((hmemH h).mp hh).1 h' ((hmemH h').mp hh').1 rfl e.symm
  · -- every exposed holder receives a good of `H`
    refine Classical.byContradiction fun hno => ?_
    have := hthreat u hu huo
    rw [hnojunk u hu fun g hJ hXg => hno ⟨g, (hmemH g).mpr ⟨hJ, hXg ▸ huo⟩, hXg⟩] at this
    exact this hexp

/-- **Lemma M** (K4.MATCH.M, `k4/matching.md` §1; the completability equivalence, without dummy slots). Under
(G1) and (G2), the state has an S\* completion with owner `o` iff some set `H` of junk goods satisfies (H1) and
has a slot matching (a matching of all of `H` into the holders other than `o` along edges of Γ(H), covering every
exposed holder). -/
theorem lemmaM {B : A → List G} {o : A} (hgd : goods.Nodup) (hst : ValidState agents goods B) (ho : o ∈ agents)
    (hG1 : G1 v agents B o) (hG2 : G2 v agents goods B) :
    SStar v agents goods B o ↔ ∃ (H : List G) (m : G → A), (∀ h ∈ H, h ∈ junkOf agents goods B) ∧
      H1 v agents goods B o H ∧ SlotMatching v agents goods B o H m :=
  ⟨slotMatching_of_sStar hgd hst ho, fun ⟨_, _, hHJ, hH1, hm⟩ => sStar_of_slotMatching hgd hst ho hG1 hG2 hHJ hH1 hm⟩

/-- An S\* completion is a one-absorber completion (the owner absorbs). -/
theorem oneAbsorber_of_sStar {B : A → List G} {o : A} (h : SStar v agents goods B o) :
    OneAbsorber v agents goods B :=
  let ⟨X, hX, hE, hb, _, hone⟩ := h
  ⟨X, hX, hE, hb, o, hone⟩

end lemmaM

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.efx0L_iff
#print axioms EFX.OC1Max.threat_congr
#print axioms EFX.OC1Max.not_threat_small
#print axioms EFX.OC1Max.sStar_of_slotMatching
#print axioms EFX.OC1Max.slotMatching_of_sStar
#print axioms EFX.OC1Max.lemmaM
#print axioms EFX.OC1Max.oneAbsorber_of_sStar
