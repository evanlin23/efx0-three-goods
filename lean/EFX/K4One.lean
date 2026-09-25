import EFX.LB4R

/-!
# TARGET₄ with at most one 4-good agent (ledger K4.ONE.FRAME)

The frame for Conjecture C₄¹ (`k4/c4.md`, ledger K4.C4.1): if every connected strict k = 4 core in which **at most one**
agent has four relevant goods has a sound completion (`EFX.LB4R.C4existsOne`), then every instance in which every
agent has at most four relevant goods and at most one agent has exactly four has an EFX₀ allocation
(`EFX.LB4R.target4one_of_C4existsOne`).

**The reduction adds no 4-good agent.** Every step of the induction of K4.CORE (`EFX.core_reduction4_conn`: junk
goods by L3, peeling by R1 and by R2, components by L6) passes to a sub-instance: a sublist of the agents, a sublist
of the goods, the same values. No gadget is added and no value changes. An agent's relevant goods in a sub-instance
are among its relevant goods in the instance (`EFX.relevant_sublist`), so with at most four relevant goods per agent,
an agent with four in a sub-instance has the same four in the instance (`EFX.atMostOne4_sublist`). K4.TIE's
perturbation `EFX.tieBreak` keeps which goods each agent values (`EFX.pos_tieBreak_iff`, which `EFX.tie_reduction`
passes on as its positivity hypothesis; also `EFX.relevant_tieBreak`). Hence:
- `core_reduction4_conn_of`: K4.CORE for any class of instances closed under sub-instances (the proof of
  `EFX.core_reduction4_conn`, with the class carried along: each recursive call is on a sub-instance);
- `core_reduction4_mixed_of`: the same, only connected cores with a 4-good agent needed (Corollary D for the rest);
- `core_reduction4_one_strict`, `target4one_of_strict_cores`: with K4.TIE, for the class `AtMostOne4`;
- `C4existsOne`, `C4existsOne_iff` (a sound completion ⟺ a D2-shaped EFX₀ allocation, as for `C4exists_iff`),
  `C4existsOne_of_C4exists`, `C4existsOne_of_C4existsConn` (with `sound_of_three_cores`: Corollary D covers the cores
  whose agents all have three goods), `target4one_of_C4existsOne`.

`C4existsOne` asks for every connected strict core with at most one 4-good agent; `target4one_of_C4existsOne` uses
it only for cores with exactly one (Corollary D covers the cores whose agents all have three goods).
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- At most one agent of `agents` has four relevant goods in `goods`. -/
def AtMostOne4 (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ i ∈ agents, ∀ j ∈ agents, (relevant v i goods).length = 4 → (relevant v j goods).length = 4 → i = j

omit [DecidableEq A] [DecidableEq G] in
/-- **A sub-instance adds no 4-good agent.** If every agent has at most four relevant goods and at most one has
four, the same holds for any sublist of the agents and any sublist of the goods: an agent with four relevant goods
among fewer goods has those four in the larger instance too. -/
theorem atMostOne4_sublist {v : A → G → Nat} {agents agents' : List A} {goods goods' : List G}
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) (h1 : AtMostOne4 v agents goods)
    (ha : agents'.Sublist agents) (hg : goods'.Sublist goods) : AtMostOne4 v agents' goods' := by
  intro i hi j hj hi4 hj4
  have hi' := ha.subset hi
  have hj' := ha.subset hj
  refine h1 i hi' j hj' ?_ ?_
  · have := relevant_sublist v (i := i) hg; have := h4 i hi'; omega
  · have := relevant_sublist v (i := j) hg; have := h4 j hj'; omega

/-- **K4.CORE for a class of instances closed under sub-instances.** `EFX.core_reduction4_conn` with a predicate
`P` carried along: every step of its induction (junk goods, R1, R2, components) recurses on a sublist of the agents
and a sublist of the goods with the same values, so if `P` passes to sub-instances, only the connected k = 4 cores
satisfying `P` are needed. The proof is that of `EFX.core_reduction4_conn`. -/
theorem core_reduction4_conn_of (v : A → G → Nat) (N : Nat) (P : List A → List G → Prop)
    (hP : ∀ (agents agents' : List A) (goods goods' : List G), P agents goods → agents'.Sublist agents →
      goods'.Sublist goods → P agents' goods')
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      P agents goods → IsCore4 v agents goods → Connected v agents goods →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → P agents goods → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  suffices H : ∀ s (agents : List A) (goods : List G), agents.length + goods.length = s →
      agents ≠ [] → agents.Nodup → goods.Nodup → agents.length ≤ N → P agents goods →
      (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X from
    fun agents goods => H _ agents goods rfl
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro agents goods hs hne hag hgd hN hPa h4
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil agents hne
  -- no goods: nothing to allocate
  by_cases hg0 : goods = []
  · subst hg0
    exact ⟨fun _ => i0, fun g hg => by simp at hg, fun _ _ _ _ _ g hg => by simp [bundle] at hg⟩
  -- one agent: it takes everything
  by_cases h1 : agents.length ≤ 1
  · refine ⟨fun _ => i0, fun _ _ => hi0, fun x hx y hy hxy => ?_⟩
    exfalso
    have : x = y := by
      cases agents with
      | nil => simp at hx
      | cons a l =>
        cases l with
        | nil => simp at hx hy; rw [hx, hy]
        | cons b l => simp at h1
    exact hxy this
  -- 1. junk goods (L3): the same agents, a sublist of the goods
  by_cases hjunk : ∃ g ∈ goods, isJunk v agents g = true
  · obtain ⟨g, hg, hgj⟩ := hjunk
    have hlt : (goods.filter (fun g => !isJunk v agents g)).length < goods.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [hgj]⟩
    obtain ⟨X', hX', hE'⟩ := ih _ (by omega) agents (goods.filter (fun g => !isJunk v agents g)) rfl hne
      hag (hgd.sublist List.filter_sublist) hN (hP _ _ _ _ hPa (List.Sublist.refl _) List.filter_sublist)
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i hi))
    exact junk v hne hX' hE'
  -- 2. peeling by R1: one agent and one good fewer
  by_cases hR1 : ∃ i ∈ agents, ∃ p ∈ goods, value v i (goods.erase p) ≤ v i p
  · obtain ⟨i, hi, p, hp, htop⟩ := hR1
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    have hmeas : (agents.erase i).length + (goods.erase p).length < s := by
      rw [← hs, List.length_erase_of_mem hi, List.length_erase_of_mem hp]
      have := List.length_pos_of_mem hi
      have := List.length_pos_of_mem hp
      omega
    obtain ⟨X', hX', hE'⟩ := ih _ hmeas
      (agents.erase i) (goods.erase p) rfl hrest (hag.erase i) (hgd.erase p)
      (by rw [List.length_erase_of_mem hi]; omega) (hP _ _ _ _ hPa List.erase_sublist List.erase_sublist)
      (fun j hj => Nat.le_trans (relevant_sublist v List.erase_sublist) (h4 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peel v (List.Nodup.not_mem_erase hag) hp hgd hX' hE' htop
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- every agent has at least three relevant goods and is strictly balanced
  have hbal : ∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods :=
    fun i hi => not_R1 v hg0 (fun ⟨p, hp, h⟩ => hR1 ⟨i, hi, p, hp, h⟩)
  -- 3. peeling by R2: one agent fewer, a sublist of the goods
  by_cases hR2 : ∃ i ∈ agents,
      value v i (relevant v i (goods.filter (fun g => !isPrivate v i (agents.erase i) g))) ≤
        value v i (goods.filter (isPrivate v i (agents.erase i)))
  · obtain ⟨i, hi, hb⟩ := hR2
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    have hmeas : (agents.erase i).length +
        (goods.filter (fun g => !isPrivate v i (agents.erase i) g)).length < s := by
      rw [← hs, List.length_erase_of_mem hi]
      have := List.length_pos_of_mem hi
      have := (List.filter_sublist (p := fun g => !isPrivate v i (agents.erase i) g) (l := goods)).length_le
      omega
    obtain ⟨X', hX', hE'⟩ := ih _ hmeas
      (agents.erase i) (goods.filter (fun g => !isPrivate v i (agents.erase i) g)) rfl hrest (hag.erase i)
      (hgd.sublist List.filter_sublist) (by rw [List.length_erase_of_mem hi]; omega)
      (hP _ _ _ _ hPa List.erase_sublist List.filter_sublist)
      (fun j hj => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peelR2 v (List.Nodup.not_mem_erase hag) hX' hE' hb
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- 4. components (L6): each side is a sublist of the agents and a sublist of the goods
  by_cases hconn : ¬ Connected v agents goods
  · obtain ⟨S, hS, a, ha, b, hb, hab⟩ : ∃ S : A → Bool,
        (∀ g ∈ goods, ∀ i ∈ agents, ∀ j ∈ agents, 0 < v i g → 0 < v j g → S i = S j) ∧
        ∃ a ∈ agents, ∃ b ∈ agents, S a = true ∧ S b = false := by
      refine Classical.byContradiction fun hno => hconn fun S hS i hi j hj => ?_
      cases hSi : S i <;> cases hSj : S j
      · rfl
      · exact absurd ⟨S, hS, j, hj, i, hi, hSj, hSi⟩ hno
      · exact absurd ⟨S, hS, i, hi, j, hj, hSi, hSj⟩ hno
      · rfl
    let T : G → Bool := fun g => decide (∃ a ∈ agents, S a = true ∧ 0 < v a g)
    have hST : ∀ i ∈ agents, ∀ g ∈ goods, 0 < v i g → S i = T g := by
      intro i hi g hg hpos
      cases hSi : S i
      · refine (decide_eq_false fun ⟨a', ha', hSa', hpa'⟩ => ?_).symm
        have := hS g hg i hi a' ha' hpos hpa'
        rw [hSi, hSa'] at this
        exact Bool.noConfusion this
      · exact (decide_eq_true ⟨i, hi, hSi, hpos⟩).symm
    have hlenS : (agents.filter S).length < agents.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨b, hb, by simp [hab.2]⟩
    have hlenN : (agents.filter (fun i => !S i)).length < agents.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨a, ha, by simp [hab.1]⟩
    have hgS := (List.filter_sublist (p := T) (l := goods)).length_le
    have hgN := (List.filter_sublist (p := fun g => !T g) (l := goods)).length_le
    obtain ⟨X1, hX1, hE1⟩ := ih _ (by omega) (agents.filter S) (goods.filter T) rfl
      (List.ne_nil_of_mem (List.mem_filter.mpr ⟨ha, hab.1⟩)) (hag.filter _) (hgd.filter _) (by omega)
      (hP _ _ _ _ hPa List.filter_sublist List.filter_sublist)
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i (List.mem_filter.mp hi).1))
    obtain ⟨X2, hX2, hE2⟩ := ih _ (by omega) (agents.filter (fun i => !S i)) (goods.filter (fun g => !T g))
      rfl (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hb, by simp [hab.2]⟩)) (hag.filter _) (hgd.filter _)
      (by omega) (hP _ _ _ _ hPa List.filter_sublist List.filter_sublist)
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i (List.mem_filter.mp hi).1))
    exact ⟨_, efx0_split v S T hST hX1 hE1 hX2 hE2⟩
  have hconn : Connected v agents goods := Classical.byContradiction hconn
  -- 5. a connected k = 4 core in the class
  have hq : ∀ i, ∀ g, isPrivate v i (agents.erase i) g = true → 0 < v i g :=
    fun i g hg => ((isPrivate_iff v hag).mp hg).1
  refine hcore agents goods hag hgd hN hPa ⟨by omega, fun i hi => ⟨(hbal i hi).1, h4 i hi⟩,
    fun i hi => (hbal i hi).2, fun i hi => ?_, fun i hi _ => ?_, fun g hg => ?_⟩ hconn
  · rw [privateGoods_eq v hag, length_relevant_split v i _ goods (hq i)]
    refine Nat.add_le_add_left (Nat.le_of_not_lt fun hlt => hR2 ⟨i, hi, ?_⟩) _
    exact R2_balance_of_le_one v _ (hbal i hi).2 (by omega)
  · rw [privateGoods_eq v hag, sharedGoods_eq v hag]
    exact Nat.lt_of_not_le fun hle => hR2 ⟨i, hi, hle⟩
  · refine Classical.byContradiction fun hno => hjunk ⟨g, hg, ?_⟩
    simp only [isJunk, List.all_eq_true, beq_iff_eq]
    intro j hj
    exact Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hpos⟩

/-- **K4.CORE for a sub-instance-closed class, new cores only**: as `EFX.core_reduction4_mixed`, a k = 4 core whose
agents all have three relevant goods is covered by Corollary D. -/
theorem core_reduction4_mixed_of (v : A → G → Nat) (N : Nat) (P : List A → List G → Prop)
    (hP : ∀ (agents agents' : List A) (goods goods' : List G), P agents goods → agents'.Sublist agents →
      goods'.Sublist goods → P agents' goods')
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      P agents goods → IsCore4 v agents goods → Connected v agents goods →
      (∃ i ∈ agents, (relevant v i goods).length = 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → P agents goods → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  refine core_reduction4_conn_of v N P hP fun agents goods hag hgd hN hPa hc hconn => ?_
  by_cases h4 : ∃ i ∈ agents, (relevant v i goods).length = 4
  · exact hcore agents goods hag hgd hN hPa hc hconn h4
  have h3 : ∀ i ∈ agents, (relevant v i goods).length = 3 := fun i hi => by
    have := (hc.2.1 i hi).1
    have := (hc.2.1 i hi).2
    have : (relevant v i goods).length ≠ 4 := fun h => h4 ⟨i, hi, h⟩
    omega
  obtain ⟨hlen, hk1, hk2, -, -⟩ := isCore_of_isCore4 v hc h3
  have hne : agents ≠ [] := fun h => by rw [h] at hlen; simp at hlen
  obtain ⟨X, hX, hE, -⟩ := LB.corollaryD_lists v hag hgd hne hk1 (fun i hi g hg => Nat.le_of_lt (hk2 i hi g hg))
  exact ⟨X, hX, hE⟩

/-- **K4.CORE with K4.TIE, at most one 4-good agent.** If every connected strict k = 4 core with at most `N` agents
and exactly one 4-good agent has an EFX₀ allocation, then so does every instance with at most `N` agents in which
every agent has at most four relevant goods and at most one has four. The class "every agent at most four, at most
one with four" passes to sub-instances (`atMostOne4_sublist`), and the perturbation keeps the relevant goods
(`EFX.pos_tieBreak_iff`, through `EFX.tie_reduction`'s positivity hypothesis). -/
theorem core_reduction4_one_strict (N : Nat)
    (hcore : ∀ (w : A → G → Nat) (agents : List A) (goods : List G), agents.Nodup → goods.Nodup →
      agents.length ≤ N → IsCore4 w agents goods → Connected w agents goods → Strict w agents goods →
      AtMostOne4 w agents goods → (∃ i ∈ agents, (relevant w i goods).length = 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L w agents goods X)
    (v : A → G → Nat) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → AtMostOne4 v agents goods → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  intro agents goods hne hag hgd hN h1 h4
  refine core_reduction4_mixed_of v N
    (fun ag gd => AtMostOne4 v ag gd ∧ ∀ i ∈ ag, (relevant v i gd).length ≤ 4)
    (fun _ _ _ _ ⟨h1, h4⟩ ha hg => ⟨atMostOne4_sublist h4 h1 ha hg,
      fun i hi => Nat.le_trans (relevant_sublist v hg) (h4 i (ha.subset hi))⟩)
    (fun ag gd hag hgd hN ⟨h1, _⟩ hc hconn ⟨i, hi, hi4⟩ => tie_reduction v hgd
      (fun w hw hcw hconnw hsw => by
        have hrel : ∀ j, relevant w j gd = relevant v j gd := fun j => List.filter_congr fun g _ => by simp [hw]
        exact hcore w ag gd hag hgd hN hcw hconnw hsw
          (fun j hj k hk hj4 hk4 => h1 j hj k hk (hrel j ▸ hj4) (hrel k ▸ hk4)) ⟨i, hi, (hrel i).symm ▸ hi4⟩)
      hc hconn)
    agents goods hne hag hgd hN ⟨h1, h4⟩ h4

/-- **K4.CORE with K4.TIE in the model's terms, at most one 4-good agent.** If every connected strict k = 4 core
on `I`'s agents and goods (any values) with at most `N` agents and exactly one 4-good agent has an EFX₀
allocation, and every agent of `I` positively values at most four goods, at most one agent exactly four, then `I`
has a complete EFX₀ allocation. -/
theorem target4one_of_strict_cores (I : Inst) (hn : 0 < I.n) (N : Nat) (hN : I.n ≤ N)
    (hcore : ∀ (w : Fin I.n → Fin I.m → Nat) (agents : List (Fin I.n)) (goods : List (Fin I.m)),
      agents.Nodup → goods.Nodup → agents.length ≤ N → IsCore4 w agents goods → Connected w agents goods →
      Strict w agents goods → AtMostOne4 w agents goods → (∃ i ∈ agents, (relevant w i goods).length = 4) →
      ∃ X : Fin I.m → Fin I.n, IsAllocation agents goods X ∧ EFX0L w agents goods X)
    (h : ∀ i, numRelevant I i ≤ 4) (h1 : ∀ i j, numRelevant I i = 4 → numRelevant I j = 4 → i = j) :
    ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := core_reduction4_one_strict N hcore I.v (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n) (List.nodup_finRange I.m)
    (by rw [List.length_finRange]; exact hN)
    (fun i _ j _ hi hj => h1 i j ((numRelevant_eq I i).trans hi) ((numRelevant_eq I j).trans hj))
    (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

namespace LB4R

open LB4

/-- **C₄∃ with at most one 4-good agent** (the conclusion of Conjecture C₄¹, ledger K4.C4.1): every
connected strict k = 4 core in which at most one agent has four relevant goods has a sound completion
(`EFX.LB4.SoundCompletion`), equivalently a D2-shaped EFX₀ allocation (`C4existsOne_iff`). -/
def C4existsOne (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup →
    IsCore4 v agents goods → Connected v agents goods → Strict v agents goods → AtMostOne4 v agents goods →
      ∃ (base : G → Option A) (N : A → G → Prop) (o : Option A) (X : G → A),
        SoundCompletion v agents goods base N o X

/-- **C₄∃ with at most one 4-good agent ⟺ K4.D on those cores**: a sound completion is a D2-shaped EFX₀ allocation
(`EFX.LB4.SoundCompletion.efx0_d2`) and conversely (`sound_of_d2`), as in `C4exists_iff`. -/
theorem C4existsOne_iff :
    C4existsOne A G ↔
      ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup →
        IsCore4 v agents goods → Connected v agents goods → Strict v agents goods → AtMostOne4 v agents goods →
          ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
            ∃ w ∈ agents, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 := by
  constructor
  · intro h agents goods v hag hgd hc hconn hs h1
    have hne : agents ≠ [] := fun e => by have := hc.1; rw [e] at this; simp at this
    obtain ⟨base, N, o, X, hS⟩ := h agents goods v hag hgd hc hconn hs h1
    exact ⟨X, hS.efx0_d2 hgd hne⟩
  · intro h agents goods v hag hgd hc hconn hs h1
    obtain ⟨X, hX, hE, w, hw, h2⟩ := h agents goods v hag hgd hc hconn hs h1
    obtain ⟨base, N, o, hS⟩ := sound_of_d2 hgd hX hE hw h2
    exact ⟨base, N, o, X, hS⟩

/-- C₄∃ (every strict k = 4 core) implies its restriction to at most one 4-good agent. -/
theorem C4existsOne_of_C4exists (h : TheoremC4exists A G) : C4existsOne A G :=
  fun agents goods v hag hgd hc _ hs _ => h agents goods v hag hgd hc hs

/-- **A core whose agents all have three goods has a sound completion**: Corollary D gives an EFX₀ allocation with at
most one bundle of more than two goods (`EFX.LB.corollaryD_lists`), and such an allocation is a sound completion
(`sound_of_d2`). -/
theorem sound_of_three_cores {agents : List A} {goods : List G} {v : A → G → Nat} (hag : agents.Nodup)
    (hgd : goods.Nodup) (hc : IsCore4 v agents goods) (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3) :
    ∃ (base : G → Option A) (N : A → G → Prop) (o : Option A) (X : G → A),
      SoundCompletion v agents goods base N o X := by
  have hne : agents ≠ [] := fun e => by have := hc.1; rw [e] at this; simp at this
  obtain ⟨X, hX, hE, o, ho⟩ :=
    LB.corollaryD_lists v hag hgd hne h3 (fun i hi g hg => Nat.le_of_lt (hc.2.2.1 i hi g hg))
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil agents hne
  by_cases hoa : o ∈ agents
  · obtain ⟨base, N, o', hS⟩ := sound_of_d2 hgd hX hE hoa ho
    exact ⟨base, N, o', X, hS⟩
  · obtain ⟨base, N, o', hS⟩ := sound_of_d2 hgd hX hE hi0 fun j hj _ => ho j hj fun e => hoa (e ▸ hj)
    exact ⟨base, N, o', X, hS⟩

/-- **`C4existsOne` is the restriction of `C4existsConn`** to at most one 4-good agent: a core with exactly one is
covered by `C4existsConn`, a core with none by Corollary D (`sound_of_three_cores`). -/
theorem C4existsOne_of_C4existsConn (h : C4existsConn A G) : C4existsOne A G := by
  intro agents goods v hag hgd hc hconn hs _
  by_cases h4 : ∃ i ∈ agents, (relevant v i goods).length = 4
  · exact h agents goods v hag hgd hc hconn hs h4
  · refine sound_of_three_cores hag hgd hc fun i hi => ?_
    have := (hc.2.1 i hi).1
    have := (hc.2.1 i hi).2
    have : (relevant v i goods).length ≠ 4 := fun e => h4 ⟨i, hi, e⟩
    omega

/-- **C₄∃ with at most one 4-good agent ⟹ TARGET₄ with at most one 4-good agent.** Every instance with at least one
agent in which every agent has at most four relevant goods, and at most one agent exactly four, has an EFX₀
allocation. `C4existsOne` is a hypothesis, not an axiom. -/
theorem target4one_of_C4existsOne (I : Inst) (hn : 0 < I.n) (hC : C4existsOne (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) (h1 : ∀ i j, numRelevant I i = 4 → numRelevant I j = 4 → i = j) :
    ∃ X : I.Alloc, I.EFX0 X :=
  target4one_of_strict_cores I hn I.n (Nat.le_refl _) (fun w agents goods hag hgd _ hc hconn hs h1 _ => by
    have hne : agents ≠ [] := fun e => by have := hc.1; rw [e] at this; simp at this
    obtain ⟨base, N, o, X, hS⟩ := hC agents goods w hag hgd hc hconn hs h1
    obtain ⟨hX, hE, -⟩ := hS.efx0_d2 hgd hne
    exact ⟨X, hX, hE⟩) h h1

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.atMostOne4_sublist
#print axioms EFX.core_reduction4_conn_of
#print axioms EFX.core_reduction4_mixed_of
#print axioms EFX.core_reduction4_one_strict
#print axioms EFX.target4one_of_strict_cores
#print axioms EFX.LB4R.C4existsOne_iff
#print axioms EFX.LB4R.C4existsOne_of_C4exists
#print axioms EFX.LB4R.sound_of_three_cores
#print axioms EFX.LB4R.C4existsOne_of_C4existsConn
#print axioms EFX.LB4R.target4one_of_C4existsOne
