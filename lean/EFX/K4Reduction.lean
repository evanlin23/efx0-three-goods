import EFX.Target

/-!
# The k = 4 core reduction (`k4/SCOUT.md` §2, K4.CORE)

- `sharedGoods`: the goods of `goods` relevant to `i` and to some other agent.
- `IsCore4`: a *k = 4 core* (`k4/SCOUT.md` §2, K4.CORE): at least two agents; (C1) every agent has 3 or 4
  relevant goods; (C2) every agent is strictly balanced, each good worth less than its other goods together;
  (C3) an agent with `d` relevant goods has at most `d − 2` private goods (relevant to no other agent): at
  most 1 with 3 goods, at most 2 with 4; (C4) an agent with two private goods `p, q` values them less than
  its shared goods `s, t`, `v(p) + v(q) < v(s) + v(t)`; (C5) every good is relevant to some agent.
- `core_reduction4`: **K4.CORE**. If every k = 4 core with at most `N` agents has an EFX₀ allocation, so
  does every instance with at most `N` agents in which every agent has at most four relevant goods. The
  induction of `EFX.core_reduction` (`proofs/lemmas.md`, CORE), which never uses k: junk goods by L3
  (`EFX.junk`), then peeling by R1 (`EFX.peel`), then by R2 (`EFX.peelR2`, applied whenever its balance
  condition `v_i(R_i ∖ P) ≤ v_i(P)` holds); what remains is a k = 4 core.
- `core_reduction4_mixed`: the same with only the k = 4 cores that have an agent with four relevant goods:
  a k = 4 core whose agents all have three goods is a core in the sense of `EFX.IsCore`, which Corollary D
  (`EFX.LB.corollaryD_lists`) covers.
- `target4_of_cores`: `core_reduction4_mixed` in the model's terms (`EFX.Inst`, `numRelevant I i ≤ 4`).
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The goods of `goods` shared by `i` among `agents`: relevant to `i` and to some other agent. -/
def sharedGoods (v : A → G → Nat) (agents : List A) (i : A) (goods : List G) : List G :=
  goods.filter (fun g => decide (0 < v i g ∧ ∃ j ∈ agents, j ≠ i ∧ 0 < v j g))

/-- A k = 4 core (`k4/SCOUT.md` §2, K4.CORE): (C1)–(C5), with at least two agents. -/
def IsCore4 (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  2 ≤ agents.length ∧
  (∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ (relevant v i goods).length ≤ 4) ∧
  (∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g < value v i goods) ∧
  (∀ i ∈ agents, (privateGoods v agents i goods).length + 2 ≤ (relevant v i goods).length) ∧
  (∀ i ∈ agents, (privateGoods v agents i goods).length = 2 →
    value v i (privateGoods v agents i goods) < value v i (sharedGoods v agents i goods)) ∧
  (∀ g ∈ goods, ∃ i ∈ agents, 0 < v i g)

section lemmas
variable (v : A → G → Nat)

omit [DecidableEq A] [DecidableEq G] in
/-- Splitting `i`'s relevant goods by a test `q` that only relevant goods pass. -/
theorem length_relevant_split (i : A) (q : G → Bool) (goods : List G)
    (hq : ∀ g, q g = true → 0 < v i g) :
    (relevant v i goods).length =
      (goods.filter q).length + (relevant v i (goods.filter (fun g => !q g))).length := by
  have hpriv : (relevant v i (goods.filter q)).length = (goods.filter q).length := by
    unfold relevant
    congr 1
    rw [List.filter_eq_self]
    intro g hg
    simpa using hq g (List.mem_filter.mp hg).2
  rw [← hpriv]
  unfold relevant
  rw [List.filter_filter, List.filter_filter]
  rw [LB.length_filter_add (goods.filter (fun g => decide (0 < v i g))) q, List.filter_filter,
    List.filter_filter]
  congr 2 <;> apply List.filter_congr <;> intro g _ <;> simp [Bool.and_comm]

omit [DecidableEq A] [DecidableEq G] in
/-- R2's balance condition for a strictly balanced agent with at most one relevant good outside `P`
(the goods passing `q`): `v_i(R_i ∖ P) ≤ v_i(P)`. -/
theorem R2_balance_of_le_one {i : A} {goods : List G} (q : G → Bool)
    (hlt : ∀ g ∈ goods, 2 * v i g < value v i goods)
    (h1 : (relevant v i (goods.filter (fun g => !q g))).length ≤ 1) :
    value v i (relevant v i (goods.filter (fun g => !q g))) ≤ value v i (goods.filter q) := by
  rw [value_relevant]
  have hsplit := value_filter_add v i q goods
  have hQ1 : (goods.filter (fun g => !q g)).countP (fun g => decide (0 < v i g)) ≤ 1 := by
    rw [List.countP_eq_length_filter]
    exact h1
  cases hfav : favorite (v i) (goods.filter (fun g => !q g)) with
  | none =>
    rw [(favorite_eq_none_iff _).mp hfav, value_nil]
    exact Nat.zero_le _
  | some z =>
    obtain ⟨hz, hmax⟩ := favorite_spec _ hfav
    have hQ := value_le_of_countP_le_one v i (v i z) hmax hQ1
    have := hlt z (List.mem_filter.mp hz).1
    omega

omit [DecidableEq G] in
/-- The shared goods are the relevant goods that are not private. -/
theorem sharedGoods_eq {agents : List A} (hag : agents.Nodup) (i : A) (goods : List G) :
    sharedGoods v agents i goods =
      relevant v i (goods.filter (fun g => !isPrivate v i (agents.erase i) g)) := by
  unfold sharedGoods relevant
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  have hp := isPrivate_iff v hag (i := i) (g := g)
  cases h : isPrivate v i (agents.erase i) g
  · have hn : ¬ (0 < v i g ∧ ∀ j ∈ agents, j ≠ i → v j g = 0) := fun h' => by
      have := hp.mpr h'; simp_all
    by_cases hi : 0 < v i g
    · have : ∃ j ∈ agents, j ≠ i ∧ 0 < v j g :=
        Classical.byContradiction fun hno =>
          hn ⟨hi, fun j hj hji => Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hji, hpos⟩⟩
      simp [hi, this]
    · simp [hi]
  · obtain ⟨hi, hall⟩ := hp.mp h
    have : ¬ ∃ j ∈ agents, j ≠ i ∧ 0 < v j g := fun ⟨j, hj, hji, hpos⟩ => by
      have := hall j hj hji; omega
    simp [this]

omit [DecidableEq G] in
/-- The private goods of `i`, as R2's test selects them. -/
theorem privateGoods_eq {agents : List A} (hag : agents.Nodup) (i : A) (goods : List G) :
    privateGoods v agents i goods = goods.filter (isPrivate v i (agents.erase i)) := by
  unfold privateGoods
  apply List.filter_congr
  intro g _
  rw [Bool.eq_iff_iff, decide_eq_true_eq, isPrivate_iff v hag]

end lemmas

/-- **The k = 4 CORE theorem** (K4.CORE, `k4/SCOUT.md` §2). If every k = 4 core with at most `N` agents has
an EFX₀ allocation, then so does every instance with at most `N` agents in which every agent has at most
four relevant goods. -/
theorem core_reduction4 (v : A → G → Nat) (N : Nat)
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      IsCore4 v agents goods → ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  suffices H : ∀ s (agents : List A) (goods : List G), agents.length + goods.length = s →
      agents ≠ [] → agents.Nodup → goods.Nodup → agents.length ≤ N →
      (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X from
    fun agents goods => H _ agents goods rfl
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro agents goods hs hne hag hgd hN h4
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
  -- 1. junk goods (L3)
  by_cases hjunk : ∃ g ∈ goods, isJunk v agents g = true
  · obtain ⟨g, hg, hgj⟩ := hjunk
    have hlt : (goods.filter (fun g => !isJunk v agents g)).length < goods.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [hgj]⟩
    obtain ⟨X', hX', hE'⟩ := ih _ (by omega) agents (goods.filter (fun g => !isJunk v agents g)) rfl hne
      hag (hgd.sublist List.filter_sublist) hN
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i hi))
    exact junk v hne hX' hE'
  -- 2. peeling by R1
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
      (by rw [List.length_erase_of_mem hi]; omega)
      (fun j hj => Nat.le_trans (relevant_sublist v List.erase_sublist) (h4 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peel v (List.Nodup.not_mem_erase hag) hp hgd hX' hE' htop
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- every agent has at least three relevant goods and is strictly balanced
  have hbal : ∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods :=
    fun i hi => not_R1 v hg0 (fun ⟨p, hp, h⟩ => hR1 ⟨i, hi, p, hp, h⟩)
  -- 3. peeling by R2: an agent whose private goods `P` are worth at least `R_i ∖ P` leaves with them
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
      (fun j hj => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peelR2 v (List.Nodup.not_mem_erase hag) hX' hE' hb
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- 4. a k = 4 core
  have hq : ∀ i, ∀ g, isPrivate v i (agents.erase i) g = true → 0 < v i g :=
    fun i g hg => ((isPrivate_iff v hag).mp hg).1
  refine hcore agents goods hag hgd hN ⟨by omega, fun i hi => ⟨(hbal i hi).1, h4 i hi⟩,
    fun i hi => (hbal i hi).2, fun i hi => ?_, fun i hi _ => ?_, fun g hg => ?_⟩
  · -- (C3): at least two relevant goods are shared, or else R2 applies
    rw [privateGoods_eq v hag, length_relevant_split v i _ goods (hq i)]
    refine Nat.add_le_add_left (Nat.le_of_not_lt fun hlt => hR2 ⟨i, hi, ?_⟩) _
    exact R2_balance_of_le_one v _ (hbal i hi).2 (by omega)
  · -- (C4): the private goods are worth less than the shared ones, or else R2 applies
    rw [privateGoods_eq v hag, sharedGoods_eq v hag]
    exact Nat.lt_of_not_le fun hle => hR2 ⟨i, hi, hle⟩
  · refine Classical.byContradiction fun hno => hjunk ⟨g, hg, ?_⟩
    simp only [isJunk, List.all_eq_true, beq_iff_eq]
    intro j hj
    exact Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hpos⟩

/-- **The k = 4 CORE theorem, new cores only.** It suffices to treat the k = 4 cores in which some agent has
four relevant goods: a k = 4 core whose agents all have three is a core (`EFX.IsCore`), and Corollary D
covers it. -/
theorem core_reduction4_mixed (v : A → G → Nat) (N : Nat)
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      IsCore4 v agents goods → (∃ i ∈ agents, (relevant v i goods).length = 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  refine core_reduction4 v N fun agents goods hag hgd hN hc => ?_
  by_cases h4 : ∃ i ∈ agents, (relevant v i goods).length = 4
  · exact hcore agents goods hag hgd hN hc h4
  obtain ⟨hlen, hk1, hk2, -, -, -⟩ := hc
  have hne : agents ≠ [] := fun h => by rw [h] at hlen; simp at hlen
  have h3 : ∀ i ∈ agents, (relevant v i goods).length = 3 := fun i hi => by
    have := hk1 i hi
    have : (relevant v i goods).length ≠ 4 := fun h => h4 ⟨i, hi, h⟩
    omega
  obtain ⟨X, hX, hE, -⟩ := LB.corollaryD_lists v hag hgd hne h3 (fun i hi g hg => Nat.le_of_lt (hk2 i hi g hg))
  exact ⟨X, hX, hE⟩

/-- **The k = 4 CORE theorem in the model's terms.** If every k = 4 core of `I`'s agents and goods with at
most `N` agents, some agent having four relevant goods, has an EFX₀ allocation, and every agent of `I`
positively values at most four goods (`|R_i| ≤ 4`), then `I` has a complete EFX₀ allocation. -/
theorem target4_of_cores (I : Inst) (hn : 0 < I.n) (N : Nat) (hN : I.n ≤ N)
    (hcore : ∀ (agents : List (Fin I.n)) (goods : List (Fin I.m)), agents.Nodup → goods.Nodup →
      agents.length ≤ N → IsCore4 I.v agents goods → (∃ i ∈ agents, (relevant I.v i goods).length = 4) →
      ∃ X : Fin I.m → Fin I.n, IsAllocation agents goods X ∧ EFX0L I.v agents goods X)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := core_reduction4_mixed I.v N hcore (List.finRange I.n)
    (List.finRange I.m) (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n)
    (List.nodup_finRange I.m) (by rw [List.length_finRange]; exact hN)
    (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.length_relevant_split
#print axioms EFX.R2_balance_of_le_one
#print axioms EFX.sharedGoods_eq
#print axioms EFX.privateGoods_eq
#print axioms EFX.core_reduction4
#print axioms EFX.core_reduction4_mixed
#print axioms EFX.target4_of_cores
