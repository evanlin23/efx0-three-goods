import EFX.LemmaM

/-!
# Lemma T6: one move serves unit demands (`k4/ttc.md` §14.2)

Lemma T6 (`claude/k4-ttc`, `k4/ttc.md` §14.2; refereed CORRECT). Let `B` be a state in which every agent holds exactly
one pick `y k` (a perfect matching start), `B'` the bases after one improving move (`EFX.OC1Max.OneMove`: an
addition, a chain or a ring), and `X` any complete allocation keeping the new bases (any number of absorbers). Then:
- (a) `t6_dominate`: `X` value-dominates the picks;
- (b) `t6_count`: every bundle of `X` holds at most two picks of other agents (`foreignPicks`);
- (c) `t6_two`: if a bundle `X_i` holds two, then `i` moved, and its new base is another agent `j`'s pick plus junk,
  with `y j ∈ X_i` and `v_i(y_i) < v_i(B'_i) ≤ v_i(y_j) + v_i(J ∩ R_i)`.

**Corollary** (`no_completion_of_cert`, the certificate that one move fails): if every complete EFX₀ allocation that
value-dominates the picks has an agent holding three or more other agents' picks, or two or more with
`v_i(y_k) + v_i(J ∩ R_i) ≤ v_i(y_i)` for each of them, then no state one move reaches has an EFX₀ completion.

The proof follows the note: at one-good bases a move releases at most one pick (`EFX.OC1Max.move_released`), and a
moved agent's new base lies in one other agent's base and the junk (`EFX.OC1Max.move_local`).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The listed agents other than `i` whose pick `X` gives to `i`. -/
def foreignPicks (agents : List A) (y : A → G) (X : G → A) (i : A) : List A :=
  agents.filter (fun k => decide (k ≠ i ∧ X (y k) = i))

section t6
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq G] in
theorem mem_foreignPicks {y : A → G} {X : G → A} {i k : A} :
    k ∈ foreignPicks agents y X i ↔ k ∈ agents ∧ k ≠ i ∧ X (y k) = i := by
  simp [foreignPicks]

omit [DecidableEq A] [DecidableEq G] in
/-- At one-good bases the picks of different agents differ. -/
theorem pick_inj {B : A → List G} {y : A → G} (hst : ValidState agents goods B) (hy : ∀ k ∈ agents, B k = [y k])
    {k l : A} (hk : k ∈ agents) (hl : l ∈ agents) (h : y k = y l) : k = l :=
  Classical.byContradiction fun hkl => hst.2 k hk l hl hkl (y k) (by rw [hy k hk]; simp) (by rw [hy l hl, h]; simp)

omit [DecidableEq A] in
theorem pick_not_junk {B : A → List G} {y : A → G} (hy : ∀ k ∈ agents, B k = [y k]) {k : A} (hk : k ∈ agents) :
    y k ∉ junkOf agents goods B := fun h => (mem_junkOf.mp h).2 k hk (by rw [hy k hk]; simp)

/-- **T6 (a)**: a completion of a one-move state value-dominates the picks. -/
theorem t6_dominate {B B' : A → List G} (hst : ValidState agents goods B) (hm : OneMove v agents goods B B')
    {X : G → A} (hX : ∀ i ∈ agents, ∀ g ∈ B' i, X g = i) :
    ∀ i ∈ agents, value v i (B i) ≤ value v i (bundle goods X i) := by
  intro i hi
  rcases move_local (fun k hk => (hst.1 k hk).1) hm i hi with he | ⟨j, hj, hnd, hmem, hgain⟩
  · exact value_le_of_nodup_sub i (hst.1 i hi).1 fun g hg =>
      mem_bundle.mpr ⟨(hst.1 i hi).2 g hg, hX i hi g (he ▸ hg)⟩
  · refine Nat.le_trans (Nat.le_of_lt hgain) (value_le_of_nodup_sub i hnd fun g hg => mem_bundle.mpr ⟨?_, hX i hi g hg⟩)
    rcases hmem g hg with h1 | h1
    · exact (hst.1 j hj).2 g h1
    · exact (mem_junkOf.mp h1).1

/-- The foreign picks of a bundle lie in `{j, r}`: `r` the agent whose pick the move may release, `j` the agent whose
base `i`'s new base came from (no `j` if `i` did not move). -/
theorem foreign_sub {B B' : A → List G} {y : A → G} (hst : ValidState agents goods B) (hy : ∀ k ∈ agents, B k = [y k])
    (hm : OneMove v agents goods B B') {X : G → A} (hX : ∀ i ∈ agents, ∀ g ∈ B' i, X g = i) {r : A}
    (hr : ∀ k ∈ agents, (∀ j ∈ agents, y k ∉ B' j) → k = r) {i : A} (hi : i ∈ agents) :
    (B' i = B i ∧ ∀ k ∈ foreignPicks agents y X i, k = r) ∨
      ∃ j ∈ agents, (B' i).Nodup ∧ (∀ g ∈ B' i, g ∈ B j ∨ g ∈ junkOf agents goods B) ∧
        value v i (B i) < value v i (B' i) ∧ ∀ k ∈ foreignPicks agents y X i, k = j ∨ k = r := by
  -- a foreign pick of `X_i` in some new base is in `B'_i`
  have hin : ∀ k ∈ foreignPicks agents y X i, k = r ∨ y k ∈ B' i := by
    intro k hk
    obtain ⟨hka, -, hXk⟩ := mem_foreignPicks.mp hk
    by_cases hb : ∃ j ∈ agents, y k ∈ B' j
    · obtain ⟨j, hj, hyj⟩ := hb
      rw [hX j hj (y k) hyj] at hXk; subst hXk
      exact Or.inr hyj
    · exact Or.inl (hr k hka fun j hj hyj => hb ⟨j, hj, hyj⟩)
  rcases move_local (fun k hk => (hst.1 k hk).1) hm i hi with he | ⟨j, hj, hnd, hmem, hgain⟩
  · refine Or.inl ⟨he, fun k hk => (hin k hk).resolve_right fun hyk => ?_⟩
    obtain ⟨hka, hki, -⟩ := mem_foreignPicks.mp hk
    rw [he, hy i hi, List.mem_singleton] at hyk
    exact hki (pick_inj hst hy hka hi hyk)
  · refine Or.inr ⟨j, hj, hnd, hmem, hgain, fun k hk => ?_⟩
    rcases hin k hk with h | hyk
    · exact Or.inr h
    · obtain ⟨hka, -, -⟩ := mem_foreignPicks.mp hk
      rcases hmem (y k) hyk with h1 | h1
      · rw [hy j hj, List.mem_singleton] at h1
        exact Or.inl (pick_inj hst hy hka hj h1)
      · exact absurd h1 (pick_not_junk hy hka)

omit [DecidableEq A] [DecidableEq G] in
theorem length_le_of_sub_pair {L : List A} (hL : L.Nodup) {a b : A} (h : ∀ k ∈ L, k = a ∨ k = b) : L.length ≤ 2 := by
  have := hL.length_le_of_subset (l₂ := [a, b]) fun k hk => by
    rcases h k hk with rfl | rfl <;> simp
  simpa using this

/-- **T6 (b)**: every bundle of a completion of a one-move state holds at most two picks of other agents. -/
theorem t6_count {B B' : A → List G} {y : A → G} (hag : agents.Nodup) (hst : ValidState agents goods B)
    (hy : ∀ k ∈ agents, B k = [y k]) (hm : OneMove v agents goods B B') {X : G → A}
    (hX : ∀ i ∈ agents, ∀ g ∈ B' i, X g = i) : ∀ i ∈ agents, (foreignPicks agents y X i).length ≤ 2 := by
  intro i hi
  obtain ⟨r, hr⟩ := move_released y hy hm
  have hnd : (foreignPicks agents y X i).Nodup := hag.sublist List.filter_sublist
  rcases foreign_sub hst hy hm hX hr hi with ⟨-, h⟩ | ⟨j, -, -, -, -, h⟩
  · exact length_le_of_sub_pair hnd (a := r) (b := r) fun k hk => Or.inl (h k hk)
  · exact length_le_of_sub_pair hnd h

/-- **T6 (c)**: if a bundle `X_i` of a completion of a one-move state holds two picks of other agents, then `i`
moved: its new base lies in another agent `j`'s pick and the junk, `X` gives `y j` to `i`, and `i`'s step gained,
`v_i(y_i) < v_i(B'_i) ≤ v_i(y_j) + v_i(J ∩ R_i)`. -/
theorem t6_two {B B' : A → List G} {y : A → G} (hag : agents.Nodup) (hst : ValidState agents goods B)
    (hy : ∀ k ∈ agents, B k = [y k]) (hm : OneMove v agents goods B B') {X : G → A}
    (hX : ∀ i ∈ agents, ∀ g ∈ B' i, X g = i) {i : A} (hi : i ∈ agents)
    (h2 : 2 ≤ (foreignPicks agents y X i).length) :
    ∃ j ∈ foreignPicks agents y X i, (∀ g ∈ B' i, g = y j ∨ g ∈ junkOf agents goods B) ∧
      value v i (B i) < value v i (B' i) ∧
      value v i (B' i) ≤ v i (y j) + value v i (relevant v i (junkOf agents goods B)) := by
  obtain ⟨r, hr⟩ := move_released y hy hm
  have hnd : (foreignPicks agents y X i).Nodup := hag.sublist List.filter_sublist
  rcases foreign_sub hst hy hm hX hr hi with ⟨-, h⟩ | ⟨j, hj, hndB, hmem, hgain, h⟩
  · have := length_le_of_sub_pair hnd (a := r) (b := r) fun k hk => Or.inl (h k hk)
    exact absurd h2 (by have := length_le_one_of_eq hnd fun a ha b hb => (h a ha).trans (h b hb).symm; omega)
  · have hjmem : j ∈ foreignPicks agents y X i := Classical.byContradiction fun hjn => by
      have := length_le_one_of_eq hnd fun a ha b hb => by
        have ha' := (h a ha).resolve_left fun e => hjn (e ▸ ha)
        have hb' := (h b hb).resolve_left fun e => hjn (e ▸ hb)
        exact ha'.trans hb'.symm
      omega
    have hmem' : ∀ g ∈ B' i, g = y j ∨ g ∈ junkOf agents goods B := fun g hg => by
      rcases hmem g hg with h1 | h1
      · rw [hy j hj, List.mem_singleton] at h1; exact Or.inl h1
      · exact Or.inr h1
    refine ⟨j, hjmem, hmem', hgain, ?_⟩
    have := value_le_of_nodup_sub (v := v) i hndB (M := y j :: junkOf agents goods B) fun g hg => by
      rcases hmem' g hg with h1 | h1
      · rw [h1]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    rwa [value_cons, ← value_relevant v i (junkOf agents goods B)] at this

/-- **The corollary of T6: a certificate that one move fails.** At a state in which every agent holds one pick, if
every complete EFX₀ allocation that value-dominates the picks has an agent `i` holding three or more other agents'
picks, or two or more, each with `v_i(y_k) + v_i(J ∩ R_i) ≤ v_i(y_i)`, then no state one improving move reaches
has an EFX₀ completion (with any number of absorbers). -/
theorem no_completion_of_cert {B : A → List G} {y : A → G} (hag : agents.Nodup) (hst : ValidState agents goods B)
    (hy : ∀ k ∈ agents, B k = [y k])
    (hcert : ∀ X : G → A, IsAllocation agents goods X → EFX0L v agents goods X →
      (∀ i ∈ agents, value v i (B i) ≤ value v i (bundle goods X i)) →
      ∃ i ∈ agents, 3 ≤ (foreignPicks agents y X i).length ∨
        (2 ≤ (foreignPicks agents y X i).length ∧ ∀ k ∈ foreignPicks agents y X i,
          v i (y k) + value v i (relevant v i (junkOf agents goods B)) ≤ value v i (B i)))
    {B' : A → List G} (hm : OneMove v agents goods B B') :
    ¬ ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧ ∀ i ∈ agents, ∀ g ∈ B' i, X g = i := by
  rintro ⟨X, hXa, hE, hX⟩
  obtain ⟨i, hi, h3 | ⟨h2, hb⟩⟩ := hcert X hXa hE (t6_dominate hst hm hX)
  · have := t6_count hag hst hy hm hX i hi; omega
  · obtain ⟨j, hj, -, hgain, hle⟩ := t6_two hag hst hy hm hX hi h2
    have := hb j hj
    omega

end t6

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.t6_dominate
#print axioms EFX.OC1Max.foreign_sub
#print axioms EFX.OC1Max.t6_count
#print axioms EFX.OC1Max.t6_two
#print axioms EFX.OC1Max.no_completion_of_cert
