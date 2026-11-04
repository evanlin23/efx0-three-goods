import EFX.DE4CaseL

/-!
# The robust order on cores of 3-good agents: every maximum is completable (`k4/de4.md` §10.3; ledger
K4.DE4V3R.LEAN)

A consistency check of the frame `target4_of_HC3'_HLL`. On a strict R1-core in which every agent values exactly three
goods, no agent has a lower pair and every upper set is robust. So both hypotheses of the frame hold, with no
conjecture. `HC3'` holds: a free agent on an F₂-clash cycle holds one good, or a robust upper set, which Lemma 25(a)
excludes. `HLL` holds vacuously: (V3) is empty, so by `selfUp_breaks_v3` a maximum has no free self-upgrade. Hence, by
the machine-checked chain, every maximum of the robust order of such a core is completable, an independent proof of
the 3-good case at the level of cores.

**Results.**
- `robust_of_three`: an upper set of an agent with three relevant goods is robust.
- `v3_of_noLP`, `noLP_of_three`: (V3) holds in every state when nobody can hold a lower pair, as on 3-good cores.
- `claimTMax_tame`, `completable_tame`: on a strict R1-core that is **tame** (no agent can hold a lower pair, every
  upper set is robust), every maximum of the robust order is completable, with no hypothesis. Tame agents are the
  3-good ones and the 4-good ones with v(a) > v(b) + v(c) and v(b) > v(c) + v(d).
- `claimTMax_three`, `completable_three`: the case of 3-good cores.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section three
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] in
/-- An upper set of an agent with exactly three relevant goods is robust: at most one relevant good lies outside it,
and that good is worth at most the top. -/
theorem robust_of_three (hgd : goods.Nodup) {i : A} (h3 : (relevant v i goods).length = 3) {S : List G}
    (hS : IsUpper v i goods S) (hSnd : S.Nodup) (hSg : ∀ g ∈ S, g ∈ goods) : IsRobust v i goods S := by
  unfold IsRobust
  have hv := value_filter_pos (v := v) i (goods.filter (fun g => decide (g ∉ S)))
  have hLnd : ((goods.filter (fun g => decide (g ∉ S))).filter (fun g => decide (0 < v i g))).Nodup :=
    (hgd.filter _).filter _
  have hS2 := two_le_of_upper hS hSg
  have hnd : (((goods.filter (fun g => decide (g ∉ S))).filter (fun g => decide (0 < v i g))) ++ S).Nodup := by
    refine List.nodup_append.mpr ⟨hLnd, hSnd, fun a ha b hb e => ?_⟩
    have h1 := (List.mem_filter.mp (List.mem_filter.mp ha).1).2
    subst e
    exact absurd hb (of_decide_eq_true h1)
  have hsub : ∀ g ∈ ((goods.filter (fun g => decide (g ∉ S))).filter (fun g => decide (0 < v i g))) ++ S,
      g ∈ relevant v i goods := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · have h1 := List.mem_filter.mp h
      exact mem_relevant.mpr ⟨(List.mem_filter.mp h1.1).1, of_decide_eq_true h1.2⟩
    · exact mem_relevant.mpr ⟨hSg g h, hS.1 g h⟩
  have hlen := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_append] at hlen
  have hL1 : ((goods.filter (fun g => decide (g ∉ S))).filter (fun g => decide (0 < v i g))).length ≤ 1 := by
    omega
  have hle := value_le_of_length_le_one' (v := v) i hL1 (c := topV v i goods)
    (fun g hg => le_topV v i goods (List.mem_filter.mp (List.mem_filter.mp hg).1).1)
  have := hS.2.1
  omega

omit [DecidableEq G] in
/-- (V3) holds in every state when no listed agent can hold a lower pair. -/
theorem v3_of_noLP (hnolp : ∀ i ∈ agents, ∀ S : List G, ¬ IsLowerPair v i goods S) (base : G → Option A) :
    V3 v agents goods base :=
  fun i hi hlp => absurd hlp (hnolp i hi _)

omit [DecidableEq A] [DecidableEq G] in
/-- An agent with three relevant goods has no lower pair. -/
theorem noLP_of_three {i : A} (h3 : (relevant v i goods).length = 3) (S : List G) : ¬ IsLowerPair v i goods S :=
  fun hlp => by have := hlp.1; rw [h3] at this; exact absurd this (by decide)

/-- **Claim T′ on tame cores** (no hypothesis beyond tameness): on a strict R1-core in which no agent can hold a lower
pair and every upper set is robust, a non-completable maximum of the robust order has every agent holding an upper
set. -/
theorem claimTMax_tame (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) (hnolp : ∀ i ∈ agents, ∀ S : List G, ¬ IsLowerPair v i goods S)
    (hrob : ∀ i ∈ agents, ∀ S : List G, IsUpper v i goods S → S.Nodup → (∀ g ∈ S, g ∈ goods) →
      IsRobust v i goods S)
    {base : G → Option A} (hmax : IsMaximumR v agents goods base) (hnc : ¬ Completable v agents goods base) :
    ∀ i ∈ agents, IsUpper v i goods (hold goods base i) := by
  have hb := hmax.1.1
  -- a free self-upgrade would break (V3), which is empty here
  have hnoup : ∀ x ∈ agents, ¬ FreeSelfUp v agents goods base x := by
    rintro x hx ⟨hfree, p, hp, hN, h2, hgain⟩
    exact selfUp_breaks_v3 hgd hmax hx hfree p hp hN h2 hgain (v3_of_noLP hnolp _)
  by_cases hH : CondH v agents goods base
  · refine Classical.byContradiction fun _ => ?_
    have hE : ∀ i ∈ agents, hold goods base i ≠ [] := fun i hi he => hnc (completable_of_empty hb hi he hH.1)
    obtain ⟨x, d, C, hC⟩ := exists_clashCycle hb hag hgd hnc hne hH.1
    refine no_f1_clashCycle hgd hc hs hmax hH hC fun o ho hnf => ?_
    rcases hb.allowed o (hC.2.1 o ho) with ⟨hl1, _⟩ | hup | hlp
    · match hY : hold goods base o, hl1 with
      | [], _ => exact absurd hY (hE o (hC.2.1 o ho))
      | [y], _ => exact ⟨y, rfl⟩
    · exact absurd (robust_not_on_clashCycle hC ho hup
        (hrob o (hC.2.1 o ho) _ hup (hold_nodup hgd base o) (fun g hg => (mem_hold.mp hg).1))) id
    · exact absurd hlp (hnolp o (hC.2.1 o ho) _)
  · exfalso
    by_cases hJ : ∀ i ∈ agents, value v i (leftover goods base) ≤ value v i (hold goods base i)
    · refine hH ⟨hJ, fun x hx hfree p hp hN h2 hgain => ?_⟩
      exact hnoup x hx ⟨hfree, p, hp, hN, h2, hgain⟩
    · obtain ⟨i, hi, hJi⟩ : ∃ i ∈ agents, value v i (hold goods base i) < value v i (leftover goods base) :=
        Classical.byContradiction fun hno => hJ fun i hi => Nat.le_of_not_lt fun hlt => hno ⟨i, hi, hlt⟩
      obtain ⟨x, hx, hup⟩ := threat_at_max hgd hs hc (topR_of_maxR hgd hmax) hi hJi
      exact hnoup x hx hup

/-- **Every maximum of the robust order of a strict tame R1-core is completable** (machine-checked, no hypothesis):
Claim T′ there, and Theorem A′. -/
theorem completable_tame (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hc : R1Core4 v agents goods) (hs : Strict v agents goods)
    (hnolp : ∀ i ∈ agents, ∀ S : List G, ¬ IsLowerPair v i goods S)
    (hrob : ∀ i ∈ agents, ∀ S : List G, IsUpper v i goods S → S.Nodup → (∀ g ∈ S, g ∈ goods) →
      IsRobust v i goods S)
    {base : G → Option A} (hmax : IsMaximumR v agents goods base) : Completable v agents goods base := by
  refine Classical.byContradiction fun hnc => ?_
  have hup := claimTMax_tame hne hag hgd hc hs hnolp hrob hmax hnc
  obtain ⟨b', hv', hb'⟩ := thmAllUpper v agents goods hne hag hgd hc hs base hmax.1 hup hnc
  exact hmax.2 b' hv' hb'

/-- **Claim T′ on cores of 3-good agents** (no hypothesis). -/
theorem claimTMax_three (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3) {base : G → Option A}
    (hmax : IsMaximumR v agents goods base) (hnc : ¬ Completable v agents goods base) :
    ∀ i ∈ agents, IsUpper v i goods (hold goods base i) :=
  claimTMax_tame hne hag hgd hc hs (fun i hi => noLP_of_three (h3 i hi))
    (fun i hi _ hS hnd hg => robust_of_three hgd (h3 i hi) hS hnd hg) hmax hnc

/-- **Every maximum of the robust order of a strict R1-core of 3-good agents is completable** (machine-checked, no
hypothesis). -/
theorem completable_three (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hc : R1Core4 v agents goods) (hs : Strict v agents goods) (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3)
    {base : G → Option A} (hmax : IsMaximumR v agents goods base) : Completable v agents goods base :=
  completable_tame hne hag hgd hc hs (fun i hi => noLP_of_three (h3 i hi))
    (fun i hi _ hS hnd hg => robust_of_three hgd (h3 i hi) hS hnd hg) hmax

end three

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.robust_of_three
#print axioms EFX.DE4.v3_of_noLP
#print axioms EFX.DE4.noLP_of_three
#print axioms EFX.DE4.claimTMax_tame
#print axioms EFX.DE4.completable_tame
#print axioms EFX.DE4.claimTMax_three
#print axioms EFX.DE4.completable_three
