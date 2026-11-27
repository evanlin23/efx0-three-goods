import EFX.SDE

/-!
# Lemma SD-E(round) (`k4/oc1max_multi.md` §17 on `proof/k4-oc1max-multi-2`)

Refereed CORRECT (`k4/referee/oc1max_multi.md` §15). A *round* settles a set `K` of agents at once. Each `k ∈ K` gets a
chain `P_k = (k = x₀, …, x_t = z_k)`, `t ≥ 1`, a **prefix** of the earliest-wanter chain `E(k)`: each `x_l` is the
σ-earliest wanter of `Y_{x_{l−1}}`, and the head `z_k` may be frozen. The chains are vertex-disjoint, and `k` takes a
set `T_k` whose only possible pick is its head's, the `T_k` pairwise disjoint. A head pick that no `T_k` takes is
*released*. With strict values, suppose

- **(H)** every agent outside `K` that wants a released head pick at the picks values its good after the round above
  that pick.

Then the state after the round, without `K` and `⋃ T_k`, is the serial-dictatorship outcome of `σ` with `K` deleted
(`sdE_round`).

The proof is SD-E's (`EFX.OC1Max.sdE`) with one new case, and it runs through an abstract form (`sdE_round_abs`):
the round is a map `s` (after the round, `a ∉ K` holds the pick of `s a`) such that every moved agent wants the pick it
receives and is its earliest wanter, no two agents receive the same pick, no received good is taken, and (H) holds for
the picks that nobody receives and nobody takes.
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

omit [DecidableEq A] in
/-- The order of two kept elements is unchanged by a filter. -/
theorem before_filter (p : A → Bool) {c a : A} (hc : p c = true) (ha : p a = true) :
    ∀ {l : List A}, Before (l.filter p) c a ↔ Before l c a
  | [] => by simp [Before]
  | x :: xs => by
    have ih := before_filter p hc ha (l := xs)
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx]
      simp only [Before, List.mem_filter, ha, and_true, ih]
    · rw [List.filter_cons_of_neg hx]
      simp only [Before, ih]
      constructor
      · exact Or.inr
      · rintro (⟨rfl, -⟩ | h)
        · exact absurd hc hx
        · exact h

section abs
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **Lemma SD-E(round), abstract form.** Let `Y` be the picks of `σ` (strict values) and `s` a round: after it, an
agent `a ∉ K` holds the pick of `s a`, where
- (s1) `s a` is `a` itself, or `a` wants `Y_{s a}`;
- (s2) if `s a ≠ a`, `a` is the σ-earliest wanter of `Y_{s a}`;
- (s3) no two agents outside `K` hold the same pick;
- (s4) no good held after the round is in `U` (the goods taken by `K`);
- (H) an agent outside `K` that wants a pick that nobody holds after the round and that is not taken values its good
  after the round above that pick.

Then the state after the round is the serial-dictatorship outcome of `σ` without `K`, on the goods outside `U`. -/
theorem sdE_round_abs (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) {K : List A} {U : List G} {s : A → A}
    (hs1 : ∀ a ∈ agents, a ∉ K → s a ∈ agents ∧ (s a = a ∨ Wants v (sdPick v σ goods) a (s a)))
    (hs2 : ∀ a ∈ agents, a ∉ K → s a ≠ a → ∀ c ∈ agents, c ≠ a → Wants v (sdPick v σ goods) c (s a) →
      Before σ a c)
    (hs3 : ∀ a ∈ agents, ∀ c ∈ agents, a ∉ K → c ∉ K → s a = s c → a = c)
    (hs4 : ∀ a ∈ agents, a ∉ K → ∀ b, sdPick v σ goods (s a) = some b → b ∉ U)
    (hH : ∀ a ∈ agents, a ∉ K → ∀ j ∈ agents, ∀ g, sdPick v σ goods j = some g →
      (∀ c ∈ agents, c ∉ K → sdPick v σ goods (s c) ≠ some g) → g ∉ U → Wants v (sdPick v σ goods) a j →
      ∃ b, sdPick v σ goods (s a) = some b ∧ v a g < v a b) :
    ∀ a ∈ σ.filter (fun a => decide (a ∉ K)),
      sdPick v (σ.filter (fun a => decide (a ∉ K))) (goods.filter (fun g => decide (g ∉ U))) a =
        sdPick v σ goods (s a) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = sdPick v σ goods := ⟨_, rfl⟩
  rw [← hY] at hs1 hs2 hs4 hH ⊢
  have hm : IsMatching v agents goods Y := hY ▸ isMatching_sdPick (v := v) hσ hgd
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hmemσ : ∀ a, a ∈ σ.filter (fun a => decide (a ∉ K)) ↔ a ∈ agents ∧ a ∉ K := fun a => by
    rw [List.mem_filter, hσ.mem_iff]; simp
  have hbef : ∀ c a, c ∉ K → a ∉ K → (Before (σ.filter (fun a => decide (a ∉ K))) c a ↔ Before σ c a) :=
    fun c a hc ha => before_filter _ (by simpa using hc) (by simpa using ha)
  -- the value after the round is at least the pick value
  have hgain : ∀ a ∈ agents, a ∉ K → ∀ b, Y (s a) = some b → mval v Y a ≤ v a b := fun a ha haK b hb => by
    rcases (hs1 a ha haK).2 with h | ⟨y, hy, hlt⟩
    · rw [h] at hb; rw [mval_some hb]; exact Nat.le_refl _
    · rw [hy] at hb; cases hb; exact Nat.le_of_lt hlt
  have hstrict' : ∀ a ∈ σ.filter (fun a => decide (a ∉ K)), ∀ g ∈ goods.filter (fun g => decide (g ∉ U)),
      ∀ h ∈ goods.filter (fun g => decide (g ∉ U)), 0 < v a g → v a g = v a h → g = h := fun a ha g hg h hh =>
    hsv a ((hmemσ a).mp ha).1 g (List.mem_filter.mp hg).1 h (List.mem_filter.mp hh).1
  refine sdPick_eq_of_greedy v _ _ _ (hnd.sublist List.filter_sublist) (hgd.sublist List.filter_sublist) hstrict'
    (fun a ha b hb => ?_) (fun a ha c hc b hb hb' => ?_) (fun a ha g hg havail hpos => ?_)
  · -- (g1) the goods are relevant and not taken
    obtain ⟨ha', haK⟩ := (hmemσ a).mp ha
    obtain ⟨-, hbG, hbpos⟩ := hm.mem _ b hb
    refine ⟨List.mem_filter.mpr ⟨hbG, decide_eq_true (hs4 a ha' haK b hb)⟩, ?_⟩
    rcases (hs1 a ha' haK).2 with h | ⟨y, hy, hlt⟩
    · rw [h] at hb; exact (hm.mem a b hb).2.2
    · rw [hy] at hb; cases hb; omega
  · -- (g2) distinct goods
    obtain ⟨ha', haK⟩ := (hmemσ a).mp ha
    obtain ⟨hc', hcK⟩ := (hmemσ c).mp hc
    exact hs3 a ha' c hc' haK hcK (hm.inj _ _ b hb hb')
  · -- (g3) every agent gets its favourite among the goods left
    obtain ⟨ha', haK⟩ := (hmemσ a).mp ha
    obtain ⟨hgG, hgU⟩ := List.mem_filter.mp hg
    have hgU' : g ∉ U := by simpa using hgU
    refine Classical.byContradiction fun hno => ?_
    have hab : ∀ b, Y (s a) = some b → v a b < v a g := fun b hb =>
      Nat.lt_of_not_le fun hle => hno ⟨b, hb, hle⟩
    have hwant : mval v Y a < v a g := by
      cases hb : Y (s a) with
      | none =>
        rcases (hs1 a ha' haK).2 with h | ⟨y, hy, -⟩
        · rw [h] at hb; rw [mval_none hb]; exact hpos
        · rw [hy] at hb; cases hb
      | some b => exact Nat.lt_of_le_of_lt (hgain a ha' haK b hb) (hab b hb)
    by_cases hpicked : ∃ j, Y j = some g
    · obtain ⟨j, hj⟩ := hpicked
      have hjag := (hm.mem j g hj).1
      have hwj : Wants v Y a j := ⟨g, hj, hwant⟩
      by_cases hheld : ∃ b' ∈ agents, b' ∉ K ∧ Y (s b') = some g
      · -- `g` is held after the round by `b'`, who comes before `a`
        obtain ⟨b', hb', hb'K, hb'g⟩ := hheld
        have hsb' : s b' = j := hm.inj _ _ g hb'g hj
        have hb'a : b' ≠ a := fun e => by
          rw [e] at hb'g; exact absurd (hab g hb'g) (Nat.lt_irrefl _)
        have hBa : Before σ b' a := by
          by_cases hfix : s b' = b'
          · have haj : a ≠ j := fun e => by
              rw [e] at hwant; rw [mval_some hj] at hwant; omega
            have hjb : j = b' := hsb'.symm.trans hfix
            rw [hjb] at hwj haj
            exact before_of_wants hσ hag hgd ha' hb' haj (hY ▸ hwj)
          · exact hs2 b' hb' hb'K hfix a ha' (fun e => hb'a e.symm) (by rw [hsb']; exact hwj)
        exact havail b' ((hbef b' a hb'K haK).mpr hBa) hb'g
      · -- `g` is a released pick: (H)
        have hnone : ∀ c ∈ agents, c ∉ K → Y (s c) ≠ some g := fun c hc hcK h => hheld ⟨c, hc, hcK, h⟩
        obtain ⟨b, hb, hlt⟩ := hH a ha' haK j hjag g hj hnone hgU' hwj
        exact absurd (hab b hb) (Nat.lt_asymm hlt)
    · -- `g` is junk of `Y`: available at `a`'s turn
      have hpk : ∀ j, Y j ≠ some g := fun j hj => hpicked ⟨j, hj⟩
      obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods hnd hgd a (hσ.mem_iff.mpr ha') g hgG
        (fun c _ => by rw [← hY]; exact hpk c) hpos
      rw [← hY] at hy
      rw [mval_some hy] at hwant
      omega

end abs

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.before_filter
#print axioms EFX.Round.sdE_round_abs
