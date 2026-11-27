import EFX.RoundRSD

/-!
# Proposition SEP and Corollary LIFT-SEP (`k4/base_phantom.md` §4.1)

Both refereed CORRECT (ledger K4.BASE.SEP). A settled agent (phantom) `k` holds `T ⊆ R_k` with threshold
`τ = v_k(T)`, and is **P1-free** (`P1Free`) if every good outside `T` is worth at most `τ` to it, so Lemma PHANTOM's
"ℓ alone" constraint never arises. Let `X` be a bundle disjoint from `T`.

**Proposition SEP.**
1. If `|X| ≤ 2` (`sep_small`), or `X` contains at most one good of `R_k ∖ T` (`sep_one`), `X` does not threaten `k`.
2. With `|R_k| ≤ 4`: if `|T| = 3`, nothing threatens `k` (`sep_three`); if `|T| = 2` and `R_k = T ∪ {y, ℓ}`, `X`
   threatens `k` exactly when `{y, ℓ} ⊆ X`, `|X| ≥ 3` and `v_k(y) + v_k(ℓ) > τ` (`sep_two`, from Lemma PHANTOM).
3. In a state all of whose phantoms are P1-free, every remaining good, in particular every junk good, is worth at
   most each phantom's threshold (`p3_of_p1Free`): (P3) of the phantom class holds, and no agent is phantom-frozen.

**Corollary LIFT-SEP** (`liftSep`). At a reachable state of the ROUND-RSD frame, an EFX₀ allocation `X` of the
remaining instance that extends the state (values at least the picks') lifts, with every phantom keeping its set, to
an EFX₀ allocation of the whole instance *iff* no bundle of `X` threatens a phantom at its threshold. With P1-free
phantoms only bundles of three or more goods, two of them relevant to the phantom, matter (`liftSep_p1Free`).
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `k`, holding `T`, is **P1-free**: every good outside `T` is worth at most `v_k(T)` to it. -/
def P1Free (v : A → G → Nat) (goods : List G) (k : A) (T : List G) : Prop :=
  ∀ g ∈ goods, g ∉ T → v k g ≤ value v k T

section sep
variable {v : A → G → Nat} {goods : List G}

omit [DecidableEq A] in
/-- **SEP 1, small bundles**: a bundle of at most two goods, disjoint from `T`, does not threaten a P1-free `k`. -/
theorem sep_small {k : A} {T X : List G} (hP : P1Free v goods k T) (hX : X.Nodup) (hXg : ∀ g ∈ X, g ∈ goods)
    (hXT : ∀ g ∈ X, g ∉ T) (hlen : X.length ≤ 2) : ¬ Threat v k X (value v k T) :=
  not_threat_small hX (fun _ hy => hy) hlen fun y hy => hP y (hXg y hy) (hXT y hy)

omit [DecidableEq A] in
/-- **SEP 1, one relevant good**: a bundle disjoint from `T` with at most one good that `k` values does not threaten
a P1-free `k`. -/
theorem sep_one {k : A} {T X : List G} (hP : P1Free v goods k T) (hXg : ∀ g ∈ X, g ∈ goods)
    (hXT : ∀ g ∈ X, g ∉ T) (h1 : (relevant v k X).length ≤ 1) : ¬ Threat v k X (value v k T) :=
  not_threat_of_relevant_le_one h1 fun y hy => hP y (hXg y hy) (hXT y hy)

omit [DecidableEq A] in
/-- **SEP 2, triples**: with `|R_k| ≤ 4` and `|T| = 3`, nothing disjoint from `T` threatens a P1-free `k`. -/
theorem sep_three {k : A} (hrel : (relevant v k goods).length ≤ 4) {T : List G} (hT : T.Nodup)
    (hTR : ∀ g ∈ T, g ∈ goods ∧ 0 < v k g) (hT3 : T.length = 3) (hP : P1Free v goods k T) {X : List G}
    (hX : X.Nodup) (hXg : ∀ g ∈ X, g ∈ goods) (hXT : ∀ g ∈ X, g ∉ T) : ¬ Threat v k X (value v k T) := by
  refine sep_one hP hXg hXT (length_le_one_of_eq (hX.sublist List.filter_sublist) fun a ha b hb => ?_)
  obtain ⟨haX, hapos⟩ := mem_relevant.mp ha
  obtain ⟨hbX, hbpos⟩ := mem_relevant.mp hb
  refine Classical.byContradiction fun hab => ?_
  have hnd : (a :: b :: T).Nodup :=
    List.nodup_cons.mpr ⟨by simp [hab, hXT a haX], List.nodup_cons.mpr ⟨hXT b hbX, hT⟩⟩
  have hsub : a :: b :: T ⊆ relevant v k goods := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact mem_relevant.mpr ⟨hXg g haX, hapos⟩
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact mem_relevant.mpr ⟨hXg g hbX, hbpos⟩
      · exact mem_relevant.mpr (hTR g hg)
  have := hnd.length_le_of_subset hsub
  simp only [List.length_cons] at this; omega

omit [DecidableEq A] in
/-- **SEP 2, pairs**: with `|R_k| ≤ 4`, `|T| = 2` and `R_k = T ∪ {y, ℓ}` (`v_k(y) < τ`), a bundle disjoint from `T`
threatens a P1-free `k` exactly when it contains `y` and `ℓ`, has at least three goods, and `v_k(y) + v_k(ℓ) > τ`.
Lemma PHANTOM's (P1) is excluded by P1-freeness. -/
theorem sep_two {k : A} (hrel : (relevant v k goods).length ≤ 4) {T : List G} (hT : T.Nodup)
    (hTR : ∀ g ∈ T, g ∈ goods ∧ 0 < v k g) (hT2 : T.length = 2) {y ℓ : G} (hy : y ∈ goods ∧ 0 < v k y)
    (hyT : y ∉ T) (hl : ℓ ∈ goods ∧ 0 < v k ℓ) (hlT : ℓ ∉ T) (hyl : y ≠ ℓ) (himp : v k y < value v k T)
    (hP : P1Free v goods k T) {X : List G} (hX : X.Nodup) (hXg : ∀ g ∈ X, g ∈ goods) (hXT : ∀ g ∈ X, g ∉ T) :
    Threat v k X (value v k T) ↔ y ∈ X ∧ ℓ ∈ X ∧ 3 ≤ X.length ∧ value v k T < v k y + v k ℓ := by
  rw [phantom_two hrel hT hTR hT2 hy hyT hl hlT hyl himp hX hXg hXT]
  have hℓ := hP ℓ hl.1 hlT
  constructor
  · rintro (⟨-, -, hlt⟩ | h)
    · omega
    · exact h
  · exact Or.inr

end sep

/-! ## SEP 3 and Corollary LIFT-SEP, at the states of the ROUND-RSD frame -/

section liftSep
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

omit [DecidableEq A] in
/-- **SEP 3**: if every phantom is P1-free, every remaining good (every junk good, every pick) is worth at most each
phantom's threshold: (P3) holds and nobody is phantom-frozen. -/
theorem p3_of_p1Free {ks : List A} {T : A → List G} (hP : ∀ φ ∈ ks, P1Free v goods φ (T φ)) {φ : A}
    (hφ : φ ∈ ks) {g : G} (hg : g ∈ remGoods goods ks T) : v φ g ≤ value v φ (T φ) :=
  hP φ hφ g (mem_remGoods.mp hg).1 ((mem_remGoods.mp hg).2 φ hφ)

/-- **Corollary LIFT-SEP.** At a state with the invariant of reachable states, an EFX₀ allocation `X` of the remaining
instance whose values are at least the picks' lifts, with every phantom keeping its set, to an EFX₀ allocation of the
whole instance iff no bundle of `X` threatens a phantom at its threshold. -/
theorem liftSep (hgd : goods.Nodup) {ks : List A} {T : A → List G}
    (hI : Inv v agents goods σ ks T) {X : G → A} (hX : IsAllocation (remAgents agents ks) (remGoods goods ks T) X)
    (hE : EFX0L v (remAgents agents ks) (remGoods goods ks T) X)
    (hfin : ∀ a ∈ remAgents agents ks,
      mval v (stPicks v σ goods ks T) a ≤ value v a (bundle (remGoods goods ks T) X a)) :
    EFX0L v agents goods (liftAlloc ks T X) ↔
      ∀ φ ∈ ks, ∀ j ∈ remAgents agents ks,
        ¬ Threat v φ (bundle (remGoods goods ks T) X j) (value v φ (T φ)) := by
  have hrnd : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  have hTg : ∀ k ∈ ks, ∀ g ∈ T k, g ∈ goods := fun k hk => (hI.sets k hk).2
  constructor
  · intro hlift φ hφ j hj
    have hjks : j ∉ ks := (mem_remAgents.mp hj).2
    have hjφ : φ ≠ j := fun e => hjks (e ▸ hφ)
    have h := efx0L_iff.mp hlift φ (hI.settled φ hφ) j (mem_remAgents.mp hj).1 hjφ
    rw [threat_congr (nodup_bundle hgd _ j) (nodup_bundle hrnd X j) fun g => mem_bundle_lift_rem hI.disj hjks,
      value_eq_of_mem_iff (nodup_bundle hgd _ φ) (hI.sets φ hφ).1 fun g =>
        mem_bundle_lift_settled hTg hI.disj hX hφ] at h
    exact h
  · intro hΦ
    exact (liftStar hgd (ks := ks) hI.settled (T := T) hI.sets hI.disj hX hE (fun _ => 0)
      (fun _ a => if a ∈ ks then value v a (T a) else value v a (bundle (remGoods goods ks T) X a)) hΦ
      (fun _ _ _ _ h => absurd h (Nat.lt_irrefl 0))
      (fun k hk a ha hak _ => by
        by_cases has : a ∈ ks
        · simp only [has, ite_true]; exact hI.phantom k hk a has (Ne.symm hak)
        · simp only [has, ite_false]
          have haS : a ∈ remAgents agents ks := mem_remAgents.mpr ⟨ha, has⟩
          exact not_threat_mono (hI.real k hk a haS) (hfin a haS))
      (fun _ _ a _ _ => ⟨fun has => by simp [has], fun has _ => by simp [has]⟩)).2

/-- **LIFT-SEP for P1-free phantoms**: only bundles of three or more goods, at least two of them relevant to the
phantom, can block the lift. -/
theorem liftSep_p1Free (hgd : goods.Nodup) {ks : List A} {T : A → List G}
    (hI : Inv v agents goods σ ks T) (hP : ∀ φ ∈ ks, P1Free v goods φ (T φ)) {X : G → A}
    (hX : IsAllocation (remAgents agents ks) (remGoods goods ks T) X)
    (hE : EFX0L v (remAgents agents ks) (remGoods goods ks T) X)
    (hfin : ∀ a ∈ remAgents agents ks,
      mval v (stPicks v σ goods ks T) a ≤ value v a (bundle (remGoods goods ks T) X a)) :
    EFX0L v agents goods (liftAlloc ks T X) ↔
      ∀ φ ∈ ks, ∀ j ∈ remAgents agents ks, 3 ≤ (bundle (remGoods goods ks T) X j).length →
        2 ≤ (relevant v φ (bundle (remGoods goods ks T) X j)).length →
        ¬ Threat v φ (bundle (remGoods goods ks T) X j) (value v φ (T φ)) := by
  have hrnd : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  rw [liftSep hgd hI hX hE hfin]
  constructor
  · exact fun h φ hφ j hj _ _ => h φ hφ j hj
  · intro h φ hφ j hj
    have hBg : ∀ g ∈ bundle (remGoods goods ks T) X j, g ∈ goods := fun g hg =>
      (mem_remGoods.mp (mem_bundle.mp hg).1).1
    have hBT : ∀ g ∈ bundle (remGoods goods ks T) X j, g ∉ T φ := fun g hg =>
      (mem_remGoods.mp (mem_bundle.mp hg).1).2 φ hφ
    by_cases h3 : 3 ≤ (bundle (remGoods goods ks T) X j).length
    · by_cases h2 : 2 ≤ (relevant v φ (bundle (remGoods goods ks T) X j)).length
      · exact h φ hφ j hj h3 h2
      · exact sep_one (hP φ hφ) hBg hBT (by omega)
    · exact sep_small (hP φ hφ) (nodup_bundle hrnd X j) hBg hBT (by omega)

end liftSep

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.sep_small
#print axioms EFX.Round.sep_one
#print axioms EFX.Round.sep_three
#print axioms EFX.Round.sep_two
#print axioms EFX.Round.p3_of_p1Free
#print axioms EFX.Round.liftSep
#print axioms EFX.Round.liftSep_p1Free
