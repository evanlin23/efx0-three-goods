import EFX.RF
import EFX.ThmU

/-!
# Lemma REC-∃ and RF for pick-holding receivers (`k4/referee/rfmin.md` §1)

**Lemma REC-∃** (the referee's, `k4/referee/rfmin.md` §1). Let `Y` be serial-dictatorship picks that form a maximum
matching. If no agent that holds a pick is a receiver, then the picks complete with one absorber
(`oneAbsorber_of_noReceiver`; no strictness is assumed). The referee's receivers hold picks. `Receiver` also counts a
pickless agent, vacuously, so here the hypothesis is stated for pick holders. The proof:
1. the last agent of the order is a receiver, so it holds no pick;
2. every pick holder `j` has a wanter, who comes later in the order; walking up gives an alternating path from an
   agent without a pick to `j` (`altReach_of_noReceiver`), so by Lemma MAX `j` values no junk;
3. an agent without a pick values no junk either (it was free at its turn);
4. so the junk is worthless to everyone, and the last agent absorbs it (Lemma M (⇐), owner that agent, `H = ∅`).

Hence every maximum-matching start where OC₁ fails has a receiver that holds a pick (`exists_pick_receiver`).

**Conjecture RF for pick-holding receivers** (`ConjRFpick`, a `Prop`): at every maximum-matching start where OC₁
fails, every receiver that holds a pick satisfies `ReceiverFirst` (some order with it first gives a maximum matching,
and every such order satisfies OC₁). This is the RF of the data, without the untested pickless receivers of
`ConjRF`. By REC-∃ it implies RF∃ (`conjRFsomeWith_of_conjRFpickWith`), hence OC₁^∃max and TARGET₄
(`target4_of_conjRFpick`).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section recExists
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **Walking up to a pickless agent**: if no pick holder is a receiver, every pick holder is reached by an
alternating path from an agent without a pick. -/
theorem altReach_of_noReceiver (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hno : ∀ u ∈ agents, (sdPick v σ goods u).isSome → ¬ Receiver v agents (sdPick v σ goods) u) :
    ∀ n, ∀ j ∈ agents, (afterL σ j).length ≤ n → (sdPick v σ goods j).isSome →
      AltReach v agents (sdPick v σ goods) j := by
  have hσnd : σ.Nodup := hσ.nodup_iff.mpr hag
  -- a pick holder has a wanter, who comes after it
  have hwanter : ∀ j ∈ agents, (sdPick v σ goods j).isSome →
      ∃ i ∈ agents, i ≠ j ∧ Wants v (sdPick v σ goods) i j := fun j hj hs =>
    Classical.byContradiction fun hne => hno j hj hs ⟨hj, fun i hi hij hw => hne ⟨i, hi, hij, hw⟩⟩
  intro n
  induction n with
  | zero =>
    intro j hj hn hs
    obtain ⟨i, hi, hij, y, hy, hlt⟩ := hwanter j hj hs
    have := afterL_lt_of_before hσnd (before_of_wants hσ hag hgd hi hj hij ⟨y, hy, hlt⟩)
    omega
  | succ n ih =>
    intro j hj hn hs
    obtain ⟨i, hi, hij, y, hy, hlt⟩ := hwanter j hj hs
    have hpos : 0 < v i y := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    cases hYi : sdPick v σ goods i with
    | none => exact AltReach.step (AltReach.start hi hYi) hy hpos
    | some _ =>
      have := afterL_lt_of_before hσnd (before_of_wants hσ hag hgd hi hj hij ⟨y, hy, hlt⟩)
      exact AltReach.step (ih i hi (by omega) (by simp [hYi])) hy hpos

/-- **Lemma REC-∃**: at a maximum-matching start where no pick holder is a receiver, the picks have a one-absorber
completion. -/
theorem oneAbsorber_of_noReceiver (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hne : agents ≠ []) (hmax : IsMaximum v agents goods (sdPick v σ goods))
    (hno : ∀ u ∈ agents, (sdPick v σ goods u).isSome → ¬ Receiver v agents (sdPick v σ goods) u) :
    OneAbsorber v agents goods (pickBase v goods σ) := by
  have hσnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hσne : σ ≠ [] := by rintro rfl; exact hne (List.Perm.eq_nil hσ.symm)
  have hℓ : σ.getLast hσne ∈ agents := hσ.mem_iff.mp (List.getLast_mem hσne)
  -- 1. the last agent is a receiver, so it holds no pick
  have hℓrec : Receiver v agents (sdPick v σ goods) (σ.getLast hσne) := ⟨hℓ, fun i hi hiℓ hw =>
    not_before_getLast hσne hσnd i (before_of_wants hσ hag hgd hi hℓ hiℓ hw)⟩
  have hℓnone : sdPick v σ goods (σ.getLast hσne) = none := by
    cases h : sdPick v σ goods (σ.getLast hσne) with
    | none => rfl
    | some _ => exact absurd hℓrec (hno _ hℓ (by simp [h]))
  -- 2, 3. nobody values a junk good
  have hzero : ∀ i ∈ agents, ∀ g ∈ junkOf agents goods (pickBase v goods σ), v i g = 0 := by
    intro i hi g hg
    obtain ⟨hgG, hfree⟩ := (mem_junkOf_pickBase hσ).mp hg
    cases h : sdPick v σ goods i with
    | none =>
      have := junk_le_pick hσ hag hgd hgG hfree hi
      rw [mval_none h] at this; omega
    | some _ =>
      exact max_no_augment hmax (altReach_of_noReceiver hσ hag hgd hno _ i hi (Nat.le_refl _) (by simp [h]))
        g hgG hfree
  -- the owner's set is the junk, worth nothing to anybody
  have hown : ∀ q ∈ agents, ∀ c,
      ¬ Threat v q (ownerSet agents goods (pickBase v goods σ) (σ.getLast hσne) []) c := fun q hq c =>
    not_threat_of_value_le (Nat.le_trans (Nat.le_of_eq (value_eq_zero_of_forall fun g hg => by
      rcases mem_ownerSet.mp hg with hgB | ⟨hgJ, -⟩
      · simp [pickBase, hℓnone] at hgB
      · exact hzero q hq g hgJ)) (Nat.zero_le c))
  -- 4. Lemma M (⇐) with owner the last agent and nothing kept out
  refine oneAbsorber_of_sStar (sStar_of_slotMatching (H := []) (m := fun _ => σ.getLast hσne) hgd
    (validState_pickBase hσ hgd) hℓ (fun j _ _ _ _ _ _ => not_threat_of_length_le_one (length_toList_le _))
    (fun g hg i hi => by rw [hzero i hi g hg]; exact Nat.zero_le _) (fun _ h => absurd h List.not_mem_nil)
    (fun q hq _ _ => hown q hq _) ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun u hu _ _ hex => absurd hex (hown u hu _)⟩)

/-- **Every OC₁-failing maximum-matching start has a receiver that holds a pick.** -/
theorem exists_pick_receiver (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (hmax : IsMaximum v agents goods (sdPick v σ goods)) (hfail : ¬ OneAbsorber v agents goods (pickBase v goods σ)) :
    ∃ u, Receiver v agents (sdPick v σ goods) u ∧ (sdPick v σ goods u).isSome :=
  Classical.byContradiction fun h => hfail (oneAbsorber_of_noReceiver hσ hag hgd hne hmax
    fun u _ hs hr => h ⟨u, hr, hs⟩)

end recExists

/-- **RF for pick-holding receivers, for a move relation `Move`**: at every maximum-matching start where OC₁ fails,
every receiver that holds a pick satisfies `ReceiverFirst`. -/
def ConjRFpickWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      IsMaximum v agents goods (sdPick v ord goods) → ¬ OC1With Move v agents goods ord →
      ∀ u, Receiver v agents (sdPick v ord goods) u → (sdPick v ord goods u).isSome →
        ReceiverFirst Move v agents goods u

/-- **RF for pick-holding receivers** for the moves of `k4/sdc.md` §29. -/
def ConjRFpick (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjRFpickWith A G (fun v agents goods => OneMove v agents goods)

/-- RF over all receivers implies RF over pick-holding ones. -/
theorem conjRFpickWith_of_conjRFWith {Move : MoveRel A G} (h : ConjRFWith A G Move) : ConjRFpickWith A G Move :=
  fun agents goods v hag hgd hc hconn hs ord hperm hmax hoc u hu _ =>
    h agents goods v hag hgd hc hconn hs ord hperm hmax hoc u hu

/-- **RF for pick-holding receivers ⟹ RF∃** (by Lemma REC-∃, a failing start has a pick-holding receiver). -/
theorem conjRFsomeWith_of_conjRFpickWith {Move : MoveRel A G} (h : ConjRFpickWith A G Move) :
    ConjRFsomeWith A G Move := by
  intro agents goods v hag hgd hc hconn hs ord hperm hmax hoc
  have hne : agents ≠ [] := by
    intro he; have := hc.1; rw [he] at this; simp at this
  obtain ⟨u, hu, hs'⟩ := exists_pick_receiver hperm hag hgd hne hmax fun h1 => hoc (Or.inl h1)
  exact ⟨u, hu, h agents goods v hag hgd hc hconn hs ord hperm hmax hoc u hu hs'⟩

/-- **RF for pick-holding receivers ⟹ OC₁^∃max** for the moves of `k4/sdc.md` §29. -/
theorem conjOC1exmax_of_conjRFpick (h : ConjRFpick A G) : ConjOC1exmax A G :=
  conjOC1exmaxWith_of_conjRFsomeWith (conjRFsomeWith_of_conjRFpickWith h)

/-- **RF for pick-holding receivers ⟹ TARGET₄.** -/
theorem target4_of_conjRFpick (I : Inst) (hn : 0 < I.n) (h : ConjRFpick (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1exmax I hn (conjOC1exmax_of_conjRFpick h) hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.altReach_of_noReceiver
#print axioms EFX.OC1Max.oneAbsorber_of_noReceiver
#print axioms EFX.OC1Max.exists_pick_receiver
#print axioms EFX.OC1Max.conjRFpickWith_of_conjRFWith
#print axioms EFX.OC1Max.conjRFsomeWith_of_conjRFpickWith
#print axioms EFX.OC1Max.conjOC1exmax_of_conjRFpick
#print axioms EFX.OC1Max.target4_of_conjRFpick
