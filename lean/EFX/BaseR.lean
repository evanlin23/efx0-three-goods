import EFX.Sep
import EFX.SPhi

/-!
# The BASE-R frame: the greedy process GR never gets stuck ⟹ TARGET₄ (`k4/base_phantom.md` §5)

**The process GR** (greedy P1-free reduction), from a hard perfect start, at the current state `S`:
1. if `S` has a *lifted completion* (`LiftedAt`: a one-absorber completion of the remaining instance that, with every
   phantom keeping its set, is EFX₀ in the whole instance), stop;
2. if `S` has a *final round* (`FinalRound`: an admissible round of any kind after which a lifted completion exists),
   apply it and stop;
3. if `S` has a *base repair* (`BaseRepair Move`: a move of the remaining instance followed by a lifted completion;
   the note's ED repair, `Move` = ED moves), apply it and stop;
4. otherwise apply any admissible round whose settlements are all P1-free (`AdmissibleP1`), and repeat.

**Conjecture BASE-R** (K4.BASE.GR; `ConjBaseRWith Move`, a `Prop`, not an axiom): at every state reached from a hard
perfect start by admissible P1-free rounds (`ReachP1`) with no lifted completion and no admissible P1-free round, a
final round or a base repair exists. It says exactly that GR never gets stuck (`ConjGRWith`, `conjGR_of_conjBaseR`).

**The frame** (`target4_of_conjBaseR`): BASE-R, for any move class, implies TARGET₄. Every stop of GR is an EFX₀
allocation of the whole instance; each round deletes an agent, so GR terminates; a start that is not hard completes at
once; Lemma RED reduces to perfect starts and K4.TIE to strict values.

The bridge to the ROUND-RSD frame (`liftedAt_iff`): at a reachable state, a lifted completion of a state whose
values are at least the picks' is exactly a one-absorber completion respecting the phantom constraints
(`OneAbsorberPhi`), by Corollary LIFT-SEP.
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Definitions -/

/-- A **lifted completion** of `B` at the state `(ks, T)`: a one-absorber completion of the remaining instance that
keeps the bases of `B` and, with every phantom keeping its set, is EFX₀ in the whole instance. -/
def LiftedAt (v : A → G → Nat) (agents : List A) (goods : List G) (ks : List A) (T : A → List G)
    (B : A → List G) : Prop :=
  ∃ X : G → A, IsAllocation (remAgents agents ks) (remGoods goods ks T) X ∧
    (∀ i ∈ remAgents agents ks, ∀ g ∈ B i, X g = i) ∧
    (∃ a, ∀ i ∈ remAgents agents ks, i ≠ a →
      ((junkOf (remAgents agents ks) (remGoods goods ks T) B).filter (fun g => X g = i)).length ≤ 1) ∧
    EFX0L v agents goods (liftAlloc ks T X)

/-- An admissible round whose settlements are all **P1-free**. -/
def AdmissibleP1 (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A)
    (T : A → List G) (K : List A) (rest : A → List A) (T' : A → List G) : Prop :=
  Admissible v agents goods σ ks T K rest T' ∧ ∀ k ∈ K, P1Free v goods k (T' k)

/-- The states reachable by admissible **P1-free** rounds. -/
inductive ReachP1 (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) :
    List A → (A → List G) → Prop
  | start : ReachP1 v agents goods σ [] (fun _ => [])
  | round {ks : List A} {T : A → List G} {K : List A} {rest : A → List A} {T' : A → List G} :
      ReachP1 v agents goods σ ks T → AdmissibleP1 v agents goods σ ks T K rest T' →
      ReachP1 v agents goods σ (ks ++ K) (updT K T' T)

/-- The picks at a state, as bases. -/
abbrev stBase (v : A → G → Nat) (goods : List G) (σ : List A) (ks : List A) (T : A → List G) : A → List G :=
  pickBase v (remGoods goods ks T) (stOrder σ ks)

/-- A **final round**: an admissible round of any kind, after which a lifted completion exists at once. -/
def FinalRound (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A)
    (T : A → List G) : Prop :=
  ∃ (K : List A) (rest : A → List A) (T' : A → List G), Admissible v agents goods σ ks T K rest T' ∧
    LiftedAt v agents goods (ks ++ K) (updT K T' T) (stBase v goods σ (ks ++ K) (updT K T' T))

/-- A **base repair** with moves `Move`: a move of the remaining instance followed by a lifted completion. -/
def BaseRepair (Move : MoveRel A G) (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A)
    (ks : List A) (T : A → List G) : Prop :=
  ∃ B', Move v (remAgents agents ks) (remGoods goods ks T) (stBase v goods σ ks T) B' ∧
    LiftedAt v agents goods ks T B'

/-- **Conjecture BASE-R** (K4.BASE.GR) for a move class `Move` (the note's: ED moves). -/
def ConjBaseRWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ σ : List A, σ.Perm agents →
      PerfectStart v agents goods (sdPick v σ goods) → ¬ OneAbsorber v agents goods (pickBase v goods σ) →
      ∀ (ks : List A) (T : A → List G), ReachP1 v agents goods σ ks T →
        ¬ LiftedAt v agents goods ks T (stBase v goods σ ks T) →
        (¬ ∃ (K : List A) (rest : A → List A) (T' : A → List G), AdmissibleP1 v agents goods σ ks T K rest T') →
        FinalRound v agents goods σ ks T ∨ BaseRepair Move v agents goods σ ks T

/-- **GR never gets stuck**: at every state it can reach, it stops or takes a P1-free round. -/
def ConjGRWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ σ : List A, σ.Perm agents →
      PerfectStart v agents goods (sdPick v σ goods) → ¬ OneAbsorber v agents goods (pickBase v goods σ) →
      ∀ (ks : List A) (T : A → List G), ReachP1 v agents goods σ ks T →
        LiftedAt v agents goods ks T (stBase v goods σ ks T) ∨ FinalRound v agents goods σ ks T ∨
          BaseRepair Move v agents goods σ ks T ∨
          ∃ (K : List A) (rest : A → List A) (T' : A → List G), AdmissibleP1 v agents goods σ ks T K rest T'

/-- **BASE-R says exactly that GR never gets stuck.** -/
theorem conjGR_iff_conjBaseR {Move : MoveRel A G} : ConjGRWith A G Move ↔ ConjBaseRWith A G Move := by
  constructor
  · intro h agents goods v hne hag hgd h4 hs σ hσ hperf hhard ks T hr hnl hnr
    rcases h agents goods v hne hag hgd h4 hs σ hσ hperf hhard ks T hr with hl | hf | hb | hround
    · exact absurd hl hnl
    · exact Or.inl hf
    · exact Or.inr hb
    · exact absurd hround hnr
  · intro h agents goods v hne hag hgd h4 hs σ hσ hperf hhard ks T hr
    by_cases hl : LiftedAt v agents goods ks T (stBase v goods σ ks T)
    · exact Or.inl hl
    · by_cases hround : ∃ (K : List A) (rest : A → List A) (T' : A → List G),
          AdmissibleP1 v agents goods σ ks T K rest T'
      · exact Or.inr (Or.inr (Or.inr hround))
      · rcases h agents goods v hne hag hgd h4 hs σ hσ hperf hhard ks T hr hl hround with hf | hb
        · exact Or.inr (Or.inl hf)
        · exact Or.inr (Or.inr (Or.inl hb))

theorem conjGR_of_conjBaseR {Move : MoveRel A G} (h : ConjBaseRWith A G Move) : ConjGRWith A G Move :=
  conjGR_iff_conjBaseR.mpr h

/-- BASE-R is monotone in the move class (ED moves are official moves). -/
theorem conjBaseR_mono {Move Move' : MoveRel A G}
    (hm : ∀ v agents goods B B', Move v agents goods B B' → Move' v agents goods B B')
    (h : ConjBaseRWith A G Move) : ConjBaseRWith A G Move' := by
  intro agents goods v hne hag hgd h4 hs σ hσ hperf hhard ks T hr hnl hnr
  rcases h agents goods v hne hag hgd h4 hs σ hσ hperf hhard ks T hr hnl hnr with hf | ⟨B', hmv, hl⟩
  · exact Or.inl hf
  · exact Or.inr ⟨B', hm _ _ _ _ _ hmv, hl⟩

/-! ## The frame -/

section frame
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- The lifted allocation is an allocation of the whole instance. -/
theorem isAllocation_liftAlloc {ks : List A} (hks : ∀ k ∈ ks, k ∈ agents) {T : A → List G} {X : G → A}
    (hX : IsAllocation (remAgents agents ks) (remGoods goods ks T) X) :
    IsAllocation agents goods (liftAlloc ks T X) := by
  intro g hg
  cases h : ks.find? (fun k => decide (g ∈ T k)) with
  | some k => simp only [liftAlloc, h]; exact hks k (List.mem_of_find?_eq_some h)
  | none =>
    have hno : ∀ k ∈ ks, g ∉ T k := fun k hk hgk => by
      have := List.find?_eq_none.mp h k hk; simp [hgk] at this
    simp only [liftAlloc, h]
    exact (mem_remAgents.mp (hX g (mem_remGoods.mpr ⟨hg, hno⟩))).1

/-- A lifted completion is an EFX₀ allocation of the whole instance. -/
theorem exists_efx0_of_liftedAt {ks : List A} (hks : ∀ k ∈ ks, k ∈ agents) {T : A → List G} {B : A → List G}
    (h : LiftedAt v agents goods ks T B) : ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨X, hX, -, -, hE⟩ := h
  exact ⟨_, isAllocation_liftAlloc hks hX, hE⟩

theorem reach_of_reachP1 {ks : List A} {T : A → List G} (h : ReachP1 v agents goods σ ks T) :
    Reach v agents goods σ ks T := by
  induction h with
  | start => exact Reach.start
  | round _ hA ih => exact Reach.round ih hA.1

/-- **The BASE-R frame at a hard perfect start**: GR stops at an EFX₀ allocation. -/
theorem exists_efx0_of_conjBaseR_hard {Move : MoveRel A G} (hBR : ConjBaseRWith A G Move) (hne : agents ≠ [])
    (hag : agents.Nodup) (hgd : goods.Nodup) (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hs : Strict v agents goods) (hσ : σ.Perm agents) (hperf : PerfectStart v agents goods (sdPick v σ goods))
    (hhard : ¬ OneAbsorber v agents goods (pickBase v goods σ)) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  have hsv := strictVals_of_strict hs
  have hGR := conjGR_of_conjBaseR hBR agents goods v hne hag hgd h4 hs σ hσ hperf hhard
  have key : ∀ n, ∀ (ks : List A) (T : A → List G), ReachP1 v agents goods σ ks T →
      (remAgents agents ks).length = n → ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ks T hr hn
      have hI := inv_of_reach hσ hag hgd hsv hperf (reach_of_reachP1 hr)
      rcases hGR ks T hr with hl | ⟨K, rest, T', hA, hl⟩ | ⟨B', -, hl⟩ | ⟨K, rest, T', hA⟩
      · -- 1. a lifted completion
        exact exists_efx0_of_liftedAt hI.settled hl
      · -- 2. a final round, then a lifted completion
        have hI' := inv_of_reach hσ hag hgd hsv hperf (Reach.round (reach_of_reachP1 hr) hA)
        exact exists_efx0_of_liftedAt hI'.settled hl
      · -- 3. a base repair
        exact exists_efx0_of_liftedAt hI.settled hl
      · -- 4. a P1-free round: one agent fewer
        have hlt : (remAgents agents (ks ++ K)).length < n := by
          rw [← hn, remAgents_append]
          cases hKc : K with
          | nil => exact absurd hKc hA.1.ne
          | cons k K' =>
            have hk : k ∈ K := by rw [hKc]; exact List.mem_cons_self
            exact List.length_filter_lt_length_iff_exists.mpr ⟨k, hA.1.present k hk, by rw [← hKc]; simpa using hk⟩
        exact ih _ hlt (ks ++ K) (updT K T' T) (ReachP1.round hr hA) rfl
  exact key _ [] (fun _ => []) ReachP1.start rfl

/-- **The BASE-R frame at a perfect start**: a start that is not hard completes at once. -/
theorem exists_efx0_of_conjBaseR_perfect {Move : MoveRel A G} (hBR : ConjBaseRWith A G Move) (hne : agents ≠ [])
    (hag : agents.Nodup) (hgd : goods.Nodup) (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hs : Strict v agents goods) (hσ : σ.Perm agents) (hperf : PerfectStart v agents goods (sdPick v σ goods)) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  by_cases hhard : OneAbsorber v agents goods (pickBase v goods σ)
  · obtain ⟨X, hX, hE, -⟩ := hhard
    exact ⟨X, hX, hE⟩
  · exact exists_efx0_of_conjBaseR_hard hBR hne hag hgd h4 hs hσ hperf hhard

/-- **The bridge to the ROUND-RSD frame** (Corollary LIFT-SEP): at a reachable state, for a state `B` of the remaining
instance whose bases are duplicate-free goods of the instance worth at least the picks, a lifted completion of `B` is
exactly a one-absorber completion of `B` respecting the phantom constraints. -/
theorem liftedAt_iff (hgd : goods.Nodup) {ks : List A} {T : A → List G} (hI : Inv v agents goods σ ks T)
    {B : A → List G}
    (hB : ∀ a ∈ remAgents agents ks, (B a).Nodup ∧ (∀ g ∈ B a, g ∈ remGoods goods ks T) ∧
      mval v (stPicks v σ goods ks T) a ≤ value v a (B a)) :
    LiftedAt v agents goods ks T B ↔ OneAbsorberPhi v agents goods ks T B := by
  have hrnd : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  have hfin : ∀ X : G → A, (∀ i ∈ remAgents agents ks, ∀ g ∈ B i, X g = i) → ∀ a ∈ remAgents agents ks,
      mval v (stPicks v σ goods ks T) a ≤ value v a (bundle (remGoods goods ks T) X a) := fun X hkeep a ha => by
    obtain ⟨hnd, hsub, hle⟩ := hB a ha
    exact Nat.le_trans hle (value_le_of_nodup_sub a hnd fun g hg => mem_bundle.mpr ⟨hsub g hg, hkeep a ha g hg⟩)
  constructor
  · rintro ⟨X, hX, hkeep, hshape, hlift⟩
    -- EFX₀ in the remaining instance: the remaining agents' bundles are unchanged by the lift
    have hE : EFX0L v (remAgents agents ks) (remGoods goods ks T) X := by
      refine efx0L_iff.mpr fun i hi j hj hij => ?_
      have hik : i ∉ ks := (mem_remAgents.mp hi).2
      have hjk : j ∉ ks := (mem_remAgents.mp hj).2
      have h := efx0L_iff.mp hlift i (mem_remAgents.mp hi).1 j (mem_remAgents.mp hj).1 hij
      rwa [threat_congr (nodup_bundle hgd _ j) (nodup_bundle hrnd X j) fun g => mem_bundle_lift_rem hI.disj hjk,
        value_eq_of_mem_iff (nodup_bundle hgd _ i) (nodup_bundle hrnd X i) fun g =>
          mem_bundle_lift_rem hI.disj hik] at h
    exact ⟨X, hX, hE, hkeep, hshape, (liftSep hgd hI hX hE (hfin X hkeep)).mp hlift⟩
  · rintro ⟨X, hX, hE, hkeep, hshape, hΦ⟩
    exact ⟨X, hX, hkeep, hshape, (liftSep hgd hI hX hE (hfin X hkeep)).mpr hΦ⟩


/-- **Theorem S^φ in the P1-free class** (`k4/base_phantom.md` §4.1, SEP 3): when every phantom is P1-free, the
receiver's good and `h` are never phantom-wanted, and a longest chain supplies the receiver when the head is frozen.
So Theorem S's hypotheses in the remaining instance and (S-φ1) alone give OC₁ with phantom constraints. -/
theorem oc1PhiAt_of_sPhi_p1Free (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {ks : List A}
    {T : A → List G} (hP : ∀ φ ∈ ks, P1Free v goods φ (T φ)) {k : A} {rest : List A}
    (hch : CChain v (remAgents agents ks) (sdPick v (stOrder σ ks) (remGoods goods ks T)) (k :: rest))
    (hlong : ∀ rest', CChain v (remAgents agents ks) (sdPick v (stOrder σ ks) (remGoods goods ks T)) (k :: rest') →
      rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z) {h : G} (hh : h ∈ remGoods goods ks T)
    (hhJ : ∀ x, sdPick v (stOrder σ ks) (remGoods goods ks T) x ≠ some h) {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀W : ∀ g ∈ H₀, g ∈ remGoods goods ks T ∧ 0 < v k g ∧
      ((∀ x, sdPick v (stOrder σ ks) (remGoods goods ks T) x ≠ some g) ∨
        sdPick v (stOrder σ ks) (remGoods goods ks T) z = some g))
    (hH₀h : h ∉ H₀) (himp : mval v (sdPick v (stOrder σ ks) (remGoods goods ks T)) k < value v k H₀)
    (hW : ∀ i ∈ remAgents agents ks, i ≠ k → i ≠ z →
      ¬ Threat v i (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
        (mval v (sdPick v (stOrder σ ks) (remGoods goods ks T)) i))
    (hZ1 : ¬ Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ¬ Threat v z (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
        (value v z (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z) + v z h))
    (hZ2 : Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ¬ Threat v z (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
        (value v z (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z)))
    (hφ1 : ∀ φ ∈ ks, ¬ Threat v φ (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
      (value v φ (T φ))) :
    OC1PhiAt v agents goods σ ks T := by
  have hσS : (stOrder σ ks).Perm (remAgents agents ks) := hσ.filter _
  have hagS : (remAgents agents ks).Nodup := hag.sublist List.filter_sublist
  have hgdS : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  obtain ⟨pre, p, hs⟩ := exists_setting hσS hagS hgdS hch hz hH₀ hH₀W himp
  have hm := hs.matching
  refine oc1PhiAt_of_sPhi hσ hag hgd hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ1 hZ2 hφ1
    (fun _ φ hφ g hg => p3_of_p1Free hP hφ ((hs.validState.1 z hs.z_agent).2 g hg))
    (fun hzf => ?_) (fun φ hφ => p3_of_p1Free hP hφ hh)
  obtain ⟨w, hw, hwc, -, hwun⟩ := hs.wanter_of_frozen hlong hzf
  refine ⟨w, hw, hwc, hwun, fun φ hφ g hg => p3_of_p1Free hP hφ ?_⟩
  rw [Option.mem_toList] at hg
  exact (hm.mem w g hg).2.1

end frame

/-! ## TARGET₄ -/

/-- **BASE-R ⟹ EFX₀ for strict instances** (Lemma RED reduces to a perfect start). -/
theorem exists_efx0_of_conjBaseR_strict {Move : MoveRel A G} (hBR : ConjBaseRWith A G Move) {v : A → G → Nat}
    {agents : List A} {goods : List G} (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  have hsv := strictVals_of_strict hs
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd hsv
  obtain ⟨agents', goods', ord', hne'', hag', hgd', hsubA, hsubG, hord', hperf, hext⟩ :=
    red hne hag hgd hs hmax (paretoOpt_sdPick hperm hag hgd hsv)
  have h4' : ∀ i ∈ agents', (relevant v i goods').length ≤ 4 := fun i hi =>
    Nat.le_trans (hsubG.filter _).length_le (h4 i (hsubA.subset hi))
  have hs' : Strict v agents' goods' := fun i hi S T hS hT hdis heq =>
    hs i (hsubA.subset hi) S T (hS.trans hsubG) (hT.trans hsubG) hdis heq
  obtain ⟨X', hX', hE'⟩ := exists_efx0_of_conjBaseR_perfect hBR hne'' hag' hgd' h4' hs' hord' hperf
  exact hext X' hX' hE'

/-- **BASE-R ⟹ TARGET₄ over lists**, ties broken by K4.TIE's perturbation. -/
theorem exists_efx0_of_conjBaseR {Move : MoveRel A G} (hBR : ConjBaseRWith A G Move) (v : A → G → Nat)
    (agents : List A) (goods : List G) (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨X, hX, hE⟩ := exists_efx0_of_conjBaseR_strict hBR (v := tieBreak v goods) hne hag hgd
    (fun i hi => by rw [relevant_tieBreak]; exact h4 i hi) (strict_tieBreak v goods hgd)
  exact ⟨X, hX, efx0_of_tieBreak v goods hgd hE⟩

/-- **The BASE-R frame: Conjecture BASE-R (GR never gets stuck), for any move class, ⟹ TARGET₄.** -/
theorem target4_of_conjBaseR (I : Inst) (hn : 0 < I.n) {Move : MoveRel (Fin I.n) (Fin I.m)}
    (hBR : ConjBaseRWith (Fin I.n) (Fin I.m) Move) (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := exists_efx0_of_conjBaseR hBR I.v (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n) (List.nodup_finRange I.m)
    (fun i _ => (numRelevant_eq I i) ▸ hk i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

/-- **The GR form: GR never gets stuck ⟹ TARGET₄.** -/
theorem target4_of_conjGR (I : Inst) (hn : 0 < I.n) {Move : MoveRel (Fin I.n) (Fin I.m)}
    (hGR : ConjGRWith (Fin I.n) (Fin I.m) Move) (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjBaseR I hn (conjGR_iff_conjBaseR.mp hGR) hk

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.conjGR_iff_conjBaseR
#print axioms EFX.Round.conjBaseR_mono
#print axioms EFX.Round.isAllocation_liftAlloc
#print axioms EFX.Round.exists_efx0_of_conjBaseR_hard
#print axioms EFX.Round.exists_efx0_of_conjBaseR_perfect
#print axioms EFX.Round.liftedAt_iff
#print axioms EFX.Round.oc1PhiAt_of_sPhi_p1Free
#print axioms EFX.Round.exists_efx0_of_conjBaseR
#print axioms EFX.Round.target4_of_conjBaseR
#print axioms EFX.Round.target4_of_conjGR
