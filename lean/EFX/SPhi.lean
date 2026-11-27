import EFX.ThmS
import EFX.RoundRSD

/-!
# Theorem S^φ: Theorem S with phantoms (`k4/oc1max_multi.md` §16)

Theorem S^φ (K4.MULTI.SPHI, refereed CORRECT with the fix (S-φ3) in `k4/referee/oc1max_multi.md` §14) is the base case
of the reduction route: at a state with settled agents (phantoms), Theorem S's repair of the remaining instance,
with every phantom keeping its set, is EFX₀ in the whole instance.

In the terms of the ROUND-RSD frame (`EFX/RoundRSD.lean`), a state is `(ks, T)`: its instance is the remaining agents
and goods, its picks `Y` the serial-dictatorship outcome of the remaining order. Let `(k, P, h, H₀)` meet Theorem S's
hypotheses there (`EFX.OC1Max.thmS_core`, `h` junk), `W = (J ∖ {h}) ∪ {Y_z}` the owner's bundle, and `r` the receiver
of `h`. Suppose
- **(S-φ1)** `W` threatens no phantom `φ` at its threshold `τ_φ = v_φ(T_φ)`;
- **(S-φ2)** the receiver's good is not phantom-wanted: the head's new good, if the head is unfrozen after `P`;
  otherwise the pick of an off-chain agent unfrozen at the picks, which then receives `h`;
- **(P3)** for `h`: `v_φ(h) ≤ τ_φ` for every phantom.

(The fix (S-φ3) concerns `h = Y_z`; here `h` is junk, and a phantom-wanted `Y_z` lies in `W`, where (S-φ1) catches it.)

Then OC₁ with phantom constraints holds at the state (`oc1PhiAt_of_sPhi`): the chain is one move, and Theorem S's
completion (`k` takes `W`, `r` takes its good and `h`, everyone else keeps its good) threatens no phantom. With the
invariant of reachable states this lifts, with every phantom keeping its set, to an EFX₀ allocation of the whole
instance (`exists_efx0_of_sPhi`). Theorem S^φ therefore proves `ConjBasePhi` wherever its hypotheses can be met
(`conjBasePhi_of_sPhi`).
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The bundles of a completion that keeps every base and assigns the junk by `H`, `m` and `o`. -/
theorem mem_bundle_of_spec {agents : List A} {goods : List G} {B : A → List G} {o : A} {H : List G} {m : G → A}
    {X : G → A} (hst : ValidState agents goods B) (hbase : ∀ i ∈ agents, ∀ g ∈ B i, X g = i)
    (hjunk : ∀ g ∈ junkOf agents goods B, X g = if g ∈ H then m g else o) {j : A} (hj : j ∈ agents) {g : G} :
    g ∈ bundle goods X j ↔ g ∈ B j ∨ (g ∈ junkOf agents goods B ∧ (if g ∈ H then m g else o) = j) := by
  rw [mem_bundle]
  constructor
  · rintro ⟨hg, hXg⟩
    rcases base_or_junk (agents := agents) (B := B) hg with ⟨i, hi, hgi⟩ | hJ
    · rw [hbase i hi g hgi] at hXg; rw [← hXg]; exact Or.inl hgi
    · rw [hjunk g hJ] at hXg; exact Or.inr ⟨hJ, hXg⟩
  · rintro (hgj | ⟨hJ, hXg⟩)
    · exact ⟨(hst.1 j hj).2 g hgj, hbase j hj g hgj⟩
    · exact ⟨(mem_junkOf.mp hJ).1, by rw [hjunk g hJ]; exact hXg⟩

section sphi
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **Theorem S^φ** (K4.MULTI.SPHI): at a state `(ks, T)`, Theorem S's hypotheses in the remaining instance together
with (S-φ1), (S-φ2) and (P3) for `h` give OC₁ with phantom constraints. -/
theorem oc1PhiAt_of_sPhi (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {ks : List A}
    {T : A → List G} {k : A} {rest : List A}
    (hch : CChain v (remAgents agents ks) (sdPick v (stOrder σ ks) (remGoods goods ks T)) (k :: rest))
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
      (value v φ (T φ)))
    (hφ2z : ¬ Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ∀ φ ∈ ks, ∀ g ∈ afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z, v φ g ≤ value v φ (T φ))
    (hφ2w : Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ∃ w ∈ remAgents agents ks, w ∉ k :: rest ∧
        ¬ Frozen v (remAgents agents ks) (fun a => (sdPick v (stOrder σ ks) (remGoods goods ks T) a).toList) w ∧
        ∀ φ ∈ ks, ∀ g ∈ (sdPick v (stOrder σ ks) (remGoods goods ks T) w).toList, v φ g ≤ value v φ (T φ))
    (hφ3 : ∀ φ ∈ ks, v φ h ≤ value v φ (T φ)) :
    OC1PhiAt v agents goods σ ks T := by
  -- the remaining instance
  have hσS : (stOrder σ ks).Perm (remAgents agents ks) := hσ.filter _
  have hagS : (remAgents agents ks).Nodup := hag.sublist List.filter_sublist
  have hgdS : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  obtain ⟨pre, p, hs⟩ := exists_setting hσS hagS hgdS hch hz hH₀ hH₀W himp
  have hst := hs.validState
  have hk := hs.k_agent
  -- the receiver and its good
  obtain ⟨r, hrk, hspec, hrφ⟩ : ∃ r, r ≠ k ∧
      SStarWith v (remAgents agents ks) (remGoods goods ks T)
        (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) k [h] (fun _ => r) ∧
      ∀ φ ∈ ks, ∀ g ∈ afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ r,
        v φ g ≤ value v φ (T φ) := by
    by_cases hzf : Frozen v (remAgents agents ks)
        (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z
    · obtain ⟨w, hw, hwc, hwun, hwφ⟩ := hφ2w hzf
      refine ⟨w, fun e => hwc (e ▸ List.mem_cons_self),
        thmS_core hσS hagS hgdS hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ2 (r := w) (Or.inr ⟨hzf, hw, hwc, hwun⟩),
        fun φ hφ g hg => hwφ φ hφ g (by rwa [hs.after_off hwc] at hg)⟩
    · exact ⟨z, hs.z_ne_k,
        thmS_core hσS hagS hgdS hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ2 (r := z) (Or.inl ⟨rfl, hzf, hZ1 hzf⟩),
        hφ2z hzf⟩
  obtain ⟨X, ⟨hXa, hXe, hXb, -, hXcnt⟩, hXj⟩ := hspec
  have hmem := fun {j : A} (hj : j ∈ remAgents agents ks) {g : G} => mem_bundle_of_spec (g := g) hst hXb hXj hj
  refine Or.inr ⟨_, Or.inr (Or.inl (cchain_isChain' hσS hch hz hH₀ hH₀W himp)),
    X, hXa, hXe, hXb, ⟨k, hXcnt⟩, fun φ hφ j hj => ?_⟩
  by_cases hjk : j = k
  · -- the owner's bundle is `W`: (S-φ1)
    rw [hjk] at hj ⊢
    have hW' : ∀ g, g ∈ bundle (remGoods goods ks T) X k ↔
        g ∈ wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h := fun g => by
      rw [hmem hj, ← hs.mem_ownerSet_wSet hhJ hH₀h, mem_ownerSet]
      refine or_congr Iff.rfl (and_congr Iff.rfl ?_)
      by_cases hgh : g ∈ [h]
      · have hite : (if g ∈ [h] then r else k) = r := by simp [hgh]
        rw [hite]; exact ⟨fun e => absurd e hrk, fun hn => absurd hgh hn⟩
      · have hite : (if g ∈ [h] then r else k) = k := by simp [hgh]
        rw [hite]; exact ⟨fun _ => hgh, fun _ => rfl⟩
    rw [threat_congr (nodup_bundle hgdS X k) (nodup_wSet hσS hgdS z h) hW']
    exact hφ1 φ hφ
  · by_cases hjr : j = r
    · -- the receiver's bundle: its good and `h`, neither phantom-wanted (S-φ2), (P3)
      rw [hjr] at hj ⊢
      have hsub : ∀ g ∈ bundle (remGoods goods ks T) X r,
          g ∈ afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ r ∨ g = h := fun g hg => by
        rcases (hmem hj).mp hg with hgr | ⟨-, hXg⟩
        · exact Or.inl hgr
        · by_cases hgh : g ∈ [h]
          · exact Or.inr (List.mem_singleton.mp hgh)
          · simp only [hgh, ite_false] at hXg; exact absurd hXg.symm hrk
      refine not_threat_small (T := afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ r ++ [h])
        (nodup_bundle hgdS X r) (fun g hg => ?_) ?_ (fun g hg => ?_)
      · rcases hsub g hg with hgr | rfl
        · exact List.mem_append_left _ hgr
        · simp
      · rw [List.length_append, afterE_ne _ rest H₀ hrk]
        have := length_toList_le (sdPick v (stOrder σ ks) (remGoods goods ks T) (src (k :: rest) r))
        simp only [List.length_singleton]; omega
      · rcases hsub g hg with hgr | rfl
        · exact hrφ φ hφ g hgr
        · exact hφ3 φ hφ
    · -- any other bundle is a single good at most
      have hsub : ∀ g ∈ bundle (remGoods goods ks T) X j,
          g ∈ afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ j := fun g hg => by
        rcases (hmem hj).mp hg with hgj | ⟨-, hXg⟩
        · exact hgj
        · by_cases hgh : g ∈ [h]
          · simp only [hgh, ite_true] at hXg; exact absurd hXg.symm hjr
          · simp only [hgh, ite_false] at hXg; exact absurd hXg.symm hjk
      refine not_threat_of_length_le_one (Nat.le_trans ((nodup_bundle hgdS X j).length_le_of_subset hsub) ?_)
      rw [afterE_ne _ rest H₀ hjk]; exact length_toList_le _

/-- **Theorem S^φ, lifted** (the note's conclusion): at a state with the invariant of reachable states, Theorem S's
repair of the remaining instance, with every phantom keeping its set, gives an EFX₀ allocation of the whole
instance. -/
theorem exists_efx0_of_sPhi (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {ks : List A}
    {T : A → List G} (hI : Inv v agents goods σ ks T) {k : A} {rest : List A}
    (hch : CChain v (remAgents agents ks) (sdPick v (stOrder σ ks) (remGoods goods ks T)) (k :: rest))
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
      (value v φ (T φ)))
    (hφ2z : ¬ Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ∀ φ ∈ ks, ∀ g ∈ afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z, v φ g ≤ value v φ (T φ))
    (hφ2w : Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ∃ w ∈ remAgents agents ks, w ∉ k :: rest ∧
        ¬ Frozen v (remAgents agents ks) (fun a => (sdPick v (stOrder σ ks) (remGoods goods ks T) a).toList) w ∧
        ∀ φ ∈ ks, ∀ g ∈ (sdPick v (stOrder σ ks) (remGoods goods ks T) w).toList, v φ g ≤ value v φ (T φ))
    (hφ3 : ∀ φ ∈ ks, v φ h ≤ value v φ (T φ)) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X :=
  lift_base hσ hgd hI (oc1PhiAt_of_sPhi hσ hag hgd hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ1 hZ2 hφ1 hφ2z hφ2w hφ3)

/-- **A Theorem S^φ case at a state**: some `(k, P, h, H₀)` meets the hypotheses of `oc1PhiAt_of_sPhi`. -/
def SPhiCase (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A) (T : A → List G) :
    Prop :=
  ∃ (k : A) (rest : List A) (z : A) (h : G) (H₀ : List G),
    CChain v (remAgents agents ks) (sdPick v (stOrder σ ks) (remGoods goods ks T)) (k :: rest) ∧
    (k :: rest).getLast? = some z ∧ h ∈ remGoods goods ks T ∧
    (∀ x, sdPick v (stOrder σ ks) (remGoods goods ks T) x ≠ some h) ∧ H₀.Nodup ∧
    (∀ g ∈ H₀, g ∈ remGoods goods ks T ∧ 0 < v k g ∧
      ((∀ x, sdPick v (stOrder σ ks) (remGoods goods ks T) x ≠ some g) ∨
        sdPick v (stOrder σ ks) (remGoods goods ks T) z = some g)) ∧
    h ∉ H₀ ∧ mval v (sdPick v (stOrder σ ks) (remGoods goods ks T)) k < value v k H₀ ∧
    (∀ i ∈ remAgents agents ks, i ≠ k → i ≠ z →
      ¬ Threat v i (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
        (mval v (sdPick v (stOrder σ ks) (remGoods goods ks T)) i)) ∧
    (¬ Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ¬ Threat v z (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
        (value v z (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z) + v z h)) ∧
    (Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ¬ Threat v z (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
        (value v z (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z))) ∧
    (∀ φ ∈ ks, ¬ Threat v φ (wSet v (remAgents agents ks) (remGoods goods ks T) (stOrder σ ks) z h)
      (value v φ (T φ))) ∧
    (¬ Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ∀ φ ∈ ks, ∀ g ∈ afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀ z, v φ g ≤ value v φ (T φ)) ∧
    (Frozen v (remAgents agents ks) (afterE (sdPick v (stOrder σ ks) (remGoods goods ks T)) k rest H₀) z →
      ∃ w ∈ remAgents agents ks, w ∉ k :: rest ∧
        ¬ Frozen v (remAgents agents ks) (fun a => (sdPick v (stOrder σ ks) (remGoods goods ks T) a).toList) w ∧
        ∀ φ ∈ ks, ∀ g ∈ (sdPick v (stOrder σ ks) (remGoods goods ks T) w).toList, v φ g ≤ value v φ (T φ)) ∧
    (∀ φ ∈ ks, v φ h ≤ value v φ (T φ))

theorem oc1PhiAt_of_sPhiCase (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {ks : List A}
    {T : A → List G} (hc : SPhiCase v agents goods σ ks T) : OC1PhiAt v agents goods σ ks T := by
  obtain ⟨k, rest, z, h, H₀, hch, hz, hh, hhJ, hH₀, hH₀W, hH₀h, himp, hW, hZ1, hZ2, hφ1, hφ2z, hφ2w, hφ3⟩ := hc
  exact oc1PhiAt_of_sPhi hσ hag hgd hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ1 hZ2 hφ1 hφ2z hφ2w hφ3

end sphi

/-- **Theorem S^φ proves the base case where it applies**: if every reachable state with a one-move repair has a
Theorem S^φ case, then `ConjBasePhi` holds. -/
theorem conjBasePhi_of_sPhi
    (h : ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
      (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ σ : List A, σ.Perm agents →
        PerfectStart v agents goods (sdPick v σ goods) → ∀ (ks : List A) (T : A → List G),
          Reach v agents goods σ ks T → OC1At v agents goods σ ks T → SPhiCase v agents goods σ ks T) :
    ConjBasePhi A G := by
  intro agents goods v hne hag hgd h4 hs σ hσ hperf ks T hr hoc
  exact oc1PhiAt_of_sPhiCase hσ hag hgd (h agents goods v hne hag hgd h4 hs σ hσ hperf ks T hr hoc)

/-! ## Non-vacuity: a Theorem S^φ case

At the start state (no phantoms) of Theorem U's two-agent instance, Theorem S's case with `h = 2` (`EFX.OC1Max.ExS`)
is a Theorem S^φ case, by `decide`. -/

namespace ExPhi
open OC1Max.ExU

theorem eA : remAgents agents ([] : List (Fin 2)) = agents := by decide
theorem eG : remGoods goods ([] : List (Fin 2)) (fun _ => ([] : List (Fin 5))) = goods := by decide
theorem eO : stOrder σ ([] : List (Fin 2)) = σ := by decide

/-- A Theorem S^φ case at the start state. -/
theorem case_start : SPhiCase v agents goods σ [] (fun _ => []) := by
  unfold SPhiCase
  rw [eA, eG, eO]
  refine ⟨0, [1], 1, 2, [3, 4], OC1Max.ExS.chain, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by unfold Threat; decide, fun _ => by unfold Threat; decide, fun _ => by unfold Threat; decide,
    fun φ hφ => absurd hφ List.not_mem_nil, fun _ φ hφ => absurd hφ List.not_mem_nil, fun hf => ?_,
    fun φ hφ => absurd hφ List.not_mem_nil⟩
  exact absurd hf (by unfold OC1Max.Frozen; decide)

end ExPhi

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.mem_bundle_of_spec
#print axioms EFX.Round.oc1PhiAt_of_sPhi
#print axioms EFX.Round.exists_efx0_of_sPhi
#print axioms EFX.Round.oc1PhiAt_of_sPhiCase
#print axioms EFX.Round.conjBasePhi_of_sPhi
#print axioms EFX.Round.ExPhi.case_start
