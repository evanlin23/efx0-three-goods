import EFX.ThmU

/-!
# Theorem S: Theorem U with a junk good kept out (`k4/oc1max_multi.md` §10)

Theorem S (K4.MULTI.S, refereed CORRECT in both forms in `k4/referee/oc1max_multi.md` §10). Let `Y` be the picks of
`σ`, `k :: rest` a *longest* canonical chain from `k` with head `z`, `h` a junk good of the picks, and
`W = (J ∖ {h}) ∪ {Y_z}` (`wSet`). Take an improving `H₀ ⊆ W ∩ R_k`. Suppose
- (S-b, S-c) `W` threatens no agent other than `k` and `z` at its pick value;
- (S-d′) `W` does not threaten `z` at its value in the completion: `v_z(a) + v_z(h)` if `z` is unfrozen after the chain
  (`z` takes `h`), `v_z(a)` otherwise, where `a` is `z`'s new good.

Then the state after the chain has an S\* completion owned by `k` (`thmS`): `h` goes to the head, or to an unfrozen
second wanter of `a`; `k` takes the rest, so its final bundle is `W`. So OC₁ holds at `Y` (`thmS_oc1`).

- `thmS_of_Sd`: the original form, (S-d) `z` values no junk good other than `h`, implies (S-d′).
- `thmS_of_DT`: the note's (S-b) and (S-c): no dangerous agent other than `k` (frozen and valuing a junk good) and
  no unfrozen pick holder other than `z` is threatened by `W` at its pick value; frozen agents valuing no junk, and
  pickless agents at a perfect start, never are.

The proof reuses Theorem U's setting (`EFX.OC1Max.USetting`): Lemma M (⇐) with owner `k` and kept-out set `{h}`, whose
owner's set is `W` (`mem_ownerSet_wSet`). Neither hardness, strict values nor `|R_z| ≤ 4` is used.
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `W = (J ∖ {h}) ∪ {Y_z}`: the junk of the picks without `h`, and the head's pick. -/
def wSet (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (z : A) (h : G) : List G :=
  (junkOf agents goods (pickBase v goods σ)).erase h ++ (sdPick v σ goods z).toList

section thmS
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

theorem mem_wSet (hσ : σ.Perm agents) (hgd : goods.Nodup) {z : A} {h g : G} :
    g ∈ wSet v agents goods σ z h ↔
      (g ∈ goods ∧ (∀ x, sdPick v σ goods x ≠ some g) ∧ g ≠ h) ∨ sdPick v σ goods z = some g := by
  have hJnd : (junkOf agents goods (pickBase v goods σ)).Nodup := hgd.sublist List.filter_sublist
  rw [wSet, List.mem_append, hJnd.mem_erase_iff, mem_junkOf_pickBase hσ, Option.mem_toList]
  constructor
  · rintro (⟨hgh, hg, hall⟩ | hz)
    · exact Or.inl ⟨hg, hall, hgh⟩
    · exact Or.inr hz
  · rintro (⟨hg, hall, hgh⟩ | hz)
    · exact Or.inl ⟨hgh, hg, hall⟩
    · exact Or.inr hz

theorem nodup_wSet (hσ : σ.Perm agents) (hgd : goods.Nodup) (z : A) (h : G) :
    (wSet v agents goods σ z h).Nodup := by
  have hJnd : (junkOf agents goods (pickBase v goods σ)).Nodup := hgd.sublist List.filter_sublist
  refine List.nodup_append.mpr ⟨hJnd.sublist List.erase_sublist, ?_, fun a ha b hb e => ?_⟩
  · cases sdPick v σ goods z <;> simp
  · have haJ := (mem_junkOf_pickBase hσ).mp (List.mem_of_mem_erase ha)
    rw [Option.mem_toList] at hb
    exact haJ.2 z (by rw [hb, e])

/-- A canonical chain in which `k` takes an improving set of junk goods and possibly the head's pick is an official
chain. -/
theorem cchain_isChain' (hσ : σ.Perm agents) {k : A} {rest : List A}
    (hch : CChain v agents (sdPick v σ goods) (k :: rest)) {z : A} (hz : (k :: rest).getLast? = some z)
    {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀J : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g))
    (himp : mval v (sdPick v σ goods) k < value v k H₀) :
    IsChain v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) k rest H₀) := by
  have hzl : (k :: rest).getLast (List.cons_ne_nil _ _) = z := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil k rest)] at hz
    exact Option.some.inj hz
  have hnd := hch.nodup
  have hk : k ∉ rest := (List.nodup_cons.mp hnd).1
  have hne : ∀ x ∈ rest, x ≠ k := fun x hx e => hk (e ▸ hx)
  refine ⟨k, rest, fun a => if a = k then H₀ else [], hch.tail_ne, hnd, hch.mem, fun x _ => ?_,
    fun x _ y _ hxy g hg hg' => ?_, fun g hg => ?_, fun x hx g hg => ?_, ?_, fun p hp => ?_, ?_,
    fun p hp => ?_, fun y hy => ?_⟩
  · by_cases hxk : x = k
    · subst hxk; simp only [ite_true]; exact ⟨hH₀, fun g hg => (hH₀J g hg).2.1⟩
    · simp [hxk]
  · by_cases hxk : x = k
    · have hyk : y ≠ k := fun e => hxy (hxk.trans e.symm)
      simp [hyk] at hg'
    · simp [hxk] at hg
  · simp only [ite_true] at hg
    obtain ⟨hgG, -, h⟩ := hH₀J g hg
    rcases h with h | h
    · exact Or.inl ((mem_junkOf_pickBase hσ).mpr ⟨hgG, h⟩)
    · exact Or.inr (by rw [hzl]; simp [pickBase, h])
  · simp [hne x hx] at hg
  · simp only [ite_true]; rw [pickBase, value_pick]; exact himp
  · have hp2 : p.2 ∈ rest := (List.of_mem_zip hp).2
    obtain ⟨y, hy, hlt⟩ := hch.wants p hp
    simp only [hne p.2 hp2, ite_false, List.append_nil]
    refine ⟨by simp [pickBase, hy], ?_⟩
    rw [pickBase, pickBase, value_pick, hy]; simpa using hlt
  · simp [afterE]
  · have hp2 : p.2 ∈ rest := (List.of_mem_zip hp).2
    simp only [afterE, hne p.2 hp2, ite_false, List.append_nil, pickBase]
    rw [src_of_pair hnd (by simpa using hp)]
  · have hyk : y ≠ k := fun e => hy (e ▸ List.mem_cons_self)
    have hyr : y ∉ rest := fun h => hy (List.mem_cons_of_mem _ h)
    simp only [afterE, hyk, ite_false, pickBase]
    rw [src_of_not_tail (by simpa using hyr)]

/-- With `h` kept out, the owner's set after the chain is `W`. -/
theorem USetting.mem_ownerSet_wSet {k : A} {rest : List A} {H₀ : List G} {pre : List A} {p z : A}
    (hs : USetting v agents goods σ k rest H₀ pre p z) {h : G} (hhJ : ∀ x, sdPick v σ goods x ≠ some h)
    (hH₀h : h ∉ H₀) {g : G} :
    g ∈ ownerSet agents goods (afterE (sdPick v σ goods) k rest H₀) k [h] ↔ g ∈ wSet v agents goods σ z h := by
  have hm := hs.matching
  rw [mem_ownerSet, afterE_self, hs.mem_junk, mem_wSet hs.perm hs.goods_nodup]
  constructor
  · rintro (hg | ⟨⟨hgG, -, hor⟩, hne⟩)
    · obtain ⟨hgG, -, hor⟩ := hs.H₀_junk g hg
      rcases hor with hall | hzg
      · exact Or.inl ⟨hgG, hall, fun e => hH₀h (e ▸ hg)⟩
      · exact Or.inr hzg
    · rcases hor with hall | hzg
      · exact Or.inl ⟨hgG, hall, fun e => hne (List.mem_singleton.mpr e)⟩
      · exact Or.inr hzg
  · rintro (⟨hgG, hall, hgh⟩ | hzg)
    · by_cases hH : g ∈ H₀
      · exact Or.inl hH
      · exact Or.inr ⟨⟨hgG, hH, Or.inl hall⟩, fun e => hgh (List.mem_singleton.mp e)⟩
    · by_cases hH : g ∈ H₀
      · exact Or.inl hH
      · refine Or.inr ⟨⟨(hm.mem z g hzg).2.1, hH, Or.inr hzg⟩, fun e => ?_⟩
        rw [List.mem_singleton.mp e] at hzg
        exact hhJ z hzg

/-- **Theorem S's completion, with an explicit receiver.** In Theorem S's setting (no longest-chain condition), the
receiver `r` of `h` is either the head `z`, unfrozen after the chain and safe at `v_z(a) + v_z(h)`, or, when the head
is frozen after the chain, any off-chain agent unfrozen at the picks. Then the S\* completion with owner `k` gives `h`
to `r`, every other junk good to `k`, and keeps every base. -/
theorem thmS_core (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    {z : A} (hz : (k :: rest).getLast? = some z) {h : G} (hh : h ∈ goods) (hhJ : ∀ x, sdPick v σ goods x ≠ some h)
    {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀W : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g))
    (hH₀h : h ∉ H₀) (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hW : ∀ i ∈ agents, i ≠ k → i ≠ z →
      ¬ Threat v i (wSet v agents goods σ z h) (mval v (sdPick v σ goods) i))
    (hZ2 : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z)))
    {r : A} (hr : (r = z ∧ ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z ∧
        ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z) + v z h)) ∨
      (Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z ∧ r ∈ agents ∧ r ∉ k :: rest ∧
        ¬ Frozen v agents (fun a => (sdPick v σ goods a).toList) r)) :
    SStarWith v agents goods (afterE (sdPick v σ goods) k rest H₀) k [h] (fun _ => r) := by
  obtain ⟨pre, p, hs⟩ := exists_setting hσ hag hgd hch hz hH₀ hH₀W himp
  have hk := hs.k_agent
  have hst := hs.validState
  have hthr : ∀ {i : A} {c : Nat}, Threat v i (ownerSet agents goods (afterE (sdPick v σ goods) k rest H₀) k [h]) c ↔
      Threat v i (wSet v agents goods σ z h) c := fun {_ _} =>
    threat_congr (nodup_ownerSet hk hst hgd _) (nodup_wSet hσ hgd z h) fun _ => hs.mem_ownerSet_wSet hhJ hH₀h
  have hlen : ∀ j, j ≠ k → (afterE (sdPick v σ goods) k rest H₀ j).length ≤ 1 := fun j hjk => by
    rw [afterE_ne _ rest H₀ hjk]; exact length_toList_le _
  -- `W` threatens nobody other than `k` and `z` after the chain
  have hno : ∀ q ∈ agents, q ≠ k → q ≠ z → ¬ Threat v q
      (ownerSet agents goods (afterE (sdPick v σ goods) k rest H₀) k [h])
      (value v q (afterE (sdPick v σ goods) k rest H₀ q)) := fun q hq hqk hqz hT =>
    not_threat_mono (hW q hq hqk hqz) (hs.value_le q) (hthr.mp hT)
  -- (G1)
  have hG1 : G1 v agents (afterE (sdPick v σ goods) k rest H₀) k := fun j _ hjk _ _ _ _ =>
    not_threat_of_length_le_one (hlen j hjk)
  -- (G2)
  have hG2 : G2 v agents goods (afterE (sdPick v σ goods) k rest H₀) := by
    intro g hg i hi
    obtain ⟨hgG, -, hor⟩ := hs.mem_junk.mp hg
    rcases hor with hall | hzg
    · exact Nat.le_trans (junk_le_pick hσ hag hgd hgG hall hi) (hs.value_le i)
    · by_cases hiz : i = z
      · rw [hiz]
        have := hs.value_lt hs.z_mem'
        rw [mval_some hzg] at this; omega
      · have hun := hch.last_unfrozen z hz
        have hle : v i g ≤ mval v (sdPick v σ goods) i := Nat.le_of_not_lt fun hlt =>
          hun (frozen_pick_iff.mpr ⟨i, hi, hiz, g, hzg, hlt⟩)
        exact Nat.le_trans hle (hs.value_le i)
  -- (H1)
  have hH1 : H1 v agents goods (afterE (sdPick v σ goods) k rest H₀) k [h] := by
    intro q hq hqk hqh
    by_cases hqz : q = z
    · rw [hqz] at hqh ⊢
      have hzf : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z :=
        Classical.byContradiction fun hnf => hqh ⟨hnf, hlen z hs.z_ne_k⟩
      exact fun hT => hZ2 hzf (hthr.mp hT)
    · exact hno q hq hqk hqz
  -- `H = {h}` lies in the junk after the chain
  have hhB : h ∈ junkOf agents goods (afterE (sdPick v σ goods) k rest H₀) :=
    hs.mem_junk.mpr ⟨hh, hH₀h, Or.inl hhJ⟩
  have hHJ : ∀ g ∈ [h], g ∈ junkOf agents goods (afterE (sdPick v σ goods) k rest H₀) := fun g hg => by
    rw [List.mem_singleton.mp hg]; exact hhB
  have hinj : ∀ (m : G → A), ∀ g ∈ [h], ∀ g' ∈ [h], m g = m g' → g = g' := fun _ g hg g' hg' _ =>
    (List.mem_singleton.mp hg).trans (List.mem_singleton.mp hg').symm
  rcases hr with ⟨rfl, hzf, hZ1⟩ | ⟨hzf, hw, hwc, hwun⟩
  · -- the receiver of `h` is the head itself
    have hEdge : Edge v agents goods (afterE (sdPick v σ goods) k rest H₀) k [h] h r := by
      by_cases hpos : 0 < v r h
      · exact Or.inr ⟨hpos, fun hT => hZ1 (hthr.mp hT)⟩
      · have h0 : v r h = 0 := by omega
        refine Or.inl fun hT => hZ1 ?_
        rw [h0, Nat.add_zero]; exact hthr.mp hT
    refine sStar_of_slotMatching_spec hgd hst hk hG1 hG2 hHJ hH1 (m := fun _ => r)
      ⟨fun g hg => ?_, hinj _, fun u hu huk _ hex => ?_⟩
    · rw [List.mem_singleton.mp hg]
      exact ⟨hs.z_agent, hs.z_ne_k, ⟨hzf, hlen r hs.z_ne_k⟩, hEdge⟩
    · by_cases huz : u = r
      · exact ⟨h, List.mem_singleton_self _, huz.symm⟩
      · exact absurd hex (hno u hu huk huz)
  · -- the receiver of `h` is an off-chain agent unfrozen at the picks
    have hwk : r ≠ k := fun e => hwc (e ▸ List.mem_cons_self)
    have hwz : r ≠ z := fun e => hwc (e ▸ hs.z_mem')
    have hwB : ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) r := by
      rintro ⟨g, hg, i, hi, hiw, hlt⟩
      rw [hs.after_off hwc, Option.mem_toList] at hg
      exact hwun (frozen_pick_iff.mpr ⟨i, hi, hiw, g, hg, Nat.lt_of_le_of_lt (hs.value_le i) hlt⟩)
    refine sStar_of_slotMatching_spec hgd hst hk hG1 hG2 hHJ hH1 (m := fun _ => r)
      ⟨fun _ _ => ⟨hw, hwk, ⟨hwB, hlen r hwk⟩, Or.inl (hno r hw hwk hwz)⟩, hinj _, fun u hu huk hhu hex => ?_⟩
    by_cases huz : u = z
    · rw [huz] at hhu; exact absurd hzf hhu.1
    · exact absurd hex (hno u hu huk huz)

/-- **Theorem S** (K4.MULTI.S, relaxed form (S-d′)). After a longest canonical chain from `k` with head `z`, in
which `k` takes an improving `H₀ ⊆ W = (J ∖ {h}) ∪ {Y_z}`, if `W` threatens no agent other than `k` and `z` at its
pick value, and `W` does not threaten `z` at its value in the completion, then the state after the chain has an
S\* completion owned by `k`, with `h` kept out. -/
theorem thmS (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z) {h : G} (hh : h ∈ goods) (hhJ : ∀ x, sdPick v σ goods x ≠ some h)
    {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀W : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g))
    (hH₀h : h ∉ H₀) (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hW : ∀ i ∈ agents, i ≠ k → i ≠ z →
      ¬ Threat v i (wSet v agents goods σ z h) (mval v (sdPick v σ goods) i))
    (hZ1 : ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z) + v z h))
    (hZ2 : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z))) :
    SStar v agents goods (afterE (sdPick v σ goods) k rest H₀) k := by
  by_cases hzf : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z
  · -- the receiver is an unfrozen second wanter of the head's new good (the longest-chain argument)
    obtain ⟨pre, p, hs⟩ := exists_setting hσ hag hgd hch hz hH₀ hH₀W himp
    obtain ⟨w, hw, hwc, -, hwun⟩ := hs.wanter_of_frozen hlong hzf
    exact sStar_of_sStarWith (thmS_core hσ hag hgd hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ2
      (r := w) (Or.inr ⟨hzf, hw, hwc, hwun⟩))
  · exact sStar_of_sStarWith (thmS_core hσ hag hgd hch hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ2
      (r := z) (Or.inl ⟨rfl, hzf, hZ1 hzf⟩))

/-- **Theorem S, as a repair**: the chain is one move, and the state after it has a one-absorber completion. -/
theorem thmS_oc1 (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z) {h : G} (hh : h ∈ goods) (hhJ : ∀ x, sdPick v σ goods x ≠ some h)
    {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀W : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g))
    (hH₀h : h ∉ H₀) (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hW : ∀ i ∈ agents, i ≠ k → i ≠ z →
      ¬ Threat v i (wSet v agents goods σ z h) (mval v (sdPick v σ goods) i))
    (hZ1 : ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z) + v z h))
    (hZ2 : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z))) :
    OneMove v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) k rest H₀) ∧
      OneAbsorber v agents goods (afterE (sdPick v σ goods) k rest H₀) :=
  ⟨Or.inr (Or.inl (cchain_isChain' hσ hch hz hH₀ hH₀W himp)),
    oneAbsorber_of_sStar (thmS hσ hag hgd hch hlong hz hh hhJ hH₀ hH₀W hH₀h himp hW hZ1 hZ2)⟩

/-- **Theorem S, original form (S-d)**: if `z` values no junk good other than `h`, (S-d′) holds, since `W` is worth at
most `p_z` to `z` and `z` gains along the chain. -/
theorem thmS_of_Sd (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z) {h : G} (hh : h ∈ goods) (hhJ : ∀ x, sdPick v σ goods x ≠ some h)
    {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀W : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g))
    (hH₀h : h ∉ H₀) (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hW : ∀ i ∈ agents, i ≠ k → i ≠ z →
      ¬ Threat v i (wSet v agents goods σ z h) (mval v (sdPick v σ goods) i))
    (hSd : ∀ g ∈ goods, (∀ x, sdPick v σ goods x ≠ some g) → g ≠ h → v z g = 0) :
    SStar v agents goods (afterE (sdPick v σ goods) k rest H₀) k := by
  obtain ⟨pre, p, hs⟩ := exists_setting hσ hag hgd hch hz hH₀ hH₀W himp
  have hJnd : (junkOf agents goods (pickBase v goods σ)).Nodup := hgd.sublist List.filter_sublist
  have hval : value v z (wSet v agents goods σ z h) = mval v (sdPick v σ goods) z := by
    rw [wSet, value_append_eq, value_pick]
    have h0 : value v z ((junkOf agents goods (pickBase v goods σ)).erase h) = 0 :=
      value_eq_zero_of_forall fun g hg => by
        obtain ⟨hgh, hgJ⟩ := hJnd.mem_erase_iff.mp hg
        obtain ⟨hgG, hall⟩ := (mem_junkOf_pickBase hσ).mp hgJ
        exact hSd g hgG hall hgh
    rw [h0, Nat.zero_add]
  have hlt := hs.value_lt hs.z_mem'
  refine thmS hσ hag hgd hch hlong hz hh hhJ hH₀ hH₀W hH₀h himp hW (fun _ => ?_) (fun _ => ?_)
  · exact not_threat_of_value_le (by omega)
  · exact not_threat_of_value_le (by omega)

/-- **Theorem S in the note's terms** ((S-b), (S-c), (S-d′)): no dangerous agent other than `k` (frozen at the picks
and valuing a junk good) and no unfrozen pick holder other than `z` is threatened by `W` at its pick value. A frozen
agent valuing no junk values `W` at most `v(Y_z)`, at most its pick value, since nobody wants the head's pick; a
pickless agent at a perfect start values nothing. -/
theorem thmS_of_DT (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hperf : PerfectStart v agents goods (sdPick v σ goods))
    {k : A} {rest : List A} (hch : CChain v agents (sdPick v σ goods) (k :: rest))
    (hlong : ∀ rest', CChain v agents (sdPick v σ goods) (k :: rest') → rest'.length ≤ rest.length)
    {z : A} (hz : (k :: rest).getLast? = some z) {h : G} (hh : h ∈ goods) (hhJ : ∀ x, sdPick v σ goods x ≠ some h)
    {H₀ : List G} (hH₀ : H₀.Nodup)
    (hH₀W : ∀ g ∈ H₀, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨ sdPick v σ goods z = some g))
    (hH₀h : h ∉ H₀) (himp : mval v (sdPick v σ goods) k < value v k H₀)
    (hDT : ∀ d ∈ agents, d ≠ k → Frozen v agents (pickBase v goods σ) d →
      (∃ g ∈ junkOf agents goods (pickBase v goods σ), 0 < v d g) →
      ¬ Threat v d (wSet v agents goods σ z h) (mval v (sdPick v σ goods) d))
    (hEJ : ∀ u ∈ agents, (sdPick v σ goods u).isSome → ¬ Frozen v agents (pickBase v goods σ) u → u ≠ z →
      ¬ Threat v u (wSet v agents goods σ z h) (mval v (sdPick v σ goods) u))
    (hZ1 : ¬ Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z) + v z h))
    (hZ2 : Frozen v agents (afterE (sdPick v σ goods) k rest H₀) z →
      ¬ Threat v z (wSet v agents goods σ z h) (value v z (afterE (sdPick v σ goods) k rest H₀ z))) :
    SStar v agents goods (afterE (sdPick v σ goods) k rest H₀) k := by
  have hJnd : (junkOf agents goods (pickBase v goods σ)).Nodup := hgd.sublist List.filter_sublist
  refine thmS hσ hag hgd hch hlong hz hh hhJ hH₀ hH₀W hH₀h himp (fun i hi hik hiz => ?_) hZ1 hZ2
  by_cases hf : Frozen v agents (pickBase v goods σ) i
  · by_cases hjunk : ∃ g ∈ junkOf agents goods (pickBase v goods σ), 0 < v i g
    · exact hDT i hi hik hf hjunk
    · -- `i` values no junk: `W` is worth at most `v_i(Y_z) ≤ p_i` to it
      refine not_threat_of_value_le ?_
      rw [wSet, value_append_eq]
      have h0 : value v i ((junkOf agents goods (pickBase v goods σ)).erase h) = 0 :=
        value_eq_zero_of_forall fun g hg =>
          Nat.eq_zero_of_not_pos fun hpos => hjunk ⟨g, List.mem_of_mem_erase hg, hpos⟩
      rw [h0, Nat.zero_add]
      cases hY : sdPick v σ goods z with
      | none => simp
      | some y =>
        simp only [Option.toList_some, value_cons, value_nil, Nat.add_zero]
        exact Nat.le_of_not_lt fun hlt =>
          hch.last_unfrozen z hz (frozen_pick_iff.mpr ⟨i, hi, hiz, y, hY, hlt⟩)
  · cases hY : sdPick v σ goods i with
    | some y => exact hEJ i hi (by simp [hY]) hf hiz
    | none =>
      have hnull : ∀ g ∈ wSet v agents goods σ z h, v i g = 0 := fun g hg =>
        Nat.eq_zero_of_not_pos fun hpos => by
          have hgG : g ∈ goods := by
            rcases (mem_wSet hσ hgd).mp hg with ⟨hgG, -, -⟩ | hzg
            · exact hgG
            · exact (isMatching_sdPick (v := v) hσ hgd |>.mem z g hzg).2.1
          have := hperf i hi ⟨g, hgG, hpos⟩
          simp [hY] at this
      exact not_threat_of_value_le (by rw [value_eq_zero_of_forall hnull]; exact Nat.zero_le _)

end thmS

/-! ## Non-vacuity: Theorem S applies

Theorem U's two-agent start (`EFX.OC1Max.ExU`) with `h = 2` kept out: `W = {3, 4, 1}`, `k = 0` takes `{3, 4}`, the
head `1` keeps its new good `0` and receives `2`. Every hypothesis of `thmS_oc1` is checked by `decide`, except the
longest-chain condition, which holds because the chain uses both agents. -/

namespace ExS
open ExU

theorem chain : CChain v agents (sdPick v σ goods) [0, 1] := by
  refine ⟨by decide, by decide, by decide, fun p hp => ?_, fun z hz => ?_⟩
  · simp at hp; subst hp; exact ⟨0, by decide, by decide⟩
  · simp at hz; subst hz; unfold Frozen; decide

theorem longest : ∀ rest', CChain v agents (sdPick v σ goods) (0 :: rest') → rest'.length ≤ [1].length := by
  intro rest' h
  have := h.nodup.length_le_of_subset (l₂ := agents) fun x hx => h.mem x hx
  simp [agents] at this ⊢; omega

/-- Theorem S applies to this start, with `h = 2`: one move repairs it. -/
theorem repair : OneMove v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) 0 [1] [3, 4]) ∧
    OneAbsorber v agents goods (afterE (sdPick v σ goods) 0 [1] [3, 4]) :=
  thmS_oc1 (h := 2) (z := 1) (List.Perm.refl _) (by decide) (by decide) chain longest (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold Threat; decide)
    (fun _ => by unfold Threat; decide) (fun _ => by unfold Threat; decide)

end ExS

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.mem_wSet
#print axioms EFX.OC1Max.cchain_isChain'
#print axioms EFX.OC1Max.USetting.mem_ownerSet_wSet
#print axioms EFX.OC1Max.thmS_core
#print axioms EFX.OC1Max.thmS
#print axioms EFX.OC1Max.thmS_oc1
#print axioms EFX.OC1Max.thmS_of_Sd
#print axioms EFX.OC1Max.thmS_of_DT
#print axioms EFX.OC1Max.ExS.repair
