import EFX.LemmaM

/-!
# Lemma LIFT-1 (`k4/matching.md` §6)

Lemma LIFT-1 (K4.MATCH.LIFT1, `proof/k4-matching`; refereed CORRECT, `k4/referee/lift.md`): at the state `B` = B₂
after the two chains of LIFT-EX, with `h` the head of the second chain and `z` its end holding the single good `t`,
let `X = B_h ∪ J` and `g` z's most valuable junk good (if z values any junk good). Then giving `h` the set `X ∖ {g}`
and `z` the set `{t, g}`, every other agent keeping its base, is an EFX₀ allocation of S\* shape with owner `h`.

**What is assumed** (`lift1`). The facts that the note derives from the two chains before the allocation step:
- `hW` (step 1, from Lemma LIFT-red's step 2): every good of `X` is unwanted at `B` (worth at most its base to every
  listed agent not holding it);
- `hOther` (Lemma LIFT-red's conclusion): no base other than `h`'s and `z`'s threatens anybody at base values;
and the lemma's own hypotheses:
- `hL1` (L1): nobody else values `t` above its base (`z` is unfrozen);
- `hL2` (L2′): `v_z(B_h) ≤ v_z(t) + v_z(g)`, and `v_z(B_h) ≤ v_z(t)` if `z` values no junk good;
- `hL3` (L3): every agent other than `h` and `z` values at most one good of `X`;
- `hR`: `|R_z| ≤ 4`.

As the referee notes, "t is z's favourite good" is not needed: by `hW` every good of `X` is worth at most `v_z(t)`
to `z`.

**Proof.** It is Lemma M's (⇐) (`EFX.OC1Max.sStar_of_slotMatching`) with owner `h`, `H = {g}` (or `H = ∅`) and the
matching `g ↦ z`: (G1) and (H1) come from `hOther` and `hL3` (`not_threat_of_relevant_le_one`), (G2) from `hW`, and
the edge at `z` from the count `value_ownerSet_le` (step 4 of the note: `|R_z ∖ {t}| ≤ 3`).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section lift1
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem value_le_mul {i : A} {c : Nat} : ∀ {L : List G}, (∀ y ∈ L, v i y ≤ c) → value v i L ≤ L.length * c
  | [], _ => by simp
  | a :: L, h => by
    rw [value_cons, List.length_cons, Nat.succ_mul]
    have := h a List.mem_cons_self
    have := value_le_mul (L := L) fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

omit [DecidableEq A] in
/-- A list in which `i` values at most one good, each good worth at most `c` to `i`, does not threaten `i` at `c`. -/
theorem not_threat_of_relevant_le_one {i : A} {L : List G} {c : Nat} (h1 : (relevant v i L).length ≤ 1)
    (hc : ∀ y ∈ L, v i y ≤ c) : ¬ Threat v i L c := by
  refine not_threat_iff.mpr fun x _ => Nat.le_trans (value_sublist v i (List.erase_sublist)) ?_
  refine value_le_of_countP_le_one v i c hc ?_
  rw [List.countP_eq_length_filter]; exact h1

omit [DecidableEq A] in
/-- A list worth at most `c` to `i` does not threaten `i` at `c`. -/
theorem not_threat_of_value_le {i : A} {L : List G} {c : Nat} (h : value v i L ≤ c) : ¬ Threat v i L c :=
  not_threat_iff.mpr fun _ _ => Nat.le_trans (value_sublist v i List.erase_sublist) h

omit [DecidableEq A] [DecidableEq G] in
theorem mem_relevant {i : A} {L : List G} {g : G} : g ∈ relevant v i L ↔ g ∈ L ∧ 0 < v i g := by
  simp [relevant]

omit [DecidableEq A] in
/-- **Step 4 of LIFT-1, the count for `z`.** With `|R_z| ≤ 4`, `z` holding `t` alone, every good of `X = B_h ∪ J`
worth at most `v_z(t)` to `z`, and `g` z's most valuable junk good, the owner's set `X ∖ {g}` is worth at most
`v_z(t) + v_z(g)` to `z`, given (L2′). -/
theorem value_ownerSet_le {B : A → List G} {h z : A} {t g : G} (hst : ValidState agents goods B) (hgd : goods.Nodup)
    (hh : h ∈ agents) (hz : z ∈ agents) (hhz : h ≠ z) (hBz : B z = [t])
    (hWz : ∀ x ∈ B h ++ junkOf agents goods B, v z x ≤ v z t) (hg : fav v z (junkOf agents goods B) = some g)
    (hL2 : value v z (B h) ≤ v z t + v z g) (hR : (relevant v z goods).length ≤ 4) :
    value v z (ownerSet agents goods B h [g]) ≤ v z t + v z g := by
  obtain ⟨hgJ, hgpos, hgmax⟩ := fav_some hg
  have hJnd : (junkOf agents goods B).Nodup := hgd.sublist List.filter_sublist
  have hBhnd := (hst.1 h hh).1
  have htmem : t ∈ B z := by rw [hBz]; exact List.mem_singleton_self t
  have htgoods : t ∈ goods := (hst.1 z hz).2 t htmem
  have hgt : v z g ≤ v z t := hWz g (List.mem_append_right _ hgJ)
  -- the three lists of `z`'s relevant goods
  let Al := relevant v z (B h)
  let Cl := relevant v z (junkOf agents goods B)
  let C' := relevant v z ((junkOf agents goods B).filter (fun x => decide (x ∉ [g])))
  have hval : value v z (ownerSet agents goods B h [g]) = value v z Al + value v z C' := by
    simp only [ownerSet, value_append_eq, Al, C', value_relevant]
  have hAle : ∀ y ∈ Al, v z y ≤ v z t := fun y hy =>
    hWz y (List.mem_append_left _ (mem_relevant.mp hy).1)
  have hC'le : ∀ y ∈ C', v z y ≤ v z g := fun y hy => by
    obtain ⟨hy1, hy2⟩ := mem_relevant.mp hy
    exact hgmax y (List.mem_filter.mp hy1).1 hy2
  -- `C'` lies in `Cl` minus `g`
  have hC'len : C'.length + 1 ≤ Cl.length := by
    have hsub : ∀ y ∈ C', y ∈ Cl.erase g := fun y hy => by
      obtain ⟨hy1, hy2⟩ := mem_relevant.mp hy
      obtain ⟨hyJ, hyg⟩ := List.mem_filter.mp hy1
      have hne : y ≠ g := by simpa using hyg
      exact (List.mem_erase_of_ne hne).mpr (mem_relevant.mpr ⟨hyJ, hy2⟩)
    have h1 : C'.length ≤ (Cl.erase g).length :=
      ((hJnd.sublist List.filter_sublist).sublist List.filter_sublist).length_le_of_subset hsub
    rw [List.length_erase_of_mem (mem_relevant.mpr ⟨hgJ, hgpos⟩)] at h1
    have := List.length_pos_of_mem (mem_relevant.mpr ⟨hgJ, hgpos⟩ : g ∈ Cl)
    show C'.length + 1 ≤ (relevant v z (junkOf agents goods B)).length
    omega
  by_cases ht0 : v z t = 0
  · -- `z` values nothing of `X`
    have hA0 : value v z Al = 0 := value_eq_zero_of_forall fun y hy => by have := hAle y hy; omega
    have hC0 : value v z C' = 0 := value_eq_zero_of_forall fun y hy => by have := hC'le y hy; omega
    rw [hval, hA0, hC0]; exact Nat.zero_le _
  -- `t` is a relevant good of `z` outside `B_h` and `(junkOf agents goods B)`: `|Al| + |Cl| ≤ 3`
  have hcount : Al.length + Cl.length + 1 ≤ 4 := by
    have hnd : (Al ++ Cl ++ [t]).Nodup := by
      refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hBhnd.sublist List.filter_sublist,
        hJnd.sublist List.filter_sublist, fun a ha b hb e => ?_⟩, by simp, fun a ha b hb e => ?_⟩
      · exact (mem_junkOf.mp (mem_relevant.mp hb).1).2 h hh (e ▸ (mem_relevant.mp ha).1)
      · rw [List.mem_singleton] at hb; subst hb
        rcases List.mem_append.mp ha with ha | ha
        · exact hst.2 h hh z hz hhz a (mem_relevant.mp ha).1 (e ▸ htmem)
        · exact (mem_junkOf.mp (mem_relevant.mp ha).1).2 z hz (e ▸ htmem)
    have := hnd.length_le_of_subset (l₂ := relevant v z goods) fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · exact mem_relevant.mpr ⟨(hst.1 h hh).2 y (mem_relevant.mp hy).1, (mem_relevant.mp hy).2⟩
        · exact mem_relevant.mpr ⟨(mem_junkOf.mp (mem_relevant.mp hy).1).1, (mem_relevant.mp hy).2⟩
      · rw [List.mem_singleton] at hy; subst hy; exact mem_relevant.mpr ⟨htgoods, Nat.pos_of_ne_zero ht0⟩
    simp only [List.length_append, List.length_singleton] at this
    omega
  rw [hval]
  by_cases ha2 : 2 ≤ Al.length
  · -- `z` values two goods of `B_h`: no relevant junk good other than `g`
    have hC'0 : C' = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hC'0, value_nil, Nat.add_zero, value_relevant]
    exact hL2
  · have hA := value_le_mul hAle
    have hC := value_le_mul hC'le
    have hAl : Al.length ≤ 1 := by omega
    have hA' : value v z Al ≤ v z t := Nat.le_trans hA (by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hAl with h0 | h1
      · rw [h0]; simp
      · rw [h1]; simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hAl with h0 | h1
    · have hc2 : C'.length ≤ 2 := by omega
      have := Nat.mul_le_mul_right (v z g) hc2
      have hA0 : value v z Al = 0 := by
        have := value_le_mul (L := Al) (c := v z t) hAle; rw [h0, Nat.zero_mul] at this; omega
      omega
    · have hc1 : C'.length ≤ 1 := by omega
      have := Nat.mul_le_mul_right (v z g) hc1
      omega

/-- **Lemma LIFT-1** (K4.MATCH.LIFT1, `k4/matching.md` §6). Under the facts of the note's step 1 and of Lemma
LIFT-red (`hW`, `hOther`) and (L1), (L2′), (L3), `|R_z| ≤ 4`: the state `B` has an S\* completion with owner `h`,
namely `h` takes `X ∖ {g}` and `z` takes `{t, g}` (`g` z's most valuable junk good, if any). -/
theorem lift1 {B : A → List G} {h z : A} {t : G} (hgd : goods.Nodup) (hst : ValidState agents goods B)
    (hh : h ∈ agents) (hz : z ∈ agents) (hhz : h ≠ z) (hBz : B z = [t])
    (hW : ∀ i ∈ agents, ∀ x ∈ B h ++ junkOf agents goods B, x ∉ B i → v i x ≤ value v i (B i))
    (hOther : ∀ j ∈ agents, j ≠ h → j ≠ z → ∀ i ∈ agents, i ≠ j → ¬ Threat v i (B j) (value v i (B i)))
    (hL1 : ∀ i ∈ agents, i ≠ z → v i t ≤ value v i (B i))
    (hL2 : ∀ g, fav v z (junkOf agents goods B) = some g → value v z (B h) ≤ v z t + v z g)
    (hL2' : fav v z (junkOf agents goods B) = none → value v z (B h) ≤ v z t)
    (hL3 : ∀ i ∈ agents, i ≠ h → i ≠ z → (relevant v i (B h ++ junkOf agents goods B)).length ≤ 1)
    (hR : (relevant v z goods).length ≤ 4) : SStar v agents goods B h := by
  have htmem : t ∈ B z := by rw [hBz]; exact List.mem_singleton_self t
  have hvalz : value v z (B z) = v z t := by rw [hBz]; simp
  -- `z` is a holder
  have hzhold : Holder v agents B z := by
    refine ⟨fun ⟨x, hx, i, hi, hiz, hlt⟩ => ?_, by rw [hBz]; simp⟩
    rw [hBz, List.mem_singleton] at hx; subst hx
    have := hL1 i hi hiz; omega
  -- goods of `X` are outside the bases of agents other than `h`
  have hXout : ∀ i ∈ agents, i ≠ h → ∀ x ∈ B h ++ (junkOf agents goods B), x ∉ B i := fun i hi hih x hx hxi => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hst.2 h hh i hi (Ne.symm hih) x hx hxi
    · exact (mem_junkOf.mp hx).2 i hi hxi
  have hWz : ∀ x ∈ B h ++ (junkOf agents goods B), v z x ≤ v z t := fun x hx => by
    have := hW z hz x hx (hXout z hz (Ne.symm hhz) x hx); rwa [hvalz] at this
  -- an owner's set inside `X`
  have hsubX : ∀ H : List G, ∀ x ∈ ownerSet agents goods B h H, x ∈ B h ++ (junkOf agents goods B) := fun H x hx => by
    rcases mem_ownerSet.mp hx with hx | ⟨hx, -⟩
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ hx
  -- agents other than `h` and `z` are threatened by no owner's set inside `X`
  have hsafe : ∀ H : List G, ∀ i ∈ agents, i ≠ h → i ≠ z →
      ¬ Threat v i (ownerSet agents goods B h H) (value v i (B i)) := fun H i hi hih hiz => by
    refine not_threat_of_relevant_le_one ?_ fun y hy => hW i hi y (hsubX H y hy) (hXout i hi hih y (hsubX H y hy))
    have hsub : ∀ y ∈ relevant v i (ownerSet agents goods B h H), y ∈ relevant v i (B h ++ (junkOf agents goods B)) := fun y hy =>
      mem_relevant.mpr ⟨hsubX H y (mem_relevant.mp hy).1, (mem_relevant.mp hy).2⟩
    exact Nat.le_trans (((nodup_ownerSet hh hst hgd H).sublist List.filter_sublist).length_le_of_subset hsub)
      (hL3 i hi hih hiz)
  have hG1 : G1 v agents B h := fun j hj hjh hjhold i hi hij =>
    hOther j hj hjh (fun e => hjhold (e ▸ hzhold)) i hi hij
  have hG2 : G2 v agents goods B := fun g hg i hi =>
    hW i hi g (List.mem_append_right _ hg) ((mem_junkOf.mp hg).2 i hi)
  have hH1 : ∀ H : List G, H1 v agents goods B h H := fun H q hq hqh hqhold =>
    hsafe H q hq hqh fun e => hqhold (e ▸ hzhold)
  cases hf : fav v z (junkOf agents goods B) with
  | none =>
    -- `z` values no junk good: `H = ∅`, and `z` is not exposed
    have hJz : ∀ x ∈ (junkOf agents goods B), v z x = 0 := fun x hx => Nat.eq_zero_of_not_pos (fav_none hf x hx)
    refine sStar_of_slotMatching hgd hst hh hG1 hG2 (H := []) (fun _ hx => by cases hx) (hH1 [])
      (m := fun _ => z) ⟨fun _ hx => (by cases hx), fun _ hx => (by cases hx), fun u hu huh huhold hexp => ?_⟩
    by_cases huz : u = z
    · subst huz
      refine absurd hexp (not_threat_of_value_le ?_)
      have : value v u (ownerSet agents goods B h []) = value v u (B h) := by
        simp only [ownerSet, value_append_eq]
        rw [value_eq_zero_of_forall fun x hx => hJz x (List.mem_filter.mp hx).1, Nat.add_zero]
      rw [this, hvalz]; exact hL2' hf
    · exact absurd hexp (hsafe [] u hu huh huz)
  | some g =>
    -- `H = {g}`, matched to `z`
    obtain ⟨hgJ, hgpos, -⟩ := fav_some hf
    refine sStar_of_slotMatching hgd hst hh hG1 hG2 (H := [g]) (fun x hx => by
      rw [List.mem_singleton] at hx; subst hx; exact hgJ) (hH1 [g]) (m := fun _ => z)
      ⟨fun x hx => ⟨hz, Ne.symm hhz, hzhold, ?_⟩, fun x hx y hy _ => by
        rw [List.mem_singleton] at hx hy; rw [hx, hy], fun u hu huh huhold hexp => ?_⟩
    · rw [List.mem_singleton] at hx; subst hx
      refine Or.inr ⟨hgpos, not_threat_of_value_le ?_⟩
      rw [hvalz]
      exact value_ownerSet_le hst hgd hh hz hhz hBz hWz hf (hL2 x hf) hR
    · by_cases huz : u = z
      · exact ⟨g, List.mem_singleton_self g, huz.symm⟩
      · exact absurd hexp (hsafe [g] u hu huh huz)

end lift1

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.not_threat_of_relevant_le_one
#print axioms EFX.OC1Max.value_ownerSet_le
#print axioms EFX.OC1Max.lift1
