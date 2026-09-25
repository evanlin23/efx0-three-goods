import EFX.LB4RRun

/-!
# Exposure, Lemma E, Theorem A₄, Theorem B₄ and Corollary C₄⁰ (`k4/c4.md` §2–§4; ledger K4.C4.AB.L)

The reviewed building blocks of `k4/c4.md` (on proof/k4-c4, PR #33), stated for LB₄ʳ's states after a run of Phase 1
and envy-free upgrades to the fixpoint (`EFX.LB4R.AfterUp`, with `r` the last-processed unmarked agent,
`EFX.LB4R.IsLast`). `k4/c4.md` states them for every run of Phase 1; `AfterUp` takes any run
(`EFX.LB4R.PhaseRun`: any P-step order, any insertion steps), so LB₄ʳ's fixed key is a special case
(`EFX.LB4R.phase1_phaseRun`). The upgrades are LB₄ʳ's (`EFX.LB4R.UpRun` with the envy-free policy: smallest-index
eligible agent, best good); `k4/c4.md` allows any order to the fixpoint and uses only (UT₂) and envy-free bases.

- **Exposure** (§2): `Wl goods s r` is **W = B_r ∪ J**; `Threatened v x L H` (`x` holding `H` strongly envies `L`) and
  `Threatened.mono`; `Exposed v agents goods s r x`; `AfterUp.W_not_NA` (W avoids NA: J by (V1), `Y_r` by (A1)).
- **Lemma E** (§2): `lemmaE` (an exposed agent has a pick; its goods in W are worth less and at least two),
  `lemmaE_three` (3-good: holds its top, the other two in W, leads its block), `lemmaE_four` (4-good: top or second;
  if second, `L_x` its two lowest, `W ⊄ R_x`, `v(L_x) > v(Y_x)`).
- **Lemma R** (§4a) for a rotation along a need chain to `r` (LB₄ʳ's `rotate`): `rotate_Wl` (W′ = W),
  `needsOf_rotate` and `rotate_valid` (NA′ ⊆ NA, validity, when the new base is worth more than the head's pick),
  `rotate_exposed`, `rotate_exposed_chain`, `rotate_last_not_exposed` (exposure after the rotation).
- **Theorem B₄** (§4): `theoremB4` ((a), (b); the rotation is a `RotStep` of LB₄ʳ and no chain agent is exposed),
  `theoremB4c` ((c): the owner step has an output on the rotated state unless `r` is exposed).
- **Theorem A₄** (§3): `theoremA4` (with no exposed 4-good agent, `r` is a valid owner or LB⁺'s bad case `BadCase`
  holds), `theoremA4_output`; the completion `placeH` (`completion_placeH_gen`, `oc_placeH_gen`) and LB⁺'s count of
  terminals (`AfterUp.terminals_out`, `AfterUp.terminals`).
- **Corollary C₄⁰** (§4): `corollaryC40'` (as `k4/c4.md` at 96ff1d0 states it: `ω ≤ 0`, or the hypotheses of A₄
  and B₄), `corollaryC40` (LB₄ʳ(τ) succeeds under the hypotheses of A₄ and B₄) and
  `succeeds_of_three` (LB₄ʳ never fails on a strict profile of a core whose agents all have three goods).
Theorems B₄ʷ, A₄ᵀ and A₄⁺ (§4a–§4c) are not formalized.
-/

set_option autoImplicit false

namespace EFX
namespace LB4R

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Exposure -/

/-- **W = B_r ∪ J** (`k4/c4.md` §1): the goods in no base or in `r`'s base. -/
def Wl (goods : List G) (s : LState A G) (r : A) : List G :=
  goods.filter (fun g => s.base g = none ∨ s.base g = some r)

/-- *threatened(x, L, H)* (`k4/c4.md` §1): `x`, holding `H`, strongly envies `L`. -/
def Threatened (v : A → G → Nat) (x : A) (L H : List G) : Prop :=
  ∃ h ∈ L, value v x H < value v x (L.erase h)

/-- `x` is **exposed** w.r.t. `r` (`k4/c4.md` §2): unmarked, not `r`, and threatened by `W` with its base. -/
def Exposed (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (r x : A) : Prop :=
  x ∈ agents ∧ ¬ s.marked x ∧ x ≠ r ∧ Threatened v x (Wl goods s r) (baseOf goods s.base x)

section lemmas
variable {v : A → G → Nat}

omit [DecidableEq A] in
/-- **Monotonicity** (`k4/c4.md` §1): a smaller bundle and a better own bundle can only remove a threat. -/
theorem Threatened.mono {x : A} {L L' H H' : List G} (h : Threatened v x L' H') (hL : L'.Sublist L)
    (hH : value v x H ≤ value v x H') : Threatened v x L H := by
  obtain ⟨h, hh, hlt⟩ := h
  exact ⟨h, hL.subset hh, Nat.lt_of_le_of_lt hH (Nat.lt_of_lt_of_le hlt (value_sublist v x (hL.erase h)))⟩

omit [DecidableEq G] in
theorem mem_Wl {goods : List G} {s : LState A G} {r : A} {g : G} :
    g ∈ Wl goods s r ↔ g ∈ goods ∧ (s.base g = none ∨ s.base g = some r) := by
  simp [Wl]

omit [DecidableEq G] in
/-- A list without repetitions inside another one of at most its length contains it. -/
theorem subset_of_length_le {l₁ l₂ : List G} (h₁ : l₁.Nodup) (hsub : ∀ g ∈ l₁, g ∈ l₂)
    (hlen : l₂.length ≤ l₁.length) : ∀ g ∈ l₂, g ∈ l₁ := by
  intro g hg
  refine Classical.byContradiction fun hn => ?_
  have := List.Nodup.length_le_of_subset (l₁ := g :: l₁) (List.nodup_cons.mpr ⟨hn, h₁⟩)
    fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hg
      · exact hsub a ha
  simp at this; omega

omit [DecidableEq A] [DecidableEq G] in
/-- On a strict profile, two goods an agent values are worth different amounts to it. -/
theorem strict_ne {agents : List A} {goods : List G} (hs : Strict v agents goods) {x : A} (hx : x ∈ agents)
    {g y : G} (hg : g ∈ goods) (hy : y ∈ goods) (hgy : g ≠ y) (hpos : 0 < v x g) : v x g ≠ v x y := by
  intro e
  have := hs x hx [g] [y] (List.singleton_sublist.mpr hg) (List.singleton_sublist.mpr hy)
    (by simpa using hgy) (by simpa using e)
  simp at this; omega

omit [DecidableEq A] [DecidableEq G] in
/-- The value of a list of at most one good, each worth less than `c > 0`, is less than `c`. -/
theorem value_lt_of_length_le_one {x : A} {c : Nat} {L : List G} (hc : 0 < c) (hL : L.length ≤ 1)
    (hlt : ∀ g ∈ L, v x g < c) : value v x L < c := by
  match L, hL with
  | [], _ => simpa using hc
  | [g], _ => simpa using hlt g (by simp)

end lemmas

/-! ## Lemma E -/

section lemmaE
variable {v : A → G → Nat} {agents : List A} {goods : List G} {run : List (A × Option G)} {s : LState A G}

/-- No good of `W` is needed: junk by (V1), `Y_r` by (A1) (`k4/c4.md` §1). -/
theorem AfterUp.W_not_NA (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {r : A} (hr : IsLast run s r)
    {g : G} (hg : g ∈ Wl goods s r) : ¬ NA agents (needsOf v goods s) g := by
  have hI := hS.inv hgd
  obtain ⟨hgg, hb | hb⟩ := mem_Wl.mp hg
  · exact hI.valid.v1 g (mem_junk.mpr ⟨hgg, hb⟩)
  · obtain ⟨t, p, hp, hpr, hrm, -⟩ := id hr
    have hrag : r ∈ agents := hpr ▸ hS.phase.agent_mem hp
    have hB := hI.unmarked r hrag hrm
    have hgB : g ∈ baseOf goods s.base r := mem_baseOf.mpr ⟨hgg, hb⟩
    rw [hB] at hgB
    cases hy : s.pick r with
    | none => rw [hy] at hgB; simp at hgB
    | some y =>
      rw [hy] at hgB; simp at hgB; subst hgB
      exact hS.last_pick_free hgd hr hy

/-- The base of an unmarked listed agent is its pick. -/
theorem AfterUp.base_pick (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {x : A} (hx : x ∈ agents)
    (hxm : ¬ s.marked x) : baseOf goods s.base x = (s.pick x).toList :=
  (hS.inv hgd).unmarked x hx hxm

/-- **Lemma E** (`k4/c4.md` §2), first part: an exposed agent `x` has a pick `Y_x`; every good of
`L_x = R_x ∩ W` is worth less to `x` than `Y_x`; and `|L_x| ≥ 2`. -/
theorem lemmaE (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods) {r x : A}
    (hr : IsLast run s r) (hx : Exposed v agents goods s r x) :
    ∃ y, s.pick x = some y ∧ y ∈ goods ∧ 0 < v x y ∧ (∀ g ∈ relevant v x (Wl goods s r), v x g < v x y) ∧
      2 ≤ (relevant v x (Wl goods s r)).length := by
  obtain ⟨hxa, hxm, hxr, h, hh, hthr⟩ := hx
  have hI := hS.inv hgd
  have hB := hS.base_pick hgd hxa hxm
  -- a good of `W` that `x` values is not needed, so it is worth at most `x`'s pick
  have hnot : ∀ g ∈ Wl goods s r, 0 < v x g → ∃ y, s.pick x = some y ∧ v x g ≤ v x y := by
    intro g hg hpos
    have hN : ¬ needsOf v goods s x g := fun hN => hS.W_not_NA hgd hr hg ⟨x, hxa, hN⟩
    rw [needsOf_unmarked hxm] at hN
    cases hy : s.pick x with
    | none => exact absurd ⟨(mem_Wl.mp hg).1, hpos, fun y hy' => by rw [hy] at hy'; cases hy'⟩ hN
    | some y =>
      refine ⟨y, rfl, Nat.le_of_not_lt fun hlt => hN ⟨(mem_Wl.mp hg).1, hpos, fun y' hy' => ?_⟩⟩
      rw [hy] at hy'; cases hy'; exact hlt
  -- `x` has a pick
  obtain ⟨y, hy⟩ : ∃ y, s.pick x = some y := by
    cases hy : s.pick x with
    | some y => exact ⟨y, rfl⟩
    | none =>
      exfalso
      have h0 : value v x ((Wl goods s r).erase h) = 0 := value_eq_zero_of_forall v x fun g hg => by
        refine Nat.eq_zero_of_not_pos fun hpos => ?_
        obtain ⟨y, hy', -⟩ := hnot g (List.mem_of_mem_erase hg) hpos
        rw [hy] at hy'; cases hy'
      omega
  have hyB : baseOf goods s.base x = [y] := by rw [hB, hy]; rfl
  have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hyB]; simp : y ∈ baseOf goods s.base x)).1
  have hyb : s.base y = some x := (mem_baseOf.mp (by rw [hyB]; simp : y ∈ baseOf goods s.base x)).2
  have hypos : 0 < v x y := hI.pickRel x hxa hxm y hy
  have hbelow : ∀ g ∈ relevant v x (Wl goods s r), v x g < v x y := by
    intro g hg
    obtain ⟨hgW, hpos⟩ := List.mem_filter.mp hg
    have hpos : 0 < v x g := by simpa using hpos
    obtain ⟨y', hy', hle⟩ := hnot g hgW hpos
    rw [hy] at hy'; cases hy'
    have hgy : g ≠ y := fun e => by
      obtain ⟨-, hb | hb⟩ := mem_Wl.mp hgW
      · rw [e, hyb] at hb; cases hb
      · rw [e, hyb] at hb; exact hxr (Option.some.inj hb)
    have := strict_ne hs hxa (mem_Wl.mp hgW).1 hyg hgy hpos
    omega
  refine ⟨y, hy, hyg, hypos, hbelow, Nat.le_of_not_lt fun hlt => ?_⟩
  -- with at most one good of `W` that `x` values, `W` is worth at most `v_x(Y_x)`
  have hle : value v x (Wl goods s r) ≤ v x y := by
    rw [← value_relevant]
    exact Nat.le_of_lt (value_lt_of_length_le_one hypos (by omega) hbelow)
  have := value_sublist v x (List.erase_sublist (l := Wl goods s r) (a := h))
  rw [hyB] at hthr
  simp at hthr
  omega

/-- The good `Y_r` and the junk were still there at the turn of every unmarked agent other than `r`: a good of `W`
was not picked before the step of such an agent. -/
theorem AfterUp.W_not_pickedBefore (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {r : A}
    (hr : IsLast run s r) {t : Nat} {p : A × Option G} (hp : run[t]? = some p) (hpm : ¬ s.marked p.1)
    (hpr : p.1 ≠ r) {g : G} (hg : g ∈ Wl goods s r) : ¬ PickedBefore run t g := by
  rintro ⟨t', ht', hpk⟩
  obtain ⟨hgg, hb | hb⟩ := mem_Wl.mp hg
  · exact hS.junk hb t' hpk
  · -- `g = Y_r`, picked at `r`'s step, which comes after `p`'s
    obtain ⟨tr, pr, hpr', hprr, hrm, -⟩ := id hr
    have hI := hS.inv hgd
    have hrag : r ∈ agents := hprr ▸ hS.phase.agent_mem hpr'
    have hgB : g ∈ baseOf goods s.base r := mem_baseOf.mpr ⟨hgg, hb⟩
    rw [hI.unmarked r hrag hrm] at hgB
    cases hyr : s.pick r with
    | none => rw [hyr] at hgB; simp at hgB
    | some yr =>
      rw [hyr] at hgB; simp at hgB; subst hgB
      have hpy : pr.2 = some g := by rw [← hS.pick hpr', hprr, hyr]
      unfold pickAt at hpk
      cases hq : run[t']? with
      | none => rw [hq] at hpk; cases hpk
      | some q =>
        rw [hq] at hpk
        have e := hS.phase.pick_unique hq hpr' hpk hpy
        subst e
        have htr := (hS.last_block hr hpr' hprr).1 t p hp hpm
        have hne : t ≠ t' := fun e => hpr (by
          have := hS.phase.pos_unique hp hpr' (by rw [e] at hp; rw [hp] at hpr'; cases hpr'; rfl)
          subst this; rw [hp] at hpr'; cases hpr'; exact hprr)
        omega

/-- **Lemma E(i)** (`k4/c4.md` §2): an exposed agent with three relevant goods holds its top, `L_x` is the other two
goods (so `R_x ∖ {Y_x} ⊆ W`), and `x` leads its block (it was processed at an insertion step). -/
theorem lemmaE_three (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods)
    {r x : A} (hr : IsLast run s r) (hx : Exposed v agents goods s r x) (h3 : (relevant v x goods).length = 3) :
    ∃ y, s.pick x = some y ∧ (∀ g ∈ goods, 0 < v x g → g ≠ y → g ∈ Wl goods s r ∧ v x g < v x y) ∧
      (relevant v x (Wl goods s r)).length = 2 ∧
      ∀ (t : Nat) (p : A × Option G), run[t]? = some p → p.1 = x → InsAt v run t := by
  obtain ⟨y, hy, hyg, hypos, hbelow, h2⟩ := lemmaE hS hgd hs hr hx
  obtain ⟨hxa, hxm, hxr, -⟩ := hx
  have hWg : ∀ g ∈ Wl goods s r, g ∈ goods := fun g hg => (mem_Wl.mp hg).1
  have hL : ∀ g ∈ relevant v x (Wl goods s r), g ∈ goods ∧ 0 < v x g ∧ g ≠ y := fun g hg => by
    obtain ⟨hgW, hpos⟩ := List.mem_filter.mp hg
    exact ⟨hWg g hgW, by simpa using hpos, fun e => by have := hbelow g hg; rw [e] at this; omega⟩
  -- `y :: L_x` lies in `R_x`, which has three goods, so it is all of `R_x`
  have hnd : (y :: relevant v x (Wl goods s r)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => (hL y hm).2.2 rfl, ((hgd.filter _).filter _)⟩
  have hsub : ∀ g ∈ y :: relevant v x (Wl goods s r), g ∈ relevant v x goods := fun g hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact List.mem_filter.mpr ⟨hyg, by simpa using hypos⟩
    · exact List.mem_filter.mpr ⟨(hL g hg).1, by simpa using (hL g hg).2.1⟩
  have hlen := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_cons] at hlen
  have hall := subset_of_length_le hnd hsub (by simp; omega)
  have hother : ∀ g ∈ goods, 0 < v x g → g ≠ y → g ∈ Wl goods s r ∧ v x g < v x y := by
    intro g hg hpos hgy
    have := hall g (List.mem_filter.mpr ⟨hg, by simpa using hpos⟩)
    rcases List.mem_cons.mp this with e | hm
    · exact absurd e hgy
    · exact ⟨(List.mem_filter.mp hm).1, hbelow g hm⟩
  refine ⟨y, hy, hother, by omega, fun t p hp hpx => hS.phase.insAt_of_not_lost hp ?_⟩
  -- at `x`'s turn, none of its goods had been picked
  rintro ⟨g, hpos, hpb⟩
  have hgg : g ∈ goods := by
    obtain ⟨t', -, hpk⟩ := hpb
    unfold pickAt at hpk
    cases hq : run[t']? with
    | none => rw [hq] at hpk; cases hpk
    | some q => rw [hq] at hpk; exact (hS.phase.pick t' q g hq hpk).1
  by_cases hgy : g = y
  · subst hgy
    have hpy : p.2 = some g := by rw [← hS.pick hp, hpx, hy]
    exact (hS.phase.pick t p g hp hpy).2.2 hpb
  · exact hS.W_not_pickedBefore hgd hr hp (hpx ▸ hxm) (hpx ▸ hxr) (hother g hgg (hpx ▸ hpos) hgy).1 hpb

/-- **Lemma E(ii)** (`k4/c4.md` §2): an exposed agent with four relevant goods holds its top or its second good (at
most one good above its pick); if its second, then `L_x` is its two lowest goods, `W ⊄ R_x`, and
`v_x(L_x) > v_x(Y_x)`. -/
theorem lemmaE_four (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods)
    {r x : A} (hr : IsLast run s r) (hx : Exposed v agents goods s r x) (h4 : (relevant v x goods).length = 4) :
    ∃ y, s.pick x = some y ∧ ((relevant v x goods).filter (fun g => v x y < v x g)).length ≤ 1 ∧
      (((relevant v x goods).filter (fun g => v x y < v x g)).length = 1 →
        (relevant v x (Wl goods s r)).length = 2 ∧ (∃ g ∈ Wl goods s r, v x g = 0) ∧
        v x y < value v x (relevant v x (Wl goods s r))) := by
  obtain ⟨y, hy, hyg, hypos, hbelow, h2⟩ := lemmaE hS hgd hs hr hx
  obtain ⟨hxa, hxm, hxr, h, hh, hthr⟩ := hx
  have hB := hS.base_pick hgd hxa hxm
  rw [hB, hy] at hthr
  simp only [Option.toList_some, value_cons, value_nil, Nat.add_zero] at hthr
  have hWg : ∀ g ∈ Wl goods s r, g ∈ goods := fun g hg => (mem_Wl.mp hg).1
  have hL : ∀ g ∈ relevant v x (Wl goods s r), g ∈ goods ∧ 0 < v x g ∧ g ≠ y := fun g hg => by
    obtain ⟨hgW, hpos⟩ := List.mem_filter.mp hg
    exact ⟨hWg g hgW, by simpa using hpos, fun e => by have := hbelow g hg; rw [e] at this; omega⟩
  have hnd : (y :: relevant v x (Wl goods s r)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => (hL y hm).2.2 rfl, ((hgd.filter _).filter _)⟩
  -- `y` and `L_x` are not above `y`
  have hsub : ∀ g ∈ y :: relevant v x (Wl goods s r),
      g ∈ (relevant v x goods).filter (fun g => !decide (v x y < v x g)) := fun g hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hyg, by simpa using hypos⟩, by simp⟩
    · exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨(hL g hg).1, by simpa using (hL g hg).2.1⟩,
        by simpa using Nat.le_of_lt (hbelow g hg)⟩
  have hlen := List.Nodup.length_le_of_subset hnd hsub
  have hsplit := LB.length_filter_add (relevant v x goods) (fun g => decide (v x y < v x g))
  simp only [List.length_cons] at hlen
  refine ⟨y, hy, by omega, fun h1 => ?_⟩
  have hL2 : (relevant v x (Wl goods s r)).length = 2 := by omega
  refine ⟨hL2, ?_, ?_⟩
  · -- if every good of `W` were valued, `W = L_x` and removing one of its two goods leaves less than `Y_x`
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ g ∈ Wl goods s r, 0 < v x g := fun g hg =>
      Nat.pos_of_ne_zero fun h0 => hno ⟨g, hg, h0⟩
    have hWL : relevant v x (Wl goods s r) = Wl goods s r :=
      List.filter_eq_self.mpr fun g hg => by simpa using hall g hg
    rw [← hWL] at hh hthr
    have hlen1 : ((relevant v x (Wl goods s r)).erase h).length ≤ 1 := by
      rw [List.length_erase_of_mem hh]; omega
    have := value_lt_of_length_le_one (v := v) (x := x) hypos hlen1
      fun g hg => hbelow g (List.mem_of_mem_erase hg)
    omega
  · have := value_sublist v x (List.erase_sublist (l := Wl goods s r) (a := h))
    rw [value_relevant]
    omega

end lemmaE

/-! ## Rotations to r: Lemma R and Theorem B₄ (a), (b) -/

section chainLists

/-- The last agent of a chain is at its last index. -/
theorem idxOf_last {c : List A} (hc : c.Nodup) {r : A} (hl : c.getLast? = some r) :
    c.idxOf r = c.length - 1 := by
  rw [List.getLast?_eq_getElem?] at hl
  exact idxOf_of_getElem? hc hl

/-- The last agent of a chain has no successor. -/
theorem getElem?_after_last {c : List A} (hc : c.Nodup) {r : A} (hl : c.getLast? = some r) :
    c[c.idxOf r + 1]? = none := by
  rw [idxOf_last hc hl]
  exact List.getElem?_eq_none (by omega)

/-- Every agent of a chain other than the last has a successor. -/
theorem exists_next {c : List A} {r a : A} (hl : c.getLast? = some r) (ha : a ∈ c) (har : a ≠ r) :
    ∃ b, c[c.idxOf a + 1]? = some b := by
  have h1 := List.idxOf_lt_length_of_mem ha
  have h2 : c.idxOf a ≠ c.length - 1 := fun e => har (by
    have := getElem?_idxOf ha; rw [e, ← List.getLast?_eq_getElem?, hl] at this; exact (Option.some.inj this).symm)
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- A successor is not the head. -/
theorem next_ne_head {c : List A} (hc : c.Nodup) {k b : A} {j : Nat} (hk : c.head? = some k)
    (hb : c[j + 1]? = some b) : b ≠ k := by
  intro e; subst e
  rw [List.head?_eq_getElem?] at hk
  have h1 := idxOf_of_getElem? hc hk
  have h2 := idxOf_of_getElem? hc hb
  omega

/-- An agent with a successor is not the last. -/
theorem ne_last_of_next {c : List A} (hc : c.Nodup) {r a b : A} {j : Nat} (hl : c.getLast? = some r)
    (ha : c[j]? = some a) (hb : c[j + 1]? = some b) : a ≠ r := by
  intro e; subst e
  have h1 := idxOf_of_getElem? hc ha
  have h2 := idxOf_last hc hl
  have := (List.getElem?_eq_some_iff.mp hb).1
  omega

/-- Every agent of a chain other than the head has a predecessor. -/
theorem exists_prev {c : List A} {k x : A} (hk : c.head? = some k) (hx : x ∈ c) (hxk : x ≠ k) :
    ∃ (j : Nat) (a : A), c[j]? = some a ∧ c[j + 1]? = some x := by
  have h1 := List.idxOf_lt_length_of_mem hx
  have h0 : c.idxOf x ≠ 0 := fun h0 => hxk (by
    have := getElem?_idxOf hx; rw [h0, ← List.head?_eq_getElem?, hk] at this; exact (Option.some.inj this).symm)
  refine ⟨c.idxOf x - 1, c[c.idxOf x - 1]'(by omega), List.getElem?_eq_getElem (by omega), ?_⟩
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
  exact getElem?_idxOf hx

end chainLists

section rotation
variable {v : A → G → Nat} {agents : List A} {goods : List G} {run : List (A × Option G)} {s : LState A G}
  {c : List A} {k r : A} {O : List G}

/-- In the rotation, a good goes to the head `k` exactly when it is in `O`. -/
theorem rotate_base_head (hc : c.Nodup) (hk : c.head? = some k) {g : G} :
    (rotate s c O).base g = some k ↔ g ∈ O := by
  by_cases hgO : g ∈ O
  · simp [rotate, hgO, hk]
  · simp only [rotate, hgO, ↓reduceIte, iff_false]
    cases hb : s.base g with
    | none => simp
    | some a =>
      by_cases hac : a ∈ c
      · simp only [hac, ↓reduceIte]
        intro h; exact next_ne_head hc hk h rfl
      · simp only [hac, ↓reduceIte, Option.some.injEq]
        intro e; subst e; exact hac (List.mem_of_mem_head? hk)

/-- In the rotation, a good ends in no base exactly when it is not in `O` and was junk or `r`'s. -/
theorem rotate_base_none (hc : c.Nodup) (hk : c.head? = some k) (hl : c.getLast? = some r) {g : G} :
    (rotate s c O).base g = none ↔ g ∉ O ∧ (s.base g = none ∨ s.base g = some r) := by
  by_cases hgO : g ∈ O
  · simp only [rotate, hgO, ↓reduceIte, hk, reduceCtorEq, not_true_eq_false, false_and]
  · simp only [rotate, hgO, ↓reduceIte, not_false_eq_true, true_and]
    cases hb : s.base g with
    | none => simp
    | some a =>
      simp only [reduceCtorEq, false_or, Option.some.injEq]
      by_cases hac : a ∈ c
      · simp only [hac, ↓reduceIte]
        constructor
        · intro h
          refine Classical.byContradiction fun har => ?_
          obtain ⟨b, hb'⟩ := exists_next hl hac har
          rw [hb'] at h; cases h
        · intro e; subst e; exact getElem?_after_last hc hl
      · simp only [hac, ↓reduceIte, reduceCtorEq, false_iff]
        intro e; subst e; exact hac (List.mem_of_getLast? hl)

/-- Outside the chain, the rotation changes no base (given `O ⊆ W`). -/
theorem rotate_base_out (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) {j : A} (hj : j ∉ c) {g : G} :
    (rotate s c O).base g = some j ↔ s.base g = some j := by
  have hrc : r ∈ c := List.mem_of_getLast? hl
  by_cases hgO : g ∈ O
  · simp only [rotate, hgO, ↓reduceIte]
    constructor
    · intro h; exact absurd (List.mem_of_mem_head? h) hj
    · intro h; rcases hO g hgO with h' | h' <;> rw [h] at h' <;> simp at h'; subst h'; exact absurd hrc hj
  · simp only [rotate, hgO, ↓reduceIte]
    cases hb : s.base g with
    | none => simp
    | some a =>
      by_cases hac : a ∈ c
      · simp only [hac, ↓reduceIte]
        constructor
        · intro h; exact absurd (List.mem_of_getElem? h) hj
        · intro h; cases h; exact absurd hac hj
      · simp [hac]

/-- In the rotation, the successor `j` of `a` in the chain takes `a`'s base goods (given `O ⊆ W`). -/
theorem rotate_base_next (hc : c.Nodup) (hk : c.head? = some k) (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) {i : Nat} {a j : A} (ha : c[i]? = some a)
    (hj : c[i + 1]? = some j) {g : G} : (rotate s c O).base g = some j ↔ s.base g = some a := by
  have hjk := next_ne_head hc hk hj
  have har := ne_last_of_next hc hl ha hj
  have hac : a ∈ c := List.mem_of_getElem? ha
  by_cases hgO : g ∈ O
  · simp only [rotate, hgO, ↓reduceIte, hk, Option.some.injEq]
    constructor
    · intro e; exact absurd e.symm hjk
    · intro h; rcases hO g hgO with h' | h' <;> rw [h] at h' <;> simp at h'; exact absurd h' har
  · simp only [rotate, hgO, ↓reduceIte]
    constructor
    · intro h
      cases hb : s.base g with
      | none => rw [hb] at h; cases h
      | some b =>
        rw [hb] at h
        by_cases hbc : b ∈ c
        · simp only [hbc, ↓reduceIte] at h
          have h1 := idxOf_of_getElem? hc h
          have h2 := idxOf_of_getElem? hc hj
          have h3 := idxOf_of_getElem? hc ha
          have : c.idxOf b = i := by omega
          rw [← this, getElem?_idxOf hbc] at ha
          rw [Option.some.inj ha]
        · simp only [hbc, ↓reduceIte, Option.some.injEq] at h
          subst h; exact absurd (List.mem_of_getElem? hj) hbc
    · intro h
      simp only [h, hac, ↓reduceIte, idxOf_of_getElem? hc ha]
      exact hj

/-- **Lemma R(a)**: the rotation keeps `W`: `W′ = O ∪ J′ = W` (as the goods in no base or in `k`'s base after the
rotation, given `O ⊆ W`). -/
theorem rotate_Wl (hc : c.Nodup) (hk : c.head? = some k) (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) :
    Wl goods (rotate s c O) k = Wl goods s r := by
  apply List.filter_congr
  intro g _
  simp only [decide_eq_decide]
  rw [rotate_base_none hc hk hl, rotate_base_head hc hk]
  by_cases hgO : g ∈ O
  · simp only [hgO, not_true_eq_false, false_and, or_true, true_iff]
    exact hO g hgO
  · simp [hgO]

/-- The rotation's picks: the head has none, every other agent of the chain takes its predecessor's pick, the agents
outside the chain keep theirs; the head is marked, the rest of the chain unmarked, the others as before. -/
theorem rotate_pick_next (hc : c.Nodup) {i : Nat} {a j : A} (ha : c[i]? = some a) (hj : c[i + 1]? = some j) :
    (rotate s c O).pick j = s.pick a := by
  have hjc : j ∈ c := List.mem_of_getElem? hj
  have h1 := idxOf_of_getElem? hc hj
  simp only [rotate, hjc, ↓reduceIte, h1, Nat.add_one_ne_zero, Nat.add_sub_cancel, ha, Option.bind_some]

theorem rotate_marked_next (hc : c.Nodup) (hk : c.head? = some k) {i : Nat} {j : A} (hj : c[i + 1]? = some j) :
    ¬ (rotate s c O).marked j := by
  rintro (h | ⟨-, h⟩)
  · rw [hk] at h; exact next_ne_head hc hk hj (Option.some.inj h).symm
  · exact h (List.mem_of_getElem? hj)

theorem rotate_out {j : A} (hj : j ∉ c) :
    (rotate s c O).pick j = s.pick j ∧ ((rotate s c O).marked j ↔ s.marked j) := by
  refine ⟨by simp [rotate, hj], ?_⟩
  simp only [rotate]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact absurd (List.mem_of_mem_head? h) hj
    · exact h
  · exact fun h => Or.inr ⟨h, hj⟩

/-- The needs of an agent outside the chain do not change. -/
theorem rotate_needs_out (hl : c.getLast? = some r) (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r)
    {j : A} (hj : j ∉ c) {g : G} : needsOf v goods (rotate s c O) j g ↔ needsOf v goods s j g := by
  obtain ⟨hp, hm⟩ := rotate_out (s := s) (O := O) hj
  have hB : baseOf goods (rotate s c O).base j = baseOf goods s.base j :=
    List.filter_congr fun h _ => by simp only [rotate_base_out hl hO hj]
  unfold needsOf
  simp only [hB, hp, hm, ne_eq, rotate_base_out hl hO hj]

omit [DecidableEq G] in
/-- The head of a chain of at least two agents is frozen and has a pick that the next agent needs. -/
theorem NeedChain.head (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hlen : 2 ≤ c.length) :
    FrozenAt v agents goods s k ∧ ∃ y b, s.pick k = some y ∧ c[1]? = some b ∧ needsOf v goods s b y := by
  have h0 : c[0]? = some k := by rw [← List.head?_eq_getElem?]; exact hk
  have h1 : c[1]? = some (c[1]'(by omega)) := List.getElem?_eq_getElem (by omega)
  obtain ⟨hF, y, hy, hN⟩ := hch.2.2.1 0 k _ h0 h1
  exact ⟨hF, y, _, hy, h1, hN⟩

/-- In the rotation, `k`'s base holds `O`. -/
theorem value_O_le (hk : c.head? = some k) (hc : c.Nodup) (hOg : ∀ g ∈ O, g ∈ goods) (hOnd : O.Nodup) :
    value v k O ≤ value v k (baseOf goods (rotate s c O).base k) :=
  value_le_of_subset k hOnd fun g hg => mem_baseOf.mpr ⟨hOg g hg, (rotate_base_head hc hk).mpr hg⟩

/-- **Lemma R(b)**, the needs: if `k` values `O` more than its pick, every need after the rotation was a need
before (`N′_k ⊆ N_k`, the chain agents' needs shrink, the others are unchanged), so `NA′ ⊆ NA`. -/
theorem needsOf_rotate (hS : AfterUp v agents goods run s) (hgd : goods.Nodup)
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r) (hlen : 2 ≤ c.length)
    (hO : ∀ g ∈ O, g ∈ goods ∧ (s.base g = none ∨ s.base g = some r)) (hOnd : O.Nodup)
    (hvO : ∀ y, s.pick k = some y → v k y < value v k O) {j : A} {g : G}
    (hN : needsOf v goods (rotate s c O) j g) : needsOf v goods s j g := by
  have hc := hch.1
  have hO' : ∀ g ∈ O, s.base g = none ∨ s.base g = some r := fun g hg => (hO g hg).2
  by_cases hjc : j ∈ c
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨⟨hkm, -⟩, y, -, hy, -, -⟩ := hch.head hk hlen
      have hv := value_O_le (s := s) (v := v) hk hc (fun g hg => (hO g hg).1) hOnd
      rcases hN with ⟨-, hg, -, hlt⟩ | ⟨hm, -⟩
      · refine (needsOf_unmarked hkm).mpr ⟨hg, by omega, fun y' hy' => ?_⟩
        rw [hy] at hy'; cases hy'
        have := hvO y hy; omega
      · exact absurd (Or.inl hk) hm
    · obtain ⟨i, a, ha, hj⟩ := exists_prev hk hjc hjk
      obtain ⟨-, y, hy, hNy⟩ := hch.2.2.1 i a j ha hj
      have hjm : ¬ s.marked j := fun hm => hS.no_needs hgd hm y hNy
      have hjm' := rotate_marked_next (O := O) (s := s) hc hk hj
      rw [needsOf_unmarked hjm'] at hN
      rw [needsOf_unmarked hjm] at hNy ⊢
      obtain ⟨hg, hpos, hlt⟩ := hN
      refine ⟨hg, hpos, fun y' hy' => ?_⟩
      have h1 := hNy.2.2 y' hy'
      have h2 := hlt y (by rw [rotate_pick_next hc ha hj, hy])
      omega
  · exact (rotate_needs_out hl hO' hjc).mp hN

theorem NA_rotate (hS : AfterUp v agents goods run s) (hgd : goods.Nodup)
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r) (hlen : 2 ≤ c.length)
    (hO : ∀ g ∈ O, g ∈ goods ∧ (s.base g = none ∨ s.base g = some r)) (hOnd : O.Nodup)
    (hvO : ∀ y, s.pick k = some y → v k y < value v k O) {g : G}
    (h : NA agents (needsOf v goods (rotate s c O)) g) : NA agents (needsOf v goods s) g := by
  obtain ⟨j, hj, hN⟩ := h
  exact ⟨j, hj, needsOf_rotate hS hgd hch hk hl hlen hO hOnd hvO hN⟩

/-- **Lemma R(b)**, validity: the rotation is a valid pre-allocation. (V1): its junk lies in `W`, which avoids `NA`;
(V2): `k`'s base `O` lies in `W`, a chain agent's base is its predecessor's pick alone, and every other base is
unchanged. -/
theorem rotate_valid (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hr : IsLast run s r)
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r) (hlen : 2 ≤ c.length)
    (hO : ∀ g ∈ O, g ∈ goods ∧ (s.base g = none ∨ s.base g = some r)) (hOnd : O.Nodup)
    (hvO : ∀ y, s.pick k = some y → v k y < value v k O) :
    Valid agents goods (rotate s c O).base (needsOf v goods (rotate s c O)) := by
  have hc := hch.1
  have hI := hS.inv hgd
  have hO' : ∀ g ∈ O, s.base g = none ∨ s.base g = some r := fun g hg => (hO g hg).2
  have hW : ∀ g ∈ goods, (s.base g = none ∨ s.base g = some r) → ¬ NA agents (needsOf v goods (rotate s c O)) g :=
    fun g hg hb hna => hS.W_not_NA hgd hr (mem_Wl.mpr ⟨hg, hb⟩) (NA_rotate hS hgd hch hk hl hlen hO hOnd hvO hna)
  refine ⟨fun g hg => ?_, fun i h2 g hg => ?_⟩
  · obtain ⟨hgg, hb⟩ := mem_junk.mp hg
    exact hW g hgg ((rotate_base_none hc hk hl).mp hb).2
  · obtain ⟨hgg, hb⟩ := mem_baseOf.mp hg
    by_cases hic : i ∈ c
    · by_cases hik : i = k
      · subst hik
        exact hW g hgg (hO' g ((rotate_base_head hc hk).mp hb))
      · -- a chain agent's base is its predecessor's one-good base
        exfalso
        obtain ⟨j, a, ha, hi⟩ := exists_prev hk hic hik
        obtain ⟨⟨-, y, hB, -⟩, -⟩ := hch.2.2.1 j a i ha hi
        have hsub : ∀ h ∈ baseOf goods (rotate s c O).base i, h ∈ [y] := fun h hh => by
          obtain ⟨hhg, hhb⟩ := mem_baseOf.mp hh
          rw [← hB]
          exact mem_baseOf.mpr ⟨hhg, (rotate_base_next hc hk hl hO' ha hi).mp hhb⟩
        have := List.Nodup.length_le_of_subset (l₁ := baseOf goods (rotate s c O).base i) (hgd.filter _) hsub
        rw [List.length_singleton] at this; omega
    · have hB : baseOf goods (rotate s c O).base i = baseOf goods s.base i :=
        List.filter_congr fun h _ => by simp only [rotate_base_out hl hO' hic]
      rw [hB] at h2
      exact fun hna => hI.valid.v2 i h2 g (mem_baseOf.mpr ⟨hgg, (rotate_base_out hl hO' hic).mp hb⟩)
        (NA_rotate hS hgd hch hk hl hlen hO hOnd hvO hna)

/-- The agents of a need chain are processed in order, in the head's block. -/
theorem AfterUp.chain_pos (hS : AfterUp v agents goods run s) (hgd : goods.Nodup)
    (hch : NeedChain v agents goods s c) {tk : Nat} {pk : A × Option G} (hpk : run[tk]? = some pk)
    (hk : c[0]? = some pk.1) :
    ∀ (i : Nat) (z : A), c[i]? = some z → ∃ (tz : Nat) (pz : A × Option G), run[tz]? = some pz ∧ pz.1 = z ∧
      SameBlock v run tk tz ∧ (0 < i → tk < tz)
  | 0, z, hz => by
    rw [hk] at hz; cases hz
    exact ⟨tk, pk, hpk, rfl, SameBlock.refl _, fun h => absurd h (by omega)⟩
  | i + 1, z, hz => by
    obtain ⟨a, ha⟩ : ∃ a, c[i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hz).1; omega)⟩
    obtain ⟨ta, pa, hpa, hpa1, hba, -⟩ := AfterUp.chain_pos hS hgd hch hpk hk i a ha
    obtain ⟨-, y, hy, hN⟩ := hch.2.2.1 i a z ha hz
    obtain ⟨tz, pz, hpz, hpz1⟩ := hS.phase.exists_pos (hch.2.1 z (List.mem_of_getElem? hz))
    obtain ⟨-, hlt, hbl⟩ := hS.chain_step hgd hy hN hpa hpa1 hpz hpz1
    exact ⟨tz, pz, hpz, hpz1, hba.trans hbl, fun _ => by have := hba.1; omega⟩

/-- A chain agent after the head takes its predecessor's pick as its whole base, which it values more than its old
base. -/
theorem AfterUp.rotate_base_better (hS : AfterUp v agents goods run s) (hgd : goods.Nodup)
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) {i : Nat} {a x : A} (ha : c[i]? = some a)
    (hx : c[i + 1]? = some x) :
    ∃ y, baseOf goods (rotate s c O).base x = [y] ∧ s.pick a = some y ∧ needsOf v goods s x y ∧
      ¬ s.marked x ∧ value v x (baseOf goods s.base x) < v x y := by
  have hc := hch.1
  have hI := hS.inv hgd
  obtain ⟨⟨ham, y', hB', -⟩, y, hy, hN⟩ := hch.2.2.1 i a x ha hx
  have haA : a ∈ agents := hch.2.1 a (List.mem_of_getElem? ha)
  have hxA : x ∈ agents := hch.2.1 x (List.mem_of_getElem? hx)
  have hBa : baseOf goods s.base a = [y] := by rw [hI.unmarked a haA ham, hy]; rfl
  have hB : baseOf goods (rotate s c O).base x = [y] := by
    rw [← hBa]; exact List.filter_congr fun h _ => by simp only [rotate_base_next hc hk hl hO ha hx]
  have hxm : ¬ s.marked x := fun hm => hS.no_needs hgd hm y hN
  refine ⟨y, hB, hy, hN, hxm, ?_⟩
  rw [hI.unmarked x hxA hxm]
  rw [needsOf_unmarked hxm] at hN
  obtain ⟨-, hpos, hlt⟩ := hN
  cases hyx : s.pick x with
  | none => simpa using hpos
  | some yx => simpa using hlt yx hyx

/-- **Lemma R(c)**, first part (`k4/c4.md` §4a): after a rotation to `r`, an agent exposed w.r.t. the new owner `k`
was exposed w.r.t. `r` before, unless it is `r`: off the chain it has the same base and faces the same `W`; on the
chain its base got better (monotonicity). -/
theorem rotate_exposed (hS : AfterUp v agents goods run s) (hgd : goods.Nodup)
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) {x : A}
    (hx : Exposed v agents goods (rotate s c O) k x) : Exposed v agents goods s r x ∨ x = r := by
  have hc := hch.1
  obtain ⟨hxa, hxm', hxk, hthr⟩ := hx
  rw [rotate_Wl hc hk hl hO] at hthr
  by_cases hxr : x = r
  · exact Or.inr hxr
  refine Or.inl ⟨hxa, ?_, hxr, ?_⟩
  all_goals by_cases hxc : x ∈ c
  · obtain ⟨i, a, ha, hx⟩ := exists_prev hk hxc hxk
    obtain ⟨_, _, _, _, hxm, _⟩ := hS.rotate_base_better hgd hch hk hl hO ha hx
    exact hxm
  · exact fun hm => hxm' ((rotate_out hxc).2.mpr hm)
  · obtain ⟨i, a, ha, hx⟩ := exists_prev hk hxc hxk
    obtain ⟨y, hB, -, -, -, hlt⟩ := hS.rotate_base_better hgd hch hk hl hO ha hx
    rw [hB] at hthr
    exact hthr.mono (List.Sublist.refl _) (by simp; omega)
  · have hB : baseOf goods (rotate s c O).base x = baseOf goods s.base x :=
      List.filter_congr fun h _ => by simp only [rotate_base_out hl hO hxc]
    rwa [hB] at hthr

/-- **Lemma R(c)**, second part: a chain agent other than the head and `r` is exposed after the rotation only if it
is a 4-good agent exposed before: a 3-good exposed agent leads its block (Lemma E(i)), while a chain agent after the
head is processed after it in its block. -/
theorem rotate_exposed_chain (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hcore : IsCore4 v agents goods) (hr : IsLast run s r) (hch : NeedChain v agents goods s c)
    (hk : c.head? = some k) (hl : c.getLast? = some r) (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r)
    {x : A} (hxc : x ∈ c) (hxr : x ≠ r) (hx : Exposed v agents goods (rotate s c O) k x) :
    Exposed v agents goods s r x ∧ (relevant v x goods).length = 4 := by
  have hE := (rotate_exposed hS hgd hch hk hl hO hx).resolve_right hxr
  refine ⟨hE, ?_⟩
  have hxk : x ≠ k := hx.2.2.1
  have hxa := hE.1
  rcases Nat.lt_or_ge (relevant v x goods).length 4 with h | h
  · exfalso
    have h3 : (relevant v x goods).length = 3 := by have := (hcore.2.1 x hxa).1; omega
    obtain ⟨-, -, -, -, hlead⟩ := lemmaE_three hS hgd hs hr hE h3
    have hkA : k ∈ agents := hch.2.1 k (List.mem_of_mem_head? hk)
    obtain ⟨tk, pk, hpk, hpk1⟩ := hS.phase.exists_pos hkA
    have hk0 : c[0]? = some pk.1 := by rw [← List.head?_eq_getElem?, hk, hpk1]
    have hi := List.idxOf_lt_length_of_mem hxc
    have hi0 : c.idxOf x ≠ 0 := fun h0 => hxk (by
      have := getElem?_idxOf hxc; rw [h0, ← List.head?_eq_getElem?, hk] at this; exact (Option.some.inj this).symm)
    obtain ⟨tx, px, hpx, hpx1, hbl, hlt⟩ := hS.chain_pos hgd hch hpk hk0 _ x (getElem?_idxOf hxc)
    exact hbl.2 tx (hlt (Nat.pos_of_ne_zero hi0)) (Nat.le_refl _) (hlead tx px hpx hpx1)
  · have := (hcore.2.1 x hxa).2; omega


/-- **Lemma R(c)**, third part (`k4/c4.md` §4, Theorem B₄(b), the case `x = r`): after a rotation to `r`, a 3-good
`r` is not exposed w.r.t. the new owner. The goods `r` values more than its old pick were picked by others, so they are
not in `W`; if `W` held two goods of `R_r`, one would be `r`'s old pick and the other a junk good below it, and `r`
could take that junk good in an envy-free upgrade, against (UT₂). So `R_r ∩ W` holds at most one good, worth less than
`r`'s new pick. -/
theorem rotate_last_not_exposed (hS : AfterUp v agents goods run s) (hgd : goods.Nodup)
    (hcore : IsCore4 v agents goods) (hr : IsLast run s r)
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) (h3 : (relevant v r goods).length = 3) :
    ¬ Exposed v agents goods (rotate s c O) k r := by
  intro hx
  have hc := hch.1
  have hI := hS.inv hgd
  obtain ⟨hra, -, hrk, hthr⟩ := hx
  rw [rotate_Wl hc hk hl hO] at hthr
  have hrc : r ∈ c := List.mem_of_getLast? hl
  obtain ⟨i, a, ha, hri⟩ := exists_prev hk hrc hrk
  obtain ⟨yp, hB, hyp, hN, hrm, -⟩ := hS.rotate_base_better hgd hch hk hl hO ha hri
  rw [hB] at hthr
  obtain ⟨h, hh, hlt⟩ := hthr
  simp only [value_cons, value_nil, Nat.add_zero] at hlt
  obtain ⟨tr, pr, hpr, hpr1, -, -⟩ := id hr
  have hpick : s.pick r = pr.2 := by rw [← hpr1]; exact hS.pick hpr
  -- a good of `W` that `r` values is worth at most its old pick
  have hle : ∀ g ∈ Wl goods s r, 0 < v r g → ∃ yr, s.pick r = some yr ∧ v r g ≤ v r yr := by
    intro g hg hpos
    refine Classical.byContradiction fun hno => ?_
    have hpb := hS.phase.pickedBefore_of_prefers hpr (mem_Wl.mp hg).1 (by rw [hpr1]; exact hpos) fun y hy => by
      rw [hpr1]; rw [← hpick] at hy
      exact Nat.lt_of_not_le fun hle' => hno ⟨y, hy, hle'⟩
    obtain ⟨t', ht', hpk⟩ := hpb
    unfold pickAt at hpk
    cases hq : run[t']? with
    | none => rw [hq] at hpk; cases hpk
    | some q =>
      rw [hq] at hpk
      have hbq := hS.base_of_pick hq hpk
      have hqr : q.1 ≠ r := fun e => by
        have := hS.phase.pos_unique hq hpr (e.trans hpr1.symm); omega
      obtain ⟨-, hb | hb⟩ := mem_Wl.mp hg
      · rw [hbq] at hb; cases hb
      · rw [hbq] at hb; exact hqr (Option.some.inj hb)
  obtain ⟨hypg, hyppos, hyplt⟩ := (needsOf_unmarked hrm).mp hN
  have hbelow : ∀ g ∈ relevant v r (Wl goods s r), v r g < v r yp := fun g hg => by
    obtain ⟨hgW, hpos⟩ := List.mem_filter.mp hg
    obtain ⟨yr, hyr, hle'⟩ := hle g hgW (by simpa using hpos)
    have := hyplt yr hyr; omega
  -- `yp` is not in `W`: it is the base of `a`, which is not `r`
  have har : a ≠ r := ne_last_of_next hc hl ha hri
  have haA : a ∈ agents := hch.2.1 a (List.mem_of_getElem? ha)
  have hypb : s.base yp = some a := by
    obtain ⟨⟨ham, -⟩, -⟩ := hch.2.2.1 i a r ha hri
    have := hI.unmarked a haA ham
    rw [hyp] at this
    exact (mem_baseOf.mp (by rw [this]; simp : yp ∈ baseOf goods s.base a)).2
  have hypW : yp ∉ Wl goods s r := fun hm => by
    obtain ⟨-, hb | hb⟩ := mem_Wl.mp hm
    · rw [hypb] at hb; cases hb
    · rw [hypb] at hb; exact har (Option.some.inj hb)
  have hLnd : (relevant v r (Wl goods s r)).Nodup := (hgd.filter _).filter _
  have hRnd : (relevant v r goods).Nodup := hgd.filter _
  have hmemR : ∀ g, g ∈ goods → 0 < v r g → g ∈ relevant v r goods :=
    fun g hg hpos => List.mem_filter.mpr ⟨hg, by simpa using hpos⟩
  have hone : (relevant v r (Wl goods s r)).length ≤ 1 := by
    refine Nat.le_of_not_lt fun h2 => ?_
    obtain ⟨g₁, g₂, rest, hL⟩ : ∃ g₁ g₂ rest, relevant v r (Wl goods s r) = g₁ :: g₂ :: rest := by
      match hm : relevant v r (Wl goods s r), h2 with
      | g₁ :: g₂ :: rest, _ => exact ⟨g₁, g₂, rest, rfl⟩
    have hg₁ : g₁ ∈ relevant v r (Wl goods s r) := by rw [hL]; simp
    have hg₂ : g₂ ∈ relevant v r (Wl goods s r) := by rw [hL]; simp
    have h12 : g₁ ≠ g₂ := by
      have := hLnd; rw [hL] at this; intro e; subst e; simp at this
    have hW₁ := (List.mem_filter.mp hg₁).1
    have hW₂ := (List.mem_filter.mp hg₂).1
    have hp₁ : 0 < v r g₁ := by simpa using (List.mem_filter.mp hg₁).2
    have hp₂ : 0 < v r g₂ := by simpa using (List.mem_filter.mp hg₂).2
    obtain ⟨yr, hyr, -⟩ := hle g₁ hW₁ hp₁
    have hyrpos : 0 < v r yr := hI.pickRel r hra hrm yr hyr
    have hBr : baseOf goods s.base r = [yr] := by rw [hI.unmarked r hra hrm, hyr]; rfl
    have hyrg : yr ∈ goods := (mem_baseOf.mp (by rw [hBr]; simp : yr ∈ baseOf goods s.base r)).1
    have hyryp : yr ≠ yp := fun e => by have := hyplt yr hyr; rw [e] at this; omega
    have hne₁ : g₁ ≠ yp := fun e => hypW (e ▸ hW₁)
    have hne₂ : g₂ ≠ yp := fun e => hypW (e ▸ hW₂)
    by_cases hyrL : yr = g₁ ∨ yr = g₂
    · -- `r`'s old pick is in `W`, with a junk good `g` below it: an envy-free upgrade applies
      obtain ⟨g, hgW, hgpos, hgyr, hgyp⟩ : ∃ g ∈ Wl goods s r, 0 < v r g ∧ g ≠ yr ∧ g ≠ yp := by
        rcases hyrL with e | e
        · exact ⟨g₂, hW₂, hp₂, fun e' => h12 (e.symm.trans e'.symm), hne₂⟩
        · exact ⟨g₁, hW₁, hp₁, fun e' => h12 (e'.trans e), hne₁⟩
      have hgg := (mem_Wl.mp hgW).1
      have hgJ : s.base g = none := by
        rcases (mem_Wl.mp hgW).2 with hb | hb
        · exact hb
        · exfalso
          have : g ∈ baseOf goods s.base r := mem_baseOf.mpr ⟨hgg, hb⟩
          rw [hBr] at this; simp at this; exact hgyr this
      -- `R_r = {yp, yr, g}`
      have hnd3 : [yp, yr, g].Nodup := by
        simp [Ne.symm hyryp, Ne.symm hgyp, Ne.symm hgyr]
      have hsub3 : ∀ z ∈ [yp, yr, g], z ∈ relevant v r goods := by
        intro z hz; simp at hz
        rcases hz with rfl | rfl | rfl
        · exact hmemR _ hypg hyppos
        · exact hmemR _ hyrg hyrpos
        · exact hmemR _ hgg hgpos
      have hall := subset_of_length_le hnd3 hsub3 (by simp; omega)
      have hval : value v r (relevant v r goods) = v r yp + v r yr + v r g := by
        have h1 := value_le_of_subset (v := v) r hnd3 hsub3
        have h2 := value_le_of_subset (v := v) r hRnd hall
        simp at h1 h2; omega
      have hbal := hcore.2.2.1 r hra yp hypg
      rw [← value_relevant, hval] at hbal
      refine hS.final r g ⟨hra, hrm, yr, hyr, hBr, hS.last_pick_free hgd hr hyr, ⟨yp, hN⟩,
        mem_junk.mpr ⟨hgg, hgJ⟩, hgpos, ⟨yp, hN, by omega⟩, ?_⟩
      show value v r ((relevant v r goods).filter (fun h => h ≠ yr ∧ h ≠ g)) ≤ v r yr + v r g
      have := value_le_of_subset (v := v) r (L₁ := (relevant v r goods).filter (fun h => h ≠ yr ∧ h ≠ g))
        (hRnd.filter _) (L₂ := [yp]) fun z hz => by
        obtain ⟨hzR, hz'⟩ := List.mem_filter.mp hz
        have hz'' : z ≠ yr ∧ z ≠ g := by simpa using hz'
        have := hall z hzR; simp at this
        rcases this with h | h | h
        · simp [h]
        · exact absurd h hz''.1
        · exact absurd h hz''.2
      simp only [value_cons, value_nil, Nat.add_zero] at this; omega
    · -- four goods of `R_r`: `yp`, `yr`, `g₁`, `g₂`
      simp only [not_or] at hyrL
      have hnd4 : [yp, yr, g₁, g₂].Nodup := by
        simp [Ne.symm hyryp, Ne.symm hne₁, Ne.symm hne₂, hyrL.1, hyrL.2, h12]
      have hsub4 : ∀ z ∈ [yp, yr, g₁, g₂], z ∈ relevant v r goods := by
        intro z hz; simp at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hmemR _ hypg hyppos
        · exact hmemR _ hyrg hyrpos
        · exact hmemR _ (mem_Wl.mp hW₁).1 hp₁
        · exact hmemR _ (mem_Wl.mp hW₂).1 hp₂
      have := List.Nodup.length_le_of_subset hnd4 hsub4
      simp at this; omega
  have h1 := value_lt_of_length_le_one hyppos hone hbelow
  have h2 := value_sublist v r (List.erase_sublist (l := Wl goods s r) (a := h))
  rw [value_relevant] at h1
  omega


/-- In the rotation, a chain agent after the head has at most one good in its base. -/
theorem rotate_chain_base_le_one (hgd : goods.Nodup) (hch : NeedChain v agents goods s c) (hk : c.head? = some k)
    (hl : c.getLast? = some r) (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) {i : A} (hic : i ∈ c)
    (hik : i ≠ k) : (baseOf goods (rotate s c O).base i).length ≤ 1 := by
  obtain ⟨j, a, ha, hi⟩ := exists_prev hk hic hik
  obtain ⟨⟨-, y, hB, -⟩, -⟩ := hch.2.2.1 j a i ha hi
  have hsub : ∀ h ∈ baseOf goods (rotate s c O).base i, h ∈ [y] := fun h hh => by
    obtain ⟨hhg, hhb⟩ := mem_baseOf.mp hh
    rw [← hB]
    exact mem_baseOf.mpr ⟨hhg, (rotate_base_next hch.1 hk hl hO ha hi).mp hhb⟩
  have := List.Nodup.length_le_of_subset (l₁ := baseOf goods (rotate s c O).base i) (hgd.filter _) hsub
  rw [List.length_singleton] at this; exact this

/-- **Theorem B₄ (a), (b)** (`k4/c4.md` §4). Let `k*` be a 3-good agent exposed w.r.t. `r` at the head of a need
chain `c` to `r` (in LB⁺'s bad case `k*` is the leader of `r`'s block, frozen and exposed, and every need chain from it
ends at `r`), and suppose no 4-good agent is exposed. Let `P′` be the rotation along `c` with base
`O = R_k* ∩ W` for `k*` (the two goods of `R_k*` other than its pick, Lemma E(i)). Then `P′` is a rotation of
LB₄ʳ (`RotStep`: it passes the checks of §5), and
- (a) `P′` is valid, `NA′ ⊆ NA`, and `k*`'s base `O` is envy-free;
- (b) `W′ = W`, and every agent exposed w.r.t. the owner `k*` in `P′` is an agent of `E_r` other than `k*`, or `r`
  when `r` has four goods. -/
theorem theoremB4 (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hcore : IsCore4 v agents goods) (hr : IsLast run s r) (hch : NeedChain v agents goods s c)
    (hk : c.head? = some k) (hl : c.getLast? = some r) (hlen : 2 ≤ c.length)
    (hkE : Exposed v agents goods s r k) (hk3 : (relevant v k goods).length = 3)
    (hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4)
    (hOd : O = relevant v k (Wl goods s r)) :
    RotStep v agents goods s (rotate s c O) ∧
      Valid agents goods (rotate s c O).base (needsOf v goods (rotate s c O)) ∧
      (∀ g, NA agents (needsOf v goods (rotate s c O)) g → NA agents (needsOf v goods s) g) ∧
      EFBase v goods (rotate s c O) k ∧
      Wl goods (rotate s c O) k = Wl goods s r ∧
      (∀ x, Exposed v agents goods (rotate s c O) k x →
        (Exposed v agents goods s r x ∧ x ≠ k) ∨ (x = r ∧ (relevant v r goods).length = 4)) ∧
      ∀ x ∈ c, x ≠ r → ¬ Exposed v agents goods (rotate s c O) k x := by
  have hc := hch.1
  have hI := hS.inv hgd
  have hkA := hkE.1
  have hkr : k ≠ r := hkE.2.2.1
  obtain ⟨y, hy, htop, hL2⟩ := (fun ⟨y, hy, htop, hL2, _⟩ => ⟨y, hy, htop, hL2⟩ :
    (∃ y, s.pick k = some y ∧ (∀ g ∈ goods, 0 < v k g → g ≠ y → g ∈ Wl goods s r ∧ v k g < v k y) ∧
      (relevant v k (Wl goods s r)).length = 2 ∧
      ∀ (t : Nat) (p : A × Option G), run[t]? = some p → p.1 = k → InsAt v run t) →
    ∃ y, s.pick k = some y ∧ (∀ g ∈ goods, 0 < v k g → g ≠ y → g ∈ Wl goods s r ∧ v k g < v k y) ∧
      (relevant v k (Wl goods s r)).length = 2) (lemmaE_three hS hgd hs hr hkE hk3)
  have hkm : ¬ s.marked k := hkE.2.1
  have hypos : 0 < v k y := hI.pickRel k hkA hkm y hy
  have hBk : baseOf goods s.base k = [y] := by rw [hI.unmarked k hkA hkm, hy]; rfl
  have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hBk]; simp : y ∈ baseOf goods s.base k)).1
  have hyb : s.base y = some k := (mem_baseOf.mp (by rw [hBk]; simp : y ∈ baseOf goods s.base k)).2
  have hyW : y ∉ Wl goods s r := fun hm => by
    obtain ⟨-, hb | hb⟩ := mem_Wl.mp hm
    · rw [hyb] at hb; cases hb
    · rw [hyb] at hb; exact hkr (Option.some.inj hb)
  have hOmem : ∀ g ∈ O, g ∈ goods ∧ 0 < v k g ∧ (s.base g = none ∨ s.base g = some r) := fun g hg => by
    rw [hOd] at hg
    obtain ⟨hgW, hpos⟩ := List.mem_filter.mp hg
    exact ⟨(mem_Wl.mp hgW).1, by simpa using hpos, (mem_Wl.mp hgW).2⟩
  have hO' : ∀ g ∈ O, g ∈ goods ∧ (s.base g = none ∨ s.base g = some r) :=
    fun g hg => ⟨(hOmem g hg).1, (hOmem g hg).2.2⟩
  have hO'' : ∀ g ∈ O, s.base g = none ∨ s.base g = some r := fun g hg => (hOmem g hg).2.2
  have hOnd : O.Nodup := by rw [hOd]; exact (hgd.filter _).filter _
  -- `R_k* = {y} ∪ O`, so by strict balance `v(O) > v(y)`
  have hyO : y ∉ O := fun hm => by rw [hOd] at hm; exact hyW (List.mem_filter.mp hm).1
  have hRnd : (relevant v k goods).Nodup := hgd.filter _
  have hsub1 : ∀ g ∈ y :: O, g ∈ relevant v k goods := fun g hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact List.mem_filter.mpr ⟨hyg, by simpa using hypos⟩
    · exact List.mem_filter.mpr ⟨(hOmem g hg).1, by simpa using (hOmem g hg).2.1⟩
  have hsub2 : ∀ g ∈ relevant v k goods, g ∈ y :: O := fun g hg => by
    obtain ⟨hgg, hpos⟩ := List.mem_filter.mp hg
    have hpos : 0 < v k g := by simpa using hpos
    by_cases hgy : g = y
    · simp [hgy]
    · exact List.mem_cons_of_mem _ (by rw [hOd]; exact List.mem_filter.mpr ⟨(htop g hgg hpos hgy).1, by simpa using hpos⟩)
  have hval : value v k (relevant v k goods) = v k y + value v k O := by
    have h1 := value_le_of_subset (v := v) k (List.nodup_cons.mpr ⟨hyO, hOnd⟩) hsub1
    have h2 := value_le_of_subset (v := v) k hRnd hsub2
    simp only [value_cons] at h1 h2; omega
  have hbal := hcore.2.2.1 k hkA y hyg
  rw [← value_relevant, hval] at hbal
  have hvO : ∀ y', s.pick k = some y' → v k y' < value v k O := fun y' hy' => by
    rw [hy] at hy'; cases hy'; omega
  have hV := rotate_valid hS hgd hr hch hk hl hlen hO' hOnd hvO
  have hNA := fun g => NA_rotate (g := g) hS hgd hch hk hl hlen hO' hOnd hvO
  have hWW := rotate_Wl (goods := goods) (s := s) (O := O) hc hk hl hO''
  have hbase2 := (hS.base_two hgd)
  -- no base of the rotation has three goods
  have hOlen : O.length = 2 := by rw [hOd]; exact hL2
  have hle2 : ∀ i, (baseOf goods (rotate s c O).base i).length ≤ 2 := by
    intro i
    by_cases hic : i ∈ c
    · by_cases hik : i = k
      · subst hik
        have := List.Nodup.length_le_of_subset (l₁ := baseOf goods (rotate s c O).base i) (hgd.filter _)
          fun g hg => (rotate_base_head hc hk).mp (mem_baseOf.mp hg).2
        omega
      · have := rotate_chain_base_le_one hgd hch hk hl hO'' hic hik; omega
    · have hB : baseOf goods (rotate s c O).base i = baseOf goods s.base i :=
        List.filter_congr fun h _ => by simp only [rotate_base_out hl hO'' hic]
      rw [hB]; exact hbase2.1 i
  refine ⟨⟨c, k, r, O, hc, hlen, hch.2.1, hk, hl, hch.2.2.1, hch.2.2.2 r hl, ?_, hOnd,
      fun g hg => hOmem g hg, rfl, hV, ?_, fun i _ j _ hi => absurd hi (by have := hle2 i; omega)⟩,
    hV, hNA, ?_, hWW, ?_, fun x hxc hxr hx => ?_⟩
  · intro e; rw [e] at hOlen; simp at hOlen
  · -- (V2) for the marked agents: `k*`'s base lies in `W`; the others keep their two-good bases
    intro i hi hm g hg hna
    obtain ⟨hgg, hgb⟩ := mem_baseOf.mp hg
    rcases hm with hm | ⟨hm, hic⟩
    · rw [hk] at hm; cases hm
      have hgO := (rotate_base_head hc hk).mp hgb
      rw [hOd] at hgO
      exact hS.W_not_NA hgd hr (List.mem_filter.mp hgO).1 (hNA g hna)
    · have hB : baseOf goods (rotate s c O).base i = baseOf goods s.base i :=
        List.filter_congr fun h _ => by simp only [rotate_base_out hl hO'' hic]
      rw [hB] at hg
      exact hI.valid.v2 i (by have := hbase2.2.1 i hm; omega) g hg (hNA g hna)
  · -- `k*`'s base is envy-free: the only other good it values is its pick
    unfold EFBase
    have h1 := value_O_le (v := v) (s := s) hk hc (fun g hg => (hOmem g hg).1) hOnd
    have h2 := value_le_of_subset (v := v) k
      (L₁ := (relevant v k goods).filter (fun h => (rotate s c O).base h ≠ some k)) (hRnd.filter _) (L₂ := [y])
      fun g hg => by
        obtain ⟨hgR, hgb⟩ := List.mem_filter.mp hg
        have hgO : g ∉ O := fun hm => by simp [(rotate_base_head hc hk).mpr hm] at hgb
        rcases List.mem_cons.mp (hsub2 g hgR) with e | e
        · simp [e]
        · exact absurd e hgO
    simp only [value_cons, value_nil, Nat.add_zero] at h2
    omega
  · -- (b): exposure after the rotation
    intro x hx
    have hxk : x ≠ k := hx.2.2.1
    rcases rotate_exposed hS hgd hch hk hl hO'' hx with h | h
    · exact Or.inl ⟨h, hxk⟩
    · subst h
      refine Or.inr ⟨rfl, ?_⟩
      have hxA := hx.1
      rcases Nat.lt_or_ge (relevant v x goods).length 4 with h4 | h4
      · exfalso
        have h3 : (relevant v x goods).length = 3 := by have := (hcore.2.1 x hxA).1; omega
        exact rotate_last_not_exposed hS hgd hcore hr hch hk hl hO'' h3 hx
      · have := (hcore.2.1 x hxA).2; omega
  · -- the chain agents other than `r` are not exposed: they would be exposed 4-good agents of `P`
    obtain ⟨hE, h4⟩ := rotate_exposed_chain hS hgd hs hcore hr hch hk hl hO'' hxc hxr hx
    exact hno4 x hE h4


end rotation

/-! ## Theorem A₄: the owner r -/

section theoremA
variable {v : A → G → Nat} {agents : List A} {goods : List G} {run : List (A × Option G)} {s : LState A G}
  {r : A}

theorem upRun_base_mem {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s')
    (h : ∀ g i, s.base g = some i → i ∈ agents) : ∀ g i, s'.base g = some i → i ∈ agents := by
  induction hR with
  | done => exact h
  | step s s' s'' hs _ ih =>
    obtain ⟨k, g', hE, -, -, rfl⟩ := hs
    refine ih fun g i hg => ?_
    simp only [upgrade] at hg
    split at hg
    · cases hg; exact hE.1
    · exact h g i hg

/-- Every base belongs to a listed agent. -/
theorem AfterUp.base_mem (hS : AfterUp v agents goods run s) {g : G} {i : A} (h : s.base g = some i) :
    i ∈ agents :=
  upRun_base_mem hS.up (fun g i hg => by
    obtain ⟨t, p, hp, rfl, -⟩ := (runState_base hS.phase).mp hg
    exact hS.phase.agent_mem hp) g i h

/-- The completion that puts the goods of `H` (junk goods) one each into the agents of `T`, in order, and gives the
owner `r` its base and the rest of the junk. -/
def placeH (s : LState A G) (r : A) (H : List G) (T : List A) (g : G) : A :=
  match s.base g with
  | some i => i
  | none => if g ∈ H then T.getD (H.idxOf g) r else r

omit [DecidableEq A] in
theorem getD_mem_of_lt {T : List A} {i : Nat} {d : A} (h : i < T.length) : T.getD i d ∈ T := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

omit [DecidableEq A] in
theorem placeH_junk {H : List G} {T : List A} (hlen : H.length ≤ T.length) {g : G}
    (hb : s.base g = none) {j : A} (hj : placeH s r H T g = j) (hjr : j ≠ r) :
    g ∈ H ∧ T.getD (H.idxOf g) r = j ∧ j ∈ T := by
  simp only [placeH, hb] at hj
  by_cases hgH : g ∈ H
  · simp only [hgH, ↓reduceIte] at hj
    have hi : H.idxOf g < T.length := Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hgH) hlen
    exact ⟨hgH, hj, hj ▸ getD_mem_of_lt hi⟩
  · simp only [hgH, ↓reduceIte] at hj; exact absurd hj.symm hjr

omit [DecidableEq A] in
/-- The owner's bundle of `placeH` is its base and the junk outside `H`: it lies in `W` and avoids `H`. -/
theorem placeH_owner {H : List G} {T : List A} (hlen : H.length ≤ T.length) (hTr : ∀ t ∈ T, t ≠ r)
    (hHJ : ∀ h ∈ H, s.base h = none) {g : G}
    (hg : placeH s r H T g = r) : (s.base g = none ∨ s.base g = some r) ∧ g ∉ H := by
  cases hb : s.base g with
  | some i =>
    simp only [placeH, hb] at hg
    refine ⟨Or.inr (by rw [hg]), fun hgH => ?_⟩
    rw [hHJ g hgH] at hb; cases hb
  | none =>
    refine ⟨Or.inl rfl, fun hgH => ?_⟩
    simp only [placeH, hb, hgH, ↓reduceIte] at hg
    have hi : H.idxOf g < T.length := Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hgH) hlen
    exact hTr _ (getD_mem_of_lt hi) hg

/-- **A completion that places a set `H` of junk goods into distinct terminals** (`k4/c4.md` Theorems A₄, B₄(c),
"Completion"; `proofs/lb_last_step.md` Lemma 1), for any state whose bases belong to listed agents and have at most two
goods, an owner `o` that is not frozen, and agents `T` (not `o`, not frozen, with at most one good in their base) at
least as many as `H`. -/
theorem completion_placeH_gen (hgd : goods.Nodup) {s₀ : LState A G} {o : A} {N : A → G → Prop}
    (hmem : ∀ g i, s₀.base g = some i → i ∈ agents) (h2 : ∀ i, (baseOf goods s₀.base i).length ≤ 2)
    (hoa : o ∈ agents) (hoF : ¬ Frozen agents goods s₀.base N o)
    {H : List G} {T : List A} (hT : T.Nodup) (hlen : H.length ≤ T.length)
    (hTt : ∀ t ∈ T, t ∈ agents ∧ t ≠ o ∧ ¬ Frozen agents goods s₀.base N t ∧ (baseOf goods s₀.base t).length ≤ 1) :
    Completion agents goods s₀.base N (some o) (placeH s₀ o H T) := by
  refine ⟨fun g _ => ?_, fun g _ i hb => by simp [placeH, hb], fun w hw => ?_, fun j _ hjo hF => ?_,
    fun j _ hjo hF => ?_⟩
  · cases hb : s₀.base g with
    | some i => simp only [placeH, hb]; exact hmem g i hb
    | none =>
      by_cases hX : placeH s₀ o H T g = o
      · rw [hX]; exact hoa
      · obtain ⟨-, -, hjT⟩ := placeH_junk hlen hb rfl hX
        exact (hTt _ hjT).1
  · cases hw; exact ⟨hoa, hoF⟩
  · have hjr : j ≠ o := fun e => hjo (by rw [e])
    refine List.eq_nil_iff_forall_not_mem.mpr fun g hg => ?_
    obtain ⟨hgb, hgX, hgn⟩ := mem_junkOf.mp hg
    obtain ⟨-, -, hjT⟩ := placeH_junk hlen hgn hgX hjr
    exact (hTt j hjT).2.2.1 hF
  · have hjr : j ≠ o := fun e => hjo (by rw [e])
    by_cases hjT : j ∈ T
    · -- one junk good at most, and a base of at most one good
      have h1 : (junkOf goods s₀.base (placeH s₀ o H T) j).length ≤ 1 := by
        cases hJ : junkOf goods s₀.base (placeH s₀ o H T) j with
        | nil => simp
        | cons g₀ rest =>
          rw [← hJ]
          have hg₀ : g₀ ∈ junkOf goods s₀.base (placeH s₀ o H T) j := by rw [hJ]; simp
          have hnd : (junkOf goods s₀.base (placeH s₀ o H T) j).Nodup :=
            (LB.nodup_bundle hgd _ _).filter _
          refine LB.length_le_one hnd (y := g₀) fun g hg => ?_
          obtain ⟨-, hgX, hgn⟩ := mem_junkOf.mp hg
          obtain ⟨-, hg₀X, hg₀n⟩ := mem_junkOf.mp hg₀
          obtain ⟨hgH, hgT, -⟩ := placeH_junk hlen hgn hgX hjr
          obtain ⟨hg₀H, hg₀T, -⟩ := placeH_junk hlen hg₀n hg₀X hjr
          have hi := Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hgH) hlen
          have hi₀ := Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hg₀H) hlen
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hgT
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₀] at hg₀T
          simp only [Option.getD_some] at hgT hg₀T
          have e : H.idxOf g = H.idxOf g₀ := (hT.getElem_inj (hi := hi) (hj := hi₀)).mp (hgT.trans hg₀T.symm)
          rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hgH),
            ← List.getElem_idxOf (List.idxOf_lt_length_of_mem hg₀H)]
          simp only [e]
      have h2' := (hTt j hjT).2.2.2
      omega
    · have h0 : junkOf goods s₀.base (placeH s₀ o H T) j = [] :=
        List.eq_nil_iff_forall_not_mem.mpr fun g hg => by
          obtain ⟨-, hgX, hgn⟩ := mem_junkOf.mp hg
          exact hjT (placeH_junk hlen hgn hgX hjr).2.2
      rw [h0]; simpa using h2 j

/-- **The completion with owner `r` that places a set `H` of junk goods into distinct terminals** (`k4/c4.md`
Theorem A₄, "Completion"; `proofs/lb_last_step.md` Lemma 1): it is a completion of the state after envy-free
upgrades, with the needs of the state. -/
theorem completion_placeH (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hr : IsLast run s r)
    {H : List G} {T : List A} (hT : T.Nodup) (hlen : H.length ≤ T.length)
    (hTt : ∀ t ∈ T, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t) :
    Completion agents goods s.base (needsOf v goods s) (some r) (placeH s r H T) := by
  obtain ⟨tr, pr, hpr, hpr1, hrm, -⟩ := id hr
  have hbase2 := hS.base_two hgd
  exact completion_placeH_gen hgd (fun g i hb => hS.base_mem hb) hbase2.1 (hpr1 ▸ hS.phase.agent_mem hpr)
    (fun hF => hS.last_not_frozen hgd hr ⟨hrm, hF⟩) hT hlen fun t ht =>
      ⟨(hTt t ht).1, (hTt t ht).2.1, fun hF => (hTt t ht).2.2.2 ⟨(hTt t ht).2.2.1, hF⟩,
        hbase2.2.2 t (hTt t ht).2.2.1⟩

/-- The ways an agent `j` is safe against every bundle of the owner `o` inside `W ∖ H` (`k4/c4.md` Theorem A₄,
"(OC₄)"): it values every other list of goods at most as much as its base (an envy-free base); or it is not threatened
by `W` with its base; or it has three goods, holds its top `y` alone, and `H` holds one of its goods. -/
def SafeAgainst (v : A → G → Nat) (goods : List G) (s₀ : LState A G) (o : A) (H : List G) (j : A) : Prop :=
  (∀ L : List G, L.Nodup → (∀ g ∈ L, g ∈ goods ∧ s₀.base g ≠ some j) →
      value v j L ≤ value v j (baseOf goods s₀.base j)) ∨
    ¬ Threatened v j (Wl goods s₀ o) (baseOf goods s₀.base j) ∨
    ∃ y, baseOf goods s₀.base j = [y] ∧ 0 < v j y ∧ (relevant v j goods).length = 3 ∧
      (∀ g ∈ goods, 0 < v j g → g ≠ y → v j g < v j y) ∧ ∃ h ∈ H, 0 < v j h

/-- **(OC₄) for `placeH`**: if every agent other than the owner is safe, nobody strongly envies the owner's bundle
`X_o ⊆ W ∖ H` (monotonicity for an agent not threatened by `W`; at most one of its goods, below its top, for an agent
holding its top with a good in `H`). -/
theorem oc_placeH_gen (hgd : goods.Nodup) {s₀ : LState A G} {o : A} {H : List G} {T : List A}
    (hHJ : ∀ h ∈ H, s₀.base h = none) (hHg : ∀ h ∈ H, h ∈ goods) (hlen : H.length ≤ T.length)
    (hTr : ∀ t ∈ T, t ≠ o) (hsafe : ∀ j ∈ agents, j ≠ o → SafeAgainst v goods s₀ o H j) :
    OC v agents goods (placeH s₀ o H T) (some o) := by
  intro w hw j hj hjw h hh
  cases hw
  have hXr : ∀ g ∈ bundle goods (placeH s₀ o H T) o, g ∈ goods ∧ (s₀.base g = none ∨ s₀.base g = some o) ∧
      g ∉ H := fun g hg => by
    obtain ⟨hgg, hgX⟩ := LB.mem_bundle.mp hg
    exact ⟨hgg, placeH_owner hlen hTr hHJ hgX⟩
  have hsubW : (bundle goods (placeH s₀ o H T) o).Sublist (Wl goods s₀ o) :=
    filter_sublist_of_imp fun g hg hgX => by
      have := (hXr g (LB.mem_bundle.mpr ⟨hg, by simpa using hgX⟩)).2.1
      simpa using this
  have hbj : value v j (baseOf goods s₀.base j) ≤ value v j (bundle goods (placeH s₀ o H T) j) :=
    value_baseOf_le (fun g _ i hb => by simp [placeH, hb]) j
  have hndr : ((bundle goods (placeH s₀ o H T) o).erase h).Nodup :=
    (LB.nodup_bundle hgd (placeH s₀ o H T) o).erase h
  rcases hsafe j hj hjw with hEF | hthr | ⟨y, hBj, hypos, h3, htop, hj₀, hj₀H, hj₀pos⟩
  · -- an envy-free base
    refine Nat.le_trans (hEF _ hndr fun g hg => ?_) hbj
    obtain ⟨hgg, hgb, -⟩ := hXr g (List.mem_of_mem_erase hg)
    refine ⟨hgg, fun e => ?_⟩
    rcases hgb with hb | hb
    · rw [e] at hb; cases hb
    · rw [e] at hb; exact hjw (Option.some.inj hb)
  · -- not threatened by `W`, hence not by `X_o ⊆ W`
    have hhW : h ∈ Wl goods s₀ o := hsubW.subset hh
    have h1 : value v j ((Wl goods s₀ o).erase h) ≤ value v j (baseOf goods s₀.base j) :=
      Nat.le_of_not_lt fun hlt => hthr ⟨h, hhW, hlt⟩
    have h2 := value_sublist v j (hsubW.erase h)
    omega
  · -- three goods, its top held, one in `H`: at most one in `X_o`, below its top
    have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hBj]; simp : y ∈ baseOf goods s₀.base j)).1
    have hyb : s₀.base y = some j := (mem_baseOf.mp (by rw [hBj]; simp : y ∈ baseOf goods s₀.base j)).2
    have hyR : y ∈ relevant v j goods := List.mem_filter.mpr ⟨hyg, by simpa using hypos⟩
    have hj₀b := hHJ hj₀ hj₀H
    have hj₀y : hj₀ ≠ y := fun e => by rw [e, hyb] at hj₀b; cases hj₀b
    have hj₀R : hj₀ ∈ (relevant v j goods).erase y :=
      (List.mem_erase_of_ne hj₀y).mpr (List.mem_filter.mpr ⟨hHg hj₀ hj₀H, by simpa using hj₀pos⟩)
    have hlen1 : (((relevant v j goods).erase y).erase hj₀).length = 1 := by
      rw [List.length_erase_of_mem hj₀R, List.length_erase_of_mem hyR, h3]
    have hLr : ∀ g ∈ relevant v j (bundle goods (placeH s₀ o H T) o),
        g ∈ ((relevant v j goods).erase y).erase hj₀ ∧ v j g < v j y := fun g hg => by
      obtain ⟨hgX, hpos⟩ := List.mem_filter.mp hg
      have hpos : 0 < v j g := by simpa using hpos
      obtain ⟨hgg, hgb, hgH⟩ := hXr g hgX
      have hgy : g ≠ y := fun e => by
        rcases hgb with hb | hb
        · rw [e, hyb] at hb; cases hb
        · rw [e, hyb] at hb; exact hjw (Option.some.inj hb)
      refine ⟨(List.mem_erase_of_ne fun e => hgH (by rw [e]; exact hj₀H)).mpr ((List.mem_erase_of_ne hgy).mpr
        (List.mem_filter.mpr ⟨hgg, by simpa using hpos⟩)), htop g hgg hpos hgy⟩
    have hlenLr := List.Nodup.length_le_of_subset (l₁ := relevant v j (bundle goods (placeH s₀ o H T) o))
      ((LB.nodup_bundle hgd _ o).filter _) fun g hg => (hLr g hg).1
    rw [hlen1] at hlenLr
    have h1 := value_lt_of_length_le_one (L := relevant v j (bundle goods (placeH s₀ o H T) o)) hypos hlenLr
      fun g hg => (hLr g hg).2
    rw [value_relevant] at h1
    have h2 := value_sublist v j (List.erase_sublist (l := bundle goods (placeH s₀ o H T) o) (a := h))
    rw [hBj] at hbj
    simp only [value_cons, value_nil, Nat.add_zero] at hbj
    omega

/-- **(OC₄) for `placeH` with owner `r`** (`k4/c4.md` Theorem A₄, "(OC₄)"): if `H` meets `R_x` for every exposed
agent `x` and no 4-good agent is exposed, nobody strongly envies `r`'s bundle `X_r ⊆ W ∖ H`: an upgraded agent holds
an envy-free base; an agent that is not exposed is not threatened by `W`, hence not by `X_r` (monotonicity); an
exposed agent has three goods, and `X_r` holds at most one of them, worth less than its pick. -/
theorem oc_placeH (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hcore : IsCore4 v agents goods) (hr : IsLast run s r) {H : List G} {T : List A}
    (hHJ : ∀ h ∈ H, s.base h = none) (hHg : ∀ h ∈ H, h ∈ goods) (hlen : H.length ≤ T.length)
    (hTr : ∀ t ∈ T, t ≠ r)
    (hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4)
    (hhit : ∀ x, Exposed v agents goods s r x → ∃ h ∈ H, 0 < v x h) :
    OC v agents goods (placeH s r H T) (some r) := by
  have hI := hS.inv hgd
  refine oc_placeH_gen hgd hHJ hHg hlen hTr fun j hj hjr => ?_
  by_cases hjm : s.marked j
  · exact Or.inl fun L hL hLg => (hS.efBase hgd j hjm).value_le hL hLg
  by_cases hjE : Exposed v agents goods s r j
  · have h3 : (relevant v j goods).length = 3 := by
      have := hcore.2.1 j hj; have := hno4 j hjE; omega
    obtain ⟨y, hy, htop, -, -⟩ := lemmaE_three hS hgd hs hr hjE h3
    refine Or.inr (Or.inr ⟨y, by rw [hI.unmarked j hj hjm, hy]; rfl, hI.pickRel j hj hjm y hy, h3,
      fun g hg hpos hgy => (htop g hg hpos hgy).2, hhit j hjE⟩)
  · exact Or.inr (Or.inl fun ht => hjE ⟨hj, hjm, hjr, ht⟩)


/-- The step at which `x` is processed. -/
def posOf (run : List (A × Option G)) (x : A) : Nat := (run.map Prod.fst).idxOf x

omit [DecidableEq G] in
theorem PhaseRun.posOf_eq (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) : posOf run p.1 = t :=
  idxOf_of_getElem? hR.nodup (by simp [hp])

omit [DecidableEq G] in
theorem PhaseRun.getElem?_posOf (hR : PhaseRun v agents goods run) {x : A} (hx : x ∈ agents) :
    ∃ p : A × Option G, run[posOf run x]? = some p ∧ p.1 = x := by
  obtain ⟨t, p, hp, rfl⟩ := hR.exists_pos hx
  exact ⟨p, by rw [hR.posOf_eq hp]; exact hp, rfl⟩

/-- `π_x = R_x ∩ J` is not empty for an exposed 3-good agent: of its two goods in `W`, at most one is `Y_r`. -/
theorem AfterUp.pi_nonempty (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hr : IsLast run s r) {x : A} (hx : Exposed v agents goods s r x) (h3 : (relevant v x goods).length = 3) :
    ∃ g ∈ goods, s.base g = none ∧ 0 < v x g := by
  obtain ⟨-, -, -, hL2, -⟩ := lemmaE_three hS hgd hs hr hx h3
  have hI := hS.inv hgd
  obtain ⟨tr, pr, hpr, hpr1, hrm, -⟩ := id hr
  have hra : r ∈ agents := hpr1 ▸ hS.phase.agent_mem hpr
  have hBr := hI.unmarked r hra hrm
  obtain ⟨g₁, g₂, hL⟩ : ∃ g₁ g₂, relevant v x (Wl goods s r) = [g₁, g₂] := by
    match hm : relevant v x (Wl goods s r), hL2 with
    | [g₁, g₂], _ => exact ⟨g₁, g₂, rfl⟩
  have hnd : (relevant v x (Wl goods s r)).Nodup := (hgd.filter _).filter _
  rw [hL] at hnd
  have h12 : g₁ ≠ g₂ := by simp at hnd; exact hnd
  have hmem : ∀ g ∈ [g₁, g₂], g ∈ goods ∧ (s.base g = none ∨ s.base g = some r) ∧ 0 < v x g := fun g hg => by
    rw [← hL] at hg
    obtain ⟨hgW, hpos⟩ := List.mem_filter.mp hg
    exact ⟨(mem_Wl.mp hgW).1, (mem_Wl.mp hgW).2, by simpa using hpos⟩
  obtain ⟨hg₁, hb₁, hp₁⟩ := hmem g₁ (by simp)
  obtain ⟨hg₂, hb₂, hp₂⟩ := hmem g₂ (by simp)
  rcases hb₁ with hb₁ | hb₁
  · exact ⟨g₁, hg₁, hb₁, hp₁⟩
  rcases hb₂ with hb₂ | hb₂
  · exact ⟨g₂, hg₂, hb₂, hp₂⟩
  -- both in `r`'s base, which has at most one good
  exfalso
  have hm₁ : g₁ ∈ baseOf goods s.base r := mem_baseOf.mpr ⟨hg₁, hb₁⟩
  have hm₂ : g₂ ∈ baseOf goods s.base r := mem_baseOf.mpr ⟨hg₂, hb₂⟩
  rw [hBr] at hm₁ hm₂
  cases hy : s.pick r with
  | none => rw [hy] at hm₁; simp at hm₁
  | some y => rw [hy] at hm₁ hm₂; simp at hm₁ hm₂; exact h12 (hm₁.trans hm₂.symm)

/-- A list without repetitions with the same goods (keeping last occurrences). -/
def dedupL : List G → List G
  | [] => []
  | a :: l => if a ∈ dedupL l then dedupL l else a :: dedupL l

theorem mem_dedupL : ∀ {l : List G} {g : G}, g ∈ dedupL l ↔ g ∈ l
  | [], _ => by simp [dedupL]
  | a :: l, g => by
    unfold dedupL
    split
    · rename_i h
      rw [mem_dedupL]
      constructor
      · exact fun hg => List.mem_cons_of_mem _ hg
      · intro hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact mem_dedupL.mp h
        · exact hg
    · simp [mem_dedupL]

theorem nodup_dedupL : ∀ l : List G, (dedupL l).Nodup
  | [] => by simp [dedupL]
  | a :: l => by
    unfold dedupL
    split
    · exact nodup_dedupL l
    · rename_i h; exact List.nodup_cons.mpr ⟨h, nodup_dedupL l⟩

theorem length_dedupL_le : ∀ l : List G, (dedupL l).length ≤ l.length
  | [] => by simp [dedupL]
  | a :: l => by
    unfold dedupL
    split
    · have := length_dedupL_le l; simp; omega
    · have := length_dedupL_le l; simp; omega

theorem length_dedupL_lt : ∀ {l : List G}, ¬ l.Nodup → (dedupL l).length < l.length
  | [], h => absurd List.nodup_nil h
  | a :: l, h => by
    unfold dedupL
    split
    · have := length_dedupL_le l; simp; omega
    · rename_i ha
      have hl : ¬ l.Nodup := fun hl => h (List.nodup_cons.mpr ⟨fun hm => ha (mem_dedupL.mpr hm), hl⟩)
      have := length_dedupL_lt hl; simp; omega

omit [DecidableEq A] in
theorem nodup_map_of_inj {f : A → A} : ∀ {l : List A}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
    (l.map f).Nodup
  | [], _, _ => by simp
  | a :: l, hnd, hinj => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_of_inj hl fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact ha (hinj a (by simp) b (by simp [hb]) hfb.symm ▸ hb)

/-- **The terminals outside `B*`** (`proofs/lb_last_step.md` §4, `k4/c4.md` Theorem A₄). Let `E` be distinct unmarked
leaders other than `r`. Their need chains end at terminals in their blocks (A4), distinct for distinct blocks. Those of
the leaders outside `r`'s block `B*` are other than `r` and outside `B*`; at most one leader of `E` is in `B*`. -/
theorem AfterUp.terminals_out (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hr : IsLast run s r)
    {E : List A} (hE : E.Nodup)
    (hEx : ∀ x ∈ E, x ∈ agents ∧ ¬ s.marked x ∧ x ≠ r ∧ InsAt v run (posOf run x)) :
    ∃ T : List A, T.Nodup ∧ (∀ t ∈ T, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t) ∧
      (∀ k ∈ E, SameBlock v run (posOf run k) (posOf run r) → ∀ t ∈ T,
        ¬ SameBlock v run (posOf run k) (posOf run t)) ∧
      (E.length ≤ T.length ∨ ∃ k ∈ E, SameBlock v run (posOf run k) (posOf run r) ∧ E.length ≤ T.length + 1 ∧
        ∀ k' ∈ E, SameBlock v run (posOf run k') (posOf run r) → k' = k) := by
  classical
  have hR := hS.phase
  obtain ⟨tr, pr, hpr, hpr1, hrm, -⟩ := id hr
  have hposr : posOf run r = tr := by rw [← hpr1]; exact hR.posOf_eq hpr
  -- a terminal in each block
  have hτ : ∀ x ∈ E, ∃ e, e ∈ agents ∧ ¬ s.marked e ∧ ¬ FrozenAt v agents goods s e ∧
      SameBlock v run (posOf run x) (posOf run e) := by
    intro x hx
    obtain ⟨hxa, hxm, -, -⟩ := hEx x hx
    obtain ⟨px, hpx, hpx1⟩ := hR.getElem?_posOf hxa
    obtain ⟨c, e, te, pe, -, -, -, hpe, hpe1, hbl, hem, hef, -⟩ :=
      hS.exists_chain hgd _ _ px (Nat.le_refl _) hpx (hpx1 ▸ hxm)
    refine ⟨e, hpe1 ▸ hR.agent_mem hpe, hem, hef, ?_⟩
    rw [← hpe1, hR.posOf_eq hpe]; exact hbl
  let τ : A → A := fun x => if h : x ∈ E then Classical.choose (hτ x h) else x
  have hτs : ∀ x (h : x ∈ E), τ x ∈ agents ∧ ¬ s.marked (τ x) ∧ ¬ FrozenAt v agents goods s (τ x) ∧
      SameBlock v run (posOf run x) (posOf run (τ x)) := fun x h => by
    simp only [τ, h, ↓reduceDIte]; exact Classical.choose_spec (hτ x h)
  -- two leaders whose blocks share a step are equal
  have hlead : ∀ x ∈ E, ∀ y ∈ E, ∀ t, SameBlock v run (posOf run x) t → SameBlock v run (posOf run y) t → x = y :=
    fun x hx y hy t hbx hby => by
      have e := leader_unique (hEx x hx).2.2.2 (hEx y hy).2.2.2 hbx hby
      obtain ⟨px, hpx, hpx1⟩ := hR.getElem?_posOf (hEx x hx).1
      obtain ⟨py, hpy, hpy1⟩ := hR.getElem?_posOf (hEx y hy).1
      rw [e] at hpx; rw [hpx] at hpy; cases hpy; exact hpx1.symm.trans hpy1
  let inB : A → Prop := fun x => SameBlock v run (posOf run x) (posOf run r)
  let E' := E.filter (fun x => !decide (inB x))
  let EB := E.filter (fun x => decide (inB x))
  have hsplit : E.length = EB.length + E'.length := LB.length_filter_add E _
  have hE'm : ∀ x ∈ E', x ∈ E ∧ ¬ inB x := fun x hx => by
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx; exact ⟨h1, by simpa using h2⟩
  have hEBm : ∀ x ∈ EB, x ∈ E ∧ inB x := fun x hx => by
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx; exact ⟨h1, by simpa using h2⟩
  have hT₀nd : (E'.map τ).Nodup := nodup_map_of_inj (hE.filter _) fun x hx y hy hxy => by
    have hx' := (hE'm x hx).1
    have hy' := (hE'm y hy).1
    exact hlead x hx' y hy' _ (hτs x hx').2.2.2 (hxy ▸ (hτs y hy').2.2.2)
  have hT₀t : ∀ t ∈ E'.map τ, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hxE, hxB⟩ := hE'm x hx
    obtain ⟨h1, h2, h3, h4⟩ := hτs x hxE
    exact ⟨h1, fun e => hxB (by show SameBlock v run (posOf run x) (posOf run r); rw [← e]; exact h4), h2, h3⟩
  have hT₀B : ∀ k ∈ E, inB k → ∀ t ∈ E'.map τ, ¬ SameBlock v run (posOf run k) (posOf run t) := by
    intro k hk hkB t ht hke
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hxE, hxB⟩ := hE'm x hx
    have := hlead x hxE k hk _ (hτs x hxE).2.2.2 hke
    subst this; exact hxB hkB
  refine ⟨E'.map τ, hT₀nd, hT₀t, hT₀B, ?_⟩
  cases hEBc : EB with
  | nil =>
    rw [hEBc] at hsplit
    exact Or.inl (by simp at hsplit ⊢; omega)
  | cons k rest =>
    have hk : k ∈ EB := by rw [hEBc]; simp
    obtain ⟨hkE, hkB⟩ := hEBm k hk
    have hEB1 : EB.length ≤ 1 := LB.length_le_one (hE.filter _) (y := k) fun x hx =>
      hlead x (hEBm x hx).1 k hkE _ (hEBm x hx).2 hkB
    refine Or.inr ⟨k, hkE, hkB, by simp; omega, fun k' hk' hk'B => hlead k' hk' k hkE _ hk'B hkB⟩

/-- **The terminals of LB⁺'s Theorem A** (`proofs/lb_last_step.md` §4, `k4/c4.md` Theorem A₄). Let `E` be distinct
unmarked leaders other than `r`. There are `|E|` distinct terminals other than `r`, unless `E` has an agent `k*` in
`B*` (its leader) that is frozen and whose need chains all end at `r`; then there are `|E| − 1`, none in `B*`. -/
theorem AfterUp.terminals (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hr : IsLast run s r)
    {E : List A} (hE : E.Nodup)
    (hEx : ∀ x ∈ E, x ∈ agents ∧ ¬ s.marked x ∧ x ≠ r ∧ InsAt v run (posOf run x)) :
    (∃ T : List A, T.Nodup ∧ E.length ≤ T.length ∧
        ∀ t ∈ T, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t) ∨
      ∃ k ∈ E, SameBlock v run (posOf run k) (posOf run r) ∧ FrozenAt v agents goods s k ∧
        (∀ c e, NeedChain v agents goods s c → c.head? = some k → c.getLast? = some e → e = r) ∧
        ∃ T : List A, T.Nodup ∧ E.length ≤ T.length + 1 ∧
          ∀ t ∈ T, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t := by
  have hR := hS.phase
  obtain ⟨T₀, hT₀nd, hT₀t, hT₀B, hlen | ⟨k, hkE, hkB, hlen, -⟩⟩ := hS.terminals_out hgd hr hE hEx
  · exact Or.inl ⟨T₀, hT₀nd, hlen, hT₀t⟩
  obtain ⟨hka, hkm, hkr, hkI⟩ := hEx k hkE
  -- one more terminal in `B*`, other than `r`, gives `|E|` terminals
  have hmore : ∀ e, e ∈ agents → e ≠ r → ¬ s.marked e → ¬ FrozenAt v agents goods s e →
      SameBlock v run (posOf run k) (posOf run e) →
      ∃ T : List A, T.Nodup ∧ E.length ≤ T.length ∧
        ∀ t ∈ T, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t :=
    fun e hea her hem hef hbe => ⟨e :: T₀, List.nodup_cons.mpr ⟨fun he => hT₀B k hkE hkB e he hbe, hT₀nd⟩,
      by simp; omega, fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hea, her, hem, hef⟩
        · exact hT₀t t ht⟩
  by_cases hkF : FrozenAt v agents goods s k
  · by_cases hall : ∀ c e, NeedChain v agents goods s c → c.head? = some k → c.getLast? = some e → e = r
    · exact Or.inr ⟨k, hkE, hkB, hkF, hall, T₀, hT₀nd, hlen, hT₀t⟩
    · -- a need chain from `k*` ends at another terminal of `B*`
      obtain ⟨c, e, hch, hck, hce, her⟩ : ∃ c e, NeedChain v agents goods s c ∧ c.head? = some k ∧
          c.getLast? = some e ∧ e ≠ r :=
        Classical.byContradiction fun hno => hall fun c e hch hck hce =>
          Classical.byContradiction fun her => hno ⟨c, e, hch, hck, hce, her⟩
      have hec : e ∈ c := List.mem_of_getLast? hce
      have hef : ¬ FrozenAt v agents goods s e := hch.2.2.2 e hce
      have hek : e ≠ k := fun h => hef (h ▸ hkF)
      obtain ⟨i, a, ha, hei⟩ := exists_prev hck hec hek
      obtain ⟨-, y, -, hN⟩ := hch.2.2.1 i a e ha hei
      have hem : ¬ s.marked e := fun hm => hS.no_needs hgd hm y hN
      obtain ⟨pk, hpk, hpk1⟩ := hR.getElem?_posOf hka
      have hk0 : c[0]? = some pk.1 := by rw [← List.head?_eq_getElem?, hck, hpk1]
      obtain ⟨te, pe, hpe, hpe1, hbl, -⟩ := hS.chain_pos hgd hch hpk hk0 (i + 1) e hei
      refine Or.inl (hmore e (hch.2.1 e hec) her hem hef ?_)
      rw [← hpe1, hR.posOf_eq hpe]; exact hbl
  · exact Or.inl (hmore k hka hkr hkm hkF (SameBlock.refl _))

/-- **LB⁺'s bad case** at `r` (`k4/c4.md` Theorem A₄, (1)–(3)): an exposed agent `k*` that leads `r`'s block, is not
`r` and is frozen; every need chain from `k*` ends at `r`; and the sets `π_x = R_x ∩ J` of the exposed agents are
pairwise disjoint. -/
def BadCase (v : A → G → Nat) (agents : List A) (goods : List G) (run : List (A × Option G)) (s : LState A G)
    (r k : A) : Prop :=
  Exposed v agents goods s r k ∧ FrozenAt v agents goods s k ∧ InsAt v run (posOf run k) ∧
    SameBlock v run (posOf run k) (posOf run r) ∧
    (∀ c e, NeedChain v agents goods s c → c.head? = some k → c.getLast? = some e → e = r) ∧
    ∀ x y g, Exposed v agents goods s r x → Exposed v agents goods s r y → x ≠ y → g ∈ goods →
      s.base g = none → 0 < v x g → 0 < v y g → False

/-- **Theorem A₄** (`k4/c4.md` §3). After a run of Phase 1 and envy-free upgrades to the fixpoint, if no 4-good agent
is exposed, then `r` is a valid owner (some completion with owner `r`, the needs of the state, satisfies (OC₄)),
except possibly in LB⁺'s bad case; in the bad case `k*` has three goods and every good of `R_k*` other than its pick
is in `W`. The proof is LB⁺'s: every exposed agent is a 3-good leader (Lemma E(i)) with a junk good in `π_x`; the
terminals of their blocks, one more terminal or a shared good for `k*`, carry a hitting set `H` of the sets `π_x`;
the completion `placeH` puts `H` into those terminals. -/
theorem theoremA4 (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hag : agents.Nodup)
    (hs : Strict v agents goods) (hcore : IsCore4 v agents goods) (hr : IsLast run s r)
    (hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4) :
    (∃ X, Completion agents goods s.base (needsOf v goods s) (some r) X ∧ OC v agents goods X (some r)) ∨
      ∃ k, BadCase v agents goods run s r k ∧ (relevant v k goods).length = 3 ∧
        ∀ g ∈ goods, 0 < v k g → s.pick k ≠ some g → g ∈ Wl goods s r := by
  classical
  let E := agents.filter (fun x => decide (Exposed v agents goods s r x))
  have hEm : ∀ x, x ∈ E ↔ Exposed v agents goods s r x := fun x => by
    simp only [E, List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hEnd : E.Nodup := hag.filter _
  have h3 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length = 3 := fun x hx => by
    have := hcore.2.1 x hx.1; have := hno4 x hx; omega
  have hEx : ∀ x ∈ E, x ∈ agents ∧ ¬ s.marked x ∧ x ≠ r ∧ InsAt v run (posOf run x) := fun x hx => by
    have hxE := (hEm x).mp hx
    obtain ⟨-, -, -, -, hlead⟩ := lemmaE_three hS hgd hs hr hxE (h3 x hxE)
    obtain ⟨px, hpx, hpx1⟩ := hS.phase.getElem?_posOf hxE.1
    exact ⟨hxE.1, hxE.2.1, hxE.2.2.1, hlead _ px hpx hpx1⟩
  -- the completion from a hitting set carried by enough terminals
  have hdone : ∀ (H : List G) (T : List A), (∀ h ∈ H, h ∈ goods ∧ s.base h = none) → T.Nodup →
      H.length ≤ T.length → (∀ t ∈ T, t ∈ agents ∧ t ≠ r ∧ ¬ s.marked t ∧ ¬ FrozenAt v agents goods s t) →
      (∀ x, Exposed v agents goods s r x → ∃ h ∈ H, 0 < v x h) →
      ∃ X, Completion agents goods s.base (needsOf v goods s) (some r) X ∧ OC v agents goods X (some r) :=
    fun H T hHJ hT hlen hTt hhit => ⟨placeH s r H T, completion_placeH hS hgd hr hT hlen hTt,
      oc_placeH hS hgd hs hcore hr (fun h hh => (hHJ h hh).2) (fun h hh => (hHJ h hh).1) hlen
        (fun t ht => (hTt t ht).2.1) hno4 hhit⟩
  by_cases hE0 : E = []
  · -- nobody is exposed
    refine Or.inl (hdone [] [] (by simp) List.nodup_nil (by simp) (by simp) fun x hx => ?_)
    have := (hEm x).mpr hx; rw [hE0] at this; simp at this
  obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil E hE0
  obtain ⟨g₀, -, -, -⟩ := hS.pi_nonempty hgd hs hr ((hEm x₀).mp hx₀) (h3 x₀ ((hEm x₀).mp hx₀))
  let c : A → G := fun x =>
    if h : ∃ g, g ∈ goods ∧ s.base g = none ∧ 0 < v x g then Classical.choose h else g₀
  have hc : ∀ x, Exposed v agents goods s r x → c x ∈ goods ∧ s.base (c x) = none ∧ 0 < v x (c x) := by
    intro x hx
    have h := hS.pi_nonempty hgd hs hr hx (h3 x hx)
    have h' : ∃ g, g ∈ goods ∧ s.base g = none ∧ 0 < v x g := by
      obtain ⟨g, hg, hb, hp⟩ := h; exact ⟨g, hg, hb, hp⟩
    simp only [c, h', ↓reduceDIte]
    exact Classical.choose_spec h'
  rcases hS.terminals hgd hr hEnd hEx with ⟨T, hT, hlen, hTt⟩ | ⟨k, hkE, hkB, hkF, hall, T, hT, hlen, hTt⟩
  · -- `|E|` terminals: one good of each `π_x`
    refine Or.inl (hdone (dedupL (E.map c)) T (fun h hh => ?_) hT ?_ hTt fun x hx => ?_)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedupL.mp hh)
      exact ⟨(hc x ((hEm x).mp hx)).1, (hc x ((hEm x).mp hx)).2.1⟩
    · have := length_dedupL_le (E.map c); simp at this; omega
    · exact ⟨c x, mem_dedupL.mpr (List.mem_map.mpr ⟨x, (hEm x).mpr hx, rfl⟩), (hc x hx).2.2⟩
  · by_cases hmeet : ∃ x y g, Exposed v agents goods s r x ∧ Exposed v agents goods s r y ∧ x ≠ y ∧
        g ∈ goods ∧ s.base g = none ∧ 0 < v x g ∧ 0 < v y g
    · -- two sets `π_x`, `π_y` meet: one good serves both
      obtain ⟨x, y, g, hx, hy, hxy, hg, hgb, hgx, hgy⟩ := hmeet
      let c' : A → G := fun z => if z = x ∨ z = y then g else c z
      have hc' : ∀ z, Exposed v agents goods s r z → c' z ∈ goods ∧ s.base (c' z) = none ∧ 0 < v z (c' z) := by
        intro z hz
        by_cases e : z = x ∨ z = y
        · simp only [c', e, ↓reduceIte]
          rcases e with rfl | rfl
          · exact ⟨hg, hgb, hgx⟩
          · exact ⟨hg, hgb, hgy⟩
        · simp only [c', e, ↓reduceIte]; exact hc z hz
      have hnd : ¬ (E.map c').Nodup := fun hnd => hxy (eq_of_mem_of_nodup_map hnd ((hEm x).mpr hx)
        ((hEm y).mpr hy) (by simp [c']))
      refine Or.inl (hdone (dedupL (E.map c')) T (fun h hh => ?_) hT ?_ hTt fun z hz => ?_)
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (mem_dedupL.mp hh)
        exact ⟨(hc' z ((hEm z).mp hz)).1, (hc' z ((hEm z).mp hz)).2.1⟩
      · have := length_dedupL_lt hnd; simp at this; omega
      · exact ⟨c' z, mem_dedupL.mpr (List.mem_map.mpr ⟨z, (hEm z).mpr hz, rfl⟩), (hc' z hz).2.2⟩
    · -- LB⁺'s bad case
      have hkX := (hEm k).mp hkE
      obtain ⟨y, hy, htop, -, -⟩ := lemmaE_three hS hgd hs hr hkX (h3 k hkX)
      refine Or.inr ⟨k, ⟨hkX, hkF, (hEx k hkE).2.2.2, hkB, hall, fun x y g hx hy hxy hg hgb hgx hgy =>
        hmeet ⟨x, y, g, hx, hy, hxy, hg, hgb, hgx, hgy⟩⟩, h3 k hkX, fun g hg hpos hpk => ?_⟩
      exact (htop g hg hpos fun e => hpk (by rw [hy, e])).1

/-- **Theorem A₄ for LB₄ʳ's owner step**: with `ω ≥ 1`, outside LB⁺'s bad case the owner step of LB₄ʳ has an output
with owner `r` (`Output`, the owner's needs from its bundle). -/
theorem theoremA4_output (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hag : agents.Nodup)
    (hs : Strict v agents goods) (hcore : IsCore4 v agents goods) (hr : IsLast run s r)
    (hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4)
    (hω : 1 ≤ omega v agents goods s) :
    (∃ X, Output v agents goods s (some r) X) ∨ ∃ k, BadCase v agents goods run s r k := by
  rcases theoremA4 hS hgd hag hs hcore hr hno4 with ⟨X, hC, hOC⟩ | ⟨k, hk, -⟩
  · refine Or.inl ⟨X, hC.toOwnerNeeds ((hS.inv hgd).needs), hOC, fun _ => ?_⟩
    constructor
    · intro h; cases h
    · intro h; omega
  · exact Or.inr ⟨k, hk⟩


/-- After a rotation along a need chain, every base belongs to a listed agent. -/
theorem rotate_base_mem (hS : AfterUp v agents goods run s) {c : List A} {k : A} {O : List G}
    (hch : NeedChain v agents goods s c) (hk : c.head? = some k) {g : G} {i : A}
    (h : (rotate s c O).base g = some i) : i ∈ agents := by
  simp only [rotate] at h
  split at h
  · rw [hk] at h; cases h; exact hch.2.1 k (List.mem_of_mem_head? hk)
  · split at h
    · cases h
    · rename_i a hb
      split at h
      · exact hch.2.1 i (List.mem_of_getElem? h)
      · cases h; exact hS.base_mem hb

/-- After a rotation along a need chain with a base `O` of at most two goods, every base has at most two goods. -/
theorem rotate_base_le_two (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {c : List A} {k : A}
    {O : List G} (hch : NeedChain v agents goods s c) (hk : c.head? = some k) (hl : c.getLast? = some r)
    (hO : ∀ g ∈ O, s.base g = none ∨ s.base g = some r) (hOlen : O.length ≤ 2) (i : A) :
    (baseOf goods (rotate s c O).base i).length ≤ 2 := by
  have hc := hch.1
  by_cases hic : i ∈ c
  · by_cases hik : i = k
    · subst hik
      have := List.Nodup.length_le_of_subset (l₁ := baseOf goods (rotate s c O).base i) (hgd.filter _)
        fun g hg => (rotate_base_head hc hk).mp (mem_baseOf.mp hg).2
      omega
    · have := rotate_chain_base_le_one hgd hch hk hl hO hic hik; omega
  · have hB : baseOf goods (rotate s c O).base i = baseOf goods s.base i :=
      List.filter_congr fun h _ => by simp only [rotate_base_out hl hO hic]
    rw [hB]; exact (hS.base_two hgd).1 i

/-- **Theorem B₄(c)** (`k4/c4.md` §4). In LB⁺'s bad case (no 4-good agent exposed), rotate along a need chain from
`k*` to `r` with base `O = R_k* ∩ W`. If `r` is not exposed w.r.t. `k*` after the rotation (in particular if `r` has
three goods, Theorem B₄(b)), the owner step of LB₄ʳ has an output on the rotated state, with no owner or with owner
`k*`: with `ω′ ≤ 0` the completion without owner, otherwise a completion with owner `k*` (`Output`). The exposed agents after the rotation are exposed
agents of `P` other than `k*` (Theorem B₄(b)), each with a junk good outside `O` (the sets `π_x` are disjoint); the
terminals of their blocks lie outside `B*`, off the chain, and stay terminals. -/
theorem theoremB4c (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hag : agents.Nodup)
    (hs : Strict v agents goods) (hcore : IsCore4 v agents goods) (hr : IsLast run s r)
    (hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4) {k : A} {c : List A}
    {O : List G} (hbad : BadCase v agents goods run s r k) (hch : NeedChain v agents goods s c)
    (hk : c.head? = some k) (hl : c.getLast? = some r) (hlen : 2 ≤ c.length)
    (hOd : O = relevant v k (Wl goods s r)) (hrE : ¬ Exposed v agents goods (rotate s c O) k r) :
    ∃ o X, (o = none ∨ o = some k) ∧ Output v agents goods (rotate s c O) o X := by
  classical
  obtain ⟨hkE, hkF, hkI, hkB, hall, hdisj⟩ := hbad
  have hk3 : (relevant v k goods).length = 3 := by
    have := hcore.2.1 k hkE.1; have := hno4 k hkE; omega
  obtain ⟨hRot, -, hNA', -, hWW, hexp, hchainE⟩ := theoremB4 hS hgd hs hcore hr hch hk hl hlen hkE hk3 hno4 hOd
  have hc := hch.1
  have hI := hS.inv hgd
  have hI' : Inv v agents goods (rotate s c O) := rotStep_inv hgd hI hRot
  have hkA : k ∈ agents := hkE.1
  have hkc : k ∈ c := List.mem_of_mem_head? hk
  have hO'' : ∀ g ∈ O, s.base g = none ∨ s.base g = some r := fun g hg => by
    rw [hOd] at hg; exact (mem_Wl.mp (List.mem_filter.mp hg).1).2
  have hOnd : O.Nodup := by rw [hOd]; exact (hgd.filter _).filter _
  have hOlen : O.length = 2 := by
    obtain ⟨-, -, -, hL2, -⟩ := lemmaE_three hS hgd hs hr hkE hk3; rw [hOd]; exact hL2
  have hOR : ∀ g ∈ O, 0 < v k g := fun g hg => by rw [hOd] at hg; simpa using (List.mem_filter.mp hg).2
  have hmem' : ∀ g i, (rotate s c O).base g = some i → i ∈ agents := fun g i h => rotate_base_mem hS hch hk h
  have hle2' := rotate_base_le_two hS hgd hch hk hl hO'' (by omega)
  by_cases hω : omega v agents goods (rotate s c O) ≤ 0
  · -- the completion without owner
    have hC := complete_none_exists (N := needsOf v goods (rotate s c O)) hag hgd
      (fun g _ i hb => hmem' g i hb) (fun j _ => hle2' j) hω k
    exact ⟨none, _, Or.inl rfl, hC.toOwnerNeeds hI'.needs, (fun w hw => by cases hw),
      fun _ => ⟨fun _ => hω, fun _ => rfl⟩⟩
  -- the completion with owner `k*`
  obtain ⟨Er, hErd⟩ : ∃ Er, Er = agents.filter (fun x => decide (Exposed v agents goods s r x)) := ⟨_, rfl⟩
  obtain ⟨E', hE'd⟩ : ∃ E', E' = agents.filter (fun x => decide (Exposed v agents goods (rotate s c O) k x)) :=
    ⟨_, rfl⟩
  have hErnd : Er.Nodup := by rw [hErd]; exact hag.filter _
  have hE'nd : E'.Nodup := by rw [hE'd]; exact hag.filter _
  have hErm : ∀ x, x ∈ Er ↔ Exposed v agents goods s r x := fun x => by
    rw [hErd]; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hE'm : ∀ x, x ∈ E' ↔ Exposed v agents goods (rotate s c O) k x := fun x => by
    rw [hE'd]; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  -- an exposed agent after the rotation was exposed before, is not `k*`, not `r`, and off the chain
  have hE'old : ∀ x, Exposed v agents goods (rotate s c O) k x →
      Exposed v agents goods s r x ∧ x ≠ k ∧ x ≠ r ∧ x ∉ c := by
    intro x hx
    rcases hexp x hx with ⟨h1, h2⟩ | ⟨h1, -⟩
    · have hxr : x ≠ r := fun e => hrE (e ▸ hx)
      exact ⟨h1, h2, hxr, fun hxc => hchainE x hxc hxr hx⟩
    · exact absurd (h1 ▸ hx) hrE
  have h3 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length = 3 := fun x hx => by
    have := hcore.2.1 x hx.1; have := hno4 x hx; omega
  have hEx : ∀ x ∈ Er, x ∈ agents ∧ ¬ s.marked x ∧ x ≠ r ∧ InsAt v run (posOf run x) := fun x hx => by
    have hxE := (hErm x).mp hx
    obtain ⟨-, -, -, -, hlead⟩ := lemmaE_three hS hgd hs hr hxE (h3 x hxE)
    obtain ⟨px, hpx, hpx1⟩ := hS.phase.getElem?_posOf hxE.1
    exact ⟨hxE.1, hxE.2.1, hxE.2.2.1, hlead _ px hpx hpx1⟩
  obtain ⟨T, hTnd, hTt, hTB, hlenT⟩ := hS.terminals_out hgd hr hErnd hEx
  have hkEr : k ∈ Er := (hErm k).mpr hkE
  have hlenT' : Er.length ≤ T.length + 1 := by
    rcases hlenT with h | ⟨-, -, -, h, -⟩ <;> omega
  -- `|E′| ≤ |E_r| − 1`
  have hE'len : E'.length + 1 ≤ Er.length := by
    have hsub : ∀ x ∈ k :: E', x ∈ Er := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hkEr
      · exact (hErm x).mpr (hE'old x ((hE'm x).mp hx)).1
    have hnd : (k :: E').Nodup := List.nodup_cons.mpr ⟨fun hm => (hE'old k ((hE'm k).mp hm)).2.1 rfl, hE'nd⟩
    have := List.Nodup.length_le_of_subset hnd hsub
    simpa using this
  -- the terminals stay terminals: they are off the chain
  have hTc : ∀ t ∈ T, t ∉ c := by
    intro t ht htc
    obtain ⟨pk, hpk, hpk1⟩ := hS.phase.getElem?_posOf hkA
    have hk0 : c[0]? = some pk.1 := by rw [← List.head?_eq_getElem?, hk, hpk1]
    obtain ⟨tt, pt, hpt, hpt1, hbl, -⟩ := hS.chain_pos hgd hch hpk hk0 _ t (getElem?_idxOf htc)
    refine hTB k hkEr hkB t ht ?_
    rw [← hpt1, hS.phase.posOf_eq hpt]; exact hbl
  have hTt' : ∀ t ∈ T, t ∈ agents ∧ t ≠ k ∧
      ¬ Frozen agents goods (rotate s c O).base (needsOf v goods (rotate s c O)) t ∧
      (baseOf goods (rotate s c O).base t).length ≤ 1 := by
    intro t ht
    obtain ⟨hta, -, htm, htF⟩ := hTt t ht
    have htc := hTc t ht
    have hB : baseOf goods (rotate s c O).base t = baseOf goods s.base t :=
      List.filter_congr fun h _ => by simp only [rotate_base_out hl hO'' htc]
    refine ⟨hta, fun e => htc (e ▸ hkc), fun ⟨y, hy, hna⟩ => htF ⟨htm, y, hB ▸ hy, hNA' y hna⟩, ?_⟩
    rw [hB]; exact (hS.base_two hgd).2.2 t htm
  -- one junk good of each `π_x` outside `O`
  obtain ⟨g₀, -, -, -⟩ := hS.pi_nonempty hgd hs hr hkE hk3
  let c₀ : A → G := fun x =>
    if h : ∃ g, g ∈ goods ∧ s.base g = none ∧ 0 < v x g then Classical.choose h else g₀
  have hc₀ : ∀ x, Exposed v agents goods s r x → x ≠ k →
      c₀ x ∈ goods ∧ (rotate s c O).base (c₀ x) = none ∧ 0 < v x (c₀ x) := by
    intro x hx hxk
    have h' : ∃ g, g ∈ goods ∧ s.base g = none ∧ 0 < v x g := by
      obtain ⟨g, hg, hb, hp⟩ := hS.pi_nonempty hgd hs hr hx (h3 x hx); exact ⟨g, hg, hb, hp⟩
    have hsp : c₀ x ∈ goods ∧ s.base (c₀ x) = none ∧ 0 < v x (c₀ x) := by
      simp only [c₀, h', ↓reduceDIte]; exact Classical.choose_spec h'
    refine ⟨hsp.1, (rotate_base_none hc hk hl).mpr ⟨fun hm => ?_, Or.inl hsp.2.1⟩, hsp.2.2⟩
    exact hdisj x k (c₀ x) hx hkE hxk hsp.1 hsp.2.1 hsp.2.2 (hOR _ hm)
  obtain ⟨H, hHd⟩ : ∃ H, H = dedupL (E'.map c₀) := ⟨_, rfl⟩
  have hHJ : ∀ h ∈ H, h ∈ goods ∧ (rotate s c O).base h = none := fun h hh => by
    rw [hHd] at hh
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedupL.mp hh)
    obtain ⟨h1, h2, -, -⟩ := hE'old x ((hE'm x).mp hx)
    exact ⟨(hc₀ x h1 h2).1, (hc₀ x h1 h2).2.1⟩
  have hlenH : H.length ≤ T.length := by
    have := length_dedupL_le (E'.map c₀); rw [hHd]; simp at this; omega
  have hC := completion_placeH_gen (N := needsOf v goods (rotate s c O)) hgd hmem' hle2' hkA
    (fun ⟨y, hy, _⟩ => by
      have := List.Nodup.length_le_of_subset (l₁ := O) hOnd fun g hg =>
        (by rw [← hy]; exact mem_baseOf.mpr ⟨(by rw [hOd] at hg; exact (mem_Wl.mp (List.mem_filter.mp hg).1).1),
          (rotate_base_head hc hk).mpr hg⟩ : g ∈ [y])
      simp at this; omega) hTnd hlenH hTt'
  have hOC := oc_placeH_gen (v := v) (agents := agents) hgd (fun h hh => (hHJ h hh).2) (fun h hh => (hHJ h hh).1) hlenH
    (fun t ht => (hTt' t ht).2.1) fun j hj hjk => ?_
  · exact ⟨some k, _, Or.inr rfl, hC.toOwnerNeeds hI'.needs, hOC, fun _ => ⟨(fun h => by cases h), fun h => absurd h hω⟩⟩
  -- every agent other than `k*` is safe
  by_cases hjm : (rotate s c O).marked j
  · -- an upgraded agent off the chain keeps its envy-free base
    have hjc : j ∉ c := by
      rcases hjm with h | ⟨-, h⟩
      · rw [hk] at h; exact absurd (Option.some.inj h).symm hjk
      · exact h
    have hjm0 : s.marked j := (rotate_out hjc).2.mp hjm
    have hB : baseOf goods (rotate s c O).base j = baseOf goods s.base j :=
      List.filter_congr fun h _ => by simp only [rotate_base_out hl hO'' hjc]
    refine Or.inl fun L hL hLg => ?_
    rw [hB]
    exact (hS.efBase hgd j hjm0).value_le hL fun g hg =>
      ⟨(hLg g hg).1, fun hb => (hLg g hg).2 ((rotate_base_out hl hO'' hjc).mpr hb)⟩
  by_cases hjE : Exposed v agents goods (rotate s c O) k j
  · -- an exposed agent: exposed before, off the chain, three goods, its top held, a good in `H`
    obtain ⟨hjE0, -, -, hjc⟩ := hE'old j hjE
    have hjm0 : ¬ s.marked j := hjE0.2.1
    obtain ⟨y, hy, htop, -, -⟩ := lemmaE_three hS hgd hs hr hjE0 (h3 j hjE0)
    have hB : baseOf goods (rotate s c O).base j = baseOf goods s.base j :=
      List.filter_congr fun h _ => by simp only [rotate_base_out hl hO'' hjc]
    refine Or.inr (Or.inr ⟨y, by rw [hB, hI.unmarked j hj hjm0, hy]; rfl, hI.pickRel j hj hjm0 y hy,
      h3 j hjE0, fun g hg hpos hgy => (htop g hg hpos hgy).2, c₀ j,
      by rw [hHd]; exact mem_dedupL.mpr (List.mem_map.mpr ⟨j, (hE'm j).mpr hjE, rfl⟩), (hc₀ j hjE0 hjk).2.2⟩)
  · exact Or.inr (Or.inl fun ht => hjE ⟨hj, hjm, hjk, ht⟩)


end theoremA

/-! ## Corollary C₄⁰ -/

section corollary
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- In LB⁺'s bad case a need chain from `k*` to `r` exists (A4), with at least two agents (`k*` is frozen). -/
theorem BadCase.chain {run : List (A × Option G)} {s : LState A G} {r k : A}
    (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) (hbad : BadCase v agents goods run s r k) :
    ∃ c, NeedChain v agents goods s c ∧ c.head? = some k ∧ c.getLast? = some r ∧ 2 ≤ c.length := by
  obtain ⟨hkE, hkF, -, -, hall, -⟩ := hbad
  obtain ⟨pk, hpk, hpk1⟩ := hS.phase.getElem?_posOf hkE.1
  obtain ⟨c, e, te, pe, hch, hck, hce, -, -, -, -, hef, -⟩ :=
    hS.exists_chain hgd _ _ pk (Nat.le_refl _) hpk (hpk1 ▸ hkE.2.1)
  rw [hpk1] at hck
  have her : e = r := hall c e hch hck hce
  subst her
  refine ⟨c, hch, hck, hce, Classical.byContradiction fun h => ?_⟩
  match c, hck, hce, h with
  | [], hck, _, _ => simp at hck
  | [x], hck, hce, _ =>
    simp at hck hce; subst hck; subst hce; exact hef hkF
  | _ :: _ :: _, _, _, h => simp at h

/-- **Corollary C₄⁰** (`k4/c4.md` §4). Take LB₄ʳ's Phase 1(τ) (LB's key) followed by envy-free upgrades to the
fixpoint, and its last unmarked agent `r`. If no 4-good agent is exposed w.r.t. `r`, and in LB⁺'s bad case `r` is not
exposed after LB⁺'s rotation along some need chain from `k*` to `r` (automatic if `r` has three goods, Theorem
B₄(b)), then LB₄ʳ(τ) succeeds: the owner step on the upgraded state (Theorem A₄, or no owner when `ω ≤ 0`), or after
one rotation (Theorems B₄ (a), (c)). -/
theorem corollaryC40 (hag : agents.Nodup) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hcore : IsCore4 v agents goods) {τ : List Nat} {s : LState A G}
    (hup : UpRun v agents goods .envyFree (phase1State v agents goods τ) s) {r : A}
    (hr : IsLast (phase1 v agents goods agents.length agents goods τ) s r)
    (hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4)
    (hrot : ∀ k, BadCase v agents goods (phase1 v agents goods agents.length agents goods τ) s r k →
      ∃ c, NeedChain v agents goods s c ∧ c.head? = some k ∧ c.getLast? = some r ∧ 2 ≤ c.length ∧
        ¬ Exposed v agents goods (rotate s c (relevant v k (Wl goods s r))) k r) :
    Succeeds v agents goods τ := by
  have hS : AfterUp v agents goods (phase1 v agents goods agents.length agents goods τ) s :=
    ⟨phase1_phaseRun hag hgd τ, hup⟩
  have hI := hS.inv hgd
  have hbase2 := hS.base_two hgd
  by_cases hω : omega v agents goods s ≤ 0
  · -- no owner
    have hC := complete_none_exists (N := needsOf v goods s) hag hgd (fun g _ i hb => hS.base_mem hb)
      (fun j _ => hbase2.1 j) hω r
    exact ⟨.envyFree, s, s, none, _, hup, RotReach.refl 3 s,
      hC.toOwnerNeeds hI.needs, (fun w hw => by cases hw), fun _ => ⟨fun _ => hω, fun _ => rfl⟩⟩
  rcases theoremA4_output hS hgd hag hs hcore hr hno4 (by omega) with ⟨X, hX⟩ | ⟨k, hbad⟩
  · exact ⟨.envyFree, s, s, some r, X, hup, RotReach.refl 3 s, hX⟩
  -- the bad case: one rotation along a need chain from `k*` to `r`
  obtain ⟨c, hch, hck, hce, hlen, hrE⟩ := hrot k hbad
  have hk3 : (relevant v k goods).length = 3 := by
    have := hcore.2.1 k hbad.1.1; have := hno4 k hbad.1; omega
  obtain ⟨hRot, -⟩ := theoremB4 hS hgd hs hcore hr hch hck hce hlen hbad.1 hk3 hno4 rfl
  obtain ⟨o, X, -, hX⟩ := theoremB4c hS hgd hag hs hcore hr hno4 hbad hch hck hce hlen rfl hrE
  exact ⟨.envyFree, s, _, o, X, hup, RotReach.step 2 s _ _ hRot (RotReach.refl 2 _), hX⟩

/-- **Corollary C₄⁰, as `k4/c4.md` states it** (proof/k4-c4 at 96ff1d0): after LB₄ʳ's Phase 1(τ) and envy-free
upgrades, if `ω ≤ 0`, or no 4-good agent is exposed w.r.t. `r` and, in LB⁺'s bad case, `r` is not exposed after the
rotation along some need chain `k* → r`, then LB₄ʳ(τ) succeeds. With `ω ≤ 0` the completion without owner is an
output; otherwise `corollaryC40`. -/
theorem corollaryC40' (hag : agents.Nodup) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hcore : IsCore4 v agents goods) {τ : List Nat} {s : LState A G}
    (hup : UpRun v agents goods .envyFree (phase1State v agents goods τ) s) {r : A}
    (hr : IsLast (phase1 v agents goods agents.length agents goods τ) s r)
    (h : omega v agents goods s ≤ 0 ∨
      ((∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4) ∧
       ∀ k, BadCase v agents goods (phase1 v agents goods agents.length agents goods τ) s r k →
        ∃ c, NeedChain v agents goods s c ∧ c.head? = some k ∧ c.getLast? = some r ∧ 2 ≤ c.length ∧
          ¬ Exposed v agents goods (rotate s c (relevant v k (Wl goods s r))) k r)) :
    Succeeds v agents goods τ := by
  rcases h with hω | ⟨hno4, hrot⟩
  · have hS : AfterUp v agents goods (phase1 v agents goods agents.length agents goods τ) s :=
      ⟨phase1_phaseRun hag hgd τ, hup⟩
    have hI := hS.inv hgd
    have hbase2 := hS.base_two hgd
    have hC := complete_none_exists (N := needsOf v goods s) hag hgd (fun g _ i hb => hS.base_mem hb)
      (fun j _ => hbase2.1 j) hω r
    exact ⟨.envyFree, s, s, none, _, hup, RotReach.refl 3 s,
      hC.toOwnerNeeds hI.needs, (fun w hw => by cases hw), fun _ => ⟨fun _ => hω, fun _ => rfl⟩⟩
  · exact corollaryC40 hag hgd hs hcore hup hr hno4 hrot

/-- **LB₄ʳ never fails when every agent has three goods** (`k4/c4.md` §4: at k = 3 the hypotheses of Corollary C₄⁰
always hold, so it contains LB⁺'s Theorem C for LB₄ʳ's search): on a strict profile of a k = 4 core whose agents all
have three relevant goods, LB₄ʳ(τ) succeeds for every τ. -/
theorem succeeds_of_three (hag : agents.Nodup) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hcore : IsCore4 v agents goods) (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3) (τ : List Nat) :
    Succeeds v agents goods τ := by
  classical
  have hR := phase1_phaseRun (v := v) hag hgd τ
  obtain ⟨s, hup⟩ := upRun_exists (v := v) (agents := agents) (goods := goods) .envyFree _
    (phase1State v agents goods τ) (Nat.le_refl _)
  have hS : AfterUp v agents goods (phase1 v agents goods agents.length agents goods τ) s := ⟨hR, hup⟩
  have hne : phase1 v agents goods agents.length agents goods τ ≠ [] := fun h => by
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil agents (fun e => by have := hcore.1; rw [e] at this; simp at this)
    obtain ⟨p, hp, -⟩ := (hR.mem i).mp hi
    rw [h] at hp; simp at hp
  obtain ⟨r, hr⟩ := hS.exists_last hne
  have hno4 : ∀ x, Exposed v agents goods s r x → (relevant v x goods).length ≠ 4 := fun x hx => by
    rw [h3 x hx.1]; omega
  refine corollaryC40 hag hgd hs hcore hup hr hno4 fun k hbad => ?_
  obtain ⟨c, hch, hck, hce, hlen⟩ := hbad.chain hS hgd
  refine ⟨c, hch, hck, hce, hlen, fun hrE => ?_⟩
  have hk3 := h3 k hbad.1.1
  obtain ⟨-, -, -, -, -, hexp, -⟩ := theoremB4 hS hgd hs hcore hr hch hck hce hlen hbad.1 hk3 hno4 rfl
  rcases hexp r hrE with ⟨h, -⟩ | ⟨-, h4⟩
  · exact h.2.2.1 rfl
  · obtain ⟨tr, pr, hpr, hpr1, -, -⟩ := id hr
    rw [h3 r (hpr1 ▸ hS.phase.agent_mem hpr)] at h4; cases h4

end corollary

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.Threatened.mono
#print axioms EFX.LB4R.AfterUp.W_not_NA
#print axioms EFX.LB4R.lemmaE
#print axioms EFX.LB4R.lemmaE_three
#print axioms EFX.LB4R.lemmaE_four
#print axioms EFX.LB4R.rotate_Wl
#print axioms EFX.LB4R.needsOf_rotate
#print axioms EFX.LB4R.rotate_valid
#print axioms EFX.LB4R.AfterUp.chain_pos
#print axioms EFX.LB4R.rotate_exposed
#print axioms EFX.LB4R.rotate_exposed_chain
#print axioms EFX.LB4R.rotate_last_not_exposed
#print axioms EFX.LB4R.theoremB4
#print axioms EFX.LB4R.completion_placeH
#print axioms EFX.LB4R.oc_placeH
#print axioms EFX.LB4R.AfterUp.pi_nonempty
#print axioms EFX.LB4R.AfterUp.terminals
#print axioms EFX.LB4R.theoremA4
#print axioms EFX.LB4R.theoremA4_output
#print axioms EFX.LB4R.completion_placeH_gen
#print axioms EFX.LB4R.oc_placeH_gen
#print axioms EFX.LB4R.AfterUp.terminals_out
#print axioms EFX.LB4R.rotate_base_le_two
#print axioms EFX.LB4R.theoremB4c
#print axioms EFX.LB4R.BadCase.chain
#print axioms EFX.LB4R.corollaryC40
#print axioms EFX.LB4R.corollaryC40'
#print axioms EFX.LB4R.succeeds_of_three
