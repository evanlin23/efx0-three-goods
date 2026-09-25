import EFX.LB4RRun

/-!
# Exposure, Lemma E, Theorem A₄ and Theorem B₄ (`k4/c4.md` §2–§4, ledger K4.C4.AB (Lean))

The reviewed building blocks of `k4/c4.md` (on proof/k4-c4), stated for LB₄ʳ's states after a run of Phase 1 and
envy-free upgrades to the fixpoint (`EFX.LB4R.AfterUp`). `k4/c4.md` states them for every run of Phase 1; `AfterUp`
takes any run (`EFX.LB4R.PhaseRun`: any P-step order, any insertion steps), so LB₄ʳ's fixed key is a special case
(`EFX.LB4R.phase1_phaseRun`).

- `Wl goods s r`: **W = B_r ∪ J**, the goods in no base or in `r`'s base.
- `Threatened v x L H`: `x` holding `H` strongly envies `L` (some `h ∈ L` has `v_x(L ∖ {h}) > v_x(H)`), and
  `Threatened.mono`, its monotonicity.
- `Exposed v agents goods s r x`: `x` is unmarked, `x ≠ r`, and threatened by `W` with its base (§2).
- `W_not_NA`: no good of `W` is needed (J by (V1), `Y_r` by (A1)).
- **Lemma E** (`lemmaE`, `lemmaE_three`, `lemmaE_four`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

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

/-- **Monotonicity** (`k4/c4.md` §1): a smaller bundle and a better own bundle can only remove a threat. -/
theorem Threatened.mono {x : A} {L L' H H' : List G} (h : Threatened v x L' H') (hL : L'.Sublist L)
    (hH : value v x H ≤ value v x H') : Threatened v x L H := by
  obtain ⟨h, hh, hlt⟩ := h
  exact ⟨h, hL.subset hh, Nat.lt_of_le_of_lt hH (Nat.lt_of_lt_of_le hlt (value_sublist v x (hL.erase h)))⟩

theorem mem_Wl {goods : List G} {s : LState A G} {r : A} {g : G} :
    g ∈ Wl goods s r ↔ g ∈ goods ∧ (s.base g = none ∨ s.base g = some r) := by
  simp [Wl]

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

/-- On a strict profile, two goods an agent values are worth different amounts to it. -/
theorem strict_ne {agents : List A} {goods : List G} (hs : Strict v agents goods) {x : A} (hx : x ∈ agents)
    {g y : G} (hg : g ∈ goods) (hy : y ∈ goods) (hgy : g ≠ y) (hpos : 0 < v x g) : v x g ≠ v x y := by
  intro e
  have := hs x hx [g] [y] (List.singleton_sublist.mpr hg) (List.singleton_sublist.mpr hy)
    (by simpa using hgy) (by simpa using e)
  simp at this; omega

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

end rotation

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
