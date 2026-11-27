import EFX.LB4R

/-!
# Conjecture NOF, certified by LB₄ʳ's owner step (`k4/sdc.md` §11–§13)

Conjecture NOF (ledger K4.SDC.NOF) says: run serial dictatorship in the *neediest-first* order (at each step the
unprocessed agent whose best available good beats its next two by the most picks, with or without LB's R1 priority);
either its picks extend to an EFX₀ allocation, or the picks of the same order with one agent moved to the end do.
On every instance tested, a candidate of NOF also has an **LB₄ʳ output**: after a run of upgrades of one of LB₄ʳ's
policies, the owner step of `EFX.LB4R.Output` succeeds (ledger K4.SDC.NOF.K, EVIDENCE).

This file states that certified form and proves it implies TARGET₄. Contents:
- `sdList`: serial dictatorship in a given order; `sdList_spec`: it satisfies `EFX.LB4R.RunSpec`.
- `runState`: the state of a run (picks as bases, nobody marked), as `EFX.LB4R.phase1State` but for any run;
  `runState_inv`: the invariant `EFX.LB4R.Inv` holds for the state of every run satisfying `RunSpec`.
  The proofs follow `EFX.LB4R.phase1State_*`, which only use `RunSpec`.
- `need`, `nofChoose`, `runWith`, `nofOrder`: the neediest-first order (with R1 priority if `r1`);
  `nofCandidates`: that order and its variants with one agent moved last; every candidate is a permutation.
- `ConjSDCK`: some order's serial dictatorship, after upgrades, has an LB₄ʳ output (SD-C certified by LB₄ʳ);
  `ConjNOFK r1`: the same for one of NOF's candidates. Both are `Prop`s, not axioms.
- `target4_of_conjSDCK`, `target4_of_conjNOFK`: each implies TARGET₄ (through `EFX.LB4R.target4_of_C4exists`).
-/

set_option autoImplicit false

namespace EFX
namespace NOF

open LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Serial dictatorship in a given order -/

/-- Serial dictatorship in the order `ord`: each agent in turn takes its favourite available good. -/
def sdList (v : A → G → Nat) : List A → List G → List (A × Option G)
  | [], _ => []
  | x :: xs, G0 => (x, fav v x G0) :: sdList v xs (takeOut G0 (fav v x G0))

omit [DecidableEq A] in
/-- Serial dictatorship satisfies Phase 1's run specification (on the agents of the order). -/
theorem sdList_spec (v : A → G → Nat) : ∀ (ord : List A) (G0 : List G), ord.Nodup → G0.Nodup →
    RunSpec v ord G0 ord.length (sdList v ord G0)
  | [], _, _, _ => ⟨by simp [sdList], by simp [sdList], fun _ x hx => by simp at hx, by simp [sdList],
      by simp [sdList], by simp [sdList]⟩
  | x :: xs, G0, hU, hG => by
    have hxs : xs.Nodup := (List.nodup_cons.mp hU).2
    have hxn : x ∉ xs := (List.nodup_cons.mp hU).1
    have hG' : (takeOut G0 (fav v x G0)).Nodup := by
      cases fav v x G0 with
      | none => exact hG
      | some y => exact hG.erase y
    have T := sdList_spec v xs (takeOut G0 (fav v x G0)) hxs hG'
    have hrun : sdList v (x :: xs) G0 = (x, fav v x G0) :: sdList v xs (takeOut G0 (fav v x G0)) := rfl
    rw [hrun]
    have hsub : ∀ g, g ∈ takeOut G0 (fav v x G0) → g ∈ G0 := by
      intro g hg
      cases hf : fav v x G0 with
      | none => rw [hf] at hg; exact hg
      | some y => rw [hf] at hg; exact List.mem_of_mem_erase hg
    have hxT : ∀ p ∈ sdList v xs (takeOut G0 (fav v x G0)), p.1 ≠ x :=
      fun p hp e => hxn (e ▸ T.mem p hp)
    have hyT : ∀ y, fav v x G0 = some y → y ∉ takeOut G0 (fav v x G0) := by
      intro y hy
      rw [hy]
      exact List.Nodup.not_mem_erase hG
    refine ⟨fun p hp => ?_, ?_, fun _ z hz => ?_, fun p hp y hpy => ?_, fun p hp q hq y hpy hqy => ?_,
      fun p hp g hg hpos hnone => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (T.mem p hp)
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hm => by
        obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
        exact hxT p hp hpx, T.nodup⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨p, hp, hpz⟩ := T.cover (Nat.le_refl _) z hz
        exact ⟨p, List.mem_cons_of_mem _ hp, hpz⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · obtain ⟨h1, h2, -⟩ := fav_some hpy
        exact ⟨h1, h2⟩
      · obtain ⟨h1, h2⟩ := T.pickMem p hp y hpy
        exact ⟨hsub y h1, h2⟩
    · rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact absurd (T.pickMem q hq y hqy).1 (hyT y hpy)
      · exact absurd (T.pickMem p hp y hpy).1 (hyT y hqy)
      · exact T.pickInj p hp q hq y hpy hqy
    · rcases List.mem_cons.mp hp with rfl | hp
      · cases hf : fav v x G0 with
        | none => exact absurd hpos (fav_none hf g hg)
        | some y => exact ⟨y, rfl, (fav_some hf).2.2 g hg hpos⟩
      · have hgT : g ∈ takeOut G0 (fav v x G0) := by
          cases hf : fav v x G0 with
          | none => exact hg
          | some y =>
            have hne : g ≠ y := fun e => hnone (x, fav v x G0) List.mem_cons_self (by rw [hf, e])
            exact (List.mem_erase_of_ne hne).mpr hg
        exact T.best p hp g hgT hpos fun q hq => hnone q (List.mem_cons_of_mem _ hq)

omit [DecidableEq A] [DecidableEq G] in
/-- The run specification only depends on the agents up to permutation. -/
theorem runSpec_of_perm {v : A → G → Nat} {U U' : List A} {G0 : List G} {run : List (A × Option G)}
    (h : RunSpec v U G0 U.length run) (hp : U.Perm U') : RunSpec v U' G0 U'.length run :=
  ⟨fun p hq => hp.mem_iff.mp (h.mem p hq), h.nodup,
    fun _ x hx => h.cover (Nat.le_refl _) x (hp.mem_iff.mpr hx), h.pickMem, h.pickInj, h.best⟩

/-! ## The state of a run -/

/-- The state of a run: every pick is a base, nobody is marked (`EFX.LB4R.phase1State` for an arbitrary run). -/
def runState (run : List (A × Option G)) : LState A G :=
  { base := fun g => (run.find? (fun p => p.2 == some g)).map Prod.fst
    pick := fun i => ((run.find? (fun p => p.1 == i)).map Prod.snd).join
    marked := fun _ => False }

section runState
variable {v : A → G → Nat} {agents : List A} {goods : List G} {run : List (A × Option G)}

theorem runState_pick (hR : RunSpec v agents goods agents.length run) {p : A × Option G} (hp : p ∈ run) :
    (runState run).pick p.1 = p.2 := by
  simp only [runState]
  cases hq : run.find? (fun q => q.1 == p.1) with
  | none => exact absurd (List.find?_eq_none.mp hq p hp) (by simp)
  | some q =>
    have hqm := List.mem_of_find?_eq_some hq
    have hq1 : q.1 = p.1 := by simpa using List.find?_some hq
    rw [eq_of_mem_of_nodup_map hR.nodup hqm hp hq1]
    simp

theorem runState_pick_none {i : A} (h : ∀ p ∈ run, p.1 ≠ i) : (runState run).pick i = none := by
  simp only [runState]
  rw [List.find?_eq_none.mpr fun p hp => by simpa using h p hp]
  simp

theorem runState_base (hR : RunSpec v agents goods agents.length run) {g : G} {i : A} :
    (runState run).base g = some i ↔ ∃ p ∈ run, p.1 = i ∧ p.2 = some g := by
  simp only [runState]
  constructor
  · intro h
    cases hq : run.find? (fun q => q.2 == some g) with
    | none => rw [hq] at h; simp at h
    | some q =>
      rw [hq] at h; simp at h
      exact ⟨q, List.mem_of_find?_eq_some hq, h, by simpa using List.find?_some hq⟩
  · rintro ⟨p, hp, hpi, hpg⟩
    cases hq : run.find? (fun q => q.2 == some g) with
    | none => exact absurd (List.find?_eq_none.mp hq p hp) (by simp [hpg])
    | some q =>
      have hqg : q.2 = some g := by simpa using List.find?_some hq
      rw [hR.pickInj q (List.mem_of_find?_eq_some hq) p hp g hqg hpg]
      simp [hpi]

theorem runState_baseOf (hR : RunSpec v agents goods agents.length run) (hgd : goods.Nodup) (i : A) :
    baseOf goods (runState run).base i = ((runState run).pick i).toList := by
  by_cases hi : ∃ p ∈ run, p.1 = i
  · obtain ⟨p, hp, rfl⟩ := hi
    rw [runState_pick hR hp]
    have hb : ∀ g, (runState run).base g = some p.1 ↔ p.2 = some g := fun g => by
      rw [runState_base hR]
      constructor
      · rintro ⟨q, hq, hq1, hq2⟩
        rw [← eq_of_mem_of_nodup_map hR.nodup hq hp hq1]; exact hq2
      · intro h; exact ⟨p, hp, rfl, h⟩
    cases hp2 : p.2 with
    | none =>
      simp only [Option.toList_none]
      exact List.filter_eq_nil_iff.mpr fun g _ h => by
        have := (hb g).mp (by simpa using h); rw [hp2] at this; cases this
    | some y =>
      simp only [Option.toList_some]
      exact filter_eq_single hgd (hR.pickMem p hp y hp2).1 fun g _ => by
        rw [decide_eq_true_iff, hb g, hp2]; simp [eq_comm]
  · rw [runState_pick_none fun p hp e => hi ⟨p, hp, e⟩]
    exact List.filter_eq_nil_iff.mpr fun g _ h => by
      obtain ⟨p, hp, hpi, -⟩ := (runState_base hR).mp (by simpa using h)
      exact hi ⟨p, hp, hpi⟩

/-- **The invariant holds after any run of serial dictatorship** (any order, any selection rule): the state is a
valid pre-allocation in which every agent's base is exactly its pick. As `EFX.LB4R.phase1State_inv`. -/
theorem runState_inv (hR : RunSpec v agents goods agents.length run) (hgd : goods.Nodup) :
    Inv v agents goods (runState run) := by
  have hbo := runState_baseOf hR hgd
  refine ⟨⟨fun g hg hna => ?_, fun i h2 => ?_⟩, fun i _ _ => hbo i, fun i _ _ y hy => ?_⟩
  · -- (V1): an unpicked good needed by `i` was available at `i`'s turn
    obtain ⟨hgg, hgb⟩ := mem_junk.mp hg
    obtain ⟨i, hi, hN⟩ := hna
    rcases hN with ⟨hm, -⟩ | ⟨-, -, hpos, hlt⟩
    · exact hm
    obtain ⟨p, hp, rfl⟩ := hR.cover (Nat.le_refl _) i hi
    have hnone : ∀ q ∈ run, q.2 ≠ some g := fun q hq hqg => by
      have := (runState_base hR (g := g) (i := q.1)).mpr ⟨q, hq, rfl, hqg⟩
      rw [hgb] at this; cases this
    obtain ⟨y, hy, hle⟩ := hR.best p hp g hgg hpos hnone
    have := hlt y (by rw [runState_pick hR hp, hy])
    omega
  · -- (V2): every base has at most one good
    rw [hbo i] at h2
    cases hp : (runState run).pick i <;> rw [hp] at h2 <;> simp at h2
  · by_cases hi : ∃ p ∈ run, p.1 = i
    · obtain ⟨p, hp, rfl⟩ := hi
      rw [runState_pick hR hp] at hy
      exact (hR.pickMem p hp y hy).2
    · rw [runState_pick_none fun p hp e => hi ⟨p, hp, e⟩] at hy; cases hy

end runState

/-! ## The neediest-first order and NOF's candidates -/

/-- The need of `i` on the available goods `G0`: the value of its best available good minus the values of its next
two (missing ones count 0). -/
def need (v : A → G → Nat) (i : A) (G0 : List G) : Int :=
  let vs := ((relevant v i G0).map (v i)).mergeSort (fun a b => decide (b ≤ a))
  (vs.getD 0 0 : Int) - (vs.getD 1 0 : Int) - (vs.getD 2 0 : Int)

/-- The first element of a list with the largest `f`. -/
def argmaxBy (f : A → Int) : List A → Option A
  | [] => none
  | a :: l =>
    match argmaxBy f l with
    | none => some a
    | some b => if f b ≤ f a then some a else some b

omit [DecidableEq A] in
theorem argmaxBy_mem {f : A → Int} : ∀ {l : List A} {a : A}, argmaxBy f l = some a → a ∈ l
  | [], _, h => by simp [argmaxBy] at h
  | b :: l, a, h => by
    simp only [argmaxBy] at h
    cases hb : argmaxBy f l with
    | none => simp only [hb, Option.some.injEq] at h; subst h; exact List.mem_cons_self
    | some c =>
      simp only [hb] at h
      by_cases hc : f c ≤ f b
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h; subst h; exact List.mem_cons_self
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h; subst h
        exact List.mem_cons_of_mem _ (argmaxBy_mem hb)

/-- The neediest-first choice among the unprocessed agents `U`: with `r1`, only the agents that lost a good if there
are any (LB's R1 priority); the largest need, the first in `U` on ties. -/
def nofChoose (v : A → G → Nat) (goods : List G) (r1 : Bool) (U : List A) (G0 : List G) : Option A :=
  let L := U.filter (lost v goods G0)
  argmaxBy (fun i => need v i G0) (if r1 && !L.isEmpty then L else U)

/-- Serial dictatorship driven by a selection rule (the first unprocessed agent if the rule returns nothing outside
the unprocessed agents). -/
def runWith (v : A → G → Nat) (choose : List A → List G → Option A) :
    Nat → List A → List G → List (A × Option G)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, u :: us, G0 =>
    let x := match choose (u :: us) G0 with
      | some a => if a ∈ u :: us then a else u
      | none => u
    (x, fav v x G0) :: runWith v choose fuel ((u :: us).erase x) (takeOut G0 (fav v x G0))

/-- The agents of a selection-rule run, in order, are a permutation of the unprocessed agents (enough fuel). -/
theorem runWith_perm (v : A → G → Nat) (choose : List A → List G → Option A) :
    ∀ (fuel : Nat) (U : List A) (G0 : List G), U.length ≤ fuel → ((runWith v choose fuel U G0).map Prod.fst).Perm U
  | 0, U, _, h => by
    have : U = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [runWith]
  | fuel + 1, [], _, _ => by simp [runWith]
  | fuel + 1, u :: us, G0, h => by
    simp only [runWith, List.map_cons]
    generalize hx : (match choose (u :: us) G0 with
      | some a => if a ∈ u :: us then a else u
      | none => u) = x
    have hxm : x ∈ u :: us := by
      rw [← hx]
      cases choose (u :: us) G0 with
      | none => exact List.mem_cons_self
      | some a =>
        simp only
        by_cases ha : a ∈ u :: us
        · simp [ha]
        · simp [ha]
    have hlen : ((u :: us).erase x).length ≤ fuel := by
      rw [List.length_erase_of_mem hxm]; simp at h ⊢; omega
    exact ((runWith_perm v choose fuel _ _ hlen).cons x).trans (List.perm_cons_erase hxm).symm

/-- **The neediest-first order** on all agents (with R1 priority if `r1`). -/
def nofOrder (v : A → G → Nat) (agents : List A) (goods : List G) (r1 : Bool) : List A :=
  (runWith v (nofChoose v goods r1) agents.length agents goods).map Prod.fst

/-- **NOF's candidate orders**: the neediest-first order, and the same order with one agent moved to the end. -/
def nofCandidates (v : A → G → Nat) (agents : List A) (goods : List G) (r1 : Bool) : List (List A) :=
  nofOrder v agents goods r1 :: (nofOrder v agents goods r1).map
    (fun o => (nofOrder v agents goods r1).erase o ++ [o])

theorem nofOrder_perm (v : A → G → Nat) (agents : List A) (goods : List G) (r1 : Bool) :
    (nofOrder v agents goods r1).Perm agents :=
  runWith_perm v _ agents.length agents goods (Nat.le_refl _)

/-- Every candidate order is a permutation of the agents. -/
theorem nofCandidates_perm {v : A → G → Nat} {agents : List A} {goods : List G} {r1 : Bool} {ord : List A}
    (h : ord ∈ nofCandidates v agents goods r1) : ord.Perm agents := by
  have hπ := nofOrder_perm v agents goods r1
  rcases List.mem_cons.mp h with rfl | h
  · exact hπ
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h
    exact (List.perm_append_singleton o _).trans ((List.perm_cons_erase ho).symm.trans hπ)

/-! ## The conjectures and their consequences -/

/-- **SD-C certified by LB₄ʳ** (ledger K4.SDC.K): for every strict profile of every k = 4 core, some order's serial
dictatorship, after a run of upgrades of one of LB₄ʳ's policies, has an output of the owner step. -/
def ConjSDCK (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods →
      ∃ ord : List A, ord.Perm agents ∧ ∃ (pol : Policy) (s : LState A G) (o : Option A) (X : G → A),
        UpRun v agents goods pol (runState (sdList v ord goods)) s ∧ Output v agents goods s o X

/-- **Conjecture NOF certified by LB₄ʳ** (ledger K4.SDC.NOF.K): the order can be taken among NOF's candidates (the
neediest-first order, with R1 priority if `r1`, or that order with one agent moved last). -/
def ConjNOFK (A G : Type) [DecidableEq A] [DecidableEq G] (r1 : Bool) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods →
      ∃ ord ∈ nofCandidates v agents goods r1, ∃ (pol : Policy) (s : LState A G) (o : Option A) (X : G → A),
        UpRun v agents goods pol (runState (sdList v ord goods)) s ∧ Output v agents goods s o X

/-- NOF's certified form implies SD-C's. -/
theorem conjSDCK_of_conjNOFK {r1 : Bool} (h : ConjNOFK A G r1) : ConjSDCK A G := by
  intro agents goods v hag hgd hc hs
  obtain ⟨ord, hord, rest⟩ := h agents goods v hag hgd hc hs
  exact ⟨ord, nofCandidates_perm hord, rest⟩

/-- **SD-C certified by LB₄ʳ ⟹ C₄∃**: the state of any serial dictatorship satisfies LB₄ʳ's invariant, upgrades keep
it, and every output is then a sound completion. -/
theorem C4exists_of_conjSDCK (h : ConjSDCK A G) : TheoremC4exists A G := by
  intro agents goods v hag hgd hc hs
  obtain ⟨ord, hperm, pol, s, o, X, hup, hout⟩ := h agents goods v hag hgd hc hs
  have hR : RunSpec v agents goods agents.length (sdList v ord goods) :=
    runSpec_of_perm (sdList_spec v ord goods (hperm.nodup_iff.mpr hag) hgd) hperm
  have hinv := upRun_inv hup (runState_inv hR hgd)
  exact ⟨s.base, needsOf v goods s, o, X, hinv.sound hout⟩

/-- **SD-C certified by LB₄ʳ ⟹ TARGET₄.** -/
theorem target4_of_conjSDCK (I : Inst) (hn : 0 < I.n) (h : ConjSDCK (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4exists I hn (C4exists_of_conjSDCK h) hk

/-- **Conjecture NOF certified by LB₄ʳ ⟹ TARGET₄** (with or without R1 priority). -/
theorem target4_of_conjNOFK (I : Inst) (hn : 0 < I.n) {r1 : Bool} (h : ConjNOFK (Fin I.n) (Fin I.m) r1)
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjSDCK I hn (conjSDCK_of_conjNOFK h) hk

/-- **LB₄ʳ with the neediest-first Phase 1** (ledger K4.SDC.NF1, `k4/sdc.md` §16): for every strict profile of every
k = 4 core, the state of the neediest-first run (with R1 priority if `r1`), after a run of upgrades of some policy and
at most `d` rotations (`EFX.LB4R.RotReach`), has an output.  This is LB₄ʳ's `Succeeds` with Phase 1 replaced by the
neediest-first run.  The data refute `r1 = true, d = 1` and support `r1 = false, d = 1`. -/
def ConjNFR (A G : Type) [DecidableEq A] [DecidableEq G] (r1 : Bool) (d : Nat) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods →
      ∃ (pol : Policy) (s₁ s : LState A G) (o : Option A) (X : G → A),
        UpRun v agents goods pol (runState (sdList v (nofOrder v agents goods r1) goods)) s₁ ∧
        RotReach v agents goods d s₁ s ∧ Output v agents goods s o X

/-- **LB₄ʳ with the neediest-first Phase 1 ⟹ C₄∃**: the run's state satisfies the invariant (`runState_inv`), upgrades
and rotations keep it (`upRun_inv`, `rotReach_inv`), and every output is then a sound completion. -/
theorem C4exists_of_conjNFR {r1 : Bool} {d : Nat} (h : ConjNFR A G r1 d) : TheoremC4exists A G := by
  intro agents goods v hag hgd hc hs
  obtain ⟨pol, s₁, s, o, X, hup, hrot, hout⟩ := h agents goods v hag hgd hc hs
  have hperm := nofOrder_perm v agents goods r1
  have hR : RunSpec v agents goods agents.length (sdList v (nofOrder v agents goods r1) goods) :=
    runSpec_of_perm (sdList_spec v _ goods (hperm.nodup_iff.mpr hag) hgd) hperm
  have hinv := rotReach_inv hgd hrot (upRun_inv hup (runState_inv hR hgd))
  exact ⟨s.base, needsOf v goods s, o, X, hinv.sound hout⟩

/-- **LB₄ʳ with the neediest-first Phase 1 and at most `d` rotations ⟹ TARGET₄.** -/
theorem target4_of_conjNFR (I : Inst) (hn : 0 < I.n) {r1 : Bool} {d : Nat} (h : ConjNFR (Fin I.n) (Fin I.m) r1 d)
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4exists I hn (C4exists_of_conjNFR h) hk

/-- **Rotation completeness** (ledger K4.SDC.RC, `k4/sdc.md` §23): for every strict profile of every k = 4 core and
*every* order of the agents, the state of that order's serial dictatorship, after a run of upgrades of some policy and
some finite number of rotations, has an output.  (Proposition H, ledger K4.C4.R, shows the number of rotations cannot
be bounded for a fixed order; here it is existentially quantified.) -/
def ConjRC (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      ∃ (pol : Policy) (s₁ s : LState A G) (d : Nat) (o : Option A) (X : G → A),
        UpRun v agents goods pol (runState (sdList v ord goods)) s₁ ∧
        RotReach v agents goods d s₁ s ∧ Output v agents goods s o X

/-- **Rotation completeness ⟹ C₄∃** (it is used for one order only: the agents' own list). -/
theorem C4exists_of_conjRC (h : ConjRC A G) : TheoremC4exists A G := by
  intro agents goods v hag hgd hc hs
  obtain ⟨pol, s₁, s, d, o, X, hup, hrot, hout⟩ := h agents goods v hag hgd hc hs agents (List.Perm.refl _)
  have hR : RunSpec v agents goods agents.length (sdList v agents goods) := sdList_spec v agents goods hag hgd
  have hinv := rotReach_inv hgd hrot (upRun_inv hup (runState_inv hR hgd))
  exact ⟨s.base, needsOf v goods s, o, X, hinv.sound hout⟩

/-- **Rotation completeness ⟹ TARGET₄.** -/
theorem target4_of_conjRC (I : Inst) (hn : 0 < I.n) (h : ConjRC (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4exists I hn (C4exists_of_conjRC h) hk

end NOF
end EFX

#print axioms EFX.NOF.sdList_spec
#print axioms EFX.NOF.runState_inv
#print axioms EFX.NOF.nofCandidates_perm
#print axioms EFX.NOF.C4exists_of_conjSDCK
#print axioms EFX.NOF.target4_of_conjSDCK
#print axioms EFX.NOF.target4_of_conjNOFK
#print axioms EFX.NOF.C4exists_of_conjNFR
#print axioms EFX.NOF.target4_of_conjNFR
#print axioms EFX.NOF.C4exists_of_conjRC
#print axioms EFX.NOF.target4_of_conjRC
