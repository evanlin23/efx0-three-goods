import EFX.LB4R

/-!
# The structure of a run of Phase 1 (`proofs/lb_last_step.md` §1, `k4/c4.md` §1; for `EFX/LB4R.lean`)

`k4/c4.md` §2–§4 use Phase 1 through the invariants (I1), (I2), (I3), (B1), (B2) of `proofs/lb_last_step.md` §1, which
hold for *every* run of Phase 1: any order of the steps for agents that lost a good (P-steps), any choice at the
insertion steps. This file states what a run is, by the position of each step, and proves that LB₄ʳ's Phase 1
(`EFX.LB4R.phase1`, with LB's key and τ) is one (`phase1_phaseRun`). Everything proved from `PhaseRun` holds for LB₄ʳ's
fixed key in particular, and for every other P-step order.

A run is a list of steps `(agent, pick)` in processing order (`PhaseRun`):
- every listed agent is processed exactly once;
- the pick at step `t` is a good the agent values that nobody picked before `t`;
- `fav`: every good the agent values that nobody picked before `t` is worth at most its pick (the agent takes its
  favourite remaining good);
- `step`: the agent of step `t` has lost a good (`LostAt`: some good it values was picked before `t`), or `t` is an
  insertion step (`InsAt`: no agent processed at `t` or later has lost a good).

Blocks: `blockId t` counts the insertion steps up to `t`; a block is a maximal set of steps with the same count, its
*leader* is the agent of its insertion step.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EFX
namespace LB4R

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Runs -/

/-- The pick at step `t`. -/
def pickAt (run : List (A × Option G)) (t : Nat) : Option G := run[t]?.bind Prod.snd

/-- `g` was picked at some step before `t`. -/
def PickedBefore (run : List (A × Option G)) (t : Nat) (g : G) : Prop := ∃ t' < t, pickAt run t' = some g

/-- Before step `t` of a run started from the pool `G0`, agent `x` has lost a good: some good of `goods` it values
is not in `G0` or was picked before `t`. -/
def LostFrom (v : A → G → Nat) (goods G0 : List G) (run : List (A × Option G)) (t : Nat) (x : A) : Prop :=
  ∃ g ∈ goods, 0 < v x g ∧ (g ∉ G0 ∨ PickedBefore run t g)

/-- A run from the unprocessed agents `U` and the pool `G0`, by the position of each step. -/
structure RunFrom (v : A → G → Nat) (goods : List G) (U : List A) (G0 : List G) (run : List (A × Option G)) :
    Prop where
  mem : ∀ p ∈ run, p.1 ∈ U
  nodup : (run.map Prod.fst).Nodup
  pick : ∀ (t : Nat) (p : A × Option G) (y : G), run[t]? = some p → p.2 = some y → y ∈ G0 ∧ 0 < v p.1 y ∧ ¬ PickedBefore run t y
  fav : ∀ (t : Nat) (p : A × Option G), run[t]? = some p → ∀ g ∈ G0, 0 < v p.1 g → ¬ PickedBefore run t g →
    ∃ y, p.2 = some y ∧ v p.1 g ≤ v p.1 y
  step : ∀ (t : Nat) (p : A × Option G), run[t]? = some p → LostFrom v goods G0 run t p.1 ∨
    ∀ (t' : Nat) (q : A × Option G), t ≤ t' → run[t']? = some q → ¬ LostFrom v goods G0 run t q.1

theorem not_pickedBefore_zero (run : List (A × Option G)) (g : G) : ¬ PickedBefore run 0 g :=
  fun ⟨_, ht, _⟩ => Nat.not_lt_zero _ ht

theorem pickedBefore_cons {p : A × Option G} {rest : List (A × Option G)} {t : Nat} {g : G} :
    PickedBefore (p :: rest) (t + 1) g ↔ p.2 = some g ∨ PickedBefore rest t g := by
  constructor
  · rintro ⟨t', ht', h⟩
    cases t' with
    | zero => left; simpa [pickAt] using h
    | succ t' => right; exact ⟨t', by omega, by simpa [pickAt] using h⟩
  · rintro (h | ⟨t', ht', h⟩)
    · exact ⟨0, by omega, by simp [pickAt, h]⟩
    · exact ⟨t' + 1, by omega, by simpa [pickAt] using h⟩

theorem mem_takeOut {G0 : List G} (hG : G0.Nodup) {y : Option G} {g : G} :
    g ∈ takeOut G0 y ↔ g ∈ G0 ∧ y ≠ some g := by
  cases y with
  | none => simp [takeOut]
  | some y =>
    simp only [takeOut, ne_eq, Option.some.injEq]
    rw [hG.mem_erase_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, fun e => h1 e.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun e => h2 e.symm, h1⟩

theorem lostFrom_cons {v : A → G → Nat} {goods G0 : List G} (hG : G0.Nodup) {p : A × Option G}
    {rest : List (A × Option G)} {t : Nat} {x : A} :
    LostFrom v goods G0 (p :: rest) (t + 1) x ↔ LostFrom v goods (takeOut G0 p.2) rest t x := by
  unfold LostFrom
  apply exists_congr; intro g
  simp only [pickedBefore_cons, mem_takeOut hG]
  constructor
  · rintro ⟨hg, hpos, h⟩
    refine ⟨hg, hpos, ?_⟩
    rcases h with h | h | h
    · exact Or.inl fun hh => h hh.1
    · exact Or.inl fun hh => hh.2 h
    · exact Or.inr h
  · rintro ⟨hg, hpos, h⟩
    refine ⟨hg, hpos, ?_⟩
    rcases h with h | h
    · by_cases hG0 : g ∈ G0
      · exact Or.inr (Or.inl (Classical.byContradiction fun hn => h ⟨hG0, hn⟩))
      · exact Or.inl hG0
    · exact Or.inr (Or.inr h)

theorem argmin_eq_none {f : A → Nat} : ∀ {l : List A}, argmin f l = none → l = []
  | [], _ => rfl
  | a :: l, h => by
    unfold argmin at h
    split at h
    · cases h
    · split at h <;> cases h

theorem lost_iff {v : A → G → Nat} {goods G0 : List G} {i : A} :
    lost v goods G0 i = true ↔ ∃ g ∈ goods, 0 < v i g ∧ g ∉ G0 := by
  unfold lost relevant
  simp [List.any_eq_true]

/-- **Phase 1 of LB₄ʳ is a run** (from any unprocessed agents and pool). -/
theorem phase1_runFrom (v : A → G → Nat) (agents : List A) (goods : List G) :
    ∀ fuel (U : List A) (G0 : List G) (τ : List Nat), U.Nodup → G0.Nodup →
      RunFrom v goods U G0 (phase1 v agents goods fuel U G0 τ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro U G0 τ _ _
    refine ⟨by simp [phase1], by simp [phase1], by simp [phase1], by simp [phase1], by simp [phase1]⟩
  | succ fuel ih =>
    intro U G0 τ hU hG
    cases U with
    | nil =>
      refine ⟨by simp [phase1], by simp [phase1], by simp [phase1], by simp [phase1], by simp [phase1]⟩
    | cons u us =>
      have hx := nextAgent_mem (v := v) (agents := agents) (goods := goods) (G0 := G0) (τ := τ)
        (List.mem_cons_self (a := u) (l := us))
      generalize hnx : nextAgent v agents goods (u :: us) G0 τ u = nx at hx
      obtain ⟨x, τ'⟩ := nx
      simp only at hx
      have hrun : phase1 v agents goods (fuel + 1) (u :: us) G0 τ =
          (x, fav v x G0) :: phase1 v agents goods fuel ((u :: us).erase x) (takeOut G0 (fav v x G0)) τ' := by
        simp only [phase1, hnx]
      rw [hrun]
      have hG' : (takeOut G0 (fav v x G0)).Nodup := by
        cases fav v x G0 with
        | none => exact hG
        | some y => exact hG.erase y
      have T := ih ((u :: us).erase x) (takeOut G0 (fav v x G0)) τ' (hU.erase x) hG'
      generalize phase1 v agents goods fuel ((u :: us).erase x) (takeOut G0 (fav v x G0)) τ' = rest at T ⊢
      have hxT : ∀ p ∈ rest, p.1 ≠ x :=
        fun p hp e => (List.Nodup.not_mem_erase hU) (e ▸ T.mem p hp)
      refine ⟨fun p hp => ?_, ?_, fun t p y hp hpy => ?_, fun t p hp g hg hpos hnp => ?_, fun t p hp => ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact hx
        · exact List.mem_of_mem_erase (T.mem p hp)
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨fun hm => by
          obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
          exact hxT p hp hpx, T.nodup⟩
      · cases t with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          obtain ⟨h1, h2, -⟩ := fav_some hpy
          exact ⟨h1, h2, not_pickedBefore_zero _ _⟩
        | succ t =>
          simp only [List.getElem?_cons_succ] at hp
          obtain ⟨h1, h2, h3⟩ := T.pick t p y hp hpy
          refine ⟨((mem_takeOut hG).mp h1).1, h2, fun hpb => ?_⟩
          rcases pickedBefore_cons.mp hpb with h | h
          · exact ((mem_takeOut hG).mp h1).2 h
          · exact h3 h
      · cases t with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          cases hf : fav v x G0 with
          | none => exact absurd hpos (fav_none hf g hg)
          | some y => exact ⟨y, rfl, (fav_some hf).2.2 g hg hpos⟩
        | succ t =>
          simp only [List.getElem?_cons_succ] at hp
          have hnp' : ¬ PickedBefore rest t g := fun h => hnp (pickedBefore_cons.mpr (Or.inr h))
          have hg' : g ∈ takeOut G0 (fav v x G0) :=
            (mem_takeOut hG).mpr ⟨hg, fun h => hnp (pickedBefore_cons.mpr (Or.inl h))⟩
          exact T.fav t p hp g hg' hpos hnp'
      · cases t with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          simp only
          unfold nextAgent at hnx
          split at hnx
          · rename_i x' hx'
            simp only [Prod.mk.injEq] at hnx
            obtain ⟨rfl, -⟩ := hnx
            obtain ⟨g, hg, hpos, hG0⟩ := lost_iff.mp (List.mem_filter.mp (argmin_mem hx')).2
            exact Or.inl ⟨g, hg, hpos, Or.inl hG0⟩
          · rename_i hnone
            have hemp := argmin_eq_none hnone
            refine Or.inr fun t' q _ hq ⟨g, hg, hpos, h⟩ => ?_
            have hqU : q.1 ∈ u :: us := by
              cases t' with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
                subst hq; exact hx
              | succ t' =>
                simp only [List.getElem?_cons_succ] at hq
                exact List.mem_of_mem_erase (T.mem q (List.mem_of_getElem? hq))
            have hl : lost v goods G0 q.1 = true := by
              rcases h with h | h
              · exact lost_iff.mpr ⟨g, hg, hpos, h⟩
              · exact absurd h (not_pickedBefore_zero _ _)
            have : q.1 ∈ (u :: us).filter (lost v goods G0) := List.mem_filter.mpr ⟨hqU, hl⟩
            rw [hemp] at this; simp at this
        | succ t =>
          simp only [List.getElem?_cons_succ] at hp
          rcases T.step t p hp with h | h
          · exact Or.inl ((lostFrom_cons hG).mpr h)
          · refine Or.inr fun t' q ht' hq hl => ?_
            cases t' with
            | zero => omega
            | succ t' =>
              simp only [List.getElem?_cons_succ] at hq
              exact h t' q (by omega) hq ((lostFrom_cons hG).mp hl)

/-! ## Runs of Phase 1 from the start -/

/-- Before step `t`, agent `x` has lost a good: some good it values was picked before `t`. -/
def LostAt (v : A → G → Nat) (run : List (A × Option G)) (t : Nat) (x : A) : Prop :=
  ∃ g, 0 < v x g ∧ PickedBefore run t g

/-- Step `t` is an insertion step (B1): no agent processed at step `t` or later has lost a good before `t`. -/
def InsAt (v : A → G → Nat) (run : List (A × Option G)) (t : Nat) : Prop :=
  ∀ (t' : Nat) (q : A × Option G), t ≤ t' → run[t']? = some q → ¬ LostAt v run t q.1

/-- **A run of Phase 1** (`k4/lb4.md` §2, `proofs/lb_last_step.md` §1), by the position of each step: every listed
agent is processed once; each takes a good it values that nobody took before, its favourite among those; and each
step processes an agent that lost a good, or is an insertion step. -/
structure PhaseRun (v : A → G → Nat) (agents : List A) (goods : List G) (run : List (A × Option G)) : Prop where
  mem : ∀ x, x ∈ agents ↔ ∃ p ∈ run, p.1 = x
  nodup : (run.map Prod.fst).Nodup
  pick : ∀ (t : Nat) (p : A × Option G) (y : G), run[t]? = some p → p.2 = some y → y ∈ goods ∧ 0 < v p.1 y ∧ ¬ PickedBefore run t y
  fav : ∀ (t : Nat) (p : A × Option G), run[t]? = some p → ∀ g ∈ goods, 0 < v p.1 g → ¬ PickedBefore run t g →
    ∃ y, p.2 = some y ∧ v p.1 g ≤ v p.1 y
  step : ∀ (t : Nat) (p : A × Option G), run[t]? = some p → LostAt v run t p.1 ∨ InsAt v run t

theorem lostFrom_iff {v : A → G → Nat} {goods : List G} {run : List (A × Option G)}
    (hpick : ∀ (t : Nat) (p : A × Option G) (y : G), run[t]? = some p → p.2 = some y → y ∈ goods)
    {t : Nat} {x : A} :
    LostFrom v goods goods run t x ↔ LostAt v run t x := by
  constructor
  · rintro ⟨g, _, hpos, h | h⟩
    · contradiction
    · exact ⟨g, hpos, h⟩
  · rintro ⟨g, hpos, ⟨t', ht', h⟩⟩
    unfold pickAt at h
    cases hq : run[t']? with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      exact ⟨g, hpick t' q g hq h, hpos, Or.inr ⟨t', ht', by simp [pickAt, hq, h]⟩⟩

/-- **LB₄ʳ's Phase 1 (with LB's key and any τ) is a run of Phase 1.** -/
theorem phase1_phaseRun {v : A → G → Nat} {agents : List A} {goods : List G} (hag : agents.Nodup)
    (hgd : goods.Nodup) (τ : List Nat) : PhaseRun v agents goods (phase1 v agents goods agents.length agents goods τ) := by
  have R := phase1_runFrom v agents goods agents.length agents goods τ hag hgd
  have S := phase1_spec v agents goods agents.length agents goods τ hag hgd
  have hpick : ∀ (t : Nat) (p : A × Option G) (y : G), (phase1 v agents goods agents.length agents goods τ)[t]? =
      some p → p.2 = some y → y ∈ goods := fun t p y hp hy => (R.pick t p y hp hy).1
  refine ⟨fun x => ⟨fun hx => S.cover (Nat.le_refl _) x hx, fun ⟨p, hp, hpx⟩ => hpx ▸ R.mem p hp⟩, R.nodup,
    R.pick, R.fav, fun t p hp => ?_⟩
  rcases R.step t p hp with h | h
  · exact Or.inl ((lostFrom_iff hpick).mp h)
  · exact Or.inr fun t' q ht' hq hl => h t' q ht' hq ((lostFrom_iff hpick).mpr hl)

/-- The state after a run of Phase 1: each agent's pick is its base, nobody is marked. -/
def runState (run : List (A × Option G)) : LState A G :=
  { base := fun g => (run.find? (fun p => p.2 == some g)).map Prod.fst
    pick := fun i => ((run.find? (fun p => p.1 == i)).map Prod.snd).join
    marked := fun _ => False }

theorem phase1State_eq (v : A → G → Nat) (agents : List A) (goods : List G) (τ : List Nat) :
    phase1State v agents goods τ = runState (phase1 v agents goods agents.length agents goods τ) := rfl

section run
variable {v : A → G → Nat} {agents : List A} {goods : List G} {run : List (A × Option G)}

theorem pickAt_of_getElem? {t : Nat} {p : A × Option G} (hp : run[t]? = some p) : pickAt run t = p.2 := by
  simp [pickAt, hp]

/-- An agent is processed at one step only. -/
theorem PhaseRun.pos_unique (hR : PhaseRun v agents goods run) {t t' : Nat} {p q : A × Option G}
    (hp : run[t]? = some p) (hq : run[t']? = some q) (h : p.1 = q.1) : t = t' := by
  have ht : t < run.length := (List.getElem?_eq_some_iff.mp hp).1
  have ht' : t' < run.length := (List.getElem?_eq_some_iff.mp hq).1
  have h1 : (run.map Prod.fst)[t]? = some p.1 := by simp [hp]
  have h2 : (run.map Prod.fst)[t']? = some q.1 := by simp [hq]
  rw [← h] at h2
  exact (List.Nodup.getElem?_inj (by simpa using ht) hR.nodup).mp (h1.trans h2.symm)

/-- A good is picked at one step only. -/
theorem PhaseRun.pick_unique (hR : PhaseRun v agents goods run) {t t' : Nat} {p q : A × Option G} {y : G}
    (hp : run[t]? = some p) (hq : run[t']? = some q) (hpy : p.2 = some y) (hqy : q.2 = some y) : t = t' := by
  rcases Nat.lt_trichotomy t t' with h | h | h
  · exact absurd ⟨t, h, by rw [pickAt_of_getElem? hp, hpy]⟩ (hR.pick t' q y hq hqy).2.2
  · exact h
  · exact absurd ⟨t', h, by rw [pickAt_of_getElem? hq, hqy]⟩ (hR.pick t p y hp hpy).2.2

/-- Every listed agent is processed at some step. -/
theorem PhaseRun.exists_pos (hR : PhaseRun v agents goods run) {x : A} (hx : x ∈ agents) :
    ∃ (t : Nat) (p : A × Option G), run[t]? = some p ∧ p.1 = x := by
  obtain ⟨p, hp, rfl⟩ := (hR.mem x).mp hx
  obtain ⟨t, ht, hpt⟩ := List.getElem_of_mem hp
  exact ⟨t, p, by rw [List.getElem?_eq_getElem ht, hpt], rfl⟩

theorem PhaseRun.agent_mem (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) : p.1 ∈ agents :=
  (hR.mem p.1).mpr ⟨p, List.mem_of_getElem? hp, rfl⟩

theorem runState_pick (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G} (hp : run[t]? = some p) :
    (runState run).pick p.1 = p.2 := by
  have hpm := List.mem_of_getElem? hp
  simp only [runState]
  cases hq : run.find? (fun q => q.1 == p.1) with
  | none => exact absurd (List.find?_eq_none.mp hq p hpm) (by simp)
  | some q =>
    have hqm := List.mem_of_find?_eq_some hq
    have hq1 : q.1 = p.1 := by simpa using List.find?_some hq
    rw [eq_of_mem_of_nodup_map hR.nodup hqm hpm hq1]
    simp

theorem runState_base (hR : PhaseRun v agents goods run) {g : G} {i : A} :
    (runState run).base g = some i ↔ ∃ (t : Nat) (p : A × Option G), run[t]? = some p ∧ p.1 = i ∧ p.2 = some g := by
  simp only [runState]
  constructor
  · intro h
    cases hq : run.find? (fun q => q.2 == some g) with
    | none => rw [hq] at h; simp at h
    | some q =>
      rw [hq] at h; simp at h
      obtain ⟨t, ht, htq⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hq)
      exact ⟨t, q, by rw [List.getElem?_eq_getElem ht, htq], h, by simpa using List.find?_some hq⟩
  · rintro ⟨t, p, hp, hpi, hpg⟩
    cases hq : run.find? (fun q => q.2 == some g) with
    | none => exact absurd (List.find?_eq_none.mp hq p (List.mem_of_getElem? hp)) (by simp [hpg])
    | some q =>
      have hqg : q.2 = some g := by simpa using List.find?_some hq
      obtain ⟨t', ht', htq⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hq)
      have hq' : run[t']? = some q := by rw [List.getElem?_eq_getElem ht', htq]
      have := hR.pick_unique hp hq' hpg hqg
      subst this
      rw [hp] at hq'; cases hq'
      simp [hpi]

theorem runState_base_none (hR : PhaseRun v agents goods run) {g : G} :
    (runState run).base g = none ↔ ∀ t, pickAt run t ≠ some g := by
  constructor
  · intro h t ht
    unfold pickAt at ht
    cases hq : run[t]? with
    | none => rw [hq] at ht; cases ht
    | some q =>
      rw [hq] at ht
      have := (runState_base hR (g := g) (i := q.1)).mpr ⟨t, q, hq, rfl, by simpa using ht⟩
      rw [h] at this; cases this
  · intro h
    cases hb : (runState run).base g with
    | none => rfl
    | some i =>
      obtain ⟨t, p, hp, -, hpg⟩ := (runState_base hR).mp hb
      exact absurd (by rw [pickAt_of_getElem? hp, hpg]) (h t)

theorem runState_baseOf (hR : PhaseRun v agents goods run) (hgd : goods.Nodup) (i : A) :
    baseOf goods (runState run).base i = ((runState run).pick i).toList := by
  by_cases hi : i ∈ agents
  · obtain ⟨t, p, hp, rfl⟩ := hR.exists_pos hi
    rw [runState_pick hR hp]
    have hb : ∀ g, (runState run).base g = some p.1 ↔ p.2 = some g := fun g => by
      rw [runState_base hR]
      constructor
      · rintro ⟨t', q, hq, hq1, hq2⟩
        rw [← hR.pos_unique hp hq hq1.symm] at hq
        rw [hp] at hq; cases hq; exact hq2
      · intro h; exact ⟨t, p, hp, rfl, h⟩
    cases hp2 : p.2 with
    | none =>
      simp only [Option.toList_none]
      exact List.filter_eq_nil_iff.mpr fun g _ h => by
        have := (hb g).mp (by simpa using h); rw [hp2] at this; cases this
    | some y =>
      simp only [Option.toList_some]
      exact filter_eq_single hgd (hR.pick t p y hp hp2).1 fun g _ => by
        rw [decide_eq_true_iff, hb g, hp2]; simp [eq_comm]
  · have hnone : (runState run).pick i = none := by
      simp only [runState]
      rw [List.find?_eq_none.mpr fun p hp => by
        have := hR.agent_mem (t := (List.getElem_of_mem hp).choose)
          (by rw [List.getElem?_eq_getElem (List.getElem_of_mem hp).choose_spec.1,
            (List.getElem_of_mem hp).choose_spec.2])
        simp only [beq_iff_eq]; exact fun e => hi (e ▸ this)]
      simp
    rw [hnone]
    exact List.filter_eq_nil_iff.mpr fun g _ h => by
      obtain ⟨t, p, hp, hpi, -⟩ := (runState_base hR).mp (by simpa using h)
      exact hi (hpi ▸ hR.agent_mem hp)

/-- (I1) with the favourite rule: a good that the agent of step `t` values more than its pick (or at all, if it has
none) was picked before `t`. -/
theorem PhaseRun.pickedBefore_of_prefers (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) {g : G} (hg : g ∈ goods) (hpos : 0 < v p.1 g)
    (hlt : ∀ y, p.2 = some y → v p.1 y < v p.1 g) : PickedBefore run t g :=
  Classical.byContradiction fun hn => by
    obtain ⟨y, hy, hle⟩ := hR.fav t p hp g hg hpos hn
    have := hlt y hy; omega

/-- **The state after a run of Phase 1 satisfies the invariant** of LB₄ʳ's reachable states. -/
theorem runState_inv (hR : PhaseRun v agents goods run) (hgd : goods.Nodup) :
    Inv v agents goods (runState run) := by
  have hbo := runState_baseOf hR hgd
  refine ⟨⟨fun g hg hna => ?_, fun i h2 => ?_⟩, fun i _ _ => hbo i, fun i hi _ y hy => ?_⟩
  · obtain ⟨hgg, hgb⟩ := mem_junk.mp hg
    obtain ⟨i, hi, hN⟩ := hna
    rcases hN with ⟨hm, -⟩ | ⟨-, -, hpos, hlt⟩
    · exact hm
    obtain ⟨t, p, hp, rfl⟩ := hR.exists_pos hi
    obtain ⟨t', ht', hpk⟩ := hR.pickedBefore_of_prefers hp hgg hpos fun y hy =>
      hlt y (by rw [runState_pick hR hp, hy])
    exact (runState_base_none hR).mp hgb t' hpk
  · rw [hbo i] at h2
    cases hp : (runState run).pick i <;> rw [hp] at h2 <;> simp at h2
  · obtain ⟨t, p, hp, rfl⟩ := hR.exists_pos hi
    rw [runState_pick hR hp] at hy
    exact (hR.pick t p y hp hy).2.1

/-! ### Insertion steps and blocks -/

/-- The first step is an insertion step. -/
theorem insAt_zero : InsAt v run 0 := fun _ _ _ _ ⟨_, _, h⟩ => not_pickedBefore_zero _ _ h

/-- (I3): an agent that has lost no good at its turn is processed at an insertion step. -/
theorem PhaseRun.insAt_of_not_lost (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) (h : ¬ LostAt v run t p.1) : InsAt v run t :=
  (hR.step t p hp).resolve_left h

/-- Steps `t₁ ≤ t₂` are in the same block: no insertion step in `(t₁, t₂]`. -/
def SameBlock (v : A → G → Nat) (run : List (A × Option G)) (t₁ t₂ : Nat) : Prop :=
  t₁ ≤ t₂ ∧ ∀ t, t₁ < t → t ≤ t₂ → ¬ InsAt v run t

theorem SameBlock.refl (t : Nat) : SameBlock v run t t := ⟨Nat.le_refl t, fun _ h1 h2 => absurd h2 (by omega)⟩

theorem SameBlock.trans {t₁ t₂ t₃ : Nat} (h₁ : SameBlock v run t₁ t₂) (h₂ : SameBlock v run t₂ t₃) :
    SameBlock v run t₁ t₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun t ht1 ht3 => by
    by_cases h : t ≤ t₂
    · exact h₁.2 t ht1 h
    · exact h₂.2 t (by omega) ht3⟩

theorem SameBlock.mono {t₁ t₂ t₁' t₂' : Nat} (h : SameBlock v run t₁ t₂) (h1 : t₁ ≤ t₁') (h2 : t₁' ≤ t₂')
    (h3 : t₂' ≤ t₂) : SameBlock v run t₁' t₂' :=
  ⟨h2, fun t ht1 ht2 => h.2 t (by omega) (by omega)⟩

/-- Every step lies in the block of an insertion step at or before it (its leader's step). -/
theorem exists_leader (t : Nat) : ∃ t₀, InsAt v run t₀ ∧ SameBlock v run t₀ t := by
  induction t with
  | zero => exact ⟨0, insAt_zero, SameBlock.refl 0⟩
  | succ t ih =>
    by_cases h : InsAt v run (t + 1)
    · exact ⟨t + 1, h, SameBlock.refl _⟩
    · obtain ⟨t₀, h₀, hb⟩ := ih
      exact ⟨t₀, h₀, ⟨by have := hb.1; omega, fun t' h1 h2 => by
        by_cases e : t' = t + 1
        · exact e ▸ h
        · exact hb.2 t' h1 (by omega)⟩⟩

/-- A block has one leader: two insertion steps are in different blocks. -/
theorem leader_unique {t₀ t₁ t : Nat} (h₀ : InsAt v run t₀) (h₁ : InsAt v run t₁) (hb₀ : SameBlock v run t₀ t)
    (hb₁ : SameBlock v run t₁ t) : t₀ = t₁ := by
  rcases Nat.lt_trichotomy t₀ t₁ with h | h | h
  · exact absurd h₁ (hb₀.2 t₁ h hb₁.1)
  · exact h
  · exact absurd h₀ (hb₁.2 t₀ h hb₀.1)

/-- Steps in the same block as a common later or earlier step are in the same block (in order). -/
theorem SameBlock.of_common {t₁ t₂ t : Nat} (h₁ : SameBlock v run t₁ t) (h₂ : SameBlock v run t₂ t)
    (h : t₁ ≤ t₂) : SameBlock v run t₁ t₂ := h₁.mono (Nat.le_refl _) h h₂.1

/-- **(B2)**: a good that the agent of step `t` values more than its pick (or at all, if it has none) was picked at
an earlier step of the same block. -/
theorem PhaseRun.b2 (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G} (hp : run[t]? = some p)
    {g : G} (hg : g ∈ goods) (hpos : 0 < v p.1 g) (hlt : ∀ y, p.2 = some y → v p.1 y < v p.1 g) :
    ∃ (t' : Nat) (q : A × Option G), run[t']? = some q ∧ q.2 = some g ∧ t' < t ∧ SameBlock v run t' t := by
  obtain ⟨t', ht', hpk⟩ := hR.pickedBefore_of_prefers hp hg hpos hlt
  unfold pickAt at hpk
  cases hq : run[t']? with
  | none => rw [hq] at hpk; cases hpk
  | some q =>
    rw [hq] at hpk
    refine ⟨t', q, hq, hpk, ht', Nat.le_of_lt ht', fun t'' h1 h2 hins => ?_⟩
    exact hins t p h2 hp ⟨g, hpos, t', h1, by simp [pickAt, hq, hpk]⟩

end run

/-! ## Envy-free upgrades -/

section upgrades
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- The value of a list without repetitions is at most that of any list containing its goods. -/
theorem value_le_of_subset (i : A) : ∀ {L₁ L₂ : List G}, L₁.Nodup → (∀ g ∈ L₁, g ∈ L₂) →
    value v i L₁ ≤ value v i L₂
  | [], _, _, _ => by simp
  | a :: t, L₂, hnd, hsub => by
    obtain ⟨hat, htn⟩ := List.nodup_cons.mp hnd
    have ha : a ∈ L₂ := hsub a List.mem_cons_self
    have ht : ∀ g ∈ t, g ∈ L₂.erase a := fun g hg =>
      (List.mem_erase_of_ne (fun e => by subst e; exact hat hg)).mpr (hsub g (List.mem_cons_of_mem _ hg))
    rw [value_cons, LB4.value_erase (v := v) (i := i) ha]
    have := value_le_of_subset i htn ht
    omega

/-- `k`'s base is envy-free: `k` values its other relevant goods together at most as much as its base. -/
def EFBase (v : A → G → Nat) (goods : List G) (s : LState A G) (k : A) : Prop :=
  value v k ((relevant v k goods).filter (fun h => s.base h ≠ some k)) ≤ value v k (baseOf goods s.base k)

/-- An envy-free base is never threatened: every list of other goods (without repetitions) is worth at most the
base. -/
theorem EFBase.value_le {s : LState A G} {k : A} (hk : EFBase v goods s k) {L : List G} (hL : L.Nodup)
    (hLg : ∀ g ∈ L, g ∈ goods ∧ s.base g ≠ some k) : value v k L ≤ value v k (baseOf goods s.base k) := by
  rw [← value_relevant]
  refine Nat.le_trans (value_le_of_subset k (hL.filter _) fun g hg => ?_) hk
  obtain ⟨hgL, hpos⟩ := List.mem_filter.mp hg
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨(hLg g hgL).1, hpos⟩, by simpa using (hLg g hgL).2⟩

/-- A marked agent with an envy-free base needs nothing. -/
theorem EFBase.no_needs {s : LState A G} {k : A} (hk : EFBase v goods s k) (hm : s.marked k) (g : G) :
    ¬ needsOf v goods s k g := by
  rintro (⟨-, hg, hb, hlt⟩ | ⟨hm', -⟩)
  · have := hk.value_le (L := [g]) (by simp) (by simpa using ⟨hg, hb⟩)
    simp at this; omega
  · exact hm' hm

/-- The needs of an unmarked agent depend only on its pick. -/
theorem needsOf_unmarked {s : LState A G} {k : A} (hk : ¬ s.marked k) {x : G} :
    needsOf v goods s k x ↔ x ∈ goods ∧ 0 < v k x ∧ ∀ y, s.pick k = some y → v k y < v k x := by
  constructor
  · rintro (⟨hm, -⟩ | ⟨-, h⟩)
    · exact absurd hm hk
    · exact h
  · exact fun h => Or.inr ⟨hk, h⟩

theorem upRun_pick {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s') : s'.pick = s.pick := by
  induction hR with
  | done => rfl
  | step s s' s'' hs _ ih =>
    obtain ⟨k, g, -, -, -, rfl⟩ := hs
    exact ih

theorem upRun_marked {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s') {k : A}
    (hk : s.marked k) : s'.marked k := by
  induction hR with
  | done => exact hk
  | step s s' s'' hs _ ih =>
    obtain ⟨k', g, -, -, -, rfl⟩ := hs
    exact ih (Or.inr hk)

theorem upRun_base_none {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s') {g : G}
    (hg : s'.base g = none) : s.base g = none := by
  induction hR with
  | done => exact hg
  | step s s' s'' hs _ ih =>
    obtain ⟨k', g', -, -, -, rfl⟩ := hs
    have := ih hg
    simp only [upgrade] at this
    split at this
    · cases this
    · exact this

theorem upRun_final {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s') :
    ∀ k g, ¬ UpEligible v agents goods pol s' k g := by
  induction hR with
  | done _ h => exact h
  | step _ _ _ _ _ ih => exact ih

/-- An unmarked agent that needs nothing is never upgraded. -/
theorem upRun_unmarked {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s') {k : A}
    (hk : ¬ s.marked k) (hno : ∀ x, ¬ needsOf v goods s k x) : ¬ s'.marked k := by
  induction hR with
  | done => exact hk
  | step s s' s'' hs _ ih =>
    obtain ⟨k', g, hE, -, -, rfl⟩ := hs
    obtain ⟨-, -, -, -, -, -, ⟨x, hx⟩, -⟩ := hE
    have hkk : k' ≠ k := fun e => hno x (e ▸ hx)
    refine ih (fun h => ?_) fun x hx => ?_
    · rcases h with h | h
      · exact hkk h.symm
      · exact hk h
    · have hk' : ¬ (upgrade s k' g).marked k := fun h => by
        rcases h with h | h
        · exact hkk h.symm
        · exact hk h
      rw [needsOf_unmarked hk'] at hx
      exact hno x ((needsOf_unmarked hk).mpr hx)

/-- **Envy-free upgrades give envy-free bases**: along envy-free upgrades, every marked agent keeps an envy-free
base (`k4/c4.md` §1: every upgraded agent holds an envy-free base, is never threatened and needs nothing). -/
theorem upRun_efBase {s s' : LState A G} (hR : UpRun v agents goods .envyFree s s')
    (hI : Inv v agents goods s) (hE : ∀ k, s.marked k → EFBase v goods s k) :
    ∀ k, s'.marked k → EFBase v goods s' k := by
  induction hR with
  | done => exact hE
  | step s s' s'' hs hrest ih =>
    obtain ⟨k, g, hEl, -, -, rfl⟩ := hs
    refine ih (upgrade_inv hI hEl) fun k' hk' => ?_
    obtain ⟨hkag, hkm, y, hy, hBk, hyNA, -, hgJ, hgpos, -, hef⟩ := hEl
    obtain ⟨hgg, hgb⟩ := mem_junk.mp hgJ
    have hyk : ∀ h ∈ goods, s.base h = some k ↔ h = y := fun h hh => by
      have := congrArg (h ∈ ·) hBk
      simp only [mem_baseOf, List.mem_singleton, eq_iff_iff] at this
      exact ⟨fun hb => this.mp ⟨hh, hb⟩, fun e => (this.mpr e).2⟩
    have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hBk]; simp : y ∈ baseOf goods s.base k)).1
    have hyne : y ≠ g := fun e => by
      have := (hyk y hyg).mpr rfl; rw [e, hgb] at this; cases this
    by_cases e : k' = k
    · subst e
      unfold EFBase
      have hB' : ∀ h ∈ goods, (upgrade s k' g).base h = some k' ↔ h = y ∨ h = g := fun h hh => by
        simp only [upgrade]
        by_cases hhg : h = g
        · simp [hhg]
        · simp only [hhg, ↓reduceIte, or_false]; exact hyk h hh
      have hL : (relevant v k' goods).filter (fun h => (upgrade s k' g).base h ≠ some k') =
          (relevant v k' goods).filter (fun h => h ≠ y ∧ h ≠ g) := by
        apply List.filter_congr
        intro h hh
        have := hB' h (List.mem_filter.mp hh).1
        by_cases h1 : h = y <;> by_cases h2 : h = g <;> simp_all
      rw [hL]
      refine Nat.le_trans hef (two_le_value (mem_baseOf.mpr ⟨hyg, (hB' y hyg).mpr (Or.inl rfl)⟩)
        (mem_baseOf.mpr ⟨hgg, (hB' g hgg).mpr (Or.inr rfl)⟩) hyne)
    · have hm : s.marked k' := by
        rcases hk' with h | h
        · exact absurd h e
        · exact h
      have hb : ∀ h, (upgrade s k g).base h = some k' ↔ s.base h = some k' := fun h => by
        simp only [upgrade]
        by_cases hhg : h = g
        · simp only [hhg, ↓reduceIte, hgb]
          exact ⟨fun h' => absurd (Option.some.inj h') (Ne.symm e), fun h' => by cases h'⟩
        · simp [hhg]
      have := hE k' hm
      unfold EFBase at this ⊢
      have h1 : (relevant v k' goods).filter (fun h => (upgrade s k g).base h ≠ some k') =
          (relevant v k' goods).filter (fun h => s.base h ≠ some k') :=
        List.filter_congr fun h _ => by simp only [ne_eq, hb h]
      have h2 : baseOf goods (upgrade s k g).base k' = baseOf goods s.base k' :=
        List.filter_congr fun h _ => by simp only [hb h]
      rw [h1, h2]; exact this

end upgrades

/-! ## The state after Phase 1 and envy-free upgrades -/

/-- `s` is reached from a run `run` of Phase 1 by envy-free upgrades until none applies (`k4/c4.md` §1). -/
structure AfterUp (v : A → G → Nat) (agents : List A) (goods : List G) (run : List (A × Option G))
    (s : LState A G) : Prop where
  phase : PhaseRun v agents goods run
  up : UpRun v agents goods .envyFree (runState run) s

/-- `r` is the last-processed unmarked agent (`k4/c4.md` §1, **r**). -/
def IsLast (run : List (A × Option G)) (s : LState A G) (r : A) : Prop :=
  ∃ (t : Nat) (p : A × Option G), run[t]? = some p ∧ p.1 = r ∧ ¬ s.marked r ∧
    ∀ (t' : Nat) (q : A × Option G), t < t' → run[t']? = some q → s.marked q.1

/-- A need chain `c = x₀ :: … :: x_t` (`k4/c4.md` §1, (A4)): distinct listed agents, each but the last frozen and
holding a pick that the next one needs, the last not frozen. -/
def NeedChain (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (c : List A) : Prop :=
  c.Nodup ∧ (∀ x ∈ c, x ∈ agents) ∧
  (∀ (i : Nat) (a b : A), c[i]? = some a → c[i + 1]? = some b →
    FrozenAt v agents goods s a ∧ ∃ y, s.pick a = some y ∧ needsOf v goods s b y) ∧
  ∀ last, c.getLast? = some last → ¬ FrozenAt v agents goods s last

section after
variable {v : A → G → Nat} {agents : List A} {goods : List G} {run : List (A × Option G)} {s : LState A G}

theorem AfterUp.inv (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) : Inv v agents goods s :=
  upRun_inv hS.up (runState_inv hS.phase hgd)

theorem AfterUp.pick (hS : AfterUp v agents goods run s) {t : Nat} {p : A × Option G} (hp : run[t]? = some p) :
    s.pick p.1 = p.2 := by
  rw [upRun_pick hS.up]; exact runState_pick hS.phase hp

theorem AfterUp.efBase (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) :
    ∀ k, s.marked k → EFBase v goods s k :=
  upRun_efBase hS.up (runState_inv hS.phase hgd) fun _ h => False.elim h

theorem AfterUp.no_needs (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {k : A} (hk : s.marked k)
    (g : G) : ¬ needsOf v goods s k g :=
  (hS.efBase hgd k hk).no_needs hk g

/-- A junk good was never picked. -/
theorem AfterUp.junk (hS : AfterUp v agents goods run s) {g : G} (hg : s.base g = none) :
    ∀ t, pickAt run t ≠ some g :=
  (runState_base_none hS.phase).mp (upRun_base_none hS.up hg)

/-- (UT₂): no envy-free upgrade applies any more. -/
theorem AfterUp.final (hS : AfterUp v agents goods run s) : ∀ k g, ¬ UpEligible v agents goods .envyFree s k g :=
  upRun_final hS.up

/-- A leader holds its top: at an insertion step every good the agent values is still there. -/
theorem PhaseRun.leader_top (hR : PhaseRun v agents goods run) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) (hins : InsAt v run t) :
    ∀ g ∈ goods, 0 < v p.1 g → ∃ y, p.2 = some y ∧ v p.1 g ≤ v p.1 y :=
  fun g hg hpos => hR.fav t p hp g hg hpos fun hpb => hins t p (Nat.le_refl _) hp ⟨g, hpos, hpb⟩

/-- A leader needs nothing, so it is never upgraded. -/
theorem AfterUp.leader_unmarked (hS : AfterUp v agents goods run s) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) (hins : InsAt v run t) : ¬ s.marked p.1 := by
  refine upRun_unmarked hS.up (fun h => h) fun x hx => ?_
  rw [needsOf_unmarked (fun h => h)] at hx
  obtain ⟨hxg, hpos, hlt⟩ := hx
  obtain ⟨y, hy, hle⟩ := hS.phase.leader_top hp hins x hxg hpos
  have := hlt y (by rw [runState_pick hS.phase hp, hy]); omega

/-- An unmarked agent's need: the needed good was picked at an earlier step of the same block. -/
theorem AfterUp.need_step (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {b : A} {g : G}
    (hN : needsOf v goods s b g) {t : Nat} {p : A × Option G} (hp : run[t]? = some p) (hpb : p.1 = b) :
    ¬ s.marked b ∧ ∃ (t' : Nat) (q : A × Option G), run[t']? = some q ∧ q.2 = some g ∧ t' < t ∧
      SameBlock v run t' t := by
  have hbm : ¬ s.marked b := fun hm => hS.no_needs hgd hm g hN
  refine ⟨hbm, ?_⟩
  rw [needsOf_unmarked hbm] at hN
  obtain ⟨hg, hpos, hlt⟩ := hN
  subst hpb
  exact hS.phase.b2 hp hg hpos fun y hy => hlt y (by rw [hS.pick hp, hy])

/-- **A step of a need chain goes forward in the same block** (`k4/c4.md` (A4), from (B2)): if `b` needs the pick
of `a`, then `b` is unmarked and processed after `a` in `a`'s block. -/
theorem AfterUp.chain_step (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {a b : A} {y : G}
    (hy : s.pick a = some y) (hN : needsOf v goods s b y) {ta tb : Nat} {pa pb : A × Option G}
    (hpa : run[ta]? = some pa) (hpa1 : pa.1 = a) (hpb : run[tb]? = some pb) (hpb1 : pb.1 = b) :
    ¬ s.marked b ∧ ta < tb ∧ SameBlock v run ta tb := by
  obtain ⟨hbm, t', q, hq, hqy, ht', hbl⟩ := hS.need_step hgd hN hpb hpb1
  have hay : pa.2 = some y := by rw [← hS.pick hpa, hpa1, hy]
  have := hS.phase.pick_unique hq hpa hqy hay
  subst this
  exact ⟨hbm, ht', hbl⟩

/-- **(A1) r is a terminal**: nobody needs `r`'s pick (in particular `r` is not frozen). -/
theorem AfterUp.last_pick_free (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {r : A}
    (hr : IsLast run s r) {y : G} (hy : s.pick r = some y) : ¬ NA agents (needsOf v goods s) y := by
  obtain ⟨t, p, hp, hpr, -, hlast⟩ := hr
  rintro ⟨j, hj, hN⟩
  obtain ⟨tj, pj, hpj, hpj1⟩ := hS.phase.exists_pos hj
  obtain ⟨hjm, hlt, -⟩ := hS.chain_step hgd hy hN hp hpr hpj hpj1
  exact hjm (hpj1 ▸ hlast tj pj hlt hpj)

theorem AfterUp.last_not_frozen (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) {r : A}
    (hr : IsLast run s r) : ¬ FrozenAt v agents goods s r := by
  rintro ⟨hrm, y, hB, hNA⟩
  have hI := hS.inv hgd
  obtain ⟨t, p, hp, hpr, -, -⟩ := id hr
  have hrag : r ∈ agents := hpr ▸ hS.phase.agent_mem hp
  have := hI.unmarked r hrag hrm
  rw [hB] at this
  cases hpk : s.pick r with
  | none => rw [hpk] at this; simp at this
  | some y' =>
    rw [hpk] at this; simp at this; subst this
    exact hS.last_pick_free hgd hr hpk hNA

/-- **(A2)**: every unmarked agent other than `r` is processed before `r`, and no insertion step follows `r`'s step,
so `r` lies in the last block. -/
theorem AfterUp.last_block (hS : AfterUp v agents goods run s) {r : A} {t : Nat} {p : A × Option G}
    (hr : IsLast run s r) (hp : run[t]? = some p) (hpr : p.1 = r) :
    (∀ (t' : Nat) (q : A × Option G), run[t']? = some q → ¬ s.marked q.1 → t' ≤ t) ∧
      ∀ t', t < t' → t' < run.length → ¬ InsAt v run t' := by
  obtain ⟨t₀, p₀, hp₀, hp₀r, -, hlast⟩ := hr
  have e : t₀ = t := hS.phase.pos_unique hp₀ hp (by rw [hp₀r, hpr])
  subst e
  refine ⟨fun t' q hq hqm => Nat.le_of_not_lt fun h => hqm (hlast t' q h hq), fun t' ht' hlen hins => ?_⟩
  have hq : run[t']? = some run[t'] := List.getElem?_eq_getElem hlen
  exact hS.leader_unmarked hq hins (hlast t' _ ht' hq)

/-- `r` exists when some agent is processed: the first agent leads its block, so it is not upgraded. -/
theorem AfterUp.exists_last (hS : AfterUp v agents goods run s) (hne : run ≠ []) : ∃ r, IsLast run s r := by
  classical
  have key : ∀ n, (∃ t, t < n ∧ ∃ q : A × Option G, run[t]? = some q ∧ ¬ s.marked q.1) →
      ∃ t, ∃ q : A × Option G, run[t]? = some q ∧ ¬ s.marked q.1 ∧
        ∀ (t' : Nat) (q' : A × Option G), t < t' → t' < n → run[t']? = some q' → s.marked q'.1 := by
    intro n
    induction n with
    | zero => rintro ⟨t, ht, -⟩; omega
    | succ n ih =>
      intro hex
      by_cases hn : ∃ q : A × Option G, run[n]? = some q ∧ ¬ s.marked q.1
      · obtain ⟨q, hq, hqm⟩ := hn
        exact ⟨n, q, hq, hqm, fun t' q' h1 h2 _ => absurd h2 (by omega)⟩
      · obtain ⟨t, ht, q, hq, hqm⟩ := hex
        have htn : t < n := by
          rcases Nat.lt_or_ge t n with h | h
          · exact h
          · exact absurd ⟨q, (show t = n by omega) ▸ hq, hqm⟩ hn
        obtain ⟨t₁, q₁, hq₁, hq₁m, hmax⟩ := ih ⟨t, htn, q, hq, hqm⟩
        refine ⟨t₁, q₁, hq₁, hq₁m, fun t' q' h1 h2 h3 => ?_⟩
        by_cases e : t' = n
        · subst e; exact Classical.byContradiction fun hm => hn ⟨q', h3, hm⟩
        · exact hmax t' q' h1 (by omega) h3
  have hlen : 0 < run.length := List.length_pos_iff.mpr hne
  have h0 : run[0]? = some (run[0]'hlen) := List.getElem?_eq_getElem hlen
  obtain ⟨t, q, hq, hqm, hmax⟩ := key run.length ⟨0, hlen, run[0]'hlen, h0, hS.leader_unmarked h0 insAt_zero⟩
  exact ⟨q.1, t, q, hq, rfl, hqm, fun t' q' h1 h2 => hmax t' q' h1 (List.getElem?_eq_some_iff.mp h2).1 h2⟩

/-- **(A4) Need chains**: from every unmarked agent `x` a need chain starts; it lies in `x`'s block, goes forward in
processing order, and ends at an unmarked agent that is not frozen (a terminal). -/
theorem AfterUp.exists_chain (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) :
    ∀ (n t : Nat) (p : A × Option G), run.length - t ≤ n → run[t]? = some p → ¬ s.marked p.1 →
      ∃ (c : List A) (e : A) (te : Nat) (pe : A × Option G), NeedChain v agents goods s c ∧ c.head? = some p.1 ∧
        c.getLast? = some e ∧ run[te]? = some pe ∧ pe.1 = e ∧ SameBlock v run t te ∧ ¬ s.marked e ∧
        ¬ FrozenAt v agents goods s e ∧
        ∀ z ∈ c, ∃ (tz : Nat) (pz : A × Option G), run[tz]? = some pz ∧ pz.1 = z ∧ SameBlock v run t tz := by
  have hI := hS.inv hgd
  intro n
  induction n with
  | zero =>
    intro t p h hp _
    have := (List.getElem?_eq_some_iff.mp hp).1; omega
  | succ n ih =>
    intro t p hn hp hpm
    have hpag := hS.phase.agent_mem hp
    by_cases hF : FrozenAt v agents goods s p.1
    · -- `p.1` is frozen: some agent `j` needs its pick; continue from `j`
      obtain ⟨-, y, hB, j, hj, hN⟩ := hF
      have hy : s.pick p.1 = some y := by
        have := hI.unmarked p.1 hpag hpm
        rw [hB] at this
        cases hpk : s.pick p.1 with
        | none => rw [hpk] at this; simp at this
        | some y' => rw [hpk] at this; simp at this; rw [this]
      obtain ⟨tj, pj, hpj, hpj1⟩ := hS.phase.exists_pos hj
      obtain ⟨hjm, htj, hbl⟩ := hS.chain_step hgd hy hN hp rfl hpj hpj1
      obtain ⟨c, e, te, pe, hc, hch, hce, hpe, hpe1, hbe, hem, hef, hcz⟩ :=
        ih tj pj (by omega) hpj (hpj1 ▸ hjm)
      have hxc : p.1 ∉ c := fun hx => by
        obtain ⟨tz, pz, hpz, hpz1, hbz⟩ := hcz p.1 hx
        have := hS.phase.pos_unique hpz hp hpz1
        have := hbz.1; omega
      refine ⟨p.1 :: c, e, te, pe, ⟨List.nodup_cons.mpr ⟨hxc, hc.1⟩, fun z hz => ?_, fun i a b ha hb => ?_,
        fun last hl => ?_⟩, rfl, ?_, hpe, hpe1, hbl.trans hbe, hem, hef, fun z hz => ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hpag
        · exact hc.2.1 z hz
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
          subst ha
          simp only [List.getElem?_cons_succ] at hb
          cases c with
          | nil => simp at hch
          | cons c0 cs =>
            simp only [List.head?_cons, Option.some.injEq] at hch
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
            subst hb; subst hch
            exact ⟨⟨hpm, y, hB, j, hj, hN⟩, y, hy, hpj1 ▸ hN⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at ha hb
          exact hc.2.2.1 i a b ha hb
      · cases c with
        | nil => simp at hch
        | cons c0 cs =>
          have : (p.1 :: c0 :: cs).getLast? = (c0 :: cs).getLast? := by simp [List.getLast?_cons]
          rw [this] at hl
          exact hc.2.2.2 last hl
      · cases c with
        | nil => simp at hch
        | cons c0 cs => simpa [List.getLast?_cons] using hce
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨t, p, hp, rfl, SameBlock.refl t⟩
        · obtain ⟨tz, pz, hpz, hpz1, hbz⟩ := hcz z hz
          exact ⟨tz, pz, hpz, hpz1, hbl.trans hbz⟩
    · -- `p.1` is a terminal
      refine ⟨[p.1], p.1, t, p, ⟨by simp, by simpa using hpag, fun i a b _ hb => ?_,
        fun last hl => ?_⟩, rfl, rfl, hp, rfl, SameBlock.refl t, hpm, hF, fun z hz => ?_⟩
      · cases i <;> simp at hb
      · simp at hl; subst hl; exact hF
      · simp at hz; subst hz; exact ⟨t, p, hp, rfl, SameBlock.refl t⟩

/-- Upgrades only give junk goods away: a good in a base stays in it. -/
theorem upRun_base_some {v : A → G → Nat} {agents : List A} {goods : List G} {pol : Policy} {s s' : LState A G}
    (hR : UpRun v agents goods pol s s') {g : G} {i : A} (hg : s.base g = some i) : s'.base g = some i := by
  induction hR with
  | done => exact hg
  | step s s' s'' hs _ ih =>
    obtain ⟨k, g', hE, -, -, rfl⟩ := hs
    obtain ⟨-, -, -, -, -, -, -, hgJ, -⟩ := hE
    apply ih
    simp only [upgrade]
    split
    · rename_i e; subst e; rw [(mem_junk.mp hgJ).2] at hg; cases hg
    · exact hg

/-- Along upgrades from a state where every base has at most one good and nobody is marked, every base has at
most two goods, and every marked agent's base has two. -/
theorem upRun_base_two {v : A → G → Nat} {agents : List A} {goods : List G} {pol : Policy} {s s' : LState A G}
    (hgd : goods.Nodup) (hR : UpRun v agents goods pol s s')
    (h2 : ∀ i, (baseOf goods s.base i).length ≤ 2) (hm : ∀ i, s.marked i → (baseOf goods s.base i).length = 2)
    (hu : ∀ i, ¬ s.marked i → (baseOf goods s.base i).length ≤ 1) :
    (∀ i, (baseOf goods s'.base i).length ≤ 2) ∧ (∀ i, s'.marked i → (baseOf goods s'.base i).length = 2) ∧
      ∀ i, ¬ s'.marked i → (baseOf goods s'.base i).length ≤ 1 := by
  induction hR with
  | done => exact ⟨h2, hm, hu⟩
  | step s s' s'' hs _ ih =>
    obtain ⟨k, g, hE, -, -, rfl⟩ := hs
    obtain ⟨-, hkm, y, -, hBk, -, -, hgJ, -⟩ := hE
    obtain ⟨hgg, hgb⟩ := mem_junk.mp hgJ
    have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hBk]; simp : y ∈ baseOf goods s.base k)).1
    have hyk : ∀ h ∈ goods, s.base h = some k ↔ h = y := fun h hh => by
      have := congrArg (h ∈ ·) hBk
      simp only [mem_baseOf, List.mem_singleton, eq_iff_iff] at this
      exact ⟨fun hb => this.mp ⟨hh, hb⟩, fun e => (this.mpr e).2⟩
    have hyne : y ≠ g := fun e => by
      have := (hyk y hyg).mpr rfl; rw [e, hgb] at this; cases this
    -- `k`'s new base is `{y, g}`; every other base is unchanged
    have hk2 : (baseOf goods (upgrade s k g).base k).length = 2 := by
      have hmem : ∀ h, h ∈ baseOf goods (upgrade s k g).base k ↔ h ∈ [y, g] := fun h => by
        rw [mem_baseOf]
        simp only [upgrade, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨hh, hb⟩
          by_cases hhg : h = g
          · exact Or.inr hhg
          · simp only [hhg, ↓reduceIte] at hb; exact Or.inl ((hyk h hh).mp hb)
        · rintro (rfl | rfl)
          · refine ⟨hyg, ?_⟩; simp only [hyne, ↓reduceIte]; exact (hyk h hyg).mpr rfl
          · exact ⟨hgg, by simp⟩
      have hnd : (baseOf goods (upgrade s k g).base k).Nodup := hgd.filter _
      have h1 := List.Nodup.length_le_of_subset hnd fun h hh => (hmem h).mp hh
      have h2' := List.Nodup.length_le_of_subset (l₁ := [y, g]) (by simp [hyne]) fun h hh => (hmem h).mpr hh
      simp at h1 h2'; omega
    have hother : ∀ i, i ≠ k → baseOf goods (upgrade s k g).base i = baseOf goods s.base i := fun i hik =>
      List.filter_congr fun h _ => by
        simp only [upgrade]
        by_cases hhg : h = g
        · subst hhg; simp only [↓reduceIte, hgb, decide_eq_decide]
          exact ⟨fun e => absurd (Option.some.inj e).symm hik, fun e => by cases e⟩
        · simp [hhg]
    refine ih (fun i => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · by_cases e : i = k
      · subst e; omega
      · rw [hother i e]; exact h2 i
    · by_cases e : i = k
      · subst e; exact hk2
      · rw [hother i e]
        rcases hi with hi | hi
        · exact absurd hi e
        · exact hm i hi
    · have e : i ≠ k := fun e => hi (Or.inl e)
      rw [hother i e]
      exact hu i fun h => hi (Or.inr h)

theorem AfterUp.base_of_pick (hS : AfterUp v agents goods run s) {t : Nat} {p : A × Option G}
    (hp : run[t]? = some p) {g : G} (hg : p.2 = some g) : s.base g = some p.1 :=
  upRun_base_some hS.up ((runState_base hS.phase).mpr ⟨t, p, hp, rfl, hg⟩)

/-- After envy-free upgrades every base has at most two goods, an upgraded agent's exactly two, the others' at most
one. -/
theorem AfterUp.base_two (hS : AfterUp v agents goods run s) (hgd : goods.Nodup) :
    (∀ i, (baseOf goods s.base i).length ≤ 2) ∧ (∀ i, s.marked i → (baseOf goods s.base i).length = 2) ∧
      ∀ i, ¬ s.marked i → (baseOf goods s.base i).length ≤ 1 := by
  have h1 : ∀ i, (baseOf goods (runState run).base i).length ≤ 1 := fun i => by
    rw [runState_baseOf hS.phase hgd]
    cases (runState run).pick i <;> simp
  exact upRun_base_two hgd hS.up (fun i => Nat.le_trans (h1 i) (by omega)) (fun _ h => False.elim h)
    fun i _ => h1 i

end after

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.phase1_runFrom
#print axioms EFX.LB4R.phase1_phaseRun
#print axioms EFX.LB4R.runState_inv
#print axioms EFX.LB4R.PhaseRun.pickedBefore_of_prefers
#print axioms EFX.LB4R.PhaseRun.insAt_of_not_lost
#print axioms EFX.LB4R.PhaseRun.b2
#print axioms EFX.LB4R.exists_leader
#print axioms EFX.LB4R.leader_unique
#print axioms EFX.LB4R.upRun_efBase
#print axioms EFX.LB4R.EFBase.value_le
#print axioms EFX.LB4R.AfterUp.leader_unmarked
#print axioms EFX.LB4R.AfterUp.chain_step
#print axioms EFX.LB4R.AfterUp.last_pick_free
#print axioms EFX.LB4R.AfterUp.last_not_frozen
#print axioms EFX.LB4R.AfterUp.last_block
#print axioms EFX.LB4R.AfterUp.exists_last
#print axioms EFX.LB4R.AfterUp.exists_chain
#print axioms EFX.LB4R.AfterUp.base_of_pick
#print axioms EFX.LB4R.AfterUp.base_two
