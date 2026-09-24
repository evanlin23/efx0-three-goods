import EFX.LBSound

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq G]

/-! ## Phase 1: serial dictatorship in a given order -/

/-- `i`'s favourite remaining good: the first of `a i`, `b i`, `c i` still in `pool`. -/
def fav (P : Profile A G) (pool : List G) (i : A) : Option G :=
  if P.a i ∈ pool then some (P.a i) else if P.b i ∈ pool then some (P.b i)
  else if P.c i ∈ pool then some (P.c i) else none

/-- The pool after a pick. -/
def removePick (pool : List G) : Option G → List G
  | none => pool
  | some g => pool.erase g

/-- The rank of `fav`, `3` if none. -/
def favRank (P : Profile A G) (pool : List G) (i : A) : Nat :=
  match fav P pool i with
  | none => 3
  | some y => P.rank i y

theorem fav_some {P : Profile A G} {pool : List G} {i : A} {y : G} (h : fav P pool i = some y) :
    y ∈ pool ∧ P.rank i y < 3 := by
  unfold fav at h
  unfold Profile.rank
  by_cases ha : P.a i ∈ pool <;> by_cases hb : P.b i ∈ pool <;> by_cases hc : P.c i ∈ pool <;>
    simp [ha, hb, hc] at h <;> subst h <;> grind

/-- No good of the pool ranks above the favourite. -/
theorem fav_best (P : Profile A G) (pool : List G) (i : A) :
    ∀ g ∈ pool, ¬ P.rank i g < favRank P pool i := by
  intro g hg hlt
  unfold favRank fav at hlt
  unfold Profile.rank at hlt
  by_cases ha : P.a i ∈ pool <;> by_cases hb : P.b i ∈ pool <;> by_cases hc : P.c i ∈ pool <;>
    simp [ha, hb, hc] at hlt <;> grind

theorem nodup_removePick {pool : List G} (h : pool.Nodup) (p : Option G) :
    (removePick pool p).Nodup := by
  cases p with
  | none => exact h
  | some g => exact h.erase g

theorem mem_removePick {pool : List G} {p : Option G} {g : G} (h : g ∈ removePick pool p) :
    g ∈ pool := by
  cases p with
  | none => exact h
  | some y => exact List.mem_of_mem_erase h

variable [DecidableEq A]

/-- Phase 1: the agents of `order` take, one at a time, their favourite remaining good (or nothing if
none of their goods remains). The result is each agent's pick. -/
def phase1 (P : Profile A G) : List A → List G → A → Option G
  | [], _, _ => none
  | i :: order, pool, k =>
    if k = i then fav P pool i else phase1 P order (removePick pool (fav P pool i)) k

/-- Phase 1 in any order of distinct agents: each pick is a good of the picker taken from the pool,
no good is picked twice, and invariant (I1) holds. -/
theorem phase1_spec (P : Profile A G) :
    ∀ (order : List A) (pool : List G), order.Nodup → pool.Nodup →
      (∀ k y, phase1 P order pool k = some y → k ∈ order ∧ y ∈ pool ∧ P.rank k y < 3) ∧
      (∀ k k' y, phase1 P order pool k = some y → phase1 P order pool k' = some y → k = k') ∧
      (∀ i ∈ order, ∀ g ∈ pool, P.Prefers (phase1 P order pool) i g →
        ∃ k, phase1 P order pool k = some g)
  | [], pool, _, _ => by simp [phase1]
  | i :: order, pool, hord, hpool => by
    have hi : i ∉ order := (List.nodup_cons.mp hord).1
    obtain ⟨ih1, ih2, ih3⟩ :=
      phase1_spec P order (removePick pool (fav P pool i)) (List.nodup_cons.mp hord).2
        (nodup_removePick hpool _)
    have hY : ∀ k, phase1 P (i :: order) pool k =
        if k = i then fav P pool i else phase1 P order (removePick pool (fav P pool i)) k :=
      fun k => rfl
    have hYi : phase1 P order (removePick pool (fav P pool i)) i = none := by
      cases h : phase1 P order (removePick pool (fav P pool i)) i with
      | none => rfl
      | some y => exact absurd (ih1 i y h).1 hi
    -- a pick of a later agent is not `i`'s pick
    have hnot : ∀ k y, fav P pool i = some y →
        phase1 P order (removePick pool (fav P pool i)) k ≠ some y := by
      intro k y hf hk
      have := (ih1 k y hk).2.1
      rw [hf] at this
      exact absurd rfl ((List.Nodup.mem_erase_iff hpool).mp this).1
    refine ⟨fun k y hk => ?_, fun k k' y hk hk' => ?_, fun i' hi' g hg hp => ?_⟩
    · rw [hY] at hk
      by_cases hki : k = i
      · subst hki; simp at hk; exact ⟨by simp, fav_some hk⟩
      · simp [hki] at hk
        obtain ⟨h1, h2, h3⟩ := ih1 k y hk
        exact ⟨by simp [h1], mem_removePick h2, h3⟩
    · rw [hY] at hk hk'
      by_cases hki : k = i <;> by_cases hki' : k' = i
      · rw [hki, hki']
      · simp [hki, hki'] at hk hk'; exact absurd hk' (hnot k' y hk)
      · simp [hki, hki'] at hk hk'; exact absurd hk (hnot k y hk')
      · simp [hki, hki'] at hk hk'; exact ih2 k k' y hk hk'
    · by_cases hii : i' = i
      · subst hii
        apply absurd hp
        have e : P.pickRank (phase1 P (i' :: order) pool) i' = favRank P pool i' := by
          unfold Profile.pickRank favRank; rw [hY]; simp only [↓reduceIte]; cases fav P pool i' <;> rfl
        unfold Profile.Prefers; rw [e]; exact fav_best P pool i' g hg
      · have hi'o : i' ∈ order := by simpa [hii] using hi'
        have hp' : P.Prefers (phase1 P order (removePick pool (fav P pool i))) i' g := by
          unfold Profile.Prefers Profile.pickRank at hp ⊢
          rw [hY] at hp
          simpa [hii] using hp
        by_cases hgf : fav P pool i = some g
        · exact ⟨i, by rw [hY]; simp [hgf]⟩
        · have hg' : g ∈ removePick pool (fav P pool i) := by
            cases hf : fav P pool i with
            | none => exact hg
            | some y =>
              have hyg : g ≠ y := fun e => hgf (by rw [hf, e])
              exact (List.Nodup.mem_erase_iff hpool).mpr ⟨hyg, hg⟩
          obtain ⟨k, hk⟩ := ih3 i' hi'o g hg' hp'
          have hki : k ≠ i := fun e => by rw [e, hYi] at hk; cases hk
          exact ⟨k, by rw [hY]; simp [hki, hk]⟩

/-! ## Phase 2: upgrades -/

/-- `NA` for the upgraded agents `up`, as a Boolean. -/
def naB (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) : Bool :=
  agents.any (fun i => !(up.contains i) && decide (P.Prefers Y i g))

theorem naB_iff {P : Profile A G} {agents up : List A} {Y : A → Option G} {g : G} :
    naB P agents up Y g = true ↔ P.NA agents (· ∈ up) Y g := by
  simp [naB, Profile.NA]

omit [DecidableEq A] in
/-- `NA` only shrinks as agents are upgraded. -/
theorem NA_mono {P : Profile A G} {agents : List A} {Y : A → Option G} {U U' : A → Prop}
    (hUU : ∀ k, U k → U' k) {g : G} (h : P.NA agents U' Y g) : P.NA agents U Y g := by
  obtain ⟨i, hi, hnu, hp⟩ := h
  exact ⟨i, hi, fun hu => hnu (hUU i hu), hp⟩

/-- LB's upgrade test for agent `k`: it is not upgraded, its pick is its `b`, its `c` is junk not yet
given away (in `J`), and its `b` is not in `NA`. -/
def canUp (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (k : A) : Bool :=
  !(up.contains k) && P.pickRank Y k == 1 && J.contains (P.c k) && !(naB P agents up Y (P.b k))

/-- LB's upgrades: while some agent passes `canUp`, the first one in `agents` receives its `c`.
Returns the upgraded agents and the junk left. Each round upgrades a new agent of `agents`, so
`fuel = agents.length` rounds run the loop to the end, as LB does. -/
def upgrades (P : Profile A G) (agents : List A) (Y : A → Option G) :
    Nat → List A → List G → List A × List G
  | 0, up, J => (up, J)
  | fuel + 1, up, J =>
    match agents.find? (canUp P agents up Y J) with
    | none => (up, J)
    | some k => upgrades P agents Y fuel (k :: up) (J.erase (P.c k))

/-- The invariant of the upgrade loop, started from the junk `J0`. -/
def UpInv (P : Profile A G) (agents : List A) (Y : A → Option G) (J0 : List G) (up : List A)
    (J : List G) : Prop :=
  J.Nodup ∧ (∀ g ∈ J, g ∈ J0) ∧ (∀ g ∈ J0, g ∉ J → ∃ k ∈ up, P.c k = g) ∧
  ∀ k ∈ up, P.pickRank Y k = 1 ∧ ¬ P.NA agents (· ∈ up) Y (P.b k) ∧ P.c k ∈ J0 ∧ P.c k ∉ J ∧
    ∀ k' ∈ up, P.c k' = P.c k → k' = k

omit [DecidableEq A] in
theorem upInv_init (P : Profile A G) (agents : List A) (Y : A → Option G) {J0 : List G}
    (h : J0.Nodup) : UpInv P agents Y J0 [] J0 :=
  ⟨h, fun _ hg => hg, fun _ hg hn => absurd hg hn, fun _ hk => by simp at hk⟩

theorem upInv_upgrades (P : Profile A G) (agents : List A) (Y : A → Option G) (J0 : List G) :
    ∀ (fuel : Nat) (up : List A) (J : List G), UpInv P agents Y J0 up J →
      UpInv P agents Y J0 (upgrades P agents Y fuel up J).1 (upgrades P agents Y fuel up J).2
  | 0, _, _, h => h
  | fuel + 1, up, J, h => by
    unfold upgrades
    cases hf : agents.find? (canUp P agents up Y J) with
    | none => exact h
    | some k =>
      apply upInv_upgrades P agents Y J0 fuel
      have hc := List.find?_some hf
      simp only [canUp, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem,
        beq_iff_eq] at hc
      obtain ⟨⟨⟨hku, hr⟩, hcJ⟩, hna⟩ := hc
      have hku : k ∉ up := by simpa using hku
      have hna : ¬ P.NA agents (· ∈ up) Y (P.b k) := fun h' => by
        rw [← naB_iff] at h'; rw [h'] at hna; cases hna
      obtain ⟨hJnd, hJ0, hcov, hup⟩ := h
      have hmono : ∀ {g}, P.NA agents (· ∈ k :: up) Y g → P.NA agents (· ∈ up) Y g :=
        NA_mono (fun x hx => List.mem_cons_of_mem k hx)
      refine ⟨hJnd.erase _, fun g hg => hJ0 g (List.mem_of_mem_erase hg), fun g hg hgn => ?_,
        fun k' hk' => ?_⟩
      · by_cases hgc : g = P.c k
        · exact ⟨k, by simp, hgc.symm⟩
        · have : g ∉ J := fun hgJ => hgn ((List.Nodup.mem_erase_iff hJnd).mpr ⟨hgc, hgJ⟩)
          obtain ⟨k'', hk'', he⟩ := hcov g hg this
          exact ⟨k'', List.mem_cons_of_mem k hk'', he⟩
      · rcases List.mem_cons.mp hk' with rfl | hk'
        · refine ⟨hr, fun h' => hna (hmono h'), hJ0 _ hcJ, fun h' => ?_, fun k'' hk'' he => ?_⟩
          · exact absurd rfl ((List.Nodup.mem_erase_iff hJnd).mp h').1
          · rcases List.mem_cons.mp hk'' with rfl | hk''
            · rfl
            · exact absurd (he ▸ hcJ) (hup k'' hk'').2.2.2.1
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hup k' hk'
          refine ⟨h1, fun h' => h2 (hmono h'), h3, fun h' => h4 (List.mem_of_mem_erase h'),
            fun k'' hk'' he => ?_⟩
          rcases List.mem_cons.mp hk'' with rfl | hk''
          · exact absurd (he ▸ hcJ) h4
          · exact h5 k'' hk'' he

end LB
end EFX
