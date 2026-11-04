import EFX.DE4ClaimC3

/-!
# Lemma 4 in the robust order at a maximum: Claim T′ where (H) fails is the case (L) (`k4/de4.md` §10.1; ledger
K4.DE4V3R.LEAN)

At a maximum of the robust order, if the leftover goods alone threaten some agent, Lemma 4's construction is either a
want trade (the walk from a frozen agent, or a want ring), in which every receiver takes a single good it wants and so
strictly rises in robust level, against Lemma R, or a free self-upgrade of at most two goods. With `selfUp_breaks_v3`,
the hypothesis HL (Claim T′ where (H) fails) reduces to the case (L): some free agent has a self-upgrade of at most two
goods (and every such upgrade breaks (V3)).

**Results.**
- `levelR_lt_of_want`: taking a single good it wants strictly raises an agent's robust level.
- `trade_potentialR_lt`: a want trade with a receiver strictly raises the robust level sum; `trade_contra`: so it
  contradicts maximality (Lemma R).
- `small_at_max`, `threat_at_max` (**Lemma 4 at a maximum**): an agent threatened by the leftover goods alone gives a
  free agent with a self-upgrade of at most two goods (`FreeSelfUp`).
- `HLL` (**Claim T′ in case (L)**, a hypothesis, never an axiom), `hl'_of_hll`, `hl_of_hll`, and
  `target4_of_HC3'_HLL`: **HC3′ and Claim T′ in case (L) imply TARGET₄**.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- A free agent with an allowed self-upgrade of at most two goods, from its holding and the leftover goods (Lemma 4′
applies to it). -/
abbrev FreeSelfUp (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (x : A) : Prop :=
  (∀ y ∈ hold goods base x, ∀ w ∈ agents, ¬ value v w (hold goods base w) < v w y) ∧
    ∃ p : G → Bool, (∀ g ∈ goods, p g = true → base g = some x ∨ base g = none) ∧
      Allowed v x goods (goods.filter p) ∧ (goods.filter p).length ≤ 2 ∧
      value v x (hold goods base x) < value v x (goods.filter p)

section robustLemma4
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- Taking a single good it wants strictly raises an agent's robust level. -/
theorem levelR_lt_of_want (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {i : A} (hi : i ∈ agents)
    {base : G → Option A} (hY : Allowed v i goods (hold goods base i)) {y : G} (hy : y ∈ goods)
    (hyY : y ∉ hold goods base i) (hlt : value v i (hold goods base i) < v i y) :
    levelR v i goods (hold goods base i) < levelR v i goods [y] := by
  have hytop := le_topV v i goods hy
  have hyr : y ∈ relevant v i goods := mem_relevant.mpr ⟨hy, by omega⟩
  have hrnd : (relevant v i goods).Nodup := hgd.filter _
  have hR4 := (hc i hi).2.1
  have hcnt : ((relevant v i goods).filter (fun g' => decide (v i y < v i g'))).length ≤ 3 := by
    have hsub : ∀ g ∈ (relevant v i goods).filter (fun g' => decide (v i y < v i g')),
        g ∈ (relevant v i goods).erase y := by
      intro g hg
      have h1 := List.mem_filter.mp hg
      have hne : g ≠ y := fun e => by subst e; simp at h1
      exact (List.Nodup.mem_erase_iff hrnd).mpr ⟨hne, h1.1⟩
    have := List.Nodup.length_le_of_subset (hrnd.filter _) hsub
    rw [List.length_erase_of_mem hyr] at this
    omega
  have hRy : levelR v i goods [y] = level v i goods [y] := by
    unfold levelR
    have : ¬ (IsUpper v i goods [y] ∧ IsRobust v i goods [y]) := fun h => by
      have := h.1.2.1; rw [value_singleton] at this; omega
    simp only [this, ↓reduceIte]
  have hRY : levelR v i goods (hold goods base i) = level v i goods (hold goods base i) := by
    unfold levelR
    have : ¬ (IsUpper v i goods (hold goods base i) ∧ IsRobust v i goods (hold goods base i)) := fun h => by
      have := h.1.2.1; omega
    simp only [this, ↓reduceIte]
  rw [hRy, hRY, level_single]
  rcases hY with ⟨hl1, _⟩ | hup | hlp
  · match hS : hold goods base i, hl1 with
    | [], _ => simp only [level]; omega
    | [s], _ =>
      rw [hS, value_singleton] at hlt
      rw [level_single]
      have hyf : y ∉ (relevant v i goods).filter (fun g' => decide (v i y < v i g')) := by simp
      have hsub : ∀ g ∈ y :: (relevant v i goods).filter (fun g' => decide (v i y < v i g')),
          g ∈ (relevant v i goods).filter (fun g' => decide (v i s < v i g')) := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact List.mem_filter.mpr ⟨hyr, decide_eq_true hlt⟩
        · have h1 := List.mem_filter.mp hg
          have h2 := of_decide_eq_true h1.2
          exact List.mem_filter.mpr ⟨h1.1, decide_eq_true (by omega)⟩
      have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hyf, hrnd.filter _⟩) hsub
      simp only [List.length_cons] at this
      omega
  · have := hup.2.1; omega
  · have hlen := hlp.2.1
    rw [level_multi v i goods (by omega)]
    have hLP := hlp.2.2.2.1
    simp only [show ¬ topV v i goods < value v i (hold goods base i) by omega, ↓reduceIte]
    have hyt : ¬ v i y < topV v i goods := fun h => by
      have := hlp.2.2.2.2.2 y hyr hyY h; omega
    have h0 : ((relevant v i goods).filter (fun g' => decide (v i y < v i g'))).length = 0 := by
      match hf : (relevant v i goods).filter (fun g' => decide (v i y < v i g')) with
      | [] => rfl
      | g :: _ =>
        exfalso
        have hg : g ∈ (relevant v i goods).filter (fun g' => decide (v i y < v i g')) := by rw [hf]; simp
        have h1 := List.mem_filter.mp hg
        have h2 := of_decide_eq_true h1.2
        have := le_topV v i goods (mem_relevant.mp h1.1).1
        omega
    omega

/-- A want trade with a receiver strictly raises the robust level sum. -/
theorem trade_potentialR_lt (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {base : G → Option A}
    (hb : Valid v agents goods base) {x : A} {q : G → Bool} {r : A → Option A} {up : Bool}
    (h : TradeOK v agents goods base x q r up) (hrec : ∃ j w, r j = some w) :
    potentialR v agents goods base < potentialR v agents goods (trade base x q r up) := by
  have recv_lt : ∀ {i}, Receives r i →
      levelR v i goods (hold goods base i) < levelR v i goods (hold goods (trade base x q r up) i) := by
    intro i ⟨j, hj⟩
    obtain ⟨_, hi, y, hyg, hy, hlt⟩ := h.give j i hj
    have hwx : up = true → i ≠ x := fun hu e => (h.upx hu).1 (e ▸ ⟨j, hj⟩)
    rw [hold_trade_recv hgd h hj hwx hy]
    have hyY : y ∉ hold goods base i := fun hm => by have := le_value_of_mem v i hm; omega
    exact levelR_lt_of_want hgd hc hi (hb.allowed i hi) hyg hyY hlt
  apply sum_map_lt
  · intro i hi
    by_cases hir : Receives r i
    · exact Nat.le_of_lt (recv_lt hir)
    · by_cases hux : up = true ∧ i = x
      · obtain ⟨hu, rfl⟩ := hux
        subst hu
        rw [hold_trade_up h]
        exact levelR_mono v hgd (hb.allowed i hi) (h.upx rfl).2.2.2.1 (hold_nodup hgd base i) (hgd.filter q)
          (fun g hg => (mem_hold.mp hg).1) (fun g hg => (List.mem_filter.mp hg).1) (h.upx rfl).2.2.2.2.1
      · rw [hold_trade_other h hir (fun hu e => hux ⟨hu, e⟩)]
        exact Nat.le_refl _
  · obtain ⟨j, w, hjw⟩ := hrec
    exact ⟨w, (h.give j w hjw).2.1, recv_lt ⟨j, hjw⟩⟩

/-- At a maximum, a valid want trade with a receiver is impossible (Lemma R). -/
theorem trade_contra (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {base : G → Option A}
    (hmax : IsMaximumR v agents goods base) {x : A} {q : G → Bool} {r : A → Option A} {up : Bool}
    (h : TradeOK v agents goods base x q r up) (hval : Valid v agents goods (trade base x q r up))
    (hrec : ∃ j w, r j = some w) : False := by
  have h1 := trade_potentialR_lt hgd hc hmax.1.1 h hrec
  have h2 := potentialR_le_of_max hgd hmax hval
  omega

omit [DecidableEq G] in
/-- The walk from a frozen agent to a free one has a receiver. -/
theorem path_recv {base : G → Option A} {x l : A} {Q : List A} (hQh : Q.head? = some x) (hQnd : Q.Nodup)
    (hl : Q.getLast? = some l) (hfx : Frozen v agents goods base x) (hlf : ¬ Frozen v agents goods base l) :
    ∃ j w, nextIn Q j = some w := by
  have hxQ : x ∈ Q := List.mem_of_mem_head? hQh
  have hne : Q.getLast? ≠ some x := by
    rw [hl]; intro e; injection e with e; subst e; exact hlf hfx
  obtain ⟨w, hw⟩ := nextIn_some hQnd hxQ hne
  exact ⟨x, w, hw⟩

/-- Lemma 4 for an upgrade of at most two goods, at a maximum: the agent is free (a frozen one starts a want trade,
against Lemma R), so it has a free self-upgrade. -/
theorem small_at_max (hgd : goods.Nodup) (hc : R1Core4 v agents goods) {base : G → Option A}
    (hmax : IsMaximumR v agents goods base) {x : A} (hx : x ∈ agents) {q : G → Bool}
    (hq : ∀ g ∈ goods, q g = true → base g = none) (hN : Allowed v x goods (goods.filter q))
    (hgain : value v x (hold goods base x) < value v x (goods.filter q)) (h2 : (goods.filter q).length ≤ 2) :
    ∃ x' ∈ agents, FreeSelfUp v agents goods base x' := by
  have hb := hmax.1.1
  by_cases hfx : Frozen v agents goods base x
  · exfalso
    have hwalk := exists_walk (v := v) (agents := agents) (goods := goods) (base := base) agents.length [x]
      (by omega) (by simp) (by simp) (fun j hj => by simp at hj; subst hj; exact ⟨hx, hfx⟩) trivial
    rcases hwalk with ⟨Q, hQh, hQnd, hQc, hQa, l, hl, hlf⟩ | ⟨C, hCnd, hCc, hCa, c, w₀, hcl, hw₀, hcw⟩
    · have hok := tradeOK_path hb (by simpa using hQh) hQnd hQc hQa hl hlf hfx hq hN hgain
      exact trade_contra hgd hc hmax hok
        (trade_valid_better hb hgd hok (fun _ h3 => absurd h3 (by omega)) (Or.inl rfl)).1
        (path_recv (by simpa using hQh) hQnd hl hfx hlf)
    · have hok := tradeOK_cycle hCnd hCc hCa hcl hw₀ hcw
      exact trade_contra hgd hc hmax hok
        (trade_valid_better hb hgd hok (fun h => absurd h (by simp)) (Or.inr ⟨c, w₀, by simp [cycNext]⟩)).1
        ⟨c, w₀, by simp [cycNext]⟩
  · exact ⟨x, hx, free_of_not_frozen hb hfx, q, fun g hg hqg => Or.inr (hq g hg hqg), hN, h2, hgain⟩

/-- **Lemma 4 at a maximum of the robust order.** If the leftover goods alone threaten an agent, some free agent has
an allowed self-upgrade of at most two goods: every case of Lemma 4 that passes a good to a wanter strictly raises the
robust level sum, against Lemma R. -/
theorem threat_at_max (hgd : goods.Nodup) (hs : Strict v agents goods) (hc : R1Core4 v agents goods)
    {base : G → Option A} (hmax : IsMaximumR v agents goods base) {x : A} (hx : x ∈ agents)
    (hJ : value v x (hold goods base x) < value v x (leftover goods base)) :
    ∃ x' ∈ agents, FreeSelfUp v agents goods base x' := by
  have hb := hmax.1.1
  obtain ⟨q, hq, hN, hgain, _, hlen⟩ := exists_upgrade hb hgd hs hc hx hJ
  rcases hlen with h2 | ⟨y, hy, hytop, h3⟩
  · exact small_at_max hgd hc hmax hx hq hN hgain h2
  have hNsub : ∀ g ∈ goods.filter q, g ∈ goods ∧ base g = none := fun g hg =>
    ⟨(List.mem_filter.mp hg).1, hq g (List.mem_filter.mp hg).1 (List.mem_filter.mp hg).2⟩
  have hNpos := allowed_pos hN
  have hyg : y ∈ goods ∧ base y = some x := mem_hold.mp (by rw [hy]; simp)
  by_cases hfx : Frozen v agents goods base x
  · -- frozen: the walk from x
    have hwalk := exists_walk (v := v) (agents := agents) (goods := goods) (base := base) agents.length [x]
      (by omega) (by simp) (by simp) (fun j hj => by simp at hj; subst hj; exact ⟨hx, hfx⟩) trivial
    rcases hwalk with ⟨Q, hQh, hQnd, hQc, hQa, l, hl, hlf⟩ | ⟨C, hCnd, hCc, hCa, c, w₀, hcl, hw₀, hcw⟩
    · have hok := tradeOK_path hb (by simpa using hQh) hQnd hQc hQa hl hlf hfx hq hN hgain
      by_cases hbig : ∀ i ∈ agents, i ≠ x → ∀ hh ∈ goods.filter q,
          value v i ((goods.filter q).erase hh) ≤ value v i (hold goods (trade base x q (nextIn Q) true) i)
      · exact (trade_contra hgd hc hmax hok (trade_valid_better hb hgd hok (fun _ _ => hbig) (Or.inl rfl)).1
          (path_recv (by simpa using hQh) hQnd hl hfx hlf)).elim
      · -- the three-good switch: an agent threatened by the triple has an upgrade of at most two goods
        obtain ⟨i, hi⟩ := Classical.not_forall.mp hbig
        have hi' : i ∈ agents := Classical.byContradiction fun hn => hi fun h => absurd h hn
        have hix : i ≠ x := Classical.byContradiction fun hn => hi fun _ h => absurd h hn
        obtain ⟨hh, hhh⟩ : ∃ hh ∈ goods.filter q, value v i (hold goods (trade base x q (nextIn Q) true) i) <
            value v i ((goods.filter q).erase hh) := by
          refine Classical.byContradiction fun hn => hi fun _ _ hh hhm => Nat.le_of_not_lt fun hlt => hn ⟨hh, hhm, hlt⟩
        obtain ⟨hhm, hlt⟩ := hhh
        have hge := trade_value_ge hgd hok i hi'
        have hsub : ((goods.filter q).erase hh).Sublist (leftover goods base) :=
          List.erase_sublist.trans (filter_sublist_filter (fun g hg hqg => by
            simpa using hq g hg hqg))
        have hJi : value v i (hold goods base i) < value v i (leftover goods base) :=
          Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hge hlt) (value_sublist v i hsub)
        obtain ⟨qi, hqi, hNi, hgaini, hmini, hleni⟩ := exists_upgrade hb hgd hs hc hi' hJi
        rcases hleni with h2i | ⟨ai, hai, haitop, h3i⟩
        · exact small_at_max hgd hc hmax hi' hqi hNi hgaini h2i
        · exfalso
          -- the goods of the triple that i values all lie in i's own triple, so they are worth at most its top
          have haig : ai ∈ goods ∧ base ai = some i := mem_hold.mp (by rw [hai]; simp)
          let T := ((goods.filter q).erase hh).filter (fun g => decide (0 < v i g))
          have hTv : value v i T = value v i ((goods.filter q).erase hh) := value_filter_pos i _
          have hTnd : T.Nodup := ((hgd.filter q).sublist List.erase_sublist).sublist List.filter_sublist
          have hTmem : ∀ g ∈ T, g ∈ goods ∧ base g = none ∧ 0 < v i g := by
            intro g hg
            have h1 := List.mem_filter.mp hg
            have h2 := hNsub g (List.mem_of_mem_erase h1.1)
            exact ⟨h2.1, h2.2, by simpa using h1.2⟩
          have hNind : (goods.filter qi).Nodup := hgd.filter qi
          have hNimem : ∀ g ∈ goods.filter qi, g ∈ goods ∧ base g = none :=
            fun g hg => ⟨(List.mem_filter.mp hg).1, hqi g (List.mem_filter.mp hg).1 (List.mem_filter.mp hg).2⟩
          have hNipos := allowed_pos hNi
          have hrel : ∀ g, g ∈ goods → 0 < v i g → g ∈ relevant v i goods := fun g hg hp => by
            simp only [relevant, List.mem_filter, decide_eq_true_eq]; exact ⟨hg, hp⟩
          have haiN : ai ∉ goods.filter qi := fun hm => by
            rw [(hNimem ai hm).2] at haig; exact absurd haig.2 (by simp)
          have hR4 := (hc i hi').2.1
          have hallrel : ∀ g ∈ relevant v i goods, g = ai ∨ g ∈ goods.filter qi := by
            have hsub' := subset_of_length_le (l₁ := ai :: goods.filter qi) (l₂ := relevant v i goods)
              (List.nodup_cons.mpr ⟨haiN, hNind⟩)
              (fun g hg => by
                rcases List.mem_cons.mp hg with rfl | hm
                · exact hrel g haig.1 (by rw [haitop]; exact topV_pos hc hi')
                · exact hrel g (hNimem g hm).1 (hNipos g hm))
              (by simp; omega)
            intro g hg
            have := hsub' g hg
            rcases List.mem_cons.mp this with e | hm
            · exact Or.inl e
            · exact Or.inr hm
          have hTN : ∀ g ∈ T, g ∈ goods.filter qi := by
            intro g hg
            obtain ⟨hgg, hgb, hgp⟩ := hTmem g hg
            rcases hallrel g (hrel g hgg hgp) with rfl | hm
            · rw [hgb] at haig; exact absurd haig.2 (by simp)
            · exact hm
          have hTlen : T.length ≤ 2 := by
            have := List.length_filter_le (fun g => decide (0 < v i g)) ((goods.filter q).erase hh)
            rw [List.length_erase_of_mem hhm, h3] at this
            exact Nat.le_trans this (by omega)
          obtain ⟨g, hgN, hgT⟩ : ∃ g ∈ goods.filter qi, g ∉ T := by
            refine Classical.byContradiction fun hn => ?_
            have hall : ∀ g ∈ goods.filter qi, g ∈ T := fun g hg =>
              Classical.byContradiction fun hgT => hn ⟨g, hg, hgT⟩
            have := List.Nodup.length_le_of_subset hNind hall
            omega
          have hTsub : ∀ g' ∈ T, g' ∈ (goods.filter qi).erase g := by
            intro g' hg'
            have hne : g' ≠ g := fun e => hgT (e ▸ hg')
            exact (List.mem_erase_of_ne hne).mpr (hTN g' hg')
          have h1 := value_le_of_subset v i hTnd (hNind.erase g) hTsub
          have h2 := hmini g hgN
          omega
    · have hok := tradeOK_cycle hCnd hCc hCa hcl hw₀ hcw
      exact (trade_contra hgd hc hmax hok (trade_valid_better hb hgd hok (fun h => absurd h (by simp))
        (Or.inr ⟨c, w₀, by simp [cycNext]⟩)).1 ⟨c, w₀, by simp [cycNext]⟩).elim
  · -- free: take the top and the best... any good b of the triple: {a, b} is an upper set
    obtain ⟨b, hb₁⟩ : ∃ b, b ∈ goods.filter q := by
      match hm : goods.filter q, h3 with
      | b :: _, _ => exact ⟨b, by simp⟩
    have hbg := hNsub b hb₁
    have hyb : y ≠ b := fun e => by rw [e] at hyg; rw [hyg.2] at hbg; exact absurd hbg.2 (by simp)
    let p : G → Bool := fun g => decide (g = y ∨ g = b)
    have hLnd : (goods.filter p).Nodup := hgd.filter p
    have hLmem : ∀ g, g ∈ goods.filter p ↔ g = y ∨ g = b := by
      intro g
      simp only [List.mem_filter, p, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨hyg.1, Or.inl rfl⟩
        · exact ⟨hbg.1, Or.inr rfl⟩
    have hyb' : [y, b].Nodup := by simp [hyb]
    have hval2 : value v x (goods.filter p) = v x y + v x b := by
      have h1 := value_le_of_subset v x hLnd hyb' (fun g hg => by
        rcases (hLmem g).mp hg with rfl | rfl <;> simp)
      have h2 := value_le_of_subset v x hyb' hLnd (fun g hg => by
        simp at hg; exact (hLmem g).mpr hg)
      simp [value] at h1 h2
      simp only [value] at *
      omega
    have hlen2 : (goods.filter p).length = 2 := by
      have h1 := List.Nodup.length_le_of_subset hLnd (l₂ := [y, b]) (fun g hg => by
        rcases (hLmem g).mp hg with rfl | rfl <;> simp)
      have h2 := List.Nodup.length_le_of_subset hyb' (l₂ := goods.filter p) (fun g hg => by
        simp at hg; exact (hLmem g).mpr hg)
      simp at h1 h2
      omega
    have hbpos := hNpos b hb₁
    have hupper : IsUpper v x goods (goods.filter p) := by
      refine ⟨fun g hg => ?_, by rw [hval2, hytop]; omega, fun g hg => ?_⟩
      · rcases (hLmem g).mp hg with rfl | rfl
        · rw [hytop]; exact topV_pos hc hx
        · exact hbpos
      · have hl1 : ((goods.filter p).erase g).length ≤ 1 := by rw [List.length_erase_of_mem hg]; omega
        exact value_le_of_length_le_one' x hl1 (fun g' hg' => le_topV v x goods
          ((hLmem g').mp (List.mem_of_mem_erase hg') |>.elim (fun e => e ▸ hyg.1) (fun e => e ▸ hbg.1)))
    refine ⟨x, hx, free_of_not_frozen hb hfx, p, fun g hg hpg => ?_, Or.inr (Or.inl hupper), by omega,
      by rw [hy, value_singleton, hval2]; omega⟩
    have : g = y ∨ g = b := (hLmem g).mp (List.mem_filter.mpr ⟨hg, hpg⟩)
    rcases this with rfl | rfl
    · exact Or.inl hyg.2
    · exact Or.inr hbg.2


end robustLemma4

/-- **Claim T′ in case (L)** (a hypothesis, never an axiom): a non-completable maximum of the robust order in which
some free agent has an allowed self-upgrade of at most two goods (each such upgrade then breaks (V3):
`selfUp_breaks_v3`) has every agent holding an upper set. -/
def HLL (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumR v agents goods base → ¬ Completable v agents goods base →
      (∃ x ∈ agents, FreeSelfUp v agents goods base x) → ∀ i ∈ agents, IsUpper v i goods (hold goods base i)

/-- With Lemma 4 at a maximum, `HLL` implies `HL'`. -/
theorem hl'_of_hll (h : HLL A G) : HL' A G := by
  intro v agents goods hne hag hgd hc hs base hmax hnc hcase
  refine h v agents goods hne hag hgd hc hs base hmax hnc ?_
  rcases hcase with ⟨i, hi, hJi⟩ | ⟨x, hx, hfree, p, hp, hN, h2, hgain, _⟩
  · exact threat_at_max hgd hs hc hmax hi hJi
  · exact ⟨x, hx, hfree, p, hp, hN, h2, hgain⟩

/-- `HLL` implies `HL`. -/
theorem hl_of_hll (h : HLL A G) : HL A G := hl_of_hl' (hl'_of_hll h)

/-- **No lower-pair or non-robust upper holder on an F₂-clash cycle at a maximum (`HC3'`), and Claim T′ in case (L)
(`HLL`), imply TARGET₄.** -/
theorem target4_of_HC3'_HLL (I : Inst) (hn : 0 < I.n) (h3 : HC3' (Fin I.n) (Fin I.m)) (hl : HLL (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_HC3'_HL' I hn h3 (hl'_of_hll hl) h4

end DE4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE4.levelR_lt_of_want
#print axioms EFX.DE4.trade_potentialR_lt
#print axioms EFX.DE4.trade_contra
#print axioms EFX.DE4.path_recv
#print axioms EFX.DE4.small_at_max
#print axioms EFX.DE4.threat_at_max
#print axioms EFX.DE4.hl'_of_hll
#print axioms EFX.DE4.hl_of_hll
#print axioms EFX.DE4.target4_of_HC3'_HLL
