import EFX.OC1Max

/-!
# Perfect starts and Lemma RED (`k4/sdc.md` §31, Lemma RED)

Lemma RED reduces OC₁ at maximum-matching starts to OC₁ at *perfect starts*, where every agent that values some
good holds a pick (agents that value nothing, *null agents*, are allowed). Let `Y` be maximum-matching picks of a
strict instance, `U` the pickless agents, `S` the agents with a pick reachable from `U` by `Y`-alternating paths,
and `T` the other agents. By Lemma MAX (`EFX.OC1Max.max_no_augment`) every good valued by an agent of `S ∪ U` is the
pick of an agent of `S` (`red_values`). Remove `S` with its picks: the rest `I′` (agents `T ∪ U`, goods the
others) is again a strict instance with at most four relevant goods per agent, `Y` restricted to it is Pareto
optimal there, hence (SDPO) the picks of some order of `I′` (`red_order`), and that start is perfect
(`red_perfect`). An EFX₀ allocation of `I′` extended by the singletons `{Y_s}` of the agents of `S` is EFX₀ for the
whole instance (`red_extend`): a singleton is never strongly envied, and the agents of `S ∪ U` value nothing outside
the picks of `S`.

- `PerfectStart`, `ConjOC1perfWith` (any move relation), `ConjOC1perf` (the moves of `EFX.OC1Max.OneMove`):
  **Conjecture OC₁ᵖᵉʳᶠ**, for every strict instance with at most four relevant goods per agent and at least one
  agent, and every order giving a perfect start, a one-absorber completion at the picks or after one move. Both are
  `Prop`s. (At least one agent is needed: with none, no allocation of a nonempty set of goods exists.)
- `exists_efx0_of_conjOC1perfWith`, `target4_of_conjOC1perfWith`, **`target4_of_conjOC1perf`: OC₁ᵖᵉʳᶠ ⟹ TARGET₄**,
  without the core reduction: ties by K4.TIE's perturbation (`EFX.tieBreak`), then MAXSD and RED.

Only the allocation part of RED (iii) is formalized; the transfer of moves and absorber counts from `I′` to the
whole instance is not needed for TARGET₄.
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- A **perfect start**: every listed agent that values some good of `goods` is matched. -/
def PerfectStart (v : A → G → Nat) (agents : List A) (goods : List G) (μ : A → Option G) : Prop :=
  ∀ i ∈ agents, (∃ g ∈ goods, 0 < v i g) → (μ i).isSome

/-- **OC₁ at perfect starts, for any move relation `Move`**: in every strict instance with at least one agent and
at most four relevant goods per agent, for every order whose picks form a perfect start, the picks have a
one-absorber completion, or some state one `Move` reaches from them has one. -/
def ConjOC1perfWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ ord : List A, ord.Perm agents →
      PerfectStart v agents goods (sdPick v ord goods) →
      OneAbsorber v agents goods (pickBase v goods ord) ∨
        ∃ B', Move v agents goods (pickBase v goods ord) B' ∧ OneAbsorber v agents goods B'

/-- **Conjecture OC₁ᵖᵉʳᶠ** (`k4/sdc.md` §31, Lemma RED): `ConjOC1perfWith` for the moves of `k4/sdc.md` §29 (an
addition, a chain or a ring). A `Prop`, not an axiom. It is **false** (`EFX.OC1Max.not_conjOC1perf` in
`EFX/OC1MaxCex.lean`); the implication `target4_of_conjOC1perf` stands. -/
def ConjOC1perf (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjOC1perfWith A G (fun v agents goods => OneMove v agents goods)

section red
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem value_eq_zero_of_forall {i : A} : ∀ {S : List G}, (∀ g ∈ S, v i g = 0) → value v i S = 0
  | [], _ => rfl
  | g :: S, h => by
    rw [value_cons, h g List.mem_cons_self, value_eq_zero_of_forall fun x hx => h x (List.mem_cons_of_mem _ hx)]

omit [DecidableEq A] [DecidableEq G] in
/-- A reachable agent is reached from an unmatched listed agent. -/
theorem exists_start {μ : A → Option G} {b : A} (h : AltReach v agents μ b) : ∃ u ∈ agents, μ u = none := by
  induction h with
  | start ha hμ => exact ⟨_, ha, hμ⟩
  | step _ _ _ ih => exact ih

omit [DecidableEq G] in
/-- **RED (ii)**: at a maximum matching `Y`, every good valued by an agent reachable from an unmatched agent is held
by a reachable matched agent (an agent of `S`). -/
theorem red_values {Y : A → Option G} (hmax : IsMaximum v agents goods Y) {i : A} (hi : AltReach v agents Y i)
    {g : G} (hg : g ∈ goods) (hpos : 0 < v i g) : ∃ b, Y b = some g ∧ (Y b).isSome ∧ AltReach v agents Y b := by
  have : ∃ b, Y b = some g := Classical.byContradiction fun hno => by
    have := max_no_augment hmax hi g hg fun x hx => hno ⟨x, hx⟩
    omega
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb, by simp [hb], AltReach.step hi hb hpos⟩

/-- **Lemma RED, the allocation part.** Let `Y` be a maximum matching of a strict instance, Pareto optimal (as
serial-dictatorship picks are), and `P a` say that `a` is unmatched or not reachable (`a ∈ T ∪ U`). The reduced
instance (the agents with `P`, the goods that no agent outside `P` holds) has an order whose picks are `Y` restricted
to it and form a perfect start; and every EFX₀ allocation of the reduced instance, extended by giving each agent
outside `P` its pick, is an EFX₀ allocation of the whole instance. -/
theorem red {Y : A → Option G} (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hs : Strict v agents goods)
    (hmax : IsMaximum v agents goods Y) (hpo : ParetoOpt v agents goods Y) :
    ∃ (agents' : List A) (goods' : List G) (ord' : List A),
      agents' ≠ [] ∧ agents'.Nodup ∧ goods'.Nodup ∧ agents'.Sublist agents ∧ goods'.Sublist goods ∧
      ord'.Perm agents' ∧ PerfectStart v agents' goods' (sdPick v ord' goods') ∧
      ∀ X' : G → A, IsAllocation agents' goods' X' → EFX0L v agents' goods' X' →
        ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  classical
  have hYm := hmax.1
  -- `P a`: `a` is in `T ∪ U`
  let P : A → Prop := fun a => Y a = none ∨ ¬ AltReach v agents Y a
  let agents' := agents.filter (fun a => decide (P a))
  let goods' := goods.filter (fun g => decide (∀ s, Y s = some g → P s))
  have hmemA : ∀ a, a ∈ agents' ↔ a ∈ agents ∧ P a := fun a => by simp [agents']
  have hmemG : ∀ g, g ∈ goods' ↔ g ∈ goods ∧ ∀ s, Y s = some g → P s := fun g => by simp [goods']
  -- agents of `S ∪ U` value no good of `goods'`
  have hzero : ∀ i, AltReach v agents Y i → ∀ g ∈ goods', v i g = 0 := by
    intro i hi g hg
    obtain ⟨hg1, hg2⟩ := (hmemG g).mp hg
    refine Nat.eq_zero_of_not_pos fun hpos => ?_
    obtain ⟨b, hb, hbs, hbr⟩ := red_values hmax hi hg1 hpos
    rcases hg2 b hb with h | h
    · rw [h] at hbs; cases hbs
    · exact h hbr
  -- the restricted picks
  let Y' : A → Option G := fun a => if P a then Y a else none
  have hY'm : IsMatching v agents' goods' Y' := by
    refine ⟨fun a g ha => ?_, fun a b g ha hb => ?_⟩
    · by_cases hPa : P a
      · simp only [Y', hPa, ite_true] at ha
        obtain ⟨h1, h2, h3⟩ := hYm.mem a g ha
        refine ⟨(hmemA a).mpr ⟨h1, hPa⟩, (hmemG g).mpr ⟨h2, fun s hs => ?_⟩, h3⟩
        rw [hYm.inj s a g hs ha]; exact hPa
      · simp only [Y', hPa, ite_false] at ha; cases ha
    · by_cases hPa : P a <;> by_cases hPb : P b
      · simp only [Y', hPa, hPb, ite_true] at ha hb; exact hYm.inj a b g ha hb
      · simp only [Y', hPb, ite_false] at hb; cases hb
      · simp only [Y', hPa, ite_false] at ha; cases ha
      · simp only [Y', hPa, ite_false] at ha; cases ha
  have hY'po : ParetoOpt v agents' goods' Y' := by
    refine ⟨hY'm, fun ν hν himp => ?_⟩
    obtain ⟨hle, x0, hx0, hlt⟩ := himp
    have hν' : IsMatching v agents goods (fun a => if P a then ν a else Y a) := by
      refine ⟨fun a g ha => ?_, fun a b g ha hb => ?_⟩
      · by_cases hPa : P a
        · simp only [hPa, ite_true] at ha
          obtain ⟨h1, h2, h3⟩ := hν.mem a g ha
          exact ⟨((hmemA a).mp h1).1, ((hmemG g).mp h2).1, h3⟩
        · simp only [hPa, ite_false] at ha; exact hYm.mem a g ha
      · have hout : ∀ c d, P c → ¬ P d → ν c = some g → Y d = some g → False := fun c d _ hd hc' hd' =>
          hd (((hmemG g).mp (hν.mem c g hc').2.1).2 d hd')
        by_cases hPa : P a <;> by_cases hPb : P b
        · simp only [hPa, hPb, ite_true] at ha hb; exact hν.inj a b g ha hb
        · simp only [hPa, hPb, ite_true, ite_false] at ha hb; exact (hout a b hPa hPb ha hb).elim
        · simp only [hPa, hPb, ite_true, ite_false] at ha hb; exact (hout b a hPb hPa hb ha).elim
        · simp only [hPa, hPb, ite_false] at ha hb; exact hYm.inj a b g ha hb
    refine hpo.2 _ hν' ⟨fun x hx => ?_, x0, ((hmemA x0).mp hx0).1, ?_⟩
    · by_cases hPx : P x
      · have := hle x ((hmemA x).mpr ⟨hx, hPx⟩)
        rw [mval_congr (μ := Y') (ν := Y) (by simp [Y', hPx])] at this
        rw [mval_congr (μ := fun a => if P a then ν a else Y a) (ν := ν) (by simp [hPx])]
        exact this
      · exact Nat.le_of_eq (mval_congr (by simp [hPx]))
    · have hPx := ((hmemA x0).mp hx0).2
      rw [mval_congr (μ := Y') (ν := Y) (by simp [Y', hPx])] at hlt
      rw [mval_congr (μ := fun a => if P a then ν a else Y a) (ν := ν) (by simp [hPx])]
      exact hlt
  -- the reduced instance
  have hag' : agents'.Nodup := hag.sublist List.filter_sublist
  have hgd' : goods'.Nodup := hgd.sublist List.filter_sublist
  have hs' : Strict v agents' goods' := fun i hi S T hS hT hdis heq =>
    hs i ((hmemA i).mp hi).1 S T (hS.trans List.filter_sublist) (hT.trans List.filter_sublist) hdis heq
  obtain ⟨ord', hord', hsd'⟩ := exists_order_of_paretoOpt agents'.length agents' goods' Y' rfl hag' hgd'
    (strictVals_of_strict hs') hY'po
  have hsd : sdPick v ord' goods' = Y' := funext hsd'
  refine ⟨agents', goods', ord', ?_, hag', hgd', List.filter_sublist, List.filter_sublist, hord', ?_, ?_⟩
  · -- `agents'` is not empty
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil agents hne
    refine fun h0 => ?_
    · have hnot : ∀ b ∈ agents, ¬ P b := fun b hb hPb => by
        have : b ∈ agents' := (hmemA b).mpr ⟨hb, hPb⟩
        rw [h0] at this; simp at this
      have hra : AltReach v agents Y a := Classical.byContradiction fun h => hnot a ha (Or.inr h)
      obtain ⟨u, hu, hun⟩ := exists_start hra
      exact hnot u hu (Or.inl hun)
  · -- the start is perfect
    rw [hsd]
    intro i hi ⟨g, hg, hpos⟩
    obtain ⟨hi1, hPi⟩ := (hmemA i).mp hi
    simp only [Y', hPi, ite_true]
    cases hYi : Y i with
    | some _ => rfl
    | none =>
      have := hzero i (AltReach.start hi1 hYi) g hg
      omega
  · -- the extension
    intro X' hX' hE'
    let hold : G → Option A := fun g => agents.find? (fun s => decide (Y s = some g ∧ ¬ P s))
    have hold_some : ∀ g s, hold g = some s → s ∈ agents ∧ Y s = some g ∧ ¬ P s := fun g s h => by
      have h1 := List.mem_of_find?_eq_some h
      have h2 := List.find?_some h
      simp only [decide_eq_true_eq] at h2
      exact ⟨h1, h2⟩
    have hold_none : ∀ g ∈ goods, hold g = none ↔ g ∈ goods' := fun g hg => by
      constructor
      · intro h
        refine (hmemG g).mpr ⟨hg, fun s hs => Classical.byContradiction fun hPs => ?_⟩
        have := List.find?_eq_none.mp h s (hYm.mem s g hs).1
        simp only [decide_eq_true_eq, not_and, Classical.not_not] at this
        exact hPs (this hs)
      · intro h
        cases hq : hold g with
        | none => rfl
        | some s =>
          obtain ⟨-, hs1, hs2⟩ := hold_some g s hq
          exact absurd (((hmemG g).mp h).2 s hs1) hs2
    let X : G → A := fun g => match hold g with
      | some s => s
      | none => X' g
    -- bundles of agents with `P` are those of `X'`
    have hXP : ∀ j, P j → ∀ g ∈ goods, (X g = j ↔ g ∈ goods' ∧ X' g = j) := by
      intro j hPj g hg
      cases hq : hold g with
      | some s =>
        obtain ⟨-, -, hs2⟩ := hold_some g s hq
        have hng : g ∉ goods' := fun h => by rw [(hold_none g hg).mpr h] at hq; cases hq
        simp only [X, hq]
        exact ⟨fun e => absurd (e ▸ hPj) hs2, fun h => absurd h.1 hng⟩
      | none =>
        have hg' := (hold_none g hg).mp hq
        simp only [X, hq]
        exact ⟨fun e => ⟨hg', e⟩, fun h => h.2⟩
    have hbundleP : ∀ j, P j → bundle goods X j = bundle goods' X' j := by
      intro j hPj
      simp only [bundle, goods', List.filter_filter]
      refine List.filter_congr fun g hg => ?_
      have := hXP j hPj g hg
      have hm := hmemG g
      by_cases h1 : X g = j
      · have ⟨h2, h3⟩ := this.mp h1
        have h4 := ((hmemG g).mp h2).2
        simp only [h1, h3, decide_true, Bool.true_and]
        exact (decide_eq_true h4).symm
      · have : ¬ (g ∈ goods' ∧ X' g = j) := fun h => h1 (this.mpr h)
        by_cases h4 : ∀ s, Y s = some g → P s
        · have h5 : X' g ≠ j := fun e => this ⟨(hmemG g).mpr ⟨hg, h4⟩, e⟩
          have h6 := decide_eq_true h4
          simp [h1, h5, h6]
        · simp [h1, h4]
    -- bundles of agents without `P` are their picks
    have hbundleS : ∀ j ∈ agents, ¬ P j → ∀ g ∈ bundle goods X j, ∀ h ∈ bundle goods X j, g = h := by
      intro j hj hPj g hg h hh
      have key : ∀ x ∈ bundle goods X j, Y j = some x := by
        intro x hx
        obtain ⟨hxg, hxj⟩ := List.mem_filter.mp hx
        simp only [decide_eq_true_eq] at hxj
        cases hq : hold x with
        | some s =>
          obtain ⟨-, hs1, -⟩ := hold_some x s hq
          have : X x = s := by simp only [X, hq]
          rw [← hxj, this]; exact hs1
        | none =>
          have hx' := (hold_none x hxg).mp hq
          have : X x = X' x := by simp only [X, hq]
          have hm := hX' x hx'
          rw [← this, hxj] at hm
          exact absurd ((hmemA j).mp hm).2 hPj
      have e1 := key g hg
      have e2 := key h hh
      rw [e1] at e2; cases e2; rfl
    refine ⟨X, fun g hg => ?_, fun i hi j hj hij g hg => ?_⟩
    · cases hq : hold g with
      | some s => simp only [X, hq]; exact (hold_some g s hq).1
      | none =>
        simp only [X, hq]
        exact ((hmemA _).mp (hX' g ((hold_none g hg).mp hq))).1
    · by_cases hPj : P j
      · by_cases hPi : P i
        · rw [hbundleP j hPj, hbundleP i hPi]
          rw [hbundleP j hPj] at hg
          exact hE' i ((hmemA i).mpr ⟨hi, hPi⟩) j ((hmemA j).mpr ⟨hj, hPj⟩) hij g hg
        · -- `i ∈ S` values nothing outside the picks of `S`
          have hri : AltReach v agents Y i := Classical.byContradiction fun h => hPi (Or.inr h)
          have : value v i ((bundle goods X j).erase g) = 0 := value_eq_zero_of_forall fun x hx => by
            have hx1 := List.mem_of_mem_erase hx
            obtain ⟨hxg, -⟩ := List.mem_filter.mp hx1
            have hxj : X x = j := by simpa using (List.mem_filter.mp hx1).2
            exact hzero i hri x ((hXP j hPj x hxg).mp hxj).1
          rw [this]; exact Nat.zero_le _
      · -- `j ∈ S` holds a single good
        have hnd : (bundle goods X j).Nodup := hgd.sublist List.filter_sublist
        have : value v i ((bundle goods X j).erase g) = 0 := value_eq_zero_of_forall fun x hx => by
          have hxg := (hnd.mem_erase_iff).mp hx
          exact absurd (hbundleS j hj hPj x hxg.2 g hg) hxg.1
        rw [this]; exact Nat.zero_le _

end red

/-- **OC₁ᵖᵉʳᶠ (any move relation) gives EFX₀ allocations of every strict instance** with at most four relevant goods
per agent and at least one agent: MAXSD gives maximum-matching picks, RED reduces them to a perfect start of a
smaller instance, whose completion extends. -/
theorem exists_efx0_of_conjOC1perfWith_strict {Move : MoveRel A G} (h : ConjOC1perfWith A G Move)
    {v : A → G → Nat} {agents : List A} {goods : List G} (hne : agents ≠ []) (hag : agents.Nodup)
    (hgd : goods.Nodup) (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  have hsv := strictVals_of_strict hs
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd hsv
  obtain ⟨agents', goods', ord', hne'', hag', hgd', hsubA, hsubG, hord', hperf, hext⟩ :=
    red hne hag hgd hs hmax (paretoOpt_sdPick hperm hag hgd hsv)
  have h4' : ∀ i ∈ agents', (relevant v i goods').length ≤ 4 := fun i hi =>
    Nat.le_trans (hsubG.filter _).length_le (h4 i (hsubA.subset hi))
  have hs' : Strict v agents' goods' := fun i hi S T hS hT hdis heq =>
    hs i (hsubA.subset hi) S T (hS.trans hsubG) (hT.trans hsubG) hdis heq
  rcases h agents' goods' v hne'' hag' hgd' h4' hs' ord' hord' hperf with ⟨X', hX', hE', -⟩ | ⟨_, -, X', hX', hE', -⟩
  · exact hext X' hX' hE'
  · exact hext X' hX' hE'

/-- **OC₁ᵖᵉʳᶠ (any move relation) ⟹ TARGET₄ over lists**, with ties broken by K4.TIE's perturbation. -/
theorem exists_efx0_of_conjOC1perfWith {Move : MoveRel A G} (h : ConjOC1perfWith A G Move) (v : A → G → Nat)
    (agents : List A) (goods : List G) (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨X, hX, hE⟩ := exists_efx0_of_conjOC1perfWith_strict h (v := tieBreak v goods) hne hag hgd
    (fun i hi => by rw [relevant_tieBreak]; exact h4 i hi) (strict_tieBreak v goods hgd)
  exact ⟨X, hX, efx0_of_tieBreak v goods hgd hE⟩

/-- **OC₁ᵖᵉʳᶠ (any move relation) ⟹ TARGET₄** in the model's terms. -/
theorem target4_of_conjOC1perfWith (I : Inst) (hn : 0 < I.n) {Move : MoveRel (Fin I.n) (Fin I.m)}
    (h : ConjOC1perfWith (Fin I.n) (Fin I.m) Move) (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := exists_efx0_of_conjOC1perfWith h I.v (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n) (List.nodup_finRange I.m)
    (fun i _ => (numRelevant_eq I i) ▸ hk i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

/-- **Conjecture OC₁ᵖᵉʳᶠ ⟹ TARGET₄** (`k4/sdc.md` §31, Lemma RED): no core reduction is needed. -/
theorem target4_of_conjOC1perf (I : Inst) (hn : 0 < I.n) (h : ConjOC1perf (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1perfWith I hn h hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.exists_start
#print axioms EFX.OC1Max.red_values
#print axioms EFX.OC1Max.red
#print axioms EFX.OC1Max.exists_efx0_of_conjOC1perfWith_strict
#print axioms EFX.OC1Max.exists_efx0_of_conjOC1perfWith
#print axioms EFX.OC1Max.target4_of_conjOC1perfWith
#print axioms EFX.OC1Max.target4_of_conjOC1perf
