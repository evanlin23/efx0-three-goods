import EFX.Phantom
import EFX.SDERound
import EFX.OC1Perf

/-!
# The ROUND-RSD frame: ROUND-IND and the phantom base case imply TARGET₄

The main route of `k4/oc1max_multi.md` §17 and `k4/matching.md` §6 ("ROUND-RSD"), with its two open existence
statements as hypotheses. Everything else is machine-checked: SD-E(round) (`EFX.Round.sdE_round`), LIFT\*
(`EFX.Round.liftStar`), the invariants a round must keep, monotonicity of values, and termination by deletion.

**States.** Fix a strict instance (at most four relevant goods per agent) and an order `σ` whose picks form a perfect
start. A *state* is a list `ks` of settled agents (phantoms) with their sets `T k`. Its instance is the remaining
agents `remAgents agents ks` and goods `remGoods goods ks T`, its order `stOrder σ ks`, its picks `stPicks`.

**Rounds** (`Admissible`): a nonempty set `K` of present agents, settled at once along vertex-disjoint prefixes of
their earliest-wanter chains (`EPrefix`), each `k` taking an improving `T' k` (pairwise disjoint, junk or its head's
pick), such that
- (H) of SD-E(round) holds;
- (L\*) at the round's end: no `T' k` threatens a remaining agent at its value after the round, nor a round-mate at
  its threshold;
- (P2): no `T' k` threatens an earlier phantom at its threshold;
- (P3): every released head pick is worth at most its threshold to every phantom, the round's included;
- some agent remains.

`Reach` is the set of states reachable from `([], ∅)` by admissible rounds.

**The two open statements.**
- `ConjRoundInd` (ROUND-IND): at every reachable state where the picks have no one-move repair (`OC1At` fails), an
  admissible round exists.
- `ConjBasePhi` (the base case, OC₁ with phantom constraints): at every reachable state with a one-move repair, there
  is one (`OC1PhiAt`) whose completion no bundle of which threatens a phantom at its threshold.

**The frame** (`target4_of_roundRSD`): `ConjRoundInd ∧ ConjBasePhi ⟹ TARGET₄`. Along reachable states the invariant
`Inv` holds (`inv_of_reach`): no phantom's set threatens a present agent at its pick value, no phantom's set threatens
another phantom at its threshold, and the picks are a perfect start. At a state with a one-move repair, the base case
gives a completion whose values are at least the picks' (`lift_base`), and LIFT\* lifts it, together with all the
phantoms' sets, to an EFX₀ allocation of the whole instance. Otherwise ROUND-IND gives a round, which keeps the
invariant (`inv_round`, through SD-E(round)) and deletes at least one agent. Strict instances reduce to perfect
starts by Lemma RED, and ties by K4.TIE.

**Caveat: `ConjBasePhi` is false as stated** (K4.BASE.PHI, refuted; the write-up session's reading, checked
numerically, not in Lean). At T3 (n = 3, order (0, 2, 1), picks (0, 1, 4)) the round settling agent 2 along
E(2) = (2, 1) with T = {1, 3} is admissible; after it the remaining instance has a one-move repair (`OC1At`), but no
completion respects the phantom, since good 0 is worth 38 to agent 2 (`OC1PhiAt` fails). So the hypothesis of
`target4_of_roundRSD` cannot be met; the theorem stands as an implication. The corrected route is the BASE-R frame
(`EFX/BaseR.lean`, K4.BASE.GR.LEAN), where the recursion takes P1-free rounds only and stops at a lifted completion,
a final round or a base repair.
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4 LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## States, rounds, reachable states -/

/-- The order of the agents still present at the state with settled agents `ks`. -/
def stOrder (σ ks : List A) : List A := σ.filter (fun a => decide (a ∉ ks))

/-- The picks at a state: serial dictatorship of the remaining order on the remaining goods. -/
def stPicks (v : A → G → Nat) (σ : List A) (goods : List G) (ks : List A) (T : A → List G) : A → Option G :=
  sdPick v (stOrder σ ks) (remGoods goods ks T)

/-- The settled sets after a round that settles `K` with sets `T'`. -/
def updT (K : List A) (T' T : A → List G) (a : A) : List G := if a ∈ K then T' a else T a

/-- The head of `k`'s chain `k :: rest k`. -/
abbrev headOf (rest : A → List A) (k : A) : A := (k :: rest k).getLast (List.cons_ne_nil _ _)

/-- **An admissible round** at the state `(ks, T)`: it settles `K` along the chains `k :: rest k` with sets `T' k`. -/
structure Admissible (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A)
    (T : A → List G) (K : List A) (rest : A → List A) (T' : A → List G) : Prop where
  ne : K ≠ []
  present : ∀ k ∈ K, k ∈ remAgents agents ks
  remains : ∃ a ∈ remAgents agents ks, a ∉ K
  chains : ∀ k ∈ K, EPrefix v (remAgents agents ks) (stOrder σ ks) (stPicks v σ goods ks T) (k :: rest k)
  disj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ∀ x ∈ k :: rest k, x ∉ k' :: rest k'
  sets : ∀ k ∈ K, (T' k).Nodup ∧ ∀ g ∈ T' k, g ∈ remGoods goods ks T ∧
    ((∀ x, stPicks v σ goods ks T x ≠ some g) ∨ stPicks v σ goods ks T (headOf rest k) = some g)
  sets_disj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ∀ g ∈ T' k, g ∉ T' k'
  hH : ∀ a ∈ remAgents agents ks, a ∉ K → ∀ k ∈ K, ∀ g, stPicks v σ goods ks T (headOf rest k) = some g →
    (∀ k' ∈ K, g ∉ T' k') → Wants v (stPicks v σ goods ks T) a (headOf rest k) →
    ∃ b, stPicks v σ goods ks T (roundSrc K rest a) = some b ∧ v a g < v a b
  improving : ∀ k ∈ K, mval v (stPicks v σ goods ks T) k < value v k (T' k)
  lstar : ∀ k ∈ K, ∀ a ∈ remAgents agents ks, a ∉ K →
    ¬ Threat v a (T' k) (mval v (fun b => stPicks v σ goods ks T (roundSrc K rest b)) a)
  lstar_mates : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ¬ Threat v k' (T' k) (value v k' (T' k'))
  p2 : ∀ k ∈ K, ∀ φ ∈ ks, ¬ Threat v φ (T' k) (value v φ (T φ))
  p3 : ∀ k ∈ K, ∀ g, stPicks v σ goods ks T (headOf rest k) = some g → (∀ k' ∈ K, g ∉ T' k') →
    (∀ φ ∈ ks, v φ g ≤ value v φ (T φ)) ∧ ∀ k' ∈ K, v k' g ≤ value v k' (T' k')

/-- **The reachable states**: from no phantoms, by admissible rounds. -/
inductive Reach (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) :
    List A → (A → List G) → Prop
  | start : Reach v agents goods σ [] (fun _ => [])
  | round {ks : List A} {T : A → List G} {K : List A} {rest : A → List A} {T' : A → List G} :
      Reach v agents goods σ ks T → Admissible v agents goods σ ks T K rest T' →
      Reach v agents goods σ (ks ++ K) (updT K T' T)

/-- **OC₁ at the state** (no phantom constraints): the picks have a one-absorber completion, or one move reaches a
state that has one. -/
def OC1At (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A) (T : A → List G) :
    Prop :=
  OneAbsorber v (remAgents agents ks) (remGoods goods ks T) (pickBase v (remGoods goods ks T) (stOrder σ ks)) ∨
    ∃ B', OneMove v (remAgents agents ks) (remGoods goods ks T)
      (pickBase v (remGoods goods ks T) (stOrder σ ks)) B' ∧
      OneAbsorber v (remAgents agents ks) (remGoods goods ks T) B'

/-- A one-absorber completion of `B` at the state that **respects the phantom constraints**: none of its bundles
threatens a phantom at its threshold. -/
def OneAbsorberPhi (v : A → G → Nat) (agents : List A) (goods : List G) (ks : List A) (T : A → List G)
    (B : A → List G) : Prop :=
  ∃ X : G → A, IsAllocation (remAgents agents ks) (remGoods goods ks T) X ∧
    EFX0L v (remAgents agents ks) (remGoods goods ks T) X ∧ (∀ i ∈ remAgents agents ks, ∀ g ∈ B i, X g = i) ∧
    (∃ a, ∀ i ∈ remAgents agents ks, i ≠ a →
      ((junkOf (remAgents agents ks) (remGoods goods ks T) B).filter (fun g => X g = i)).length ≤ 1) ∧
    ∀ φ ∈ ks, ∀ j ∈ remAgents agents ks, ¬ Threat v φ (bundle (remGoods goods ks T) X j) (value v φ (T φ))

/-- **OC₁ with phantom constraints at the state.** -/
def OC1PhiAt (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A) (T : A → List G) :
    Prop :=
  OneAbsorberPhi v agents goods ks T (pickBase v (remGoods goods ks T) (stOrder σ ks)) ∨
    ∃ B', OneMove v (remAgents agents ks) (remGoods goods ks T)
      (pickBase v (remGoods goods ks T) (stOrder σ ks)) B' ∧ OneAbsorberPhi v agents goods ks T B'

/-- **Conjecture ROUND-IND** (`k4/matching.md` §6, `k4/oc1max_multi.md` §17): at every reachable state with no
one-move repair, an admissible round exists. A `Prop`, not an axiom. -/
def ConjRoundInd (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ σ : List A, σ.Perm agents →
      PerfectStart v agents goods (sdPick v σ goods) → ∀ (ks : List A) (T : A → List G),
        Reach v agents goods σ ks T → ¬ OC1At v agents goods σ ks T →
          ∃ (K : List A) (rest : A → List A) (T' : A → List G), Admissible v agents goods σ ks T K rest T'

/-- **The base case: OC₁ with phantom constraints.** At every reachable state with a one-move repair, there is one
that respects the phantom constraints. A `Prop`, not an axiom. **False as stated** (K4.BASE.PHI: at T3, after its
only admissible round, no completion respects the phantom); see the module docstring and the BASE-R frame. -/
def ConjBasePhi (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ σ : List A, σ.Perm agents →
      PerfectStart v agents goods (sdPick v σ goods) → ∀ (ks : List A) (T : A → List G),
        Reach v agents goods σ ks T → OC1At v agents goods σ ks T → OC1PhiAt v agents goods σ ks T

/-! ## Lists after a round -/

omit [DecidableEq G] in
theorem mem_stOrder {σ ks : List A} {a : A} : a ∈ stOrder σ ks ↔ a ∈ σ ∧ a ∉ ks := by
  simp [stOrder]

omit [DecidableEq G] in
theorem remAgents_append (agents ks K : List A) :
    remAgents agents (ks ++ K) = (remAgents agents ks).filter (fun a => decide (a ∉ K)) := by
  unfold remAgents
  rw [List.filter_filter]
  refine List.filter_congr fun a _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_append, not_or]
  exact And.comm

omit [DecidableEq G] in
theorem stOrder_append (σ ks K : List A) :
    stOrder σ (ks ++ K) = (stOrder σ ks).filter (fun a => decide (a ∉ K)) := by
  unfold stOrder
  rw [List.filter_filter]
  refine List.filter_congr fun a _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_append, not_or]
  exact And.comm

theorem remGoods_append (goods : List G) {ks K : List A} (hK : ∀ k ∈ K, k ∉ ks) (T T' : A → List G) :
    remGoods goods (ks ++ K) (updT K T' T) =
      (remGoods goods ks T).filter (fun g => decide (g ∉ K.flatMap T')) := by
  have hupd_ks : ∀ k ∈ ks, updT K T' T k = T k := fun k hk => by
    simp [updT, show k ∉ K from fun h => hK k h hk]
  have hupd_K : ∀ k ∈ K, updT K T' T k = T' k := fun k hk => by simp [updT, hk]
  unfold remGoods
  rw [List.filter_filter]
  refine List.filter_congr fun g _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_flatMap, not_exists, not_and]
  constructor
  · intro h
    exact ⟨fun k hk hg => h k (List.mem_append_right _ hk) (by rw [hupd_K k hk]; exact hg),
      fun k hk hg => h k (List.mem_append_left _ hk) (by rw [hupd_ks k hk]; exact hg)⟩
  · rintro ⟨h1, h2⟩ k hk hg
    rcases List.mem_append.mp hk with hk | hk
    · exact h2 k hk (by rwa [hupd_ks k hk] at hg)
    · exact h1 k hk (by rwa [hupd_K k hk] at hg)

theorem stPicks_append {v : A → G → Nat} (σ : List A) (goods : List G) {ks K : List A} (hK : ∀ k ∈ K, k ∉ ks)
    (T T' : A → List G) :
    stPicks v σ goods (ks ++ K) (updT K T' T) =
      sdPick v ((stOrder σ ks).filter (fun a => decide (a ∉ K)))
        ((remGoods goods ks T).filter (fun g => decide (g ∉ K.flatMap T'))) := by
  unfold stPicks; rw [stOrder_append, remGoods_append goods hK]

omit [DecidableEq G] in
/-- An agent after a round keeps its pick or receives a pick it wants. -/
theorem roundSrc_cases {v : A → G → Nat} {agents σ : List A} {Y : A → Option G} {K : List A}
    {rest : A → List A} (hch : ∀ k ∈ K, EPrefix v agents σ Y (k :: rest k))
    (hdisj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ∀ x ∈ k :: rest k, x ∉ k' :: rest k') (a : A) :
    roundSrc K rest a = a ∨ Wants v Y a (roundSrc K rest a) := by
  by_cases h : ∃ k ∈ K, a ∈ rest k
  · obtain ⟨k, hk, ha⟩ := h
    obtain ⟨p, hp⟩ := (mem_tail_iff_pair (l := k :: rest k)).mp ha
    have hs : roundSrc K rest a = p := by rw [roundSrc_of_mem hdisj hk ha, src_of_pair (hch k hk).nodup hp]
    right; rw [hs]; exact (hch k hk).wants _ hp
  · left; exact roundSrc_of_not fun k hk ha => h ⟨k, hk, ha⟩

omit [DecidableEq G] in
/-- **Values never fall in a round.** -/
theorem mval_le_round {v : A → G → Nat} {agents σ : List A} {Y : A → Option G} {K : List A}
    {rest : A → List A} (hch : ∀ k ∈ K, EPrefix v agents σ Y (k :: rest k))
    (hdisj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ∀ x ∈ k :: rest k, x ∉ k' :: rest k') (a : A) :
    mval v Y a ≤ mval v (fun b => Y (roundSrc K rest b)) a := by
  rcases roundSrc_cases hch hdisj a with h | ⟨y, hy, hlt⟩
  · have : mval v (fun b => Y (roundSrc K rest b)) a = mval v Y a :=
      mval_congr (by show Y (roundSrc K rest a) = Y a; rw [h])
    omega
  · rw [mval_some (μ := fun b => Y (roundSrc K rest b)) (i := a) hy]; omega

/-! ## The invariant along reachable states -/

/-- **The invariant** at a state: the phantoms are listed agents with duplicate-free, pairwise disjoint sets of
goods; no phantom's set threatens a present agent at its pick value ((L\*), kept since the phantom's round), nor
another phantom at its threshold ((L\*) toward round-mates and later phantoms, (P2) toward earlier ones); and the
picks are a perfect start. -/
structure Inv (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (ks : List A)
    (T : A → List G) : Prop where
  settled : ∀ k ∈ ks, k ∈ agents
  sets : ∀ k ∈ ks, (T k).Nodup ∧ ∀ g ∈ T k, g ∈ goods
  disj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → ∀ g ∈ T k, g ∉ T k'
  real : ∀ k ∈ ks, ∀ a ∈ remAgents agents ks, ¬ Threat v a (T k) (mval v (stPicks v σ goods ks T) a)
  phantom : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → ¬ Threat v k' (T k) (value v k' (T k'))
  perfect : PerfectStart v (remAgents agents ks) (remGoods goods ks T) (stPicks v σ goods ks T)

section frame
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **An admissible round keeps the invariant.** Through SD-E(round), the picks of the new state are the goods after
the round, so values never fall; (L\*) at the round's end, improvement and (P2) cover the new phantoms. -/
theorem inv_round (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) (hsv : StrictVals v agents goods)
    {ks : List A} {T : A → List G} (hI : Inv v agents goods σ ks T) {K : List A} {rest : A → List A}
    {T' : A → List G} (hA : Admissible v agents goods σ ks T K rest T') :
    Inv v agents goods σ (ks ++ K) (updT K T' T) := by
  have hK : ∀ k ∈ K, k ∉ ks := fun k hk => (mem_remAgents.mp (hA.present k hk)).2
  have hupd_ks : ∀ k ∈ ks, updT K T' T k = T k := fun k hk => by
    simp [updT, show k ∉ K from fun h => hK k h hk]
  have hupd_K : ∀ k ∈ K, updT K T' T k = T' k := fun k hk => by simp [updT, hk]
  -- the instance at the state
  have hσS : (stOrder σ ks).Perm (remAgents agents ks) := hσ.filter _
  have hagS : (remAgents agents ks).Nodup := hag.sublist List.filter_sublist
  have hgdS : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  have hsvS : StrictVals v (remAgents agents ks) (remGoods goods ks T) := fun a ha g hg h hh =>
    hsv a (mem_remAgents.mp ha).1 g (mem_remGoods.mp hg).1 h (mem_remGoods.mp hh).1
  -- SD-E(round)
  have hsde := sdE_round hσS hagS hgdS hsvS hA.chains hA.disj (T := T')
    (fun k hk g hg => ((hA.sets k hk).2 g hg).2) hA.hH
  have hpres : ∀ a ∈ remAgents agents (ks ++ K), a ∈ remAgents agents ks ∧ a ∉ K := fun a ha => by
    obtain ⟨h1, h2⟩ := mem_remAgents.mp ha
    exact ⟨mem_remAgents.mpr ⟨h1, fun h => h2 (List.mem_append_left _ h)⟩, fun h => h2 (List.mem_append_right _ h)⟩
  have hnew : ∀ a ∈ remAgents agents (ks ++ K),
      stPicks v σ goods (ks ++ K) (updT K T' T) a = stPicks v σ goods ks T (roundSrc K rest a) := by
    intro a ha
    obtain ⟨h1, h2⟩ := mem_remAgents.mp ha
    rw [stPicks_append σ goods hK T T']
    exact hsde a (List.mem_filter.mpr ⟨mem_stOrder.mpr ⟨hσ.mem_iff.mpr h1, fun h => h2 (List.mem_append_left _ h)⟩,
      decide_eq_true fun h => h2 (List.mem_append_right _ h)⟩)
  have hmv : ∀ a ∈ remAgents agents (ks ++ K), mval v (stPicks v σ goods (ks ++ K) (updT K T' T)) a =
      mval v (fun b => stPicks v σ goods ks T (roundSrc K rest b)) a := fun a ha => mval_congr (hnew a ha)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk k' hk' hne g hg hg' => ?_, fun k hk a ha => ?_,
    fun k hk k' hk' hne => ?_, fun a ha hex => ?_⟩
  · -- the phantoms are listed agents
    rcases List.mem_append.mp hk with hk | hk
    · exact hI.settled k hk
    · exact (mem_remAgents.mp (hA.present k hk)).1
  · -- their sets
    rcases List.mem_append.mp hk with hk | hk
    · rw [hupd_ks k hk]; exact hI.sets k hk
    · rw [hupd_K k hk]
      exact ⟨(hA.sets k hk).1, fun g hg => (mem_remGoods.mp ((hA.sets k hk).2 g hg).1).1⟩
  · -- disjoint sets
    rcases List.mem_append.mp hk with hk | hk <;> rcases List.mem_append.mp hk' with hk' | hk'
    · rw [hupd_ks k hk] at hg; rw [hupd_ks k' hk'] at hg'; exact hI.disj k hk k' hk' hne g hg hg'
    · rw [hupd_ks k hk] at hg; rw [hupd_K k' hk'] at hg'
      exact (mem_remGoods.mp ((hA.sets k' hk').2 g hg').1).2 k hk hg
    · rw [hupd_K k hk] at hg; rw [hupd_ks k' hk'] at hg'
      exact (mem_remGoods.mp ((hA.sets k hk).2 g hg).1).2 k' hk' hg'
    · rw [hupd_K k hk] at hg; rw [hupd_K k' hk'] at hg'; exact hA.sets_disj k hk k' hk' hne g hg hg'
  · -- no phantom's set threatens a present agent at its new pick value
    rw [hmv a ha]
    obtain ⟨haS, haK⟩ := hpres a ha
    rcases List.mem_append.mp hk with hk | hk
    · rw [hupd_ks k hk]
      exact not_threat_mono (hI.real k hk a haS) (mval_le_round hA.chains hA.disj a)
    · rw [hupd_K k hk]; exact hA.lstar k hk a haS haK
  · -- no phantom's set threatens another phantom at its threshold
    rcases List.mem_append.mp hk with hk | hk <;> rcases List.mem_append.mp hk' with hk' | hk'
    · rw [hupd_ks k hk, hupd_ks k' hk']; exact hI.phantom k hk k' hk' hne
    · rw [hupd_ks k hk, hupd_K k' hk']
      exact not_threat_mono (hI.real k hk k' (hA.present k' hk')) (Nat.le_of_lt (hA.improving k' hk'))
    · rw [hupd_K k hk, hupd_ks k' hk']; exact hA.p2 k hk k' hk'
    · rw [hupd_K k hk, hupd_K k' hk']; exact hA.lstar_mates k hk k' hk' hne
  · -- the new picks are a perfect start
    obtain ⟨g, hg, hpos⟩ := hex
    rw [hnew a ha]
    obtain ⟨haS, -⟩ := hpres a ha
    rcases roundSrc_cases hA.chains hA.disj a with h | ⟨y, hy, -⟩
    · rw [h]
      have hg' : g ∈ remGoods goods ks T := by
        rw [remGoods_append goods hK] at hg; exact (List.mem_filter.mp hg).1
      exact hI.perfect a haS ⟨g, hg', hpos⟩
    · rw [hy]; rfl

/-- **The invariant holds at every reachable state.** -/
theorem inv_of_reach (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) (hperf : PerfectStart v agents goods (sdPick v σ goods)) {ks : List A}
    {T : A → List G} (h : Reach v agents goods σ ks T) : Inv v agents goods σ ks T := by
  induction h with
  | start =>
    have hA : remAgents agents ([] : List A) = agents := List.filter_eq_self.mpr fun a _ => by simp
    have hG : remGoods goods ([] : List A) (fun _ => []) = goods := List.filter_eq_self.mpr fun g _ => by simp
    have hO : stOrder σ ([] : List A) = σ := List.filter_eq_self.mpr fun a _ => by simp
    refine ⟨fun k hk => absurd hk List.not_mem_nil, fun k hk => absurd hk List.not_mem_nil,
      fun k hk => absurd hk List.not_mem_nil, fun k hk => absurd hk List.not_mem_nil,
      fun k hk => absurd hk List.not_mem_nil, ?_⟩
    unfold stPicks
    rw [hA, hG, hO]; exact hperf
  | round _ hA ih => exact inv_round hσ hag hgd hsv ih hA

/-- **The base case lifts.** At a state with the invariant, a one-absorber completion respecting the phantom
constraints, after at most one move, lifts with all the phantoms' sets to an EFX₀ allocation of the whole instance
(LIFT\*, every phantom in one round, at final values). -/
theorem lift_base (hσ : σ.Perm agents) (hgd : goods.Nodup) {ks : List A} {T : A → List G}
    (hI : Inv v agents goods σ ks T) (hphi : OC1PhiAt v agents goods σ ks T) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  have hgdS : (remGoods goods ks T).Nodup := hgd.sublist List.filter_sublist
  have hm := isMatching_sdPick (v := v) (hσ.filter (fun a => decide (a ∉ ks))) hgdS
  -- the picks as a state
  have hBnd : ∀ a ∈ remAgents agents ks, (pickBase v (remGoods goods ks T) (stOrder σ ks) a).Nodup := fun a _ => by
    simp only [pickBase]; cases sdPick v (stOrder σ ks) (remGoods goods ks T) a <;> simp
  have hBsub : ∀ a, ∀ g ∈ pickBase v (remGoods goods ks T) (stOrder σ ks) a, g ∈ remGoods goods ks T := by
    intro a g hg
    simp only [pickBase] at hg
    cases h : sdPick v (stOrder σ ks) (remGoods goods ks T) a with
    | none => rw [h] at hg; simp at hg
    | some y => rw [h] at hg; simp at hg; rw [hg]; exact (hm.mem a y h).2.1
  obtain ⟨B', hB', X, hX, hE, hkeep, -, hΦ⟩ : ∃ B' : A → List G,
      (∀ a ∈ remAgents agents ks, (B' a).Nodup ∧ (∀ g ∈ B' a, g ∈ remGoods goods ks T) ∧
        mval v (stPicks v σ goods ks T) a ≤ value v a (B' a)) ∧
      OneAbsorberPhi v agents goods ks T B' := by
    rcases hphi with h | ⟨B', hmove, h⟩
    · refine ⟨_, fun a ha => ⟨hBnd a ha, hBsub a, ?_⟩, h⟩
      simp only [pickBase, stPicks]; rw [value_pick]; exact Nat.le_refl _
    · refine ⟨B', fun a ha => ?_, h⟩
      have hpv : value v a (pickBase v (remGoods goods ks T) (stOrder σ ks) a) = mval v (stPicks v σ goods ks T) a := by
        simp only [pickBase, stPicks]; rw [value_pick]
      rcases move_local hBnd hmove a ha with he | ⟨j, hj, hnd, hsub, hlt⟩
      · rw [he]; exact ⟨hBnd a ha, hBsub a, by rw [hpv]; exact Nat.le_refl _⟩
      · refine ⟨hnd, fun g hg => ?_, by rw [← hpv]; exact Nat.le_of_lt hlt⟩
        rcases hsub g hg with h | h
        · exact hBsub j g h
        · exact (mem_junkOf.mp h).1
  -- values never fall at the completion
  have hfin : ∀ a ∈ remAgents agents ks,
      mval v (stPicks v σ goods ks T) a ≤ value v a (bundle (remGoods goods ks T) X a) := fun a ha => by
    obtain ⟨hnd, hsub, hle⟩ := hB' a ha
    exact Nat.le_trans hle (value_le_of_nodup_sub a hnd fun g hg => mem_bundle.mpr ⟨hsub g hg, hkeep a ha g hg⟩)
  obtain ⟨hall, hefx⟩ := liftStar hgd (ks := ks) hI.settled (T := T) hI.sets hI.disj hX hE (fun _ => 0)
    (fun _ a => if a ∈ ks then value v a (T a) else value v a (bundle (remGoods goods ks T) X a)) hΦ
    (fun _ _ _ _ h => absurd h (Nat.lt_irrefl 0))
    (fun k hk a ha hak _ => by
      by_cases has : a ∈ ks
      · simp only [has, ite_true]; exact hI.phantom k hk a has (Ne.symm hak)
      · simp only [has, ite_false]
        have haS : a ∈ remAgents agents ks := mem_remAgents.mpr ⟨ha, has⟩
        exact not_threat_mono (hI.real k hk a haS) (hfin a haS))
    (fun _ _ a _ _ => ⟨fun has => by simp [has], fun has _ => by simp [has]⟩)
  exact ⟨_, hall, hefx⟩

/-- **The ROUND-RSD frame at a perfect start**: ROUND-IND and the phantom base case give an EFX₀ allocation. The
recursion visits reachable states only, and each round deletes at least one agent. -/
theorem exists_efx0_of_rounds (hR : ConjRoundInd A G) (hB : ConjBasePhi A G) (hne : agents ≠ [])
    (hag : agents.Nodup) (hgd : goods.Nodup) (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4)
    (hs : Strict v agents goods) (hσ : σ.Perm agents) (hperf : PerfectStart v agents goods (sdPick v σ goods)) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  have hsv := strictVals_of_strict hs
  have key : ∀ n, ∀ (ks : List A) (T : A → List G), Reach v agents goods σ ks T →
      (remAgents agents ks).length = n → ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ks T hr hn
      have hI := inv_of_reach hσ hag hgd hsv hperf hr
      by_cases hoc : OC1At v agents goods σ ks T
      · exact lift_base hσ hgd hI (hB agents goods v hne hag hgd h4 hs σ hσ hperf ks T hr hoc)
      · obtain ⟨K, rest, T', hA⟩ := hR agents goods v hne hag hgd h4 hs σ hσ hperf ks T hr hoc
        have hlt : (remAgents agents (ks ++ K)).length < n := by
          rw [← hn, remAgents_append]
          cases hKc : K with
          | nil => exact absurd hKc hA.ne
          | cons k K' =>
            have hk : k ∈ K := by rw [hKc]; exact List.mem_cons_self
            exact List.length_filter_lt_length_iff_exists.mpr ⟨k, hA.present k hk, by rw [← hKc]; simpa using hk⟩
        exact ih _ hlt (ks ++ K) (updT K T' T) (Reach.round hr hA) rfl
  exact key _ [] (fun _ => []) Reach.start rfl

end frame

/-! ## TARGET₄ -/

/-- **ROUND-IND ∧ the phantom base case ⟹ EFX₀ for strict instances** (Lemma RED reduces to a perfect start). -/
theorem exists_efx0_of_roundRSD_strict (hR : ConjRoundInd A G) (hB : ConjBasePhi A G) {v : A → G → Nat}
    {agents : List A} {goods : List G} (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  have hsv := strictVals_of_strict hs
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd hsv
  obtain ⟨agents', goods', ord', hne'', hag', hgd', hsubA, hsubG, hord', hperf, hext⟩ :=
    red hne hag hgd hs hmax (paretoOpt_sdPick hperm hag hgd hsv)
  have h4' : ∀ i ∈ agents', (relevant v i goods').length ≤ 4 := fun i hi =>
    Nat.le_trans (hsubG.filter _).length_le (h4 i (hsubA.subset hi))
  have hs' : Strict v agents' goods' := fun i hi S T hS hT hdis heq =>
    hs i (hsubA.subset hi) S T (hS.trans hsubG) (hT.trans hsubG) hdis heq
  obtain ⟨X', hX', hE'⟩ := exists_efx0_of_rounds hR hB hne'' hag' hgd' h4' hs' hord' hperf
  exact hext X' hX' hE'

/-- **ROUND-IND ∧ the phantom base case ⟹ TARGET₄ over lists**, ties broken by K4.TIE's perturbation. -/
theorem exists_efx0_of_roundRSD (hR : ConjRoundInd A G) (hB : ConjBasePhi A G) (v : A → G → Nat)
    (agents : List A) (goods : List G) (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup)
    (h4 : ∀ i ∈ agents, (relevant v i goods).length ≤ 4) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨X, hX, hE⟩ := exists_efx0_of_roundRSD_strict hR hB (v := tieBreak v goods) hne hag hgd
    (fun i hi => by rw [relevant_tieBreak]; exact h4 i hi) (strict_tieBreak v goods hgd)
  exact ⟨X, hX, efx0_of_tieBreak v goods hgd hE⟩

/-- **The ROUND-RSD frame: ROUND-IND ∧ the phantom base case ⟹ TARGET₄** in the model's terms. -/
theorem target4_of_roundRSD (I : Inst) (hn : 0 < I.n) (hR : ConjRoundInd (Fin I.n) (Fin I.m))
    (hB : ConjBasePhi (Fin I.n) (Fin I.m)) (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := exists_efx0_of_roundRSD hR hB I.v (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n) (List.nodup_finRange I.m)
    (fun i _ => (numRelevant_eq I i) ▸ hk i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.remGoods_append
#print axioms EFX.Round.roundSrc_cases
#print axioms EFX.Round.mval_le_round
#print axioms EFX.Round.inv_round
#print axioms EFX.Round.inv_of_reach
#print axioms EFX.Round.lift_base
#print axioms EFX.Round.exists_efx0_of_rounds
#print axioms EFX.Round.exists_efx0_of_roundRSD_strict
#print axioms EFX.Round.exists_efx0_of_roundRSD
#print axioms EFX.Round.target4_of_roundRSD
