import EFX.K3Pareto
import EFX.Target

/-!
# Theorem K3 (`k4/c4x.md` §3; ledger K4.C4MIN.K3)

**Theorem K3** (`k4/c4x.md` §3, PR #36, read at commit efef349). At k = 3, every Pareto-maximal pre-allocation of 𝒫
of a core is completable: without owner if `ω ≤ 0`, and otherwise removal-only with a terminal as owner
(`theoremK3_owner`; `theoremK3` states the removal-only conclusion). With a Pareto-maximum, which always exists
(`exists_paretoMax`), this is a second proof of conjecture D for k = 3 cores (`corollaryD_K3`), independent of LB⁺
(`EFX.LB.corollaryD_lists`), and with the CORE reduction a second proof of TARGET (`target_K3`).

The proof follows `k4/c4x.md` §3:
- **Lemma O** (`lemmaO`): if `ω ≥ 1` and a terminal `t` has at most `S − cap(t)` labels (the junk goods of the agents
  exposed w.r.t. `t`), then `P` is removal-only completable with owner `t`: removing the labels from the owner's bundle
  protects every exposed agent (`unthreatened_labels`).
- **Counting** (`terminals_le_otherSlots`): the other terminals each have a slot, so `S − cap(t) ≥ T − 1`; a terminal
  exists when `ω ≥ 1` and `σ = 2n − m ≥ 0` (`exists_terminal`), and `σ ≥ 0` holds in a core (`sigma_nonneg`, L4).
- **The walk** (`exists_labelCycle`): if every terminal had more labels than `S − cap(t)`, a walk from terminal to
  terminal, each time through a fresh label, closes a `LabelCycle`.
- **Shortening** (`LabelCycle.cut`, `splice`): in a cycle with the fewest terminals the chains are pairwise disjoint.
- **The cycle move** (`cycle_contra`): then every exposed agent takes its two other goods, every chain rotates, and the
  result dominates `P` (`transfer_move`), a contradiction.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]
variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}

/-! ## Lemma O (owner criterion) -/

omit [DecidableEq G] in
/-- Fewer needs, fewer frozen agents, more slots. -/
theorem otherSlots_mono {M M' : A → G → Prop} (h : ∀ i ∈ agents, ∀ g, M i g → M' i g) (w : A) :
    otherSlots agents goods base M' w ≤ otherSlots agents goods base M w := by
  unfold otherSlots
  apply LB4.sum_le_sum_of_le
  intro j _
  have hF : Frozen agents goods base M j → Frozen agents goods base M' j := fun ⟨y, hy, i, hi, hN⟩ =>
    ⟨y, hy, i, hi, h i hi y hN⟩
  by_cases h1 : j = w ∨ Frozen agents goods base M' j
  · simp [h1]
  · have h2 : ¬ (j = w ∨ Frozen agents goods base M j) := fun h' => h1 (h'.imp id hF)
    simp [h1, h2]

omit [DecidableEq G] in
/-- The owner's needs from its bundle `B_o ∪ (J ∖ C)` are needs from its base. -/
theorem roNeeds_le {o : A} {C : G → Bool} {i : A} {g : G} (h : roNeeds v goods base o C i g) :
    vbNeeds v goods base i g := by
  unfold roNeeds at h
  split at h
  · rename_i hio
    subst hio
    obtain ⟨hg, hgX, hlt⟩ := h
    refine ⟨hg, fun hb => hgX (List.mem_filter.mpr ⟨hg, by simp [hb]⟩), ?_⟩
    have : value v i (baseOf goods base i) ≤ value v i (ownerBundle goods base i C) :=
      value_sublist v i (LB4.filter_sublist_of_imp fun g _ hb => by simp at hb; simp [hb])
    omega
  · exact h

/-- **A removal-only owner.** If `ω ≥ 1`, `o` is a free listed agent, removing the junk goods of `C` from its bundle
threatens nobody, and they fit the other agents' slots (with the needs from the bases), then `def(P) ≤ 0`. -/
theorem removalOnly_of_owner (hω : 0 < omegaP v agents goods base) {o : A} (ho : o ∈ agents)
    (hoF : ¬ Frozen agents goods base (vbNeeds v goods base) o) (C : G → Bool)
    (hU : Unthreatened v agents goods base o C)
    (hC : ((LB4.junk goods base).filter C).length ≤ otherSlots agents goods base (vbNeeds v goods base) o) :
    RemovalOnly v agents goods base := by
  have := otherSlots_mono (agents := agents) (goods := goods) (base := base) (M := roNeeds v goods base o C)
    (M' := vbNeeds v goods base) (fun i _ g h => roNeeds_le h) o
  exact Or.inr ⟨hω, o, ho, hoF, C, hU, by omega⟩

open Classical in
/-- The labels w.r.t. `t`: the goods relevant to some agent exposed w.r.t. `t` (on the junk, these are the goods `z_x`
of Lemma E). -/
noncomputable def labelC (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (t : A)
    (g : G) : Bool :=
  decide (∃ x ∈ agents, Exposed v agents goods base t x ∧ 0 < v x g)

/-- **Removing the labels protects every exposed agent** (the proof of Lemma O): `B_t ∪ (J ∖ Z_t)` threatens nobody
holding its base alone. -/
theorem unthreatened_labels (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    {t : A} (ht : Terminal v agents goods base t) :
    Unthreatened v agents goods base t (labelC v agents goods base t) := by
  intro x hx hxt h hh
  refine Nat.le_of_not_lt fun hlt => ?_
  have hXW : ∀ g ∈ ownerBundle goods base t (labelC v agents goods base t), g ∈ W goods base t := by
    intro g hg
    obtain ⟨hgg, hb⟩ := List.mem_filter.mp hg
    simp only [decide_eq_true_eq] at hb
    exact mem_W.mpr ⟨hgg, hb.imp id And.left⟩
  have hXnd : (ownerBundle goods base t (labelC v agents goods base t)).Nodup := hgd.sublist List.filter_sublist
  have hE := exposed_of_sub hgd hx hxt hXnd hXW hh hlt
  obtain ⟨-, a, y, z, hB, -, hz, hzb, -, hpz, -, -, -⟩ := lemmaE hgd hP hT ht hE
  obtain ⟨a', hB', hin⟩ := threat_W hgd hP.1 hT ht hx hxt hXnd hXW hlt
  rw [hB] at hB'
  have haa : a = a' := by simpa using hB'
  subst haa
  have hza : z ≠ a := fun e => by
    have := (mem_baseOf.mp (by rw [hB]; simp : a ∈ baseOf goods base x)).2
    rw [← e, hzb] at this; cases this
  have hzX := hin z hz hpz hza
  obtain ⟨-, hb⟩ := List.mem_filter.mp hzX
  simp only [decide_eq_true_eq, hzb, reduceCtorEq, true_and, false_or] at hb
  have : labelC v agents goods base t z = true := by
    simp only [labelC, decide_eq_true_eq]; exact ⟨x, hx, hE, hpz⟩
  rw [this] at hb; cases hb

/-- **Lemma O** (`k4/c4x.md` §3; k = 3). If `ω ≥ 1` and a terminal `t` has at most `S − cap(t)` labels in the junk
(`otherSlots`), then `P` is removal-only completable, with owner `t`. -/
theorem lemmaO (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    (hω : 0 < omegaP v agents goods base) {t : A} (ht : Terminal v agents goods base t)
    (hZ : ((LB4.junk goods base).filter (labelC v agents goods base t)).length ≤
      otherSlots agents goods base (vbNeeds v goods base) t) : RemovalOnly v agents goods base :=
  removalOnly_of_owner hω ht.1 ht.2.1 _ (unthreatened_labels hgd hP hT ht) hZ

/-! ## Counting terminals -/

/-- A sum of terms at least 1 on the elements of a test is at least their number. -/
theorem length_filter_le_sum {α : Type} (p : α → Bool) (f : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, p a = true → 1 ≤ f a) → (l.filter p).length ≤ (l.map f).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := length_filter_le_sum p f l fun b hb => h b (by simp [hb])
    by_cases hp : p a = true
    · have := h a (by simp) hp
      simp [hp]; omega
    · simp [hp]; omega

open Classical in
/-- **The other terminals have a slot each**: `S − cap(t) ≥ T − 1`. -/
theorem terminals_le_otherSlots (hgd : goods.Nodup) (hP : InP v agents goods base) (hT : Three v agents goods)
    (t : A) : (agents.filter (fun j => decide (Terminal v agents goods base j ∧ j ≠ t))).length ≤
      otherSlots agents goods base (vbNeeds v goods base) t := by
  unfold otherSlots
  apply length_filter_le_sum
  intro j _ hj
  obtain ⟨hjT, hjt⟩ := of_decide_eq_true hj
  have h1 := hjT.le_one hgd hP hT
  have hn : ¬ (j = t ∨ Frozen agents goods base (vbNeeds v goods base) j) := fun h => h.elim hjt hjT.2.1
  simp only [hn, ↓reduceIte]
  omega

omit [DecidableEq G] in
/-- **A terminal exists when `ω ≥ 1` and `σ = 2n − m ≥ 0`** (`k4/c4x.md` §3): then some good is needed, its holder is
frozen, and its need chain ends at a terminal (Lemma C). -/
theorem exists_terminal (hag : agents.Nodup) (hgd : goods.Nodup) (hP : ParetoMax v agents goods base)
    (hσ : goods.length ≤ 2 * agents.length) (hω : 0 < omegaP v agents goods base) :
    ∃ t, Terminal v agents goods base t := by
  classical
  have he := omega_eq hP.1.valid hag hgd hP.1.mem
  unfold omegaP at hω
  rw [he] at hω
  have hNA : 0 < numNA agents goods (vbNeeds v goods base) := by omega
  unfold numNA at hNA
  obtain ⟨g, hg, hgNA⟩ := List.countP_pos_iff.mp hNA
  have hgNA' : NA agents (vbNeeds v goods base) g := of_decide_eq_true hgNA
  -- the holder of `g` is frozen
  cases hb : base g with
  | none => exact absurd hgNA' (hP.1.valid.v1 g (mem_junk.mpr ⟨hg, hb⟩))
  | some j =>
    have hgB : g ∈ baseOf goods base j := mem_baseOf.mpr ⟨hg, hb⟩
    have h1 : (baseOf goods base j).length ≤ 1 :=
      Nat.le_of_not_lt fun h2 => hP.1.valid.v2 j h2 g hgB hgNA'
    have hBj : baseOf goods base j = [g] := by
      rcases base_le_one h1 with hB | ⟨y, hB⟩
      · rw [hB] at hgB; simp at hgB
      · rw [hB] at hgB ⊢; simp at hgB; rw [hgB]
    obtain ⟨c, hc, -⟩ := exists_needChain hgd hP (hP.1.mem g hg j hb) ⟨g, hBj, hgNA'⟩
    exact ⟨_, hc.terminal⟩

/-! ## L4: `m ≤ 2n` in a core -/

omit [DecidableEq G] in
/-- **L4** (`proofs/lemmas.md`): in a k = 3 core, `m ≤ 2n`. Every agent has three relevant goods, every good is
relevant to someone, and a good relevant to exactly one agent is private to it, which happens at most once per agent:
`3n = Σ_g deg(g) ≥ 2m − π ≥ 2m − n`. -/
theorem sigma_nonneg (hc : IsCore v agents goods) :
    goods.length ≤ 2 * agents.length := by
  classical
  obtain ⟨-, h3, -, hpriv, hrel⟩ := hc
  let p : A → G → Bool := fun i g => decide (0 < v i g)
  have hsum := LB4.sum_countP_comm p agents goods
  -- the left side is `3n`
  have hL : (agents.map (fun i => goods.countP (p i))).sum = 3 * agents.length := by
    have : ∀ l : List A, (∀ i ∈ l, i ∈ agents) → (l.map (fun i => goods.countP (p i))).sum = 3 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
        intro hl
        have hi := h3 i (hl i (by simp))
        rw [relevant, ← List.countP_eq_length_filter] at hi
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := ih fun j hj => hl j (by simp [hj])
        simp only [p] at this ⊢; omega
    exact this agents fun i hi => hi
  -- the private goods: `π = Σ_i |private_i| ≤ n`
  let q : A → G → Bool := fun i g => decide (0 < v i g ∧ ∀ j ∈ agents, j ≠ i → v j g = 0)
  have hsumq := LB4.sum_countP_comm q agents goods
  have hπ : (agents.map (fun i => goods.countP (q i))).sum ≤ agents.length := by
    have : ∀ l : List A, (∀ i ∈ l, i ∈ agents) → (l.map (fun i => goods.countP (q i))).sum ≤ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
        intro hl
        have hi := hpriv i (hl i (by simp))
        rw [privateGoods, ← List.countP_eq_length_filter] at hi
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := ih fun j hj => hl j (by simp [hj])
        simp only [q] at this ⊢; omega
    exact this agents fun i hi => hi
  -- per good: `deg(g) + [g private] ≥ 2`
  have hgood : ∀ g ∈ goods, 2 ≤ agents.countP (fun i => p i g) + agents.countP (fun i => q i g) := by
    intro g hg
    obtain ⟨i, hi, hpos⟩ := hrel g hg
    by_cases hsh : ∃ j ∈ agents, j ≠ i ∧ 0 < v j g
    · obtain ⟨j, hj, hji, hpj⟩ := hsh
      have : 2 ≤ agents.countP (fun i => p i g) := by
        have hsub : [i, j].Nodup := by simp [Ne.symm hji]
        have := LB.length_le_of_subset hsub (T := agents.filter (fun k => p k g)) fun k hk => by
          simp at hk; rcases hk with rfl | rfl
          · exact List.mem_filter.mpr ⟨hi, by simp [p, hpos]⟩
          · exact List.mem_filter.mpr ⟨hj, by simp [p, hpj]⟩
        rw [List.countP_eq_length_filter]; simpa using this
      omega
    · have hp1 : 1 ≤ agents.countP (fun i => p i g) :=
        List.countP_pos_iff.mpr ⟨i, hi, by simp [p, hpos]⟩
      have hq1 : 1 ≤ agents.countP (fun i => q i g) := List.countP_pos_iff.mpr ⟨i, hi, by
        simp only [q, decide_eq_true_eq]
        exact ⟨hpos, fun j hj hji => Nat.eq_zero_of_not_pos fun h => hsh ⟨j, hj, hji, h⟩⟩⟩
      omega
  have h2m : 2 * goods.length ≤ (goods.map (fun g => agents.countP (fun i => p i g))).sum +
      (goods.map (fun g => agents.countP (fun i => q i g))).sum := by
    have : ∀ l : List G, (∀ g ∈ l, g ∈ goods) → 2 * l.length ≤ (l.map (fun g => agents.countP (fun i => p i g))).sum +
        (l.map (fun g => agents.countP (fun i => q i g))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons g l ih =>
        intro hl
        have := hgood g (hl g (by simp))
        have := ih fun h hh => hl h (by simp [hh])
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
    exact this goods fun g hg => hg
  omega


/-! ## The walk -/

/-- **A cycle of exposures with distinct labels** (`k4/c4x.md` §3): distinct terminals `ts 0, …, ts (k−1)`, agents
`xs i` exposed w.r.t. `ts i`, pairwise distinct junk goods `zs i` relevant to `xs i` (the labels), and need chains from
`xs i` to `ts (i+1 mod k)`. -/
structure LabelCycle (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (k : Nat)
    (ts xs : Nat → A) (zs : Nat → G) : Prop where
  pos : 0 < k
  term : ∀ i < k, Terminal v agents goods base (ts i)
  tinj : ∀ i < k, ∀ j < k, ts i = ts j → i = j
  exp : ∀ i < k, Exposed v agents goods base (ts i) (xs i)
  lab : ∀ i < k, zs i ∈ goods ∧ base (zs i) = none ∧ 0 < v (xs i) (zs i)
  zinj : ∀ i < k, ∀ j < k, zs i = zs j → i = j
  chain : ∀ i < k, ChainTo v agents goods base (xs i) (ts ((i + 1) % k))

theorem nodup_map_range {α : Type} {f : Nat → α} :
    ∀ n, (∀ i < n, ∀ j < n, f i = f j → i = j) → ((List.range n).map f).Nodup
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append]
    refine List.nodup_append.mpr ⟨nodup_map_range n fun i hi j hj => h i (by omega) j (by omega), by simp,
      fun a ha b hb e => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    simp at hb; subst hb
    simp only [List.mem_range] at hi
    have := h i (by omega) n (by omega) e
    omega

omit [DecidableEq G] in
/-- A need chain from `x` gives `ChainTo x τ` for its end `τ`, a terminal. -/
theorem NeedChain.chainTo {c : List A} (hc : NeedChain v agents goods base c) {x : A} (hx : c.head? = some x) :
    ∃ τ, ChainTo v agents goods base x τ ∧ Terminal v agents goods base τ :=
  ⟨_, ⟨c, hc, hx, by rw [List.getLast?_eq_getElem?]; simp⟩, hc.terminal⟩

open Classical in
/-- **The walk** (`k4/c4x.md` §3). If every terminal has at least `T` labels (`T` the number of terminals), then a
`LabelCycle` exists: walk from a terminal `t_r` to an agent `x_r ∈ E_{t_r}` with a fresh label (at most `r < T` are used)
and on to the end `t_{r+1}` of a need chain from `x_r`; within `T` steps a terminal repeats. -/
theorem exists_labelCycle (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    {t0 : A} (ht0 : Terminal v agents goods base t0)
    (hbig : ∀ t, Terminal v agents goods base t →
      (agents.filter (fun j => decide (Terminal v agents goods base j))).length ≤
        ((LB4.junk goods base).filter (labelC v agents goods base t)).length) :
    ∃ k ts xs zs, LabelCycle v agents goods base k ts xs zs := by
  classical
  obtain ⟨nT, hnT⟩ : ∃ n, n = (agents.filter (fun j => decide (Terminal v agents goods base j))).length := ⟨_, rfl⟩
  obtain ⟨g0, -⟩ := ht0.2.2
  have walk : ∀ r, r ≤ nT → (∃ k ts xs zs, LabelCycle v agents goods base k ts xs zs) ∨
      ∃ (ts xs : Nat → A) (zs : Nat → G), (∀ i ≤ r, Terminal v agents goods base (ts i)) ∧
        (∀ i ≤ r, ∀ j ≤ r, ts i = ts j → i = j) ∧ (∀ i < r, Exposed v agents goods base (ts i) (xs i)) ∧
        (∀ i < r, zs i ∈ goods ∧ base (zs i) = none ∧ 0 < v (xs i) (zs i)) ∧
        (∀ i < r, ∀ j < r, zs i = zs j → i = j) ∧ (∀ i < r, ChainTo v agents goods base (xs i) (ts (i + 1))) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact Or.inr ⟨fun _ => t0, fun _ => t0, fun _ => g0, fun _ _ => ht0, fun i hi j hj _ => by omega,
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ r ih =>
      intro hr
      rcases ih (by omega) with h | ⟨ts, xs, zs, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl h
      -- a fresh label at `ts r`
      have htr := h1 r (Nat.le_refl _)
      have hZ := hbig (ts r) htr
      rw [← hnT] at hZ
      obtain ⟨z, hzZ, hzU⟩ : ∃ z ∈ (LB4.junk goods base).filter (labelC v agents goods base (ts r)),
          z ∉ (List.range r).map zs := by
        refine Classical.byContradiction fun hno => ?_
        have := LB.length_le_of_subset ((hgd.sublist List.filter_sublist).sublist List.filter_sublist)
          (S := (LB4.junk goods base).filter (labelC v agents goods base (ts r))) (T := (List.range r).map zs)
          fun z hz => Classical.byContradiction fun h => hno ⟨z, hz, h⟩
        simp only [List.length_map, List.length_range] at this; omega
      obtain ⟨hzJ, hzl⟩ := List.mem_filter.mp hzZ
      obtain ⟨hzg, hzb⟩ := mem_junk.mp hzJ
      obtain ⟨x, hx, hxE, hxz⟩ : ∃ x ∈ agents, Exposed v agents goods base (ts r) x ∧ 0 < v x z := by
        simpa [labelC] using hzl
      have hzU' : ∀ i < r, zs i ≠ z := fun i hi e => hzU (List.mem_map.mpr ⟨i, by simpa using hi, e⟩)
      obtain ⟨c, hc, hcx⟩ := exists_needChain hgd hP hx (lemmaE hgd hP hT htr hxE).1
      obtain ⟨τ, hxτ, hτ⟩ := hc.chainTo hcx
      by_cases hq : ∃ q ≤ r, ts q = τ
      · -- the walk closes a cycle `ts q, …, ts r`
        obtain ⟨q, hqr, hqτ⟩ := hq
        refine Or.inl ⟨r + 1 - q, fun i => ts (q + i), fun i => if q + i < r then xs (q + i) else x,
          fun i => if q + i < r then zs (q + i) else z, by omega, fun i hi => h1 _ (by omega),
          fun i hi j hj e => by have := h2 _ (by omega) _ (by omega) e; omega, fun i hi => ?_, fun i hi => ?_,
          fun i hi j hj e => ?_, fun i hi => ?_⟩
        · by_cases h : q + i < r
          · simp only [h, ↓reduceIte]; exact h3 _ h
          · simp only [h, ↓reduceIte]; rw [show q + i = r by omega]; exact hxE
        · by_cases h : q + i < r
          · simp only [h, ↓reduceIte]; exact h4 _ h
          · simp only [h, ↓reduceIte]; exact ⟨hzg, hzb, hxz⟩
        · by_cases hi' : q + i < r <;> by_cases hj' : q + j < r <;> simp only [hi', hj', ↓reduceIte] at e
          · have := h5 _ hi' _ hj' e; omega
          · exact absurd e (hzU' _ hi')
          · exact absurd e.symm (hzU' _ hj')
          · omega
        · by_cases h : i + 1 < r + 1 - q
          · rw [Nat.mod_eq_of_lt h]
            simp only [show q + i < r by omega, ↓reduceIte]
            have := h6 (q + i) (by omega)
            rwa [show q + i + 1 = q + (i + 1) by omega] at this
          · rw [show i + 1 = r + 1 - q by omega, Nat.mod_self, Nat.add_zero, hqτ]
            simp only [show ¬ (q + i < r) by omega, ↓reduceIte]
            exact hxτ
      · -- the walk goes on to `τ`
        refine Or.inr ⟨fun i => if i ≤ r then ts i else τ, fun i => if i < r then xs i else x,
          fun i => if i < r then zs i else z, fun i hi => ?_, fun i hi j hj e => ?_, fun i hi => ?_, fun i hi => ?_,
          fun i hi j hj e => ?_, fun i hi => ?_⟩
        · by_cases h : i ≤ r
          · simp only [h, ↓reduceIte]; exact h1 i h
          · simp only [h, ↓reduceIte]; exact hτ
        · by_cases hi' : i ≤ r <;> by_cases hj' : j ≤ r <;> simp only [hi', hj', ↓reduceIte] at e
          · exact h2 i hi' j hj' e
          · exact absurd ⟨i, hi', e⟩ hq
          · exact absurd ⟨j, hj', e.symm⟩ hq
          · omega
        · by_cases h : i < r
          · simp only [h, ↓reduceIte, show i ≤ r by omega]; exact h3 i h
          · simp only [h, ↓reduceIte, show i ≤ r by omega]; rw [show i = r by omega]; exact hxE
        · by_cases h : i < r
          · simp only [h, ↓reduceIte]; exact h4 i h
          · simp only [h, ↓reduceIte]; exact ⟨hzg, hzb, hxz⟩
        · by_cases hi' : i < r <;> by_cases hj' : j < r <;> simp only [hi', hj', ↓reduceIte] at e
          · exact h5 i hi' j hj' e
          · exact absurd e (hzU' _ hi')
          · exact absurd e.symm (hzU' _ hj')
          · omega
        · by_cases h : i < r
          · simp only [h, ↓reduceIte, show i + 1 ≤ r by omega]; exact h6 i h
          · simp only [h, ↓reduceIte, show ¬ (i + 1 ≤ r) by omega]; exact hxτ
  rcases walk nT (Nat.le_refl _) with h | ⟨ts, -, -, h1, h2, -⟩
  · exact h
  · -- `nT + 1` distinct terminals: impossible
    exfalso
    have hnd := nodup_map_range (f := ts) (nT + 1) fun i hi j hj e => h2 i (by omega) j (by omega) e
    have := LB.length_le_of_subset hnd (T := agents.filter (fun j => decide (Terminal v agents goods base j)))
      fun a ha => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        have := h1 i (by simp at hi; omega)
        exact List.mem_filter.mpr ⟨this.1, by simpa using this⟩
    simp at this; omega


/-! ## Shortening -/

theorem add_mod_inj {k s m m' : Nat} (hm : m < k) (hm' : m' < k) (h : (s + m) % k = (s + m') % k) : m = m' := by
  rcases Nat.le_total m m' with hle | hle
  · have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [show s + m' - (s + m) = m' - m by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [show s + m - (s + m') = m - m' by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- **Cutting a cycle**: the terminals `ts s, …, ts (s+ℓ−1)` (indices mod `k`) form a cycle of their own if a need
chain leads from the last exposed agent back to `ts s`. -/
theorem LabelCycle.cut {k : Nat} {ts xs : Nat → A} {zs : Nat → G} (hC : LabelCycle v agents goods base k ts xs zs)
    {s ℓ : Nat} (hs : s < k) (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k)
    (hclose : ChainTo v agents goods base (xs ((s + (ℓ - 1)) % k)) (ts s)) :
    LabelCycle v agents goods base ℓ (fun m => ts ((s + m) % k)) (fun m => xs ((s + m) % k))
      (fun m => zs ((s + m) % k)) := by
  have hk := hC.pos
  refine ⟨hℓ, fun i _ => hC.term _ (Nat.mod_lt _ hk), fun i hi j hj e => ?_, fun i _ => hC.exp _ (Nat.mod_lt _ hk),
    fun i _ => hC.lab _ (Nat.mod_lt _ hk), fun i hi j hj e => ?_, fun i hi => ?_⟩
  · exact add_mod_inj (by omega) (by omega) (hC.tinj _ (Nat.mod_lt _ hk) _ (Nat.mod_lt _ hk) e)
  · exact add_mod_inj (by omega) (by omega) (hC.zinj _ (Nat.mod_lt _ hk) _ (Nat.mod_lt _ hk) e)
  · by_cases h : i + 1 < ℓ
    · have := hC.chain ((s + i) % k) (Nat.mod_lt _ hk)
      rw [Nat.mod_add_mod] at this
      simp only [Nat.mod_eq_of_lt h]
      rwa [show s + i + 1 = s + (i + 1) by omega] at this
    · rw [show i + 1 = ℓ by omega, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hs]
      rwa [show i = ℓ - 1 by omega]

omit [DecidableEq A] in
/-- The entries of `c.take i ++ c'.drop j`. -/
theorem getElem_splice {c c' : List A} {i j k : Nat} (hi : i ≤ c.length)
    (hk : k < (c.take i ++ c'.drop j).length) :
    (c.take i ++ c'.drop j)[k] = if h : k < i then c[k]'(by omega) else
      c'[j + (k - i)]'(by simp [List.length_append, List.length_take, List.length_drop] at hk; omega) := by
  split
  · rename_i h
    rw [List.getElem_append_left (by simp; omega)]
    simp
  · rename_i h
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_drop, List.length_take]
    congr 1
    omega

omit [DecidableEq G] in
/-- **Splicing two need chains** at a common agent `c[i] = c'[j]` (`i ≥ 1`) that is the first agent of `c` on `c'`:
`c[0], …, c[i−1], c'[j], c'[j+1], …` is a need chain. -/
theorem splice {c c' : List A} (hc : NeedChain v agents goods base c) (hc' : NeedChain v agents goods base c')
    {i j : Nat} (hi : i < c.length) (hj : j < c'.length) (h0 : 0 < i) (hij : c[i] = c'[j])
    (hdisj : ∀ p (hp : p < i), c[p] ∉ c') : NeedChain v agents goods base (c.take i ++ c'.drop j) := by
  have hlen : (c.take i ++ c'.drop j).length = i + (c'.length - j) := by simp; omega
  refine ⟨?_, fun a ha => ?_, by omega, fun k hk => ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨hc.nodup.sublist (List.take_sublist _ _),
      hc'.nodup.sublist (List.drop_sublist _ _), fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp ha
    simp only [List.length_take] at hp
    rw [List.getElem_take] at hb
    exact hdisj p (by omega) (List.mem_of_mem_drop hb)
  · rcases List.mem_append.mp ha with ha | ha
    · exact hc.mem a (List.mem_of_mem_take ha)
    · exact hc'.mem a (List.mem_of_mem_drop ha)
  · rw [getElem_splice (by omega), getElem_splice (by omega)]
    by_cases h1 : k + 1 < i
    · simp only [show k < i by omega, h1, ↓reduceDIte]; exact hc.edge k (by omega)
    · by_cases h2 : k + 1 = i
      · simp only [show k < i by omega, show ¬ (k + 1 < i) by omega, ↓reduceDIte]
        have := hc.edge k (by omega)
        simp only [h2] at this
        rw [hij] at this
        simp only [show k + 1 - i = 0 by omega, Nat.add_zero]
        exact this
      · simp only [show ¬ (k < i) by omega, h1, ↓reduceDIte]
        have := hc'.edge (j + (k - i)) (by rw [hlen] at hk; omega)
        simp only [show j + (k - i) + 1 = j + (k + 1 - i) by omega] at this
        exact this
  · have e : (c.take i ++ c'.drop j).length - 1 = i + (c'.length - 1 - j) := by rw [hlen]; omega
    have := hc'.free
    simp only [e]
    rw [getElem_splice (by omega)]
    simp only [show ¬ (i + (c'.length - 1 - j) < i) by omega, ↓reduceDIte]
    simp only [show j + (i + (c'.length - 1 - j) - i) = c'.length - 1 by omega]
    exact this

/-- An exposed agent has no needs (all its goods are its base good, `B_t`'s good or a junk good; Lemma E), so no edge
enters it. -/
theorem exposed_no_needs (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    {t x : A} (ht : Terminal v agents goods base t) (hx : Exposed v agents goods base t x) (g : G) :
    ¬ vbNeeds v goods base x g := by
  obtain ⟨-, a, y, z, hB, hBt, hz, hzb, -, -, -, hR, -⟩ := lemmaE hgd hP hT ht hx
  intro hN
  obtain ⟨hg, hgb, hlt⟩ := id hN
  rw [hB] at hlt
  simp only [value_cons, value_nil, Nat.add_zero] at hlt
  rcases hR g hg (by omega) (fun e => hgb (by rw [e]; exact (mem_baseOf.mp (by rw [hB]; simp)).2)) with rfl | rfl
  · exact not_NA_of_free hBt ht.2.1 ⟨x, hx.1, hN⟩
  · exact hP.1.valid.v1 g (mem_junk.mpr ⟨hz, hzb⟩) ⟨x, hx.1, hN⟩

/-- An exposed agent is a *top-holder* (`k4/c4x.md` §3, Lemma E: "x is a frozen top-holder"): its one base good `a` is
worth at least every other good to it, as it needs nothing (`exposed_no_needs`). -/
theorem exposed_top (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    {t x : A} (ht : Terminal v agents goods base t) (hx : Exposed v agents goods base t x) :
    ∃ a, baseOf goods base x = [a] ∧ ∀ g ∈ goods, v x g ≤ v x a := by
  obtain ⟨-, a, -, -, hB, -⟩ := lemmaE hgd hP hT ht hx
  refine ⟨a, hB, fun g hg => ?_⟩
  by_cases hb : base g = some x
  · rw [(mem_single_base hB).mp ⟨hg, hb⟩]; exact Nat.le_refl _
  · refine Nat.le_of_not_lt fun hlt => exposed_no_needs hgd hP hT ht hx g ⟨hg, hb, ?_⟩
    rw [hB]; simpa using hlt

/-- In a `LabelCycle` the exposed agents are distinct: an exposed agent's junk goods are its one label (Lemma E). -/
theorem LabelCycle.xinj (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    {k : Nat} {ts xs : Nat → A} {zs : Nat → G} (hC : LabelCycle v agents goods base k ts xs zs) :
    ∀ i < k, ∀ j < k, xs i = xs j → i = j := by
  intro i hi j hj e
  obtain ⟨-, a, y, z, hB, hBt, -, -, -, -, -, hR, -⟩ := lemmaE hgd hP hT (hC.term i hi) (hC.exp i hi)
  have hlab : ∀ l, l ∈ goods → base l = none → 0 < v (xs i) l → l = z := by
    intro l hl hlb hpl
    rcases hR l hl hpl (fun e' => by
      have := (mem_baseOf.mp (by rw [hB]; simp : a ∈ baseOf goods base (xs i))).2
      rw [← e', hlb] at this; cases this) with rfl | rfl
    · have := (mem_baseOf.mp (by rw [hBt]; simp : l ∈ baseOf goods base (ts i))).2
      rw [hlb] at this; cases this
    · rfl
  obtain ⟨hi1, hi2, hi3⟩ := hC.lab i hi
  obtain ⟨hj1, hj2, hj3⟩ := hC.lab j hj
  rw [← e] at hj3
  exact hC.zinj i hi j hj ((hlab _ hi1 hi2 hi3).trans (hlab _ hj1 hj2 hj3).symm)

omit [DecidableEq A] in
theorem head_eq {c : List A} {x : A} (h : c.head? = some x) (h0 : 0 < c.length) : c[0] = x := by
  cases c with
  | nil => simp at h0
  | cons y c => simpa using h

omit [DecidableEq A] in
theorem last_eq {c : List A} {x : A} (h : c.getLast? = some x) (h0 : 0 < c.length) : c[c.length - 1] = x := by
  rw [List.getLast?_eq_getElem?] at h
  exact (List.getElem?_eq_some_iff.mp h).2

/-- The first index with a property. -/
theorem exists_first {P : Nat → Prop} : ∀ n, (∃ p < n, P p) → ∃ q < n, P q ∧ ∀ p < q, ¬ P p
  | 0, ⟨_, hp, _⟩ => absurd hp (Nat.not_lt_zero _)
  | n + 1, h => by
    by_cases h' : ∃ p < n, P p
    · obtain ⟨q, hq, hPq, hmin⟩ := exists_first n h'
      exact ⟨q, by omega, hPq, hmin⟩
    · obtain ⟨p, hp, hPp⟩ := h
      have hpn : p = n := Classical.byContradiction fun hne => h' ⟨p, by omega, hPp⟩
      subst hpn
      exact ⟨p, by omega, hPp, fun p' hp' hP' => h' ⟨p', hp', hP'⟩⟩

/-- **Shortening** (`k4/c4x.md` §3). In a `LabelCycle` with the fewest terminals, need chains `c i` from `xs i` to
`ts (i+1)` are pairwise disjoint. (An exposed agent lies on no other chain, as no edge enters it; if two chains met,
splicing them at the first meeting point would close a cycle through fewer terminals.) -/
theorem LabelCycle.disjoint (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods)
    {k : Nat} {ts xs : Nat → A} {zs : Nat → G} (hC : LabelCycle v agents goods base k ts xs zs)
    (hmin : ∀ k' ts' xs' zs', LabelCycle v agents goods base k' ts' xs' zs' → k ≤ k')
    {c : Nat → List A} (hc : ∀ i < k, NeedChain v agents goods base (c i) ∧ (c i).head? = some (xs i) ∧
      (c i).getLast? = some (ts ((i + 1) % k))) :
    ∀ i < k, ∀ j < k, i ≠ j → ∀ a ∈ c i, a ∉ c j := by
  have hk := hC.pos
  -- an exposed agent lies on no other chain
  have hD1 : ∀ i < k, ∀ j < k, i ≠ j → xs i ∉ c j := by
    intro i hi j hj hij hmem
    obtain ⟨p, hp, hpx⟩ := List.mem_iff_getElem.mp hmem
    obtain ⟨hcj, hhj, -⟩ := hc j hj
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [head_eq hhj (by omega)] at hpx
      exact hij (hC.xinj hgd hP hT j hj i hi hpx).symm
    · obtain ⟨g, -, hN⟩ := hcj.edge (p - 1) (by omega)
      simp only [show p - 1 + 1 = p by omega, hpx] at hN
      exact exposed_no_needs hgd hP hT (hC.term i hi) (hC.exp i hi) g hN
  intro i hi j hj hij a ha haj
  obtain ⟨hci, hhi, -⟩ := hc i hi
  obtain ⟨hcj, -, hlj⟩ := hc j hj
  -- the first agent of `c i` on `c j`
  obtain ⟨pa, hpa, hpaa⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨q, hq', ⟨hq, hqj⟩, hmin'⟩ := exists_first (P := fun p => ∃ h : p < (c i).length, (c i)[p] ∈ c j)
    (c i).length ⟨pa, hpa, hpa, hpaa ▸ haj⟩
  have hbefore : ∀ p (hp : p < q), (c i)[p]'(by omega) ∉ c j := fun p hp h => hmin' p hp ⟨_, h⟩
  have hq0 : 0 < q := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    subst h0
    rw [head_eq hhi (by omega)] at hqj
    exact hD1 i hi j hj hij hqj
  obtain ⟨j', hj', hjq⟩ := List.mem_iff_getElem.mp hqj
  have hsp := splice hci hcj hq hj' hq0 hjq.symm hbefore
  -- the spliced chain leads from `xs i` to `ts (j+1)`: a cycle through fewer terminals
  have hch : ChainTo v agents goods base (xs i) (ts ((j + 1) % k)) := by
    refine ⟨_, hsp, ?_, ?_⟩
    · rw [List.head?_append, List.head?_take] <;> simp [show q ≠ 0 by omega, hhi]
    · rw [List.getLast?_append, List.getLast?_drop] <;> simp [show ¬ (c j).length ≤ j' by omega, hlj]
  obtain ⟨s, hs, hsdef⟩ : ∃ s, s < k ∧ s = (j + 1) % k := ⟨_, Nat.mod_lt _ hk, rfl⟩
  have hsv : s = if j + 1 < k then j + 1 else 0 := by
    rw [hsdef]; split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rw [show j + 1 = k by omega, Nat.mod_self]
  let ℓ := if s ≤ i then i - s + 1 else i + k - s + 1
  have hℓ : (s + (ℓ - 1)) % k = i := by
    simp only [ℓ]
    split
    · rw [show s + (i - s + 1 - 1) = i by omega, Nat.mod_eq_of_lt hi]
    · rw [show s + (i + k - s + 1 - 1) = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  have hcut := hC.cut hs (ℓ := ℓ) (by simp only [ℓ]; split <;> omega) (by simp only [ℓ]; split <;> omega)
    (by rw [hℓ, hsdef]; exact hch)
  have := hmin _ _ _ _ hcut
  simp only [ℓ] at this
  split at this <;> split at hsv <;> omega


/-! ## The cycle move -/

omit [DecidableEq A] in
/-- The value of an exposed agent's two other goods beats its base (balance): `v_x(a) < v_x(y) + v_x(z)`. -/
theorem value_three (hgd : goods.Nodup) (hT : Three v agents goods) {x : A} (hx : x ∈ agents) {a y z : G}
    (ha : a ∈ goods) (hy : y ∈ goods) (hz : z ∈ goods) (hpa : 0 < v x a) (hpy : 0 < v x y) (hpz : 0 < v x z)
    (hya : y ≠ a) (hza : z ≠ a) (hyz : y ≠ z) : v x a < v x y + v x z := by
  have hsub : ∀ g ∈ [a, y, z], g ∈ relevant v x goods := by
    intro g hg; simp at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_relevant.mpr ⟨ha, hpa⟩
    · exact mem_relevant.mpr ⟨hy, hpy⟩
    · exact mem_relevant.mpr ⟨hz, hpz⟩
  have hperm := perm_of_subset_length (T := relevant v x goods) (by simp [Ne.symm hya, Ne.symm hza, hyz])
    (hgd.sublist List.filter_sublist) hsub (by rw [hT.three x hx]; simp)
  have hv := value_perm (v := v) (i := x) hperm
  rw [← value_relevant] at hv
  have := hT.bal x hx a ha
  simp only [value_cons, value_nil] at hv
  omega

/-- **The cycle move** (`k4/c4x.md` §3). A `LabelCycle` whose need chains are pairwise disjoint contradicts
Pareto-maximality: every exposed agent `xs i` takes `B_{ts i} = {y}` and its label `zs i`, and along every chain each
agent takes its predecessor's good, so `ts (i+1)` gives up its good to `xs (i+1)`. Every moved agent gains
(`transfer_move`). -/
theorem cycle_contra (hgd : goods.Nodup) (hP : ParetoMax v agents goods base)
    (hT : Three v agents goods) {k : Nat} {ts xs : Nat → A} {zs : Nat → G}
    (hC : LabelCycle v agents goods base k ts xs zs) {c : Nat → List A}
    (hc : ∀ i < k, NeedChain v agents goods base (c i) ∧ (c i).head? = some (xs i) ∧
      (c i).getLast? = some (ts ((i + 1) % k)))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → ∀ a ∈ c i, a ∉ c j) : False := by
  classical
  have hk := hC.pos
  have hlen : ∀ i < k, 2 ≤ (c i).length := fun i hi => (hc i hi).1.two
  have hhead : ∀ i (hi : i < k), (c i)[0]'(by have := hlen i hi; omega) = xs i := fun i hi =>
    head_eq (hc i hi).2.1 (by have := hlen i hi; omega)
  have hlast : ∀ i (hi : i < k), (c i)[(c i).length - 1]'(by have := hlen i hi; omega) = ts ((i + 1) % k) :=
    fun i hi => last_eq (hc i hi).2.2 (by have := hlen i hi; omega)
  have hnd : ∀ i < k, (c i).Nodup := fun i hi => (hc i hi).1.nodup
  -- which chain an agent is on
  obtain ⟨cidx, hcidxdef⟩ : ∃ f : A → Option Nat, f = fun a => (List.range k).find? (fun i => decide (a ∈ c i)) :=
    ⟨_, rfl⟩
  have hcidx : ∀ i < k, ∀ a ∈ c i, cidx a = some i := by
    intro i hi a ha
    simp only [hcidxdef]
    cases h : (List.range k).find? (fun i => decide (a ∈ c i)) with
    | none => exact absurd (List.find?_eq_none.mp h i (List.mem_range.mpr hi)) (by simpa using ha)
    | some i' =>
      have hi' := List.mem_range.mp (List.mem_of_find?_eq_some h)
      have ha' : a ∈ c i' := by simpa using List.find?_some h
      by_cases e : i' = i
      · rw [e]
      · exact absurd ha' (hdisj i hi i' hi' (Ne.symm e) a ha)
  -- the move
  let dstF : A → Option A := fun a => (cidx a).map (fun i => (pathNext (c i) a).getD (xs ((i + 1) % k)))
  let extra : G → Option A := fun g => ((List.range k).find? (fun i => decide (zs i = g))).map xs
  let L := agents.filter (fun a => decide (∃ i < k, a ∈ c i))
  have hmemL : ∀ a, a ∈ L ↔ a ∈ agents ∧ ∃ i < k, a ∈ c i := fun a => by simp [L]
  have hdst : ∀ i (hi : i < k) m (hm : m < (c i).length), dstF (c i)[m] =
      some (if h : m + 1 < (c i).length then (c i)[m + 1] else xs ((i + 1) % k)) := by
    intro i hi m hm
    simp only [dstF, hcidx i hi _ (List.getElem_mem hm), Option.map_some]
    split
    · rename_i h; rw [pathNext_getElem (hnd i hi) h]; rfl
    · rename_i h; rw [pathNext_last (hnd i hi) hm (by omega)]; rfl
  have hextra : ∀ g a, extra g = some a ↔ ∃ i < k, zs i = g ∧ xs i = a := by
    intro g a
    simp only [extra]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨i, List.mem_range.mp (List.mem_of_find?_eq_some hi), by simpa using List.find?_some hi, rfl⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      cases h : (List.range k).find? (fun i' => decide (zs i' = zs i)) with
      | none => exact absurd (List.find?_eq_none.mp h i (List.mem_range.mpr hi)) (by simp)
      | some i' =>
        have hi' := List.mem_range.mp (List.mem_of_find?_eq_some h)
        have := hC.zinj i' hi' i hi (by simpa using List.find?_some h)
        subst this; rfl
  -- positions of the movers
  have hpos : ∀ a ∈ L, ∃ i, ∃ hi : i < k, ∃ m, ∃ hm : m < (c i).length, (c i)[m] = a := by
    intro a ha
    obtain ⟨-, i, hi, hai⟩ := (hmemL a).mp ha
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hai
    exact ⟨i, hi, m, hm, rfl⟩
  have hinL : ∀ i (hi : i < k) m (hm : m < (c i).length), (c i)[m] ∈ L := fun i hi m hm =>
    (hmemL _).mpr ⟨(hc i hi).1.mem _ (List.getElem_mem hm), i, hi, List.getElem_mem hm⟩
  have hxsL : ∀ i (hi : i < k), xs i ∈ L := fun i hi => by
    have := hinL i hi 0 (by have := hlen i hi; omega); rwa [hhead i hi] at this
  -- an agent of a chain at a positive position is no exposed agent
  have hnotx : ∀ i (hi : i < k) m (hm : m < (c i).length), 0 < m → ∀ j < k, (c i)[m] ≠ xs j := by
    intro i hi m hm hm0 j hj e
    have hj' : (c i)[m] ∈ c j := by rw [e, ← hhead j hj]; exact List.getElem_mem _
    by_cases hij : i = j
    · subst hij
      rw [← hhead i hi, (hnd i hi).getElem_inj] at e; omega
    · exact hdisj i hi j hj hij _ (List.getElem_mem hm) hj'
  have hxinj := hC.xinj hgd hP hT
  -- the destinations are injective
  have hinj : ∀ p ∈ L, ∀ q ∈ L, ∀ a, dstF p = some a → dstF q = some a → p = q := by
    intro p hp q hq a hpa hqa
    obtain ⟨i, hi, m, hm, rfl⟩ := hpos p hp
    obtain ⟨j, hj, m', hm', rfl⟩ := hpos q hq
    rw [hdst i hi m hm, Option.some.injEq] at hpa
    rw [hdst j hj m' hm', Option.some.injEq, ← hpa] at hqa
    have hnext : ∀ i (hi : i < k), ((i + 1) % k) < k := fun _ _ => Nat.mod_lt _ hk
    by_cases h1 : m + 1 < (c i).length <;> by_cases h2 : m' + 1 < (c j).length <;>
      simp only [h1, h2, ↓reduceDIte] at hqa
    · -- both inside their chains
      by_cases hij : i = j
      · subst hij; rw [(hnd i hi).getElem_inj] at hqa
        have : m = m' := by omega
        subst this; rfl
      · have hmem : (c j)[m' + 1] ∈ c i := by rw [hqa]; exact List.getElem_mem h1
        exact absurd hmem (hdisj j hj i hi (fun e => hij e.symm) _ (List.getElem_mem h2))
    · exact absurd hqa.symm (hnotx i hi (m + 1) h1 (by omega) _ (hnext j hj))
    · exact absurd hqa (hnotx j hj (m' + 1) h2 (by omega) _ (hnext i hi))
    · have := succ_mod_inj hi hj (hxinj _ (hnext j hj) _ (hnext i hi) hqa).symm
      subst this
      have : m = m' := by omega
      subst this; rfl
  refine transfer_move (L := L) (dstF := dstF) (extra := extra) hgd hP
    (List.ne_nil_of_mem (hxsL 0 hk)) (fun a ha => ((hmemL a).mp ha).1) hinj (fun p hp a hpa => ?_)
    (fun g _ a h => ?_) (fun p hp h => ?_) (fun a ha => ?_)
  · -- destinations are movers
    obtain ⟨i, hi, m, hm, rfl⟩ := hpos p hp
    rw [hdst i hi m hm, Option.some.injEq] at hpa
    split at hpa
    · rename_i h; rw [← hpa]; exact hinL i hi (m + 1) h
    · rw [← hpa]; exact hxsL _ (Nat.mod_lt _ hk)
  · -- the extras are labels, which are junk, given to exposed agents
    obtain ⟨i, hi, rfl, rfl⟩ := (hextra g a).mp h
    exact ⟨(hC.lab i hi).2.1, hxsL i hi⟩
  · -- nothing is released
    obtain ⟨i, hi, m, hm, rfl⟩ := hpos p hp
    rw [hdst i hi m hm] at h; cases h
  · -- every mover gains
    obtain ⟨i, hi, m, hm, rfl⟩ := hpos a ha
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · -- `xs i` takes `B_{ts i}` and its label
      subst hm0
      rw [hhead i hi]
      obtain ⟨i₀, hi₀, hi₀i⟩ : ∃ i₀, i₀ < k ∧ (i₀ + 1) % k = i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · exact ⟨k - 1, by omega, by rw [show k - 1 + 1 = k by omega, Nat.mod_self, h0]⟩
        · exact ⟨i - 1, by omega, by rw [show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi]⟩
      have hl₀ : (c i₀).length - 1 < (c i₀).length := by have := hlen i₀ hi₀; omega
      have hsend : dstF (c i₀)[(c i₀).length - 1] = some (xs i) := by
        rw [hdst i₀ hi₀ _ hl₀]
        simp only [show ¬ ((c i₀).length - 1 + 1 < (c i₀).length) by omega, ↓reduceDIte, hi₀i]
      rw [recvOf_eq (hinL i₀ hi₀ _ hl₀) hsend fun q hq hqa => hinj q hq _ (hinL i₀ hi₀ _ hl₀) _ hqa hsend,
        hlast i₀ hi₀, hi₀i]
      obtain ⟨-, a₀, y, z, hB, hBt, hz, hzb, hpy, hpz, hyz, hR, -⟩ := lemmaE hgd hP hT (hC.term i hi) (hC.exp i hi)
      have hxa := (hC.exp i hi).1
      obtain ⟨hl1, hl2, hl3⟩ := hC.lab i hi
      have haB : a₀ ∈ goods ∧ base a₀ = some (xs i) := mem_baseOf.mp (by rw [hB]; simp)
      have hyB : y ∈ goods ∧ base y = some (ts i) := mem_baseOf.mp (by rw [hBt]; simp)
      -- the label is `z`
      have hzl : zs i = z := by
        rcases hR (zs i) hl1 hl3 (fun e => by rw [e, haB.2] at hl2; cases hl2) with e | e
        · rw [e, hyB.2] at hl2; cases hl2
        · exact e
      have hext : extrasOf goods base extra (xs i) = [zs i] := LB4R.filter_eq_single
        (hgd.sublist List.filter_sublist) (mem_junk.mpr ⟨hl1, hl2⟩) fun g _ => by
          simp only [decide_eq_true_eq]
          rw [hextra]
          constructor
          · rintro ⟨i', hi', rfl, e⟩; rw [hxinj i' hi' i hi e]
          · rintro rfl; exact ⟨i, hi, rfl, rfl⟩
      rw [hBt, hext, hzl]
      have hya : y ≠ a₀ := fun e => by rw [e, haB.2] at hyB; exact (hC.exp i hi).2.1 (Option.some.inj hyB.2)
      have hza : z ≠ a₀ := fun e => by rw [e, haB.2] at hzb; cases hzb
      refine ⟨by simp, fun g hg => ?_, ?_, fun _ g hg => ?_⟩
      · simp at hg; rcases hg with rfl | rfl
        · exact hpy
        · exact hpz
      · rw [hB]; simp only [value_cons, value_nil, Nat.add_zero]
        exact value_three hgd hT hxa haB.1 hyB.1 hz (hP.1.rel a₀ haB.1 _ haB.2) hpy hpz hya hza hyz
      · simp at hg; rcases hg with rfl | rfl
        · exact not_NA_of_free hBt (hC.term i hi).2.1
        · exact hP.1.valid.v1 g (mem_junk.mpr ⟨hz, hzb⟩)
    · -- inside a chain: the predecessor's good, which the agent needed
      have hm1 : m - 1 + 1 < (c i).length := by omega
      have hsend : dstF (c i)[m - 1] = some (c i)[m] := by
        rw [hdst i hi (m - 1) (by omega)]
        simp only [show m - 1 + 1 = m by omega, hm, ↓reduceDIte]
      rw [recvOf_eq (hinL i hi _ (by omega)) hsend fun q hq hqa => hinj q hq _ (hinL i hi _ (by omega)) _ hqa hsend]
      have hext : extrasOf goods base extra (c i)[m] = [] := List.filter_eq_nil_iff.mpr fun g _ h => by
        simp only [decide_eq_true_eq] at h
        obtain ⟨j, hj, -, e⟩ := (hextra g _).mp h
        exact hnotx i hi m hm hm0 j hj e.symm
      rw [hext, List.append_nil]
      have := goodNew_edge (agents := agents) ((hc i hi).1.edge (m - 1) hm1)
      simp only [show m - 1 + 1 = m by omega] at this
      exact this


/-! ## Theorem K3 -/

/-- A cycle with the fewest terminals exists once a cycle exists. -/
theorem exists_min_labelCycle (h : ∃ k ts xs zs, LabelCycle v agents goods base k ts xs zs) :
    ∃ k ts xs zs, LabelCycle v agents goods base k ts xs zs ∧
      ∀ k' ts' xs' zs', LabelCycle v agents goods base k' ts' xs' zs' → k ≤ k' := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∀ k' ts' xs' zs', LabelCycle v agents goods base k' ts' xs' zs' → n ≤ k'
    · obtain ⟨ts, xs, zs, hC⟩ := hn
      exact ⟨n, ts, xs, zs, hC, hm⟩
    · refine Classical.byContradiction fun hno => hm fun k' ts' xs' zs' hC' => Nat.le_of_not_lt fun hlt => hno ?_
      exact ih k' hlt ⟨ts', xs', zs', hC'⟩

open Classical in
/-- **Theorem K3, with its owner** (`k4/c4x.md` §3): at k = 3 with `m ≤ 2n`, a Pareto-maximal `P ∈ 𝒫` has `ω ≤ 0`, or a
terminal `t` whose labels fit the other agents' slots and whose bundle `B_t ∪ (J ∖ Z_t)` threatens nobody (Lemma O's
removal-only completion with owner `t`). If no terminal were such an owner, every terminal would have at least `T` labels,
the walk would close a cycle of exposures, and the cycle move on a shortest one would dominate `P`. -/
theorem theoremK3_owner (hag : agents.Nodup) (hgd : goods.Nodup) (hP : ParetoMax v agents goods base)
    (hT : Three v agents goods) (hσ : goods.length ≤ 2 * agents.length) :
    omegaP v agents goods base ≤ 0 ∨ ∃ t, Terminal v agents goods base t ∧
      Unthreatened v agents goods base t (labelC v agents goods base t) ∧
      ((LB4.junk goods base).filter (labelC v agents goods base t)).length ≤
        otherSlots agents goods base (vbNeeds v goods base) t := by
  by_cases hω : omegaP v agents goods base ≤ 0
  · exact Or.inl hω
  have hω' : 0 < omegaP v agents goods base := by omega
  obtain ⟨t0, ht0⟩ := exists_terminal hag hgd hP hσ hω'
  by_cases hgood : ∃ t, Terminal v agents goods base t ∧
      ((LB4.junk goods base).filter (labelC v agents goods base t)).length ≤
        otherSlots agents goods base (vbNeeds v goods base) t
  · obtain ⟨t, ht, hZ⟩ := hgood
    exact Or.inr ⟨t, ht, unthreatened_labels hgd hP hT ht, hZ⟩
  exfalso
  -- every terminal has at least `T` labels: `|Z_t| > S − cap(t) ≥ T − 1`
  have hbig : ∀ t, Terminal v agents goods base t →
      (agents.filter (fun j => decide (Terminal v agents goods base j))).length ≤
        ((LB4.junk goods base).filter (labelC v agents goods base t)).length := by
    intro t ht
    have h1 := terminals_le_otherSlots hgd hP.1 hT t
    have h2 : ¬ (((LB4.junk goods base).filter (labelC v agents goods base t)).length ≤
        otherSlots agents goods base (vbNeeds v goods base) t) := fun h => hgood ⟨t, ht, h⟩
    have h3 := LB.length_le_of_subset (hag.sublist List.filter_sublist)
      (S := agents.filter (fun j => decide (Terminal v agents goods base j)))
      (T := agents.filter (fun j => decide (Terminal v agents goods base j ∧ j ≠ t)) ++ [t]) fun j hj => by
        obtain ⟨hja, hjT⟩ := List.mem_filter.mp hj
        by_cases e : j = t
        · simp [e]
        · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hja, by simpa [e] using hjT⟩)
    simp only [List.length_append, List.length_singleton] at h3
    omega
  -- a cycle of exposures with fewest terminals, its chains, and the cycle move
  obtain ⟨k, ts, xs, zs, hC, hmin⟩ := exists_min_labelCycle (exists_labelCycle hgd hP hT ht0 hbig)
  let c : Nat → List A := fun i => if h : i < k then Classical.choose (hC.chain i h) else []
  have hc : ∀ i < k, NeedChain v agents goods base (c i) ∧ (c i).head? = some (xs i) ∧
      (c i).getLast? = some (ts ((i + 1) % k)) := by
    intro i hi
    simp only [c, hi, ↓reduceDIte]
    exact Classical.choose_spec (hC.chain i hi)
  exact cycle_contra hgd hP hT hC hc (hC.disjoint hgd hP hT hmin hc)

/-- **Theorem K3** (`k4/c4x.md` §3). Let every listed agent value exactly three goods, strictly balanced, and
`m ≤ 2n` (true in every core, `sigma_nonneg`). Then every Pareto-maximal pre-allocation of 𝒫 is removal-only
completable (`def(P) ≤ 0`): without owner if `ω ≤ 0`, and otherwise with a terminal as owner (`theoremK3_owner`). -/
theorem theoremK3 (hag : agents.Nodup) (hgd : goods.Nodup) (hP : ParetoMax v agents goods base)
    (hT : Three v agents goods) (hσ : goods.length ≤ 2 * agents.length) : RemovalOnly v agents goods base := by
  rcases theoremK3_owner hag hgd hP hT hσ with hω | ⟨t, ht, hU, hZ⟩
  · exact Or.inl ⟨hω, hω⟩
  · by_cases hω : omegaP v agents goods base ≤ 0
    · exact Or.inl ⟨hω, hω⟩
    · exact removalOnly_of_owner (by omega) ht.1 ht.2.1 _ hU hZ

/-- **Theorem K3, completable form**: every Pareto-maximal pre-allocation of 𝒫 (k = 3, `m ≤ 2n`) is completable. -/
theorem completable_K3 (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (hP : ParetoMax v agents goods base) (hT : Three v agents goods) (hσ : goods.length ≤ 2 * agents.length) :
    Completable v agents goods base :=
  completable_of_removalOnly hag hgd hne hP.1 (theoremK3 hag hgd hP hT hσ)

/-! ## A Pareto-maximum exists; D and TARGET again -/

/-- The welfare `Σ_i v_i(B_i)`. -/
def welfare (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Nat :=
  (agents.map (fun i => value v i (baseOf goods base i))).sum

theorem sum_lt_of_le_of_lt {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a) → (∃ a ∈ l, f a < g a) → (l.map f).sum < (l.map g).sum
  | [], _, ⟨_, ha, _⟩ => by simp at ha
  | a :: l, hle, ⟨b, hb, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := LB4.sum_le_sum_of_le f g l fun c hc => hle c (by simp [hc])
    have h2 := hle a (by simp)
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · have := sum_lt_of_le_of_lt f g l (fun c hc => hle c (by simp [hc])) ⟨b, hb, hlt⟩
      omega

/-- **A Pareto-maximum exists** (`k4/c4x.md` §3): 𝒫 is not empty (`inP_phase1`), and a pre-allocation of 𝒫 of
largest welfare is Pareto-maximal (a dominating one has larger welfare, which is bounded). -/
theorem exists_paretoMax (hag : agents.Nodup) (hgd : goods.Nodup) : ∃ base, ParetoMax v agents goods base := by
  let bound := (agents.map (fun i => value v i goods)).sum
  have hle : ∀ base : G → Option A, welfare v agents goods base ≤ bound := fun base =>
    LB4.sum_le_sum_of_le _ _ agents fun i _ => value_sublist v i List.filter_sublist
  have key : ∀ d, ∀ base, InP v agents goods base → bound - welfare v agents goods base = d →
      ∃ base, ParetoMax v agents goods base := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro base hP hd
      by_cases hmax : ∀ base', InP v agents goods base' → ¬ Dominates v agents goods base' base
      · exact ⟨base, hP, hmax⟩
      · obtain ⟨base', hP', hdom⟩ : ∃ base', InP v agents goods base' ∧ Dominates v agents goods base' base :=
          Classical.byContradiction fun h => hmax fun b hb hd => h ⟨b, hb, hd⟩
        have hlt := sum_lt_of_le_of_lt _ _ agents hdom.1 hdom.2
        have := hle base'
        refine ih _ ?_ base' hP' rfl
        unfold welfare at hd this ⊢
        omega
  exact key _ _ (inP_phase1 hag hgd []) rfl

/-- **Conjecture D for k = 3 cores from Theorem K3** — a second proof, independent of LB⁺: every core has a complete
EFX₀ allocation with at most one bundle of more than two goods (a sound completion of a Pareto-maximal pre-allocation).
The conclusion is literally that of `EFX.LB.corollaryD_lists` (LB⁺), whose hypotheses every core satisfies. -/
theorem corollaryD_K3 (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2 := by
  have hne : agents ≠ [] := fun e => by have := hc.1; rw [e] at this; simp at this
  obtain ⟨base, hP⟩ := exists_paretoMax (v := v) hag hgd
  have hT : Three v agents goods := ⟨hc.2.1, hc.2.2.1⟩
  obtain ⟨o, X, hS⟩ := completable_K3 hag hgd hne hP hT (sigma_nonneg hc)
  obtain ⟨hX, hE, w, -, hw⟩ := hS.efx0_d2 hgd hne
  exact ⟨X, hX, hE, w, hw⟩

/-- **The two proofs of D agree on cores**: `corollaryD_K3` (Theorem K3) and `EFX.LB.corollaryD_lists` (LB⁺) prove the
same statement for every core. -/
theorem corollaryD_K3_and_LB (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore v agents goods) :
    (∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2) ∧
    (∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2) :=
  ⟨corollaryD_K3 hag hgd hc, LB.corollaryD_lists v hag hgd (fun e => by have := hc.1; rw [e] at this; simp at this)
    hc.2.1 fun i hi g hg => Nat.le_of_lt (hc.2.2.1 i hi g hg)⟩

/-- **TARGET from Theorem K3** (lists): the CORE theorem (`EFX.core_reduction`) with `corollaryD_K3` in place of LB⁺. -/
theorem target_K3_lists (v : A → G → Nat) {agents : List A} {goods : List G} (hne : agents ≠ [])
    (hag : agents.Nodup) (hgd : goods.Nodup) (h3 : ∀ i ∈ agents, (relevant v i goods).length ≤ 3) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X :=
  core_reduction v agents.length (fun _ _ hag' hgd' _ hc => by
      obtain ⟨X, hX, hE, -⟩ := corollaryD_K3 hag' hgd' hc
      exact ⟨X, hX, hE⟩)
    agents goods hne hag hgd (Nat.le_refl _) h3

/-- **TARGET from Theorem K3**, in the model's terms (the statement of `EFX.target`): every instance in which every agent
positively values at most three goods has a complete EFX₀ allocation. -/
theorem target_K3 (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := target_K3_lists I.v (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩))
    (List.nodup_finRange I.n) (List.nodup_finRange I.m) (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.lemmaO
#print axioms EFX.C4min.unthreatened_labels
#print axioms EFX.C4min.removalOnly_of_owner
#print axioms EFX.C4min.terminals_le_otherSlots
#print axioms EFX.C4min.exists_terminal
#print axioms EFX.C4min.sigma_nonneg
#print axioms EFX.C4min.exists_labelCycle
#print axioms EFX.C4min.exposed_top
#print axioms EFX.C4min.LabelCycle.cut
#print axioms EFX.C4min.splice
#print axioms EFX.C4min.LabelCycle.disjoint
#print axioms EFX.C4min.cycle_contra
#print axioms EFX.C4min.theoremK3_owner
#print axioms EFX.C4min.theoremK3
#print axioms EFX.C4min.completable_K3
#print axioms EFX.C4min.exists_paretoMax
#print axioms EFX.C4min.corollaryD_K3
#print axioms EFX.C4min.corollaryD_K3_and_LB
#print axioms EFX.C4min.target_K3_lists
#print axioms EFX.C4min.target_K3
