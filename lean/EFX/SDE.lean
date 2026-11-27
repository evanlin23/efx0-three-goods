import EFX.OC1Perf

/-!
# Lemma SD-E: the earliest-wanter chain leaves a serial-dictatorship outcome (`k4/oc1max_multi.md` §12)

Lemma SD-E (K4.MULTI.SDE, `proof/k4-oc1max-multi`; refereed CORRECT, `k4/referee/oc1max_multi.md` §11). Let `Y` be
the serial-dictatorship outcome of the order `σ` (strict values) and `k` a frozen agent. The *earliest-wanter chain*
`E(k) = (k = x₀, x₁, …, x_t = z)` takes for `x_l` the σ-earliest wanter of `Y_{x_{l−1}}` and stops at an agent `z`
whose pick nobody wants (`EChain`). Let `T` be a set of goods containing no pick other than `Y_z`, and `B₁` the state
after `E(k)`: `x_l` holds `Y_{x_{l−1}}` (`l ≥ 1`), every other agent keeps its pick (`src`: the agent whose pick
`a` holds), and `k` takes `T`. Then `B₁` without `k` and `T` is the serial-dictatorship outcome of `σ` with `k`
deleted, on the goods without `T` (`sdE`). If `Y` is a perfect start, so is that outcome (`sdE_perfect`).

General tools: `Before σ c a` (c comes before a in σ), `sdPick_turn` (at its turn an agent takes a good at least as
good as every relevant good still available), `sdPick_eq_of_greedy` (an assignment in which every agent gets its
favourite among the goods the earlier agents left is the serial-dictatorship outcome).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Order in a list -/

/-- `c` comes before `a` in the list. -/
def Before : List A → A → A → Prop
  | [], _, _ => False
  | x :: xs, c, a => (c = x ∧ a ∈ xs) ∨ Before xs c a

omit [DecidableEq A] in
theorem before_mem : ∀ {l : List A} {c a : A}, Before l c a → c ∈ l ∧ a ∈ l
  | [], _, _, h => h.elim
  | x :: xs, c, a, h => by
    rcases h with ⟨rfl, ha⟩ | h
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ ha⟩
    · obtain ⟨h1, h2⟩ := before_mem h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

omit [DecidableEq A] in
theorem before_asymm : ∀ {l : List A}, l.Nodup → ∀ {c a : A}, Before l c a → ¬ Before l a c
  | [], _, _, _, h, _ => h.elim
  | x :: xs, hnd, c, a, h, h' => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    rcases h with ⟨rfl, ha⟩ | h <;> rcases h' with ⟨rfl, hc⟩ | h'
    · exact hx hc
    · exact hx (before_mem h').2
    · exact hx (before_mem h).2
    · exact before_asymm (List.nodup_cons.mp hnd).2 h h'

omit [DecidableEq A] in
theorem before_total : ∀ {l : List A} {c a : A}, c ∈ l → a ∈ l → c ≠ a → Before l c a ∨ Before l a c
  | [], _, _, hc, _, _ => by simp at hc
  | x :: xs, c, a, hc, ha, hne => by
    rcases List.mem_cons.mp hc with hc1 | hc1 <;> rcases List.mem_cons.mp ha with ha1 | ha1
    · exact absurd (hc1.trans ha1.symm) hne
    · exact Or.inl (Or.inl ⟨hc1, ha1⟩)
    · exact Or.inr (Or.inl ⟨ha1, hc1⟩)
    · rcases before_total hc1 ha1 hne with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- Deleting another element does not change the order. -/
theorem before_erase : ∀ {l : List A} {k c a : A}, c ≠ k → a ≠ k → (Before (l.erase k) c a ↔ Before l c a)
  | [], _, _, _, _, _ => by simp [Before]
  | x :: xs, k, c, a, hck, hak => by
    by_cases hxk : x = k
    · subst hxk
      rw [List.erase_cons_head]
      constructor
      · exact Or.inr
      · rintro (⟨rfl, -⟩ | h)
        · exact absurd rfl hck
        · exact h
    · rw [List.erase_cons_tail (by simpa using hxk)]
      simp only [Before]
      rw [before_erase hck hak, List.mem_erase_of_ne hak]

omit [DecidableEq A] in
theorem not_before_head {x : A} {xs : List A} (hx : x ∉ xs) {c : A} : ¬ Before (x :: xs) c x := by
  rintro (⟨-, h⟩ | h)
  · exact hx h
  · exact hx (before_mem h).2

/-! ## Serial dictatorship turn by turn -/

section turns
variable (v : A → G → Nat)

/-- **At its turn an agent takes a good at least as good as every relevant good still available.** -/
theorem sdPick_turn : ∀ (ord : List A) (G0 : List G), ord.Nodup → G0.Nodup → ∀ a ∈ ord, ∀ g ∈ G0,
    (∀ c, Before ord c a → sdPick v ord G0 c ≠ some g) → 0 < v a g →
      ∃ y, sdPick v ord G0 a = some y ∧ v a g ≤ v a y
  | [], _, _, _, a, ha, _, _, _, _ => by simp at ha
  | x :: xs, G0, hnd, hG, a, ha, g, hg, havail, hpos => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    by_cases hax : a = x
    · subst hax
      rw [sdPick_cons, ite_eq_left rfl]
      cases hf : fav v a G0 with
      | none => exact absurd hpos (fav_none hf g hg)
      | some y => exact ⟨y, rfl, (fav_some hf).2.2 g hg hpos⟩
    · have haxs : a ∈ xs := (List.mem_cons.mp ha).resolve_left hax
      have hxne : fav v x G0 ≠ some g := by
        have := havail x (Or.inl ⟨rfl, haxs⟩)
        rwa [sdPick_cons, ite_eq_left rfl] at this
      have hg' : g ∈ takeOut G0 (fav v x G0) := by
        cases hf : fav v x G0 with
        | none => exact hg
        | some y =>
          have : g ≠ y := fun e => hxne (by rw [hf, e])
          exact (List.mem_erase_of_ne this).mpr hg
      rw [sdPick_cons, ite_eq_right hax]
      refine sdPick_turn xs _ (List.nodup_cons.mp hnd).2 (nodup_takeOut hG _) a haxs g hg' (fun c hc => ?_) hpos
      have hcx : c ≠ x := fun e => hx (e ▸ (before_mem hc).1)
      have := havail c (Or.inr hc)
      rwa [sdPick_cons, ite_eq_right hcx] at this

/-- **The greedy characterization of serial dictatorship.** If `μ` gives distinct relevant goods of `G0`, and every
agent of the order, among the goods of `G0` that no earlier agent receives, gets a good at least as good as every
relevant one (strict values), then `μ` is the serial-dictatorship outcome. -/
theorem sdPick_eq_of_greedy : ∀ (ord : List A) (G0 : List G) (μ : A → Option G), ord.Nodup → G0.Nodup →
    (∀ a ∈ ord, ∀ g ∈ G0, ∀ h ∈ G0, 0 < v a g → v a g = v a h → g = h) →
    (∀ a ∈ ord, ∀ b, μ a = some b → b ∈ G0 ∧ 0 < v a b) →
    (∀ a ∈ ord, ∀ c ∈ ord, ∀ b, μ a = some b → μ c = some b → a = c) →
    (∀ a ∈ ord, ∀ g ∈ G0, (∀ c, Before ord c a → μ c ≠ some g) → 0 < v a g →
      ∃ b, μ a = some b ∧ v a g ≤ v a b) →
    ∀ a ∈ ord, sdPick v ord G0 a = μ a
  | [], _, _, _, _, _, _, _, _, a, ha => by simp at ha
  | x :: xs, G0, μ, hnd, hG, hsv, hmem, hinj, hgreedy, a, ha => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    -- the first agent takes `μ x`
    have hfx : fav v x G0 = μ x := by
      cases hf : fav v x G0 with
      | none =>
        cases hm : μ x with
        | none => rfl
        | some b =>
          obtain ⟨hb, hbpos⟩ := hmem x List.mem_cons_self b hm
          exact absurd hbpos (fav_none hf b hb)
      | some y =>
        obtain ⟨hy, hypos, -⟩ := fav_some hf
        obtain ⟨b, hb, hle⟩ := hgreedy x List.mem_cons_self y hy (fun c hc => absurd hc (not_before_head hx)) hypos
        obtain ⟨hbG, hbpos⟩ := hmem x List.mem_cons_self b hb
        have := (fav_some hf).2.2 b hbG hbpos
        rw [hb, hsv x List.mem_cons_self y hy b hbG hypos (by omega)]
    by_cases hax : a = x
    · subst hax; rw [sdPick_cons, ite_eq_left rfl, hfx]
    have haxs : a ∈ xs := (List.mem_cons.mp ha).resolve_left hax
    rw [sdPick_cons, ite_eq_right hax, hfx]
    -- the rest on the goods `μ x` left
    have hmemT : ∀ g, g ∈ takeOut G0 (μ x) ↔ g ∈ G0 ∧ μ x ≠ some g := fun g => by
      cases hmx : μ x with
      | none => simp [takeOut]
      | some y =>
        simp only [takeOut]
        constructor
        · intro h
          refine ⟨List.mem_of_mem_erase h, fun e => ?_⟩
          cases e; exact List.Nodup.not_mem_erase hG h
        · rintro ⟨h1, h2⟩
          exact (List.mem_erase_of_ne fun e => h2 (by rw [e])).mpr h1
    refine sdPick_eq_of_greedy xs _ μ (List.nodup_cons.mp hnd).2 (nodup_takeOut hG _)
      (fun c hc g hg h hh => hsv c (List.mem_cons_of_mem _ hc) g ((hmemT g).mp hg).1 h ((hmemT h).mp hh).1)
      (fun c hc b hb => ?_) (fun c hc d hd => hinj c (List.mem_cons_of_mem _ hc) d (List.mem_cons_of_mem _ hd))
      (fun c hc g hg havail hpos => ?_) a haxs
    · obtain ⟨h1, h2⟩ := hmem c (List.mem_cons_of_mem _ hc) b hb
      refine ⟨(hmemT b).mpr ⟨h1, fun e => ?_⟩, h2⟩
      have hcx : c ≠ x := fun e' => hx (e' ▸ hc)
      exact hcx (hinj c (List.mem_cons_of_mem _ hc) x List.mem_cons_self b hb e)
    · obtain ⟨hgG, hgx⟩ := (hmemT g).mp hg
      refine hgreedy c (List.mem_cons_of_mem _ hc) g hgG (fun d hd => ?_) hpos
      rcases hd with ⟨rfl, -⟩ | hd
      · exact hgx
      · exact havail d hd

end turns

/-! ## Chains as lists: predecessors -/

omit [DecidableEq A] in
theorem zip_tail_snd_unique : ∀ {l : List A}, l.Nodup → ∀ {p p' q : A},
    (p, q) ∈ l.zip l.tail → (p', q) ∈ l.zip l.tail → p = p'
  | [], _, _, _, _, h, _ => by simp at h
  | [_], _, _, _, _, h, _ => by simp at h
  | a :: b :: rest, hnd, p, p', q, h, h' => by
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h h'
    have hb : b ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    rcases h with ⟨hp, hq⟩ | h <;> rcases h' with ⟨hp', hq'⟩ | h'
    · rw [hp, hp']
    · have := (List.of_mem_zip h').2; rw [hq] at this; exact absurd this hb
    · have := (List.of_mem_zip h).2; rw [hq'] at this; exact absurd this hb
    · exact zip_tail_snd_unique (List.nodup_cons.mp hnd).2 h h'

omit [DecidableEq A] in
theorem zip_tail_fst_unique : ∀ {l : List A}, l.Nodup → ∀ {p q q' : A},
    (p, q) ∈ l.zip l.tail → (p, q') ∈ l.zip l.tail → q = q'
  | [], _, _, _, _, h, _ => by simp at h
  | [_], _, _, _, _, h, _ => by simp at h
  | a :: b :: rest, hnd, p, q, q', h, h' => by
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h h'
    have ha : a ∉ b :: rest := (List.nodup_cons.mp hnd).1
    rcases h with ⟨hp, hq⟩ | h <;> rcases h' with ⟨hp', hq'⟩ | h'
    · rw [hq, hq']
    · have := (List.of_mem_zip h').1; rw [hp] at this; exact absurd this ha
    · have := (List.of_mem_zip h).1; rw [hp'] at this; exact absurd this ha
    · exact zip_tail_fst_unique (List.nodup_cons.mp hnd).2 h h'

omit [DecidableEq A] in
theorem mem_tail_iff_pair {l : List A} {q : A} : q ∈ l.tail ↔ ∃ p, (p, q) ∈ l.zip l.tail := by
  constructor
  · intro h
    rw [← List.map_snd_zip (l₁ := l) (l₂ := l.tail) (by simp)] at h
    obtain ⟨⟨p, q'⟩, hp, rfl⟩ := List.mem_map.mp h
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩; exact (List.of_mem_zip hp).2

/-- The agent whose pick `a` holds after the chain `ch`: its predecessor in `ch`, or `a` itself. -/
def src (ch : List A) (a : A) : A :=
  match (ch.zip ch.tail).find? (fun pq => decide (pq.2 = a)) with
  | some pq => pq.1
  | none => a

theorem src_of_pair {ch : List A} (hnd : ch.Nodup) {p q : A} (h : (p, q) ∈ ch.zip ch.tail) : src ch q = p := by
  unfold src
  cases hq : (ch.zip ch.tail).find? (fun pq => decide (pq.2 = q)) with
  | none => exact absurd (List.find?_eq_none.mp hq _ h) (by simp)
  | some pq =>
    have h1 := List.mem_of_find?_eq_some hq
    have h2 : pq.2 = q := by simpa using List.find?_some hq
    obtain ⟨p', q'⟩ := pq
    simp only at h2 ⊢; subst h2
    exact zip_tail_snd_unique hnd h1 h

theorem src_of_not_tail {ch : List A} {a : A} (h : a ∉ ch.tail) : src ch a = a := by
  unfold src
  rw [List.find?_eq_none.mpr fun pq hpq => by
    simp only [decide_eq_true_eq]
    intro e; exact h (e ▸ (List.of_mem_zip hpq).2)]

/-! ## The earliest-wanter chain and Lemma SD-E -/

section sde
variable (v : A → G → Nat) (agents : List A) (σ : List A) (Y : A → Option G)

/-- `a` wants `j`'s pick: `j` holds a good that `a` values above its own pick. -/
def Wants (a j : A) : Prop := ∃ y, Y j = some y ∧ mval v Y a < v a y

/-- **The earliest-wanter chain** `ch = (x₀, …, x_t)` (`k4/oc1max_multi.md` §12): distinct listed agents, `t ≥ 1`,
each `x_l` (`l ≥ 1`) a wanter of `Y_{x_{l−1}}` that comes before every other wanter in `σ`, and nobody wanting the
pick of the agent without successor (the end `z`). -/
structure EChain (ch : List A) : Prop where
  nodup : ch.Nodup
  mem : ∀ x ∈ ch, x ∈ agents
  tail_ne : ch.tail ≠ []
  wants : ∀ p ∈ ch.zip ch.tail, Wants v Y p.2 p.1
  earliest : ∀ p ∈ ch.zip ch.tail, ∀ a ∈ agents, a ≠ p.2 → Wants v Y a p.1 → Before σ p.2 a
  last : ∀ z ∈ ch, (∀ q, (z, q) ∉ ch.zip ch.tail) → ∀ a ∈ agents, ¬ Wants v Y a z

end sde

section sdeProof
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- A wanter of a pick comes after its holder in the order. -/
theorem before_of_wants (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {a j : A} (ha : a ∈ agents)
    (hj : j ∈ agents) (haj : a ≠ j) (hw : Wants v (sdPick v σ goods) a j) : Before σ j a := by
  have hm := isMatching_sdPick (v := v) hσ hgd
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  refine Classical.byContradiction fun hno => ?_
  have hb := (before_total (hσ.mem_iff.mpr ha) (hσ.mem_iff.mpr hj) haj).resolve_right hno
  obtain ⟨g, hg, hlt⟩ := hw
  obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods hnd hgd a (hσ.mem_iff.mpr ha) g (hm.mem j g hg).2.1
    (fun c hc hcg => by
      have := hm.inj c j g hcg hg; subst this
      exact before_asymm hnd hc hb)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
  rw [mval_some hy] at hlt
  omega

/-- **Lemma SD-E** (K4.MULTI.SDE). Let `Y = sdPick v σ goods` with strict values, `k :: rest` an earliest-wanter
chain, and `T` a set of goods whose only possible pick is the end's. After the chain (each agent `a ≠ k` holding
the pick of `src (k :: rest) a`), the state without `k` and `T` is the serial-dictatorship outcome of `σ` with `k`
deleted, on the goods without `T`. -/
theorem sdE (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) (hsv : StrictVals v agents goods)
    {k : A} {rest : List A} (hch : EChain v agents σ (sdPick v σ goods) (k :: rest)) {T : List G}
    (hT : ∀ g ∈ T, ∀ x ∈ agents, sdPick v σ goods x = some g →
      x ∈ k :: rest ∧ ∀ q, (x, q) ∉ (k :: rest).zip rest) :
    ∀ a ∈ σ.erase k, sdPick v (σ.erase k) (goods.filter (fun g => decide (g ∉ T))) a =
      sdPick v σ goods (src (k :: rest) a) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = sdPick v σ goods := ⟨_, rfl⟩
  rw [← hY] at hch hT ⊢
  have hm : IsMatching v agents goods Y := hY ▸ isMatching_sdPick (v := v) hσ hgd
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hchnd := hch.nodup
  have hk : k ∉ rest := (List.nodup_cons.mp hchnd).1
  have hmemσ : ∀ a, a ∈ σ.erase k ↔ a ≠ k ∧ a ∈ agents := fun a => by
    rw [List.Nodup.mem_erase_iff hnd, hσ.mem_iff]
  -- the source of an agent other than `k`
  have hsrc : ∀ a, a ≠ k → (a ∈ rest ∧ (src (k :: rest) a, a) ∈ (k :: rest).zip rest) ∨
      (a ∉ rest ∧ src (k :: rest) a = a) := fun a hak => by
    by_cases har : a ∈ rest
    · obtain ⟨p, hp⟩ := (mem_tail_iff_pair (l := k :: rest)).mp har
      exact Or.inl ⟨har, by rw [src_of_pair hchnd hp]; exact hp⟩
    · exact Or.inr ⟨har, src_of_not_tail har⟩
  have hsrc_mem : ∀ a ∈ agents, a ≠ k → src (k :: rest) a ∈ agents := fun a ha hak => by
    rcases hsrc a hak with ⟨-, hp⟩ | ⟨-, h⟩
    · exact hch.mem _ (List.of_mem_zip hp).1
    · rw [h]; exact ha
  -- the value of an agent after the chain is at least its pick value
  have hgain : ∀ a, a ≠ k → ∀ b, Y (src (k :: rest) a) = some b → mval v Y a ≤ v a b := fun a hak b hb => by
    rcases hsrc a hak with ⟨-, hp⟩ | ⟨-, h⟩
    · obtain ⟨y, hy, hlt⟩ := hch.wants _ hp
      simp only at hy hlt; rw [hy] at hb; cases hb; exact Nat.le_of_lt hlt
    · rw [h] at hb; rw [mval_some hb]; exact Nat.le_refl _
  have hstrict' : ∀ a ∈ σ.erase k, ∀ g ∈ goods.filter (fun g => decide (g ∉ T)),
      ∀ h ∈ goods.filter (fun g => decide (g ∉ T)), 0 < v a g → v a g = v a h → g = h := fun a ha g hg h hh =>
    hsv a ((hmemσ a).mp ha).2 g (List.mem_filter.mp hg).1 h (List.mem_filter.mp hh).1
  refine sdPick_eq_of_greedy v _ _ _ (hnd.erase k) (hgd.sublist List.filter_sublist) hstrict'
    (fun a ha b hb => ?_) (fun a ha c hc b hb hb' => ?_) (fun a ha g hg havail hpos => ?_)
  · -- (g1) the goods are relevant and outside `T`
    obtain ⟨hak, ha'⟩ := (hmemσ a).mp ha
    have hs := hsrc_mem a ha' hak
    obtain ⟨-, hbG, hbpos⟩ := hm.mem _ b hb
    refine ⟨List.mem_filter.mpr ⟨hbG, decide_eq_true fun hbT => ?_⟩, ?_⟩
    · obtain ⟨hsch, hsno⟩ := hT b hbT _ hs hb
      rcases hsrc a hak with ⟨-, hp⟩ | ⟨har, h⟩
      · exact hsno a hp
      · rw [h] at hsch
        rcases List.mem_cons.mp hsch with e | e
        · exact hak e
        · exact har e
    · rcases hsrc a hak with ⟨-, hp⟩ | ⟨-, h⟩
      · obtain ⟨y, hy, hlt⟩ := hch.wants _ hp
        simp only at hy hlt; rw [hy] at hb; cases hb; omega
      · rw [h] at hb; exact (hm.mem a b hb).2.2
  · -- (g2) distinct goods
    obtain ⟨hak, -⟩ := (hmemσ a).mp ha
    obtain ⟨hck, -⟩ := (hmemσ c).mp hc
    have he := hm.inj _ _ b hb hb'
    rcases hsrc a hak with ⟨har, hpa⟩ | ⟨har, hsa⟩ <;> rcases hsrc c hck with ⟨hcr, hpc⟩ | ⟨hcr, hsc⟩
    · rw [he] at hpa; exact zip_tail_fst_unique hchnd hpa hpc
    · rw [he, hsc] at hpa
      have := (List.of_mem_zip hpa).1
      rcases List.mem_cons.mp this with e | e
      · exact absurd e hck
      · exact absurd e hcr
    · rw [hsa] at he; rw [← he] at hpc
      have := (List.of_mem_zip hpc).1
      rcases List.mem_cons.mp this with e | e
      · exact absurd e hak
      · exact absurd e har
    · rw [hsa, hsc] at he; exact he
  · -- (g3) every agent gets its favourite among the goods left
    obtain ⟨hak, ha'⟩ := (hmemσ a).mp ha
    obtain ⟨hgG, -⟩ := List.mem_filter.mp hg
    refine Classical.byContradiction fun hno => ?_
    -- `a` values `g` above its good after the chain, hence above its pick
    have hab : ∀ b, Y (src (k :: rest) a) = some b → v a b < v a g := fun b hb =>
      Nat.lt_of_not_le fun hle => hno ⟨b, hb, hle⟩
    have hwant : mval v Y a < v a g := by
      cases hb : Y (src (k :: rest) a) with
      | none =>
        rcases hsrc a hak with ⟨-, hp⟩ | ⟨-, h⟩
        · obtain ⟨y, hy, -⟩ := hch.wants _ hp
          simp only at hy; rw [hy] at hb; cases hb
        · rw [h] at hb; rw [mval_none hb]; exact hpos
      | some b => exact Nat.lt_of_le_of_lt (hgain a hak b hb) (hab b hb)
    by_cases hpicked : ∃ j, Y j = some g
    · obtain ⟨j, hj⟩ := hpicked
      have hjag := (hm.mem j g hj).1
      have hwj : Wants v Y a j := ⟨g, hj, hwant⟩
      have haj : a ≠ j := fun e => by
        subst e; rw [mval_some hj] at hwant; omega
      by_cases hsucc : ∃ s, (j, s) ∈ (k :: rest).zip rest
      · -- `j` is on the chain before its end: its pick is held by its successor `s`
        obtain ⟨s, hs⟩ := hsucc
        have hsrest : s ∈ rest := (List.of_mem_zip hs).2
        have hsk : s ≠ k := fun e => hk (e ▸ hsrest)
        have hsrc_s : src (k :: rest) s = j := src_of_pair hchnd hs
        have hsa : s ≠ a := fun e => by
          subst e; exact absurd (hab g (by rw [hsrc_s, hj])) (Nat.lt_irrefl _)
        have hbef := hch.earliest (j, s) hs a ha' (Ne.symm hsa) hwj
        exact havail s ((before_erase hsk hak).mpr hbef) (by rw [hsrc_s, hj])
      · by_cases hjch : j ∈ k :: rest
        · -- `j` is the end: nobody wants its pick
          exact hch.last j hjch (fun q hq => hsucc ⟨q, hq⟩) a ha' hwj
        · -- `j` is off the chain and keeps its pick; it comes before `a`
          have hjk : j ≠ k := fun e => hjch (e ▸ List.mem_cons_self)
          have hjrest : j ∉ rest := fun h => hjch (List.mem_cons_of_mem _ h)
          have hbef := before_of_wants hσ hag hgd ha' hjag haj (hY ▸ hwj)
          exact havail j ((before_erase hjk hak).mpr hbef) (by rw [src_of_not_tail hjrest, hj])
    · -- `g` is junk of `Y`: available at `a`'s turn
      have hpk : ∀ j, Y j ≠ some g := fun j hj => hpicked ⟨j, hj⟩
      obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods hnd hgd a (hσ.mem_iff.mpr ha') g hgG
        (fun c _ => by rw [← hY]; exact hpk c) hpos
      rw [← hY] at hy
      rw [mval_some hy] at hwant
      omega

/-- **SD-E, perfect starts**: if the picks form a perfect start, so does the reduced outcome. -/
theorem sdE_perfect (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) (hsv : StrictVals v agents goods)
    {k : A} {rest : List A} (hch : EChain v agents σ (sdPick v σ goods) (k :: rest)) {T : List G}
    (hT : ∀ g ∈ T, ∀ x ∈ agents, sdPick v σ goods x = some g →
      x ∈ k :: rest ∧ ∀ q, (x, q) ∉ (k :: rest).zip rest)
    (hperf : PerfectStart v agents goods (sdPick v σ goods)) :
    PerfectStart v (agents.erase k) (goods.filter (fun g => decide (g ∉ T)))
      (sdPick v (σ.erase k) (goods.filter (fun g => decide (g ∉ T)))) := by
  intro i hi ⟨g, hg, hpos⟩
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hik : i ≠ k := fun e => by subst e; exact List.Nodup.not_mem_erase hag hi
  have hiag : i ∈ agents := List.mem_of_mem_erase hi
  have hiσ : i ∈ σ.erase k := (List.Nodup.mem_erase_iff hnd).mpr ⟨hik, hσ.mem_iff.mpr hiag⟩
  rw [sdE hσ hag hgd hsv hch hT i hiσ]
  by_cases hir : i ∈ rest
  · obtain ⟨p, hp⟩ := (mem_tail_iff_pair (l := k :: rest)).mp hir
    rw [src_of_pair hch.nodup hp]
    obtain ⟨y, hy, -⟩ := hch.wants _ hp
    simp only at hy; rw [hy]; rfl
  · rw [src_of_not_tail hir]
    exact hperf i hiag ⟨g, (List.mem_filter.mp hg).1, hpos⟩

end sdeProof

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.before_erase
#print axioms EFX.OC1Max.sdPick_turn
#print axioms EFX.OC1Max.sdPick_eq_of_greedy
#print axioms EFX.OC1Max.src_of_pair
#print axioms EFX.OC1Max.before_of_wants
#print axioms EFX.OC1Max.sdE
#print axioms EFX.OC1Max.sdE_perfect
