import EFX.RecS

/-!
# Lemma SD-E(round) (`k4/oc1max_multi.md` §17 on `proof/k4-oc1max-multi-2`)

Refereed CORRECT (`k4/referee/oc1max_multi.md` §15). A *round* settles a set `K` of agents at once. Each `k ∈ K` gets a
chain `P_k = (k = x₀, …, x_t = z_k)`, `t ≥ 1`, a **prefix** of the earliest-wanter chain `E(k)`: each `x_l` is the
σ-earliest wanter of `Y_{x_{l−1}}`, and the head `z_k` may be frozen. The chains are vertex-disjoint, and `k` takes a
set `T_k` whose only possible pick is its head's, the `T_k` pairwise disjoint. A head pick that no `T_k` takes is
*released*. With strict values, suppose

- **(H)** every agent outside `K` that wants a released head pick at the picks values its good after the round above
  that pick.

Then the state after the round, without `K` and `⋃ T_k`, is the serial-dictatorship outcome of `σ` with `K` deleted
(`sdE_round`).

The proof is SD-E's (`EFX.OC1Max.sdE`) with one new case, and it runs through an abstract form (`sdE_round_abs`):
the round is a map `s` (after the round, `a ∉ K` holds the pick of `s a`) such that every moved agent wants the pick it
receives and is its earliest wanter, no two agents receive the same pick, no received good is taken, and (H) holds for
the picks that nobody receives and nobody takes.
-/

set_option autoImplicit false

namespace EFX
namespace Round

open OC1Max LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

omit [DecidableEq A] in
/-- The order of two kept elements is unchanged by a filter. -/
theorem before_filter (p : A → Bool) {c a : A} (hc : p c = true) (ha : p a = true) :
    ∀ {l : List A}, Before (l.filter p) c a ↔ Before l c a
  | [] => by simp [Before]
  | x :: xs => by
    have ih := before_filter p hc ha (l := xs)
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx]
      simp only [Before, List.mem_filter, ha, and_true, ih]
    · rw [List.filter_cons_of_neg hx]
      simp only [Before, ih]
      constructor
      · exact Or.inr
      · rintro (⟨rfl, -⟩ | h)
        · exact absurd hc hx
        · exact h

section abs
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **Lemma SD-E(round), abstract form.** Let `Y` be the picks of `σ` (strict values) and `s` a round: after it, an
agent `a ∉ K` holds the pick of `s a`, where
- (s1) `s a` is `a` itself, or `a` wants `Y_{s a}`;
- (s2) if `s a ≠ a`, `a` is the σ-earliest wanter of `Y_{s a}`;
- (s3) no two agents outside `K` hold the same pick;
- (s4) no good held after the round is in `U` (the goods taken by `K`);
- (H) an agent outside `K` that wants a pick that nobody holds after the round and that is not taken values its good
  after the round above that pick.

Then the state after the round is the serial-dictatorship outcome of `σ` without `K`, on the goods outside `U`. -/
theorem sdE_round_abs (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) {K : List A} {U : List G} {s : A → A}
    (hs1 : ∀ a ∈ agents, a ∉ K → s a ∈ agents ∧ (s a = a ∨ Wants v (sdPick v σ goods) a (s a)))
    (hs2 : ∀ a ∈ agents, a ∉ K → s a ≠ a → ∀ c ∈ agents, c ≠ a → Wants v (sdPick v σ goods) c (s a) →
      Before σ a c)
    (hs3 : ∀ a ∈ agents, ∀ c ∈ agents, a ∉ K → c ∉ K → s a = s c → a = c)
    (hs4 : ∀ a ∈ agents, a ∉ K → ∀ b, sdPick v σ goods (s a) = some b → b ∉ U)
    (hH : ∀ a ∈ agents, a ∉ K → ∀ j ∈ agents, ∀ g, sdPick v σ goods j = some g →
      (∀ c ∈ agents, c ∉ K → sdPick v σ goods (s c) ≠ some g) → g ∉ U → Wants v (sdPick v σ goods) a j →
      ∃ b, sdPick v σ goods (s a) = some b ∧ v a g < v a b) :
    ∀ a ∈ σ.filter (fun a => decide (a ∉ K)),
      sdPick v (σ.filter (fun a => decide (a ∉ K))) (goods.filter (fun g => decide (g ∉ U))) a =
        sdPick v σ goods (s a) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = sdPick v σ goods := ⟨_, rfl⟩
  rw [← hY] at hs1 hs2 hs4 hH ⊢
  have hm : IsMatching v agents goods Y := hY ▸ isMatching_sdPick (v := v) hσ hgd
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hmemσ : ∀ a, a ∈ σ.filter (fun a => decide (a ∉ K)) ↔ a ∈ agents ∧ a ∉ K := fun a => by
    rw [List.mem_filter, hσ.mem_iff]; simp
  have hbef : ∀ c a, c ∉ K → a ∉ K → (Before (σ.filter (fun a => decide (a ∉ K))) c a ↔ Before σ c a) :=
    fun c a hc ha => before_filter _ (by simpa using hc) (by simpa using ha)
  -- the value after the round is at least the pick value
  have hgain : ∀ a ∈ agents, a ∉ K → ∀ b, Y (s a) = some b → mval v Y a ≤ v a b := fun a ha haK b hb => by
    rcases (hs1 a ha haK).2 with h | ⟨y, hy, hlt⟩
    · rw [h] at hb; rw [mval_some hb]; exact Nat.le_refl _
    · rw [hy] at hb; cases hb; exact Nat.le_of_lt hlt
  have hstrict' : ∀ a ∈ σ.filter (fun a => decide (a ∉ K)), ∀ g ∈ goods.filter (fun g => decide (g ∉ U)),
      ∀ h ∈ goods.filter (fun g => decide (g ∉ U)), 0 < v a g → v a g = v a h → g = h := fun a ha g hg h hh =>
    hsv a ((hmemσ a).mp ha).1 g (List.mem_filter.mp hg).1 h (List.mem_filter.mp hh).1
  refine sdPick_eq_of_greedy v _ _ _ (hnd.sublist List.filter_sublist) (hgd.sublist List.filter_sublist) hstrict'
    (fun a ha b hb => ?_) (fun a ha c hc b hb hb' => ?_) (fun a ha g hg havail hpos => ?_)
  · -- (g1) the goods are relevant and not taken
    obtain ⟨ha', haK⟩ := (hmemσ a).mp ha
    obtain ⟨-, hbG, hbpos⟩ := hm.mem _ b hb
    refine ⟨List.mem_filter.mpr ⟨hbG, decide_eq_true (hs4 a ha' haK b hb)⟩, ?_⟩
    rcases (hs1 a ha' haK).2 with h | ⟨y, hy, hlt⟩
    · rw [h] at hb; exact (hm.mem a b hb).2.2
    · rw [hy] at hb; cases hb; omega
  · -- (g2) distinct goods
    obtain ⟨ha', haK⟩ := (hmemσ a).mp ha
    obtain ⟨hc', hcK⟩ := (hmemσ c).mp hc
    exact hs3 a ha' c hc' haK hcK (hm.inj _ _ b hb hb')
  · -- (g3) every agent gets its favourite among the goods left
    obtain ⟨ha', haK⟩ := (hmemσ a).mp ha
    obtain ⟨hgG, hgU⟩ := List.mem_filter.mp hg
    have hgU' : g ∉ U := by simpa using hgU
    refine Classical.byContradiction fun hno => ?_
    have hab : ∀ b, Y (s a) = some b → v a b < v a g := fun b hb =>
      Nat.lt_of_not_le fun hle => hno ⟨b, hb, hle⟩
    have hwant : mval v Y a < v a g := by
      cases hb : Y (s a) with
      | none =>
        rcases (hs1 a ha' haK).2 with h | ⟨y, hy, -⟩
        · rw [h] at hb; rw [mval_none hb]; exact hpos
        · rw [hy] at hb; cases hb
      | some b => exact Nat.lt_of_le_of_lt (hgain a ha' haK b hb) (hab b hb)
    by_cases hpicked : ∃ j, Y j = some g
    · obtain ⟨j, hj⟩ := hpicked
      have hjag := (hm.mem j g hj).1
      have hwj : Wants v Y a j := ⟨g, hj, hwant⟩
      by_cases hheld : ∃ b' ∈ agents, b' ∉ K ∧ Y (s b') = some g
      · -- `g` is held after the round by `b'`, who comes before `a`
        obtain ⟨b', hb', hb'K, hb'g⟩ := hheld
        have hsb' : s b' = j := hm.inj _ _ g hb'g hj
        have hb'a : b' ≠ a := fun e => by
          rw [e] at hb'g; exact absurd (hab g hb'g) (Nat.lt_irrefl _)
        have hBa : Before σ b' a := by
          by_cases hfix : s b' = b'
          · have haj : a ≠ j := fun e => by
              rw [e] at hwant; rw [mval_some hj] at hwant; omega
            have hjb : j = b' := hsb'.symm.trans hfix
            rw [hjb] at hwj haj
            exact before_of_wants hσ hag hgd ha' hb' haj (hY ▸ hwj)
          · exact hs2 b' hb' hb'K hfix a ha' (fun e => hb'a e.symm) (by rw [hsb']; exact hwj)
        exact havail b' ((hbef b' a hb'K haK).mpr hBa) hb'g
      · -- `g` is a released pick: (H)
        have hnone : ∀ c ∈ agents, c ∉ K → Y (s c) ≠ some g := fun c hc hcK h => hheld ⟨c, hc, hcK, h⟩
        obtain ⟨b, hb, hlt⟩ := hH a ha' haK j hjag g hj hnone hgU' hwj
        exact absurd (hab b hb) (Nat.lt_asymm hlt)
    · -- `g` is junk of `Y`: available at `a`'s turn
      have hpk : ∀ j, Y j ≠ some g := fun j hj => hpicked ⟨j, hj⟩
      obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods hnd hgd a (hσ.mem_iff.mpr ha') g hgG
        (fun c _ => by rw [← hY]; exact hpk c) hpos
      rw [← hY] at hy
      rw [mval_some hy] at hwant
      omega


/-- **SD-E(round), perfect starts**: if the picks form a perfect start, so does the outcome after the round. -/
theorem sdE_round_abs_perfect (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) {K : List A} {U : List G} {s : A → A}
    (hs1 : ∀ a ∈ agents, a ∉ K → s a ∈ agents ∧ (s a = a ∨ Wants v (sdPick v σ goods) a (s a)))
    (hs2 : ∀ a ∈ agents, a ∉ K → s a ≠ a → ∀ c ∈ agents, c ≠ a → Wants v (sdPick v σ goods) c (s a) →
      Before σ a c)
    (hs3 : ∀ a ∈ agents, ∀ c ∈ agents, a ∉ K → c ∉ K → s a = s c → a = c)
    (hs4 : ∀ a ∈ agents, a ∉ K → ∀ b, sdPick v σ goods (s a) = some b → b ∉ U)
    (hH : ∀ a ∈ agents, a ∉ K → ∀ j ∈ agents, ∀ g, sdPick v σ goods j = some g →
      (∀ c ∈ agents, c ∉ K → sdPick v σ goods (s c) ≠ some g) → g ∉ U → Wants v (sdPick v σ goods) a j →
      ∃ b, sdPick v σ goods (s a) = some b ∧ v a g < v a b)
    (hperf : PerfectStart v agents goods (sdPick v σ goods)) :
    PerfectStart v (agents.filter (fun a => decide (a ∉ K))) (goods.filter (fun g => decide (g ∉ U)))
      (sdPick v (σ.filter (fun a => decide (a ∉ K))) (goods.filter (fun g => decide (g ∉ U)))) := by
  intro i hi ⟨g, hg, hpos⟩
  have hi' : i ∈ agents ∧ i ∉ K := by simpa using hi
  have hiσ : i ∈ σ.filter (fun a => decide (a ∉ K)) := by
    rw [List.mem_filter, hσ.mem_iff]; simpa using hi'
  rw [sdE_round_abs hσ hag hgd hsv hs1 hs2 hs3 hs4 hH i hiσ]
  rcases (hs1 i hi'.1 hi'.2).2 with h | ⟨y, hy, -⟩
  · rw [h]; exact hperf i hi'.1 ⟨g, (List.mem_filter.mp hg).1, hpos⟩
  · rw [hy]; rfl

end abs

/-! ## Rounds of earliest-wanter prefixes -/

section sde
variable (v : A → G → Nat) (agents : List A) (σ : List A) (Y : A → Option G)

/-- **A prefix of the earliest-wanter chain** `ch = (x₀, …, x_t)`, `t ≥ 1`: distinct listed agents, each `x_l`
(`l ≥ 1`) a wanter of `Y_{x_{l−1}}` that comes before every other wanter in `σ`. Unlike `EChain`, the head may be
wanted (frozen). -/
structure EPrefix (ch : List A) : Prop where
  nodup : ch.Nodup
  mem : ∀ x ∈ ch, x ∈ agents
  tail_ne : ch.tail ≠ []
  wants : ∀ p ∈ ch.zip ch.tail, Wants v Y p.2 p.1
  earliest : ∀ p ∈ ch.zip ch.tail, ∀ a ∈ agents, a ≠ p.2 → Wants v Y a p.1 → Before σ p.2 a

end sde

omit [DecidableEq A] [DecidableEq G] in
theorem ePrefix_of_eChain {v : A → G → Nat} {agents σ : List A} {Y : A → Option G} {ch : List A}
    (h : EChain v agents σ Y ch) : EPrefix v agents σ Y ch :=
  ⟨h.nodup, h.mem, h.tail_ne, h.wants, h.earliest⟩

/-- After a round with chains `k :: rest k` (`k ∈ K`), agent `a` holds the pick of `roundSrc K rest a`: its predecessor
on the chain whose tail contains it, or its own. -/
def roundSrc (K : List A) (rest : A → List A) (a : A) : A :=
  match K.find? (fun k => decide (a ∈ rest k)) with
  | some k => src (k :: rest k) a
  | none => a

theorem roundSrc_of_mem {K : List A} {rest : A → List A}
    (hdisj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ∀ x ∈ k :: rest k, x ∉ k' :: rest k') {k : A} (hk : k ∈ K) {a : A}
    (ha : a ∈ rest k) : roundSrc K rest a = src (k :: rest k) a := by
  cases h : K.find? (fun k => decide (a ∈ rest k)) with
  | none => exact absurd (List.find?_eq_none.mp h k hk) (by simpa using ha)
  | some k' =>
    have hk' := List.mem_of_find?_eq_some h
    have ha' : a ∈ rest k' := by simpa using List.find?_some h
    have hkk : k' = k := Classical.byContradiction fun hne =>
      hdisj k' hk' k hk hne a (List.mem_cons_of_mem _ ha') (List.mem_cons_of_mem _ ha)
    simp only [roundSrc, h, hkk]

theorem roundSrc_of_not {K : List A} {rest : A → List A} {a : A} (ha : ∀ k ∈ K, a ∉ rest k) :
    roundSrc K rest a = a := by
  have h : K.find? (fun k => decide (a ∈ rest k)) = none :=
    List.find?_eq_none.mpr fun k hk => by simpa using ha k hk
  simp only [roundSrc, h]

section chains
variable {v : A → G → Nat} {agents : List A} {goods : List G} {σ : List A}

/-- **Lemma SD-E(round)** (K4.MULTI.SDER, `k4/oc1max_multi.md` §17; refereed CORRECT). Strict values; `K` settles
in one round, each `k ∈ K` along a prefix `k :: rest k` of its earliest-wanter chain, the chains vertex-disjoint;
`k` takes `T k`, whose only possible pick is its head's. Under **(H)** (an agent outside `K` that wants a released
head pick values its good after the round above it), the state after the round, without `K` and `⋃ T k`, is the
serial-dictatorship outcome of `σ` with `K` deleted. -/
theorem sdE_round (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) (hsv : StrictVals v agents goods)
    {K : List A} {rest : A → List A} (hch : ∀ k ∈ K, EPrefix v agents σ (sdPick v σ goods) (k :: rest k))
    (hdisj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ∀ x ∈ k :: rest k, x ∉ k' :: rest k') {T : A → List G}
    (hT : ∀ k ∈ K, ∀ g ∈ T k, (∀ x, sdPick v σ goods x ≠ some g) ∨
      sdPick v σ goods ((k :: rest k).getLast (List.cons_ne_nil _ _)) = some g)
    (hH : ∀ a ∈ agents, a ∉ K → ∀ k ∈ K, ∀ g,
      sdPick v σ goods ((k :: rest k).getLast (List.cons_ne_nil _ _)) = some g → (∀ k' ∈ K, g ∉ T k') →
      Wants v (sdPick v σ goods) a ((k :: rest k).getLast (List.cons_ne_nil _ _)) →
      ∃ b, sdPick v σ goods (roundSrc K rest a) = some b ∧ v a g < v a b) :
    ∀ a ∈ σ.filter (fun a => decide (a ∉ K)),
      sdPick v (σ.filter (fun a => decide (a ∉ K))) (goods.filter (fun g => decide (g ∉ K.flatMap T))) a =
        sdPick v σ goods (roundSrc K rest a) := by
  have hm := isMatching_sdPick (v := v) hσ hgd
  have hhead : ∀ k ∈ K, ∀ k' ∈ K, k ∈ k' :: rest k' → k = k' := fun k hk k' hk' h =>
    Classical.byContradiction fun hne => hdisj k hk k' hk' hne k List.mem_cons_self h
  have hk_rest : ∀ k ∈ K, k ∉ rest k := fun k hk => (List.nodup_cons.mp (hch k hk).nodup).1
  have hlast : ∀ k ∈ K, (k :: rest k).getLast (List.cons_ne_nil _ _) ∈ rest k := fun k hk => by
    have hne : rest k ≠ [] := (hch k hk).tail_ne
    rw [List.getLast_cons hne]; exact List.getLast_mem hne
  have hpair : ∀ k ∈ K, ∀ a ∈ rest k, (roundSrc K rest a, a) ∈ (k :: rest k).zip (rest k) := by
    intro k hk a ha
    obtain ⟨p, hp⟩ := (mem_tail_iff_pair (l := k :: rest k)).mp ha
    rw [roundSrc_of_mem hdisj hk ha, src_of_pair (hch k hk).nodup hp]; exact hp
  have hcase : ∀ a, (∃ k ∈ K, a ∈ rest k) ∨ (∀ k ∈ K, a ∉ rest k) := fun a => by
    by_cases h : ∃ k ∈ K, a ∈ rest k
    · exact Or.inl h
    · exact Or.inr fun k hk ha => h ⟨k, hk, ha⟩
  refine sdE_round_abs hσ hag hgd hsv (K := K) (U := K.flatMap T) (s := roundSrc K rest)
    (fun a ha haK => ?_) (fun a ha haK hne c hc hca hw => ?_) (fun a ha c hc haK hcK heq => ?_)
    (fun a ha haK b hb hbU => ?_) (fun a ha haK j hj g hjg hnone hgU hw => ?_)
  · -- (s1)
    rcases hcase a with ⟨k, hk, hak⟩ | hno
    · have hp := hpair k hk a hak
      exact ⟨(hch k hk).mem _ (List.of_mem_zip hp).1, Or.inr ((hch k hk).wants _ hp)⟩
    · rw [roundSrc_of_not hno]; exact ⟨ha, Or.inl rfl⟩
  · -- (s2)
    rcases hcase a with ⟨k, hk, hak⟩ | hno
    · exact (hch k hk).earliest _ (hpair k hk a hak) c hc hca hw
    · exact absurd (roundSrc_of_not hno) hne
  · -- (s3)
    rcases hcase a with ⟨k, hk, hak⟩ | hnoa <;> rcases hcase c with ⟨k', hk', hck⟩ | hnoc
    · have hpa := hpair k hk a hak
      have hpc := hpair k' hk' c hck
      rw [← heq] at hpc
      have hkk : k = k' := Classical.byContradiction fun hne =>
        hdisj k hk k' hk' hne _ (List.of_mem_zip hpa).1 (List.of_mem_zip hpc).1
      rw [← hkk] at hpc
      exact zip_tail_fst_unique (hch k hk).nodup hpa hpc
    · have hpa := hpair k hk a hak
      rw [heq, roundSrc_of_not hnoc] at hpa
      rcases List.mem_cons.mp (List.of_mem_zip hpa).1 with e | e
      · exact absurd (e ▸ hk) hcK
      · exact absurd e (hnoc k hk)
    · have hpc := hpair k' hk' c hck
      rw [← heq, roundSrc_of_not hnoa] at hpc
      rcases List.mem_cons.mp (List.of_mem_zip hpc).1 with e | e
      · exact absurd (e ▸ hk') haK
      · exact absurd e (hnoa k' hk')
    · rw [roundSrc_of_not hnoa, roundSrc_of_not hnoc] at heq; exact heq
  · -- (s4): a good held after the round is not taken
    obtain ⟨k', hk', hbT⟩ := List.mem_flatMap.mp hbU
    rcases hT k' hk' b hbT with hall | hz
    · exact hall _ hb
    · have hsz := hm.inj _ _ b hb hz
      rcases hcase a with ⟨k, hk, hak⟩ | hno
      · have hpa := hpair k hk a hak
        rw [hsz] at hpa
        have hkk : k = k' := Classical.byContradiction fun hne =>
          hdisj k hk k' hk' hne _ (List.of_mem_zip hpa).1 (List.mem_cons_of_mem _ (hlast k' hk'))
        rw [← hkk] at hpa
        exact getLast_no_succ (List.cons_ne_nil k (rest k)) (hch k hk).nodup a hpa
      · rw [roundSrc_of_not hno] at hsz
        exact hno k' hk' (hsz ▸ hlast k' hk')
  · -- (H): a pick nobody holds after the round is a released head pick
    have hgU' : ∀ k' ∈ K, g ∉ T k' := fun k' hk' h => hgU (List.mem_flatMap.mpr ⟨k', hk', h⟩)
    by_cases hon : ∃ k ∈ K, j ∈ k :: rest k
    · obtain ⟨k, hk, hjk⟩ := hon
      by_cases hjz : j = (k :: rest k).getLast (List.cons_ne_nil _ _)
      · rw [hjz] at hjg hw
        exact hH a ha haK k hk g hjg hgU' hw
      · obtain ⟨q, hq⟩ := exists_succ_of_ne_getLast (List.cons_ne_nil k (rest k)) hjk hjz
        have hqr : q ∈ rest k := (List.of_mem_zip hq).2
        have hqK : q ∉ K := fun hqK => by
          have := hhead q hqK k hk (List.mem_cons_of_mem _ hqr)
          exact hk_rest k hk (this ▸ hqr)
        have hsq : roundSrc K rest q = j := by
          rw [roundSrc_of_mem hdisj hk hqr, src_of_pair (hch k hk).nodup hq]
        exact absurd (by rw [hsq]; exact hjg) (hnone q ((hch k hk).mem q (List.mem_cons_of_mem _ hqr)) hqK)
    · have hjK : j ∉ K := fun hjK => hon ⟨j, hjK, List.mem_cons_self⟩
      have hno : ∀ k ∈ K, j ∉ rest k := fun k hk h => hon ⟨k, hk, List.mem_cons_of_mem _ h⟩
      exact absurd (by rw [roundSrc_of_not hno]; exact hjg) (hnone j hj hjK)


/-- **SD-E is the one-chain round.** For a single full earliest-wanter chain, (H) is vacuous (nobody wants the end's
pick), so `sdE_round` gives SD-E's conclusion, on `σ` without `k`. -/
theorem sdE_round_single (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hsv : StrictVals v agents goods) {k : A} {rest : List A}
    (hch : EChain v agents σ (sdPick v σ goods) (k :: rest)) {T : List G}
    (hT : ∀ g ∈ T, (∀ x, sdPick v σ goods x ≠ some g) ∨
      sdPick v σ goods ((k :: rest).getLast (List.cons_ne_nil _ _)) = some g) :
    ∀ a ∈ σ.filter (fun a => decide (a ∉ [k])),
      sdPick v (σ.filter (fun a => decide (a ∉ [k])))
          (goods.filter (fun g => decide (g ∉ [k].flatMap (fun _ => T)))) a =
        sdPick v σ goods (roundSrc [k] (fun _ => rest) a) := by
  refine sdE_round hσ hag hgd hsv (K := [k]) (rest := fun _ => rest) (T := fun _ => T)
    (fun k' hk' => by rw [List.mem_singleton.mp hk']; exact ePrefix_of_eChain hch)
    (fun k₁ h₁ k₂ h₂ hne => absurd ((List.mem_singleton.mp h₁).trans (List.mem_singleton.mp h₂).symm) hne)
    (fun k' hk' g hg => by rw [List.mem_singleton.mp hk']; exact hT g hg)
    (fun a ha _ k' hk' g _ _ hw => ?_)
  rw [List.mem_singleton.mp hk'] at hw
  exact absurd hw (hch.last _ (List.getLast_mem _) (getLast_no_succ _ hch.nodup) a ha)

end chains

end Round
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Round.before_filter
#print axioms EFX.Round.sdE_round_abs
#print axioms EFX.Round.sdE_round_abs_perfect
#print axioms EFX.Round.sdE_round
#print axioms EFX.Round.sdE_round_single
