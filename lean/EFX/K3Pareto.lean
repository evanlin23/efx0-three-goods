import EFX.C4min

/-!
# Theorem K3: the extremal principle at k = 3 (`k4/c4x.md` §3; ledger K4.C4X.K3.LEAN)

The building blocks of Theorem K3 of `k4/c4x.md` (PR #36, branch `proof/k4-c4x`, read at commit efef349) over the space 𝒫 of
`EFX/C4min.lean`: Pareto-maximality, Lemmas U, C, R and E, the moves they use (validity and strict Pareto
improvement), and the owner criterion (Lemma O).

**Definitions.**
- `Dominates base' base`: `P′` Pareto-dominates `P` (`v_i(B′_i) ≥ v_i(B_i)` for every listed agent, one strict);
  `ParetoMax`: a pre-allocation of 𝒫 that no pre-allocation of 𝒫 dominates.
- `Edge y z`: the need digraph's edge `y → z` (`B_y` is one good `g`, and `g ∈ N_z`); `NeedChain c`: a need chain, a
  list `x₀, …, x_s` of distinct listed agents with `s ≥ 1`, consecutive agents joined by edges (so `x₀, …, x_{s−1}` are
  frozen), and `x_s` free (a terminal: it needs the previous good).
- `transfer T extra base`: the move in which every giver `p` of `T` (pairs `(p, r)`) hands its base to `r` (another
  agent, or the junk when `r = none`), and every junk good `g` with `extra g = some a` goes to `a`. Rotations along
  need chains and cycles, LB⁺'s rotation (Lemma R) and the cycle move of Theorem K3 are instances.

**Results.**
- `inP_of_gain`: a base map whose bases have at most two goods, in which no listed agent loses, whose junk and
  two-good bases avoid the old `NA`, is in 𝒫 (the needs only shrink: `vbNeeds_mono`).
- `lemmaU`: (any k) at a Pareto-maximum a free agent with at most one base good values no junk good.
- `transfer_inP_dominates`, `transfer_move`, `cycle_move`, `path_move`: **the validity of the rotations and the strict
  Pareto improvement**, from any `P ∈ 𝒫` (`transfer_inP_dominates`; the others are its contrapositives at a
  Pareto-maximum). If
  every mover's new base (what it receives plus its extra junk goods) has at most two goods, all relevant to it, is worth
  more to it than its base, and avoids `NA` when it has two goods, and every base released to the junk avoids `NA`,
  then the result is in 𝒫 and dominates `P`. `cycle_move`: the bases pass around a cycle `L[k] → L[k+1 mod n]` (Lemma C's
  cycle rotation, Lemma R's rotation when `B_τ` is a good of `x`, the cycle move of Theorem K3); `path_move`: along a path,
  the last base released (Lemma R's rotation otherwise).
- `no_edge_cycle` (Lemma C, first half; any k): at a Pareto-maximum the need digraph has no cycle; `exists_needChain`
  (second half): every frozen agent has a need chain (to a terminal, `NeedChain.terminal`).
- `threat_shape` (facts (i)–(iii) of §3 in one statement; `|R_x| = 3` only): a set of goods avoiding `B_x` and `x`'s needs
  that threatens `x` holding its base alone forces `B_x = {a}` and both other goods of `x` into the set;
  `no_needs_two` (fact (i)): a two-good base has no needs, so a terminal holds at most one good (`Terminal.le_one`).
- `lemmaR` (k = 3): at a Pareto-maximum, if `x` holds one good `a` and heads a need chain ending at `τ`, not both other
  goods of `x` lie in `J ∪ B_τ`.
- `lemmaE` (k = 3): an agent exposed w.r.t. a terminal `t` is frozen with one good `a`, `B_t = {y}` with `y` a good of
  `x`, the third good `z` of `x` is junk, and no need chain from `x` ends at `t`.

**Choices where the prose leaves room.**
1. The k = 3 setting is `Three`: exactly three relevant goods per listed agent and strict balance
   (`2 v_i(g) < v_i(M)`). The text also assumes strict types; none of the proofs here uses them.
2. "Top-holder" is not defined separately: Lemma R assumes `B_x = {a}` for some good `a` (the rotation only needs
   `v_x(a) < v_x(l₁) + v_x(l₂)`, which is balance), and Lemma E derives `B_x = {a}`; that `a` is `x`'s top good (the
   text's "top-holder") follows because an exposed agent needs nothing (`EFX.C4min.exposed_no_needs`,
   `EFX.C4min.exposed_top` in `EFX/K3Theorem.lean`).
3. `E_t` uses `W_t` itself as the threatening set (`Exposed`); a subset `X ⊆ W_t` that threatens `x` exposes it
   (`exposed_of_sub`).
4. A need chain is a list of agents with its edges; its end is free, so it is a terminal (it needs the previous good).
5. The move of Lemma C's cycle, Lemma R's rotation and the cycle of Theorem K3 is `transfer`: movers hand their whole
   base on (to the next mover or to the junk), and receive junk goods through `extra`.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Pareto-maximality -/

/-- `P′` Pareto-dominates `P`: no listed agent's base is worth less to it, and one is worth more. -/
def Dominates (v : A → G → Nat) (agents : List A) (goods : List G) (base' base : G → Option A) : Prop :=
  (∀ i ∈ agents, value v i (baseOf goods base i) ≤ value v i (baseOf goods base' i)) ∧
    ∃ i ∈ agents, value v i (baseOf goods base i) < value v i (baseOf goods base' i)

/-- A Pareto-maximal pre-allocation of 𝒫: no pre-allocation of 𝒫 dominates it. -/
def ParetoMax (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  InP v agents goods base ∧ ∀ base', InP v agents goods base' → ¬ Dominates v agents goods base' base

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}

/-! ## Base maps: small lemmas -/

omit [DecidableEq G] in
theorem baseOf_congr {base' : G → Option A} {i : A} (h : ∀ g ∈ goods, base' g = some i ↔ base g = some i) :
    baseOf goods base' i = baseOf goods base i := by
  unfold baseOf
  apply List.filter_congr
  intro g hg
  simp [h g hg]

omit [DecidableEq G] in
/-- A base is determined, up to order, by its members. -/
theorem baseOf_perm (hgd : goods.Nodup) {i : A} {L : List G} (hL : L.Nodup)
    (h : ∀ g, g ∈ L ↔ g ∈ goods ∧ base g = some i) : (baseOf goods base i).Perm L := by
  apply (List.perm_ext_iff_of_nodup (hgd.sublist List.filter_sublist) hL).mpr
  intro g
  show g ∈ baseOf goods base i ↔ g ∈ L
  rw [mem_baseOf, h g]

omit [DecidableEq A] [DecidableEq G] in
theorem value_perm {i : A} {S T : List G} (h : S.Perm T) : value v i S = value v i T := by
  unfold value; exact (h.map (v i)).sum_nat

omit [DecidableEq A] [DecidableEq G] in
theorem value_append (i : A) (S T : List G) : value v i (S ++ T) = value v i S + value v i T := by
  unfold value; simp

omit [DecidableEq G] in
/-- A base of one good. -/
theorem baseOf_single (hgd : goods.Nodup) {i : A} {y : G} (hy : y ∈ goods)
    (h : ∀ g ∈ goods, base g = some i ↔ g = y) : baseOf goods base i = [y] := by
  have := baseOf_perm (base := base) hgd (L := [y]) (by simp)
    (fun g => ⟨fun hg => by rw [List.mem_singleton] at hg; subst hg; exact ⟨hy, (h g hy).mpr rfl⟩,
      fun hgb => by rw [List.mem_singleton]; exact (h g hgb.1).mp hgb.2⟩)
  exact List.perm_singleton.mp this

omit [DecidableEq G] in
theorem mem_single_base {i : A} {y g : G} (hB : baseOf goods base i = [y]) :
    g ∈ goods ∧ base g = some i ↔ g = y := by
  rw [← mem_baseOf, hB, List.mem_singleton]

omit [DecidableEq G] in
/-- The goods of a base of at most one good. -/
theorem base_le_one {i : A} (h : (baseOf goods base i).length ≤ 1) :
    baseOf goods base i = [] ∨ ∃ y, baseOf goods base i = [y] := by
  match hB : baseOf goods base i, h with
  | [], _ => exact Or.inl rfl
  | [y], _ => exact Or.inr ⟨y, rfl⟩
  | _ :: _ :: _, h => simp at h

/-! ## Moves that keep 𝒫 -/

omit [DecidableEq G] in
/-- **Needs only shrink when nobody loses**: if `v_i(B′_i) ≥ v_i(B_i)`, then `N′_i ⊆ N_i` (a good of `B_i` is worth at
most `v_i(B_i)`). -/
theorem vbNeeds_mono {base' : G → Option A} {i : A}
    (hi : value v i (baseOf goods base i) ≤ value v i (baseOf goods base' i)) {g : G}
    (h : vbNeeds v goods base' i g) : vbNeeds v goods base i g := by
  obtain ⟨hg, -, hlt⟩ := h
  refine ⟨hg, fun hb => ?_, by omega⟩
  have := le_value_of_mem v i (mem_baseOf.mpr ⟨hg, hb⟩ : g ∈ baseOf goods base i)
  omega

omit [DecidableEq G] in
theorem NA_mono {base' : G → Option A}
    (hgain : ∀ i ∈ agents, value v i (baseOf goods base i) ≤ value v i (baseOf goods base' i)) {g : G}
    (h : NA agents (vbNeeds v goods base') g) : NA agents (vbNeeds v goods base) g := by
  obtain ⟨i, hi, hN⟩ := h
  exact ⟨i, hi, vbNeeds_mono (hgain i hi) hN⟩

omit [DecidableEq G] in
/-- **A move that keeps 𝒫.** A base map whose base goods go to listed agents that value them, whose bases have at most
two goods, in which no listed agent loses, and whose junk goods and goods of two-good bases are not in the old `NA`, is
a pre-allocation of 𝒫. -/
theorem inP_of_gain {base' : G → Option A}
    (hmem : ∀ g ∈ goods, ∀ i, base' g = some i → i ∈ agents)
    (hrel : ∀ g ∈ goods, ∀ i, base' g = some i → 0 < v i g)
    (htwo : ∀ i, (baseOf goods base' i).length ≤ 2)
    (hgain : ∀ i ∈ agents, value v i (baseOf goods base i) ≤ value v i (baseOf goods base' i))
    (hJ : ∀ g ∈ goods, base' g = none → ¬ NA agents (vbNeeds v goods base) g)
    (h2 : ∀ i, 2 ≤ (baseOf goods base' i).length → ∀ g ∈ baseOf goods base' i, ¬ NA agents (vbNeeds v goods base) g) :
    InP v agents goods base' :=
  ⟨hmem, hrel, htwo, ⟨fun g hg hna => hJ g (mem_junk.mp hg).1 (mem_junk.mp hg).2 (NA_mono hgain hna),
    fun i hi g hg hna => h2 i hi g hg (NA_mono hgain hna)⟩⟩

omit [DecidableEq G] in
/-- A frozen agent's base good is in `NA`; a free agent's one-good base is not. -/
theorem not_NA_of_free {j : A} {y : G} (hB : baseOf goods base j = [y])
    (hF : ¬ Frozen agents goods base (vbNeeds v goods base) j) : ¬ NA agents (vbNeeds v goods base) y :=
  fun h => hF ⟨y, hB, h⟩

/-! ## Lemma U (no upgrade) -/

/-- **Lemma U** (`k4/c4x.md` §3; any k). At a Pareto-maximum, a free listed agent with at most one base good values no
junk good. -/
theorem lemmaU (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) {x : A} (hx : x ∈ agents)
    (hF : ¬ Frozen agents goods base (vbNeeds v goods base) x) (h1 : (baseOf goods base x).length ≤ 1) :
    ∀ g ∈ LB4.junk goods base, v x g = 0 := by
  intro g hgJ
  obtain ⟨hg, hgb⟩ := mem_junk.mp hgJ
  refine Nat.eq_zero_of_not_pos fun hpos => ?_
  rcases base_le_one h1 with hB | ⟨y, hB⟩
  · -- an empty base needs every relevant good, and junk is not needed (V1)
    exact hP.1.valid.v1 g hgJ ⟨x, hx, hg, by rw [hgb]; simp, by rw [hB]; simpa using hpos⟩
  · -- `x` takes `g` into its base: a pre-allocation of 𝒫 that dominates
    have hyg : y ≠ g := fun e => by
      have := (mem_single_base hB).mpr rfl; rw [e, hgb] at this; simp at this
    have hy : y ∈ goods := ((mem_single_base hB).mpr rfl).1
    let base' : G → Option A := fun h => if h = g then some x else base h
    have hother : ∀ i, i ≠ x → baseOf goods base' i = baseOf goods base i := fun i hix =>
      baseOf_congr fun h _ => by
        by_cases hh : h = g
        · subst hh; simp [base', hgb, Ne.symm hix]
        · simp [base', hh]
    have hBx : (baseOf goods base' x).Perm [y, g] := baseOf_perm hgd (by simp [hyg]) fun h => by
      by_cases hh : h = g
      · subst hh; simp [base', hg]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, base', hh, ↓reduceIte]
        exact ⟨fun e => e ▸ (mem_single_base hB).mpr rfl, fun h' => (mem_single_base hB).mp h'⟩
    have hvx : value v x (baseOf goods base' x) = v x y + v x g := by
      rw [value_perm hBx]; simp
    have hvB : value v x (baseOf goods base x) = v x y := by rw [hB]; simp
    have hgain : ∀ i ∈ agents, value v i (baseOf goods base i) ≤ value v i (baseOf goods base' i) := by
      intro i _
      by_cases hix : i = x
      · subst hix; omega
      · rw [hother i hix]; exact Nat.le_refl _
    have hIn : InP v agents goods base' := by
      refine inP_of_gain (fun h hh i hb => ?_) (fun h hh i hb => ?_) (fun i => ?_) hgain
        (fun h hh hb => ?_) (fun i h2 h hh => ?_)
      · by_cases e : h = g
        · simp [base', e] at hb; exact hb ▸ hx
        · simp [base', e] at hb; exact hP.1.mem h hh i hb
      · by_cases e : h = g
        · simp [base', e] at hb; subst hb; subst e; exact hpos
        · simp [base', e] at hb; exact hP.1.rel h hh i hb
      · by_cases hix : i = x
        · subst hix; rw [hBx.length_eq]; simp
        · rw [hother i hix]; exact hP.1.two i
      · have e : h ≠ g := fun e => by simp [base', e] at hb
        simp only [base', e, ↓reduceIte] at hb
        exact hP.1.valid.v1 h (mem_junk.mpr ⟨hh, hb⟩)
      · by_cases hix : i = x
        · subst hix
          rcases List.mem_cons.mp (hBx.mem_iff.mp hh) with e | e
          · exact e ▸ not_NA_of_free hB hF
          · simp at e; subst e; exact hP.1.valid.v1 h hgJ
        · rw [hother i hix] at h2 hh; exact hP.1.valid.v2 i h2 h hh
    exact hP.2 base' hIn ⟨hgain, x, hx, by omega⟩


/-! ## The transfer move -/

/-- **The transfer move**: every mover `p ∈ L` hands its base to `dstF p` (to the junk if `dstF p = none`), every junk
good `g` with `extra g = some a` goes to `a`, and every other good stays. -/
def transfer (L : List A) (dstF : A → Option A) (extra : G → Option A) (base : G → Option A) (g : G) : Option A :=
  match base g with
  | some p => if p ∈ L then dstF p else some p
  | none => extra g

/-- The junk goods that `extra` gives to `a`. -/
def extrasOf (goods : List G) (base : G → Option A) (extra : G → Option A) (a : A) : List G :=
  (LB4.junk goods base).filter (fun g => extra g = some a)

/-- What `a` receives from the movers: the base of the first mover whose base goes to `a`, if any. -/
def recvOf (goods : List G) (base : G → Option A) (L : List A) (dstF : A → Option A) (a : A) : List G :=
  match L.find? (fun p => dstF p = some a) with
  | some p => baseOf goods base p
  | none => []

/-- The conditions on a mover `a` whose new base is `S`: at most two goods, all relevant to `a`, worth more to `a` than
its base, and none in `NA` if there are two. -/
structure GoodNew (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (a : A) (S : List G) :
    Prop where
  two : S.length ≤ 2
  rel : ∀ g ∈ S, 0 < v a g
  gain : value v a (baseOf goods base a) < value v a S
  na : 2 ≤ S.length → ∀ g ∈ S, ¬ NA agents (vbNeeds v goods base) g

omit [DecidableEq G] in
theorem recvOf_eq {L : List A} {dstF : A → Option A} {a p : A} (hp : p ∈ L) (hpa : dstF p = some a)
    (hinj : ∀ q ∈ L, dstF q = some a → q = p) : recvOf goods base L dstF a = baseOf goods base p := by
  unfold recvOf
  cases hf : L.find? (fun p => dstF p = some a) with
  | none => exact absurd (List.find?_eq_none.mp hf p hp) (by simp [hpa])
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have := List.find?_some hf
    simp only [decide_eq_true_eq] at this
    rw [hinj q hq this]

omit [DecidableEq G] in
theorem recvOf_none {L : List A} {dstF : A → Option A} {a : A} (h : ∀ q ∈ L, dstF q ≠ some a) :
    recvOf goods base L dstF a = [] := by
  unfold recvOf
  rw [List.find?_eq_none.mpr fun q hq => by simpa using h q hq]

section transfer
variable {L : List A} {dstF : A → Option A} {extra : G → Option A}

omit [DecidableEq G] in
theorem mem_baseOf_transfer {a : A} {g : G} :
    g ∈ baseOf goods (transfer L dstF extra base) a ↔ g ∈ goods ∧
      ((∃ p ∈ L, base g = some p ∧ dstF p = some a) ∨ (a ∉ L ∧ base g = some a) ∨
        (base g = none ∧ extra g = some a)) := by
  rw [mem_baseOf]
  apply and_congr_right
  intro _
  unfold transfer
  cases hb : base g with
  | none => simp
  | some p =>
    simp only [Option.some.injEq, reduceCtorEq, false_and, or_false]
    by_cases hp : p ∈ L
    · simp only [hp, ↓reduceIte]
      constructor
      · intro h; exact Or.inl ⟨p, hp, rfl, h⟩
      · rintro (⟨q, _, rfl, h⟩ | ⟨ha, rfl⟩)
        · exact h
        · exact absurd hp ha
    · simp only [hp, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; exact Or.inr ⟨hp, rfl⟩
      · rintro (⟨q, hq, rfl, _⟩ | ⟨_, rfl⟩)
        · exact absurd hq hp
        · rfl

omit [DecidableEq G] in
/-- **The transfer move stays in 𝒫 and dominates** (any `P ∈ 𝒫`, not only a Pareto-maximum): if the movers `L`
(listed, not empty) hand their bases to distinct movers or to the junk, the extras are junk goods given to movers, every
released base avoids `NA`, and every mover's new base (what it receives plus its extras) satisfies `GoodNew`, the result
is a pre-allocation of 𝒫 that Pareto-dominates `P`. -/
theorem transfer_inP_dominates (hgd : goods.Nodup) (hP : InP v agents goods base) (hne : L ≠ [])
    (hLa : ∀ a ∈ L, a ∈ agents)
    (hinj : ∀ p ∈ L, ∀ q ∈ L, ∀ a, dstF p = some a → dstF q = some a → p = q)
    (hdstL : ∀ p ∈ L, ∀ a, dstF p = some a → a ∈ L)
    (hex : ∀ g ∈ goods, ∀ a, extra g = some a → base g = none ∧ a ∈ L)
    (hrelease : ∀ p ∈ L, dstF p = none → ∀ g ∈ baseOf goods base p, ¬ NA agents (vbNeeds v goods base) g)
    (hnew : ∀ a ∈ L, GoodNew v agents goods base a (recvOf goods base L dstF a ++ extrasOf goods base extra a)) :
    InP v agents goods (transfer L dstF extra base) ∧
      Dominates v agents goods (transfer L dstF extra base) base := by
  let base' := transfer L dstF extra base
  -- the new bases
  have hstay : ∀ a, a ∉ L → baseOf goods base' a = baseOf goods base a := fun a ha =>
    baseOf_congr fun g hg => by
      have := (mem_baseOf_transfer (goods := goods) (L := L) (dstF := dstF) (extra := extra) (base := base) (a := a)
        (g := g))
      rw [mem_baseOf] at this
      constructor
      · intro h
        rcases (this.mp ⟨hg, h⟩).2 with ⟨p, hp, -, hpa⟩ | ⟨-, hb⟩ | ⟨-, hx⟩
        · exact absurd (hdstL p hp a hpa) ha
        · exact hb
        · exact absurd (hex g hg a hx).2 ha
      · intro h; exact (this.mpr ⟨hg, Or.inr (Or.inl ⟨ha, h⟩)⟩).2
  have hmove : ∀ a ∈ L, (baseOf goods base' a).Perm (recvOf goods base L dstF a ++ extrasOf goods base extra a) := by
    intro a ha
    have hnd : (recvOf goods base L dstF a ++ extrasOf goods base extra a).Nodup := by
      unfold recvOf extrasOf
      apply List.nodup_append.mpr
      refine ⟨?_, (hgd.sublist List.filter_sublist).sublist List.filter_sublist, fun x hx y hy e => ?_⟩
      · split
        · exact hgd.sublist List.filter_sublist
        · exact List.nodup_nil
      · subst e
        have hy' := (mem_junk.mp (List.mem_filter.mp hy).1).2
        split at hx
        · rw [(mem_baseOf.mp hx).2] at hy'; cases hy'
        · simp at hx
    apply baseOf_perm hgd hnd
    intro g
    rw [List.mem_append]
    constructor
    · rintro (hr | hx)
      · unfold recvOf at hr
        split at hr
        · rename_i p hf
          have hp := List.mem_of_find?_eq_some hf
          have hpa : dstF p = some a := by simpa using List.find?_some hf
          obtain ⟨hg, hb⟩ := mem_baseOf.mp hr
          exact mem_baseOf.mp (mem_baseOf_transfer.mpr ⟨hg, Or.inl ⟨p, hp, hb, hpa⟩⟩)
        · simp at hr
      · obtain ⟨hJ, hxa⟩ := List.mem_filter.mp hx
        obtain ⟨hg, hb⟩ := mem_junk.mp hJ
        exact mem_baseOf.mp (mem_baseOf_transfer.mpr ⟨hg, Or.inr (Or.inr ⟨hb, by simpa using hxa⟩)⟩)
    · intro hga
      obtain ⟨hg, h⟩ := mem_baseOf_transfer.mp (mem_baseOf.mpr hga)
      rcases h with ⟨p, hp, hb, hpa⟩ | ⟨ha', -⟩ | ⟨hb, hx⟩
      · left
        rw [recvOf_eq hp hpa fun q hq hqa => hinj q hq p hp a hqa hpa]
        exact mem_baseOf.mpr ⟨hg, hb⟩
      · exact absurd ha ha'
      · right; exact List.mem_filter.mpr ⟨mem_junk.mpr ⟨hg, hb⟩, by simp [hx]⟩
  have hgain : ∀ i ∈ agents, value v i (baseOf goods base i) ≤ value v i (baseOf goods base' i) := by
    intro i _
    by_cases hi : i ∈ L
    · rw [value_perm (hmove i hi)]; exact Nat.le_of_lt (hnew i hi).gain
    · rw [hstay i hi]; exact Nat.le_refl _
  have hIn : InP v agents goods base' := by
    refine inP_of_gain (fun g hg i hb => ?_) (fun g hg i hb => ?_) (fun i => ?_) hgain (fun g hg hb => ?_)
      (fun i h2 g hgi => ?_)
    · have := mem_baseOf_transfer.mp (mem_baseOf.mpr ⟨hg, hb⟩)
      rcases this.2 with ⟨p, hp, -, hpa⟩ | ⟨-, hb'⟩ | ⟨-, hx⟩
      · exact hLa i (hdstL p hp i hpa)
      · exact hP.mem g hg i hb'
      · exact hLa i (hex g hg i hx).2
    · have hgi : g ∈ baseOf goods base' i := mem_baseOf.mpr ⟨hg, hb⟩
      by_cases hi : i ∈ L
      · exact (hnew i hi).rel g ((hmove i hi).mem_iff.mp hgi)
      · rw [hstay i hi] at hgi; exact hP.rel g hg i (mem_baseOf.mp hgi).2
    · by_cases hi : i ∈ L
      · rw [(hmove i hi).length_eq]; exact (hnew i hi).two
      · rw [hstay i hi]; exact hP.two i
    · simp only [base', transfer] at hb
      cases hbg : base g with
      | none =>
        rw [hbg] at hb
        exact hP.valid.v1 g (mem_junk.mpr ⟨hg, hbg⟩)
      | some p =>
        rw [hbg] at hb
        by_cases hp : p ∈ L
        · simp only [hp, ↓reduceIte] at hb
          exact hrelease p hp hb g (mem_baseOf.mpr ⟨hg, hbg⟩)
        · simp [hp] at hb
    · by_cases hi : i ∈ L
      · rw [(hmove i hi).length_eq] at h2
        exact (hnew i hi).na h2 g ((hmove i hi).mem_iff.mp hgi)
      · rw [hstay i hi] at h2 hgi; exact hP.valid.v2 i h2 g hgi
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hne
  refine ⟨hIn, hgain, a, hLa a ha, ?_⟩
  rw [value_perm (hmove a ha)]; exact (hnew a ha).gain

omit [DecidableEq G] in
/-- **The transfer move dominates, so it does not exist at a Pareto-maximum** (`transfer_inP_dominates`). -/
theorem transfer_move (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hne : L ≠ [])
    (hLa : ∀ a ∈ L, a ∈ agents)
    (hinj : ∀ p ∈ L, ∀ q ∈ L, ∀ a, dstF p = some a → dstF q = some a → p = q)
    (hdstL : ∀ p ∈ L, ∀ a, dstF p = some a → a ∈ L)
    (hex : ∀ g ∈ goods, ∀ a, extra g = some a → base g = none ∧ a ∈ L)
    (hrelease : ∀ p ∈ L, dstF p = none → ∀ g ∈ baseOf goods base p, ¬ NA agents (vbNeeds v goods base) g)
    (hnew : ∀ a ∈ L, GoodNew v agents goods base a (recvOf goods base L dstF a ++ extrasOf goods base extra a)) :
    False :=
  let h := transfer_inP_dominates hgd hP.1 hne hLa hinj hdstL hex hrelease hnew
  hP.2 _ h.1 h.2

end transfer

/-! ## Successors in lists -/

/-- `i < n`, `j < n` and `(i + 1) % n = (j + 1) % n` give `i = j`. -/
theorem succ_mod_inj {n i j : Nat} (hi : i < n) (hj : j < n) (h : (i + 1) % n = (j + 1) % n) : i = j := by
  rcases Nat.lt_or_ge (i + 1) n with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show j + 1 = n by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show i + 1 = n by omega, Nat.mod_self] at h; omega
  · omega

/-- The cyclic successor in `L`: the next element, the first after the last (`none` off `L`). -/
def cycNext (L : List A) (a : A) : Option A := L[(L.idxOf a + 1) % L.length]?

/-- The successor on the path `L`: the next element, `none` for the last (and off `L`). -/
def pathNext (L : List A) (a : A) : Option A := L[L.idxOf a + 1]?

section succ
variable {L : List A}

theorem cycNext_getElem (hL : L.Nodup) {k : Nat} (hk : k < L.length) :
    cycNext L L[k] = some (L[(k + 1) % L.length]'(Nat.mod_lt _ (by omega))) := by
  unfold cycNext; rw [List.Nodup.idxOf_getElem hL k hk]; simp

theorem pathNext_getElem (hL : L.Nodup) {k : Nat} (hk : k + 1 < L.length) :
    pathNext L L[k] = some L[k + 1] := by
  unfold pathNext; rw [List.Nodup.idxOf_getElem hL k (by omega)]; simp [hk]

theorem pathNext_last (hL : L.Nodup) {k : Nat} (hk : k < L.length) (hl : k + 1 = L.length) :
    pathNext L L[k] = none := by
  unfold pathNext; rw [List.Nodup.idxOf_getElem hL k hk]; simp [hl]

theorem cycNext_mem {a b : A} (h : cycNext L a = some b) : b ∈ L := by
  unfold cycNext at h; exact List.mem_of_getElem? h

theorem pathNext_mem {a b : A} (h : pathNext L a = some b) : b ∈ L := by
  unfold pathNext at h; exact List.mem_of_getElem? h

theorem cycNext_inj (hL : L.Nodup) {p q a : A} (hp : p ∈ L) (hq : q ∈ L) (hpa : cycNext L p = some a)
    (hqa : cycNext L q = some a) : p = q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  rw [cycNext_getElem hL hi] at hpa
  rw [cycNext_getElem hL hj, ← hpa, Option.some.injEq, hL.getElem_inj] at hqa
  have := succ_mod_inj hi hj hqa.symm
  subst this; rfl

theorem pathNext_inj (hL : L.Nodup) {p q a : A} (hp : p ∈ L) (hq : q ∈ L) (hpa : pathNext L p = some a)
    (hqa : pathNext L q = some a) : p = q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  rcases Nat.lt_or_ge (i + 1) L.length with h1 | h1
  · rcases Nat.lt_or_ge (j + 1) L.length with h2 | h2
    · rw [pathNext_getElem hL h1] at hpa
      rw [pathNext_getElem hL h2, ← hpa, Option.some.injEq, hL.getElem_inj] at hqa
      have : i = j := by omega
      subst this; rfl
    · rw [pathNext_last hL hj (by omega)] at hqa; cases hqa
  · rw [pathNext_last hL hi (by omega)] at hpa; cases hpa

/-- The first element of a path is nobody's successor. -/
theorem pathNext_ne_head (hL : L.Nodup) (h0 : 0 < L.length) {p : A} (hp : p ∈ L) : pathNext L p ≠ some L[0] := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  intro h
  rcases Nat.lt_or_ge (i + 1) L.length with h1 | h1
  · rw [pathNext_getElem hL h1, Option.some.injEq, hL.getElem_inj] at h; omega
  · rw [pathNext_last hL hi (by omega)] at h; cases h

end succ

omit [DecidableEq G] in
/-- **A cycle move** (the transfer along a cycle): the movers `L[0], …, L[n−1]` pass their bases cyclically, `L[k]`'s to
`L[k+1 mod n]`, and receive extras from the junk. If every new base satisfies `GoodNew`, this contradicts Pareto-
maximality. -/
theorem cycle_move (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) {L : List A} (hL : L.Nodup)
    (hne : L ≠ []) (hLa : ∀ a ∈ L, a ∈ agents) {extra : G → Option A}
    (hex : ∀ g ∈ goods, ∀ a, extra g = some a → base g = none ∧ a ∈ L)
    (hnew : ∀ k (hk : k < L.length), GoodNew v agents goods base (L[(k + 1) % L.length]'(Nat.mod_lt _ (by omega)))
      (baseOf goods base L[k] ++ extrasOf goods base extra (L[(k + 1) % L.length]'(Nat.mod_lt _ (by omega))))) :
    False := by
  refine transfer_move (dstF := cycNext L) hgd hP hne hLa (fun p hp q hq a => cycNext_inj hL hp hq)
    (fun _ _ _ h => cycNext_mem h) hex (fun p hp h => ?_) (fun a ha => ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    rw [cycNext_getElem hL hi] at h; cases h
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    -- the sender of `L[j]` is `L[j − 1]` (cyclically)
    have hn : 0 < L.length := by omega
    obtain ⟨k, hk, hkj⟩ : ∃ k, ∃ hk : k < L.length, (k + 1) % L.length = j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · exact ⟨L.length - 1, by omega, by rw [show L.length - 1 + 1 = L.length by omega, Nat.mod_self, h0]⟩
      · exact ⟨j - 1, by omega, by rw [show j - 1 + 1 = j by omega, Nat.mod_eq_of_lt hj]⟩
    subst hkj
    have hs := cycNext_getElem hL hk
    rw [recvOf_eq (List.getElem_mem hk) hs fun q hq hqa => cycNext_inj hL hq (List.getElem_mem hk) hqa hs]
    exact hnew k hk

omit [DecidableEq G] in
/-- **A path move** (the transfer along a path, releasing the last base): `L[k]`'s base goes to `L[k+1]`, the last
agent's base goes to the junk, and the movers receive extras from the junk. If the released base avoids `NA` and
every new base satisfies `GoodNew`, this contradicts Pareto-maximality. -/
theorem path_move (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) {L : List A} (hL : L.Nodup)
    (h0 : 0 < L.length) (hLa : ∀ a ∈ L, a ∈ agents) {extra : G → Option A}
    (hex : ∀ g ∈ goods, ∀ a, extra g = some a → base g = none ∧ a ∈ L)
    (hrel : ∀ g ∈ baseOf goods base (L[L.length - 1]'(by omega)), ¬ NA agents (vbNeeds v goods base) g)
    (hhead : GoodNew v agents goods base L[0] (extrasOf goods base extra L[0]))
    (hnew : ∀ k (hk : k + 1 < L.length), GoodNew v agents goods base L[k + 1]
      (baseOf goods base L[k] ++ extrasOf goods base extra L[k + 1])) : False := by
  refine transfer_move (dstF := pathNext L) hgd hP (List.ne_nil_of_length_pos h0) hLa
    (fun p hp q hq a => pathNext_inj hL hp hq) (fun _ _ _ h => pathNext_mem h) hex (fun p hp h => ?_)
    (fun a ha => ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    rcases Nat.lt_or_ge (i + 1) L.length with h1 | h1
    · rw [pathNext_getElem hL h1] at h; cases h
    · have : i = L.length - 1 := by omega
      subst this; exact hrel
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [recvOf_none fun q hq => pathNext_ne_head hL h0 hq, List.nil_append]
      exact hhead
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hs := pathNext_getElem hL hj
      rw [recvOf_eq (List.getElem_mem (by omega)) hs fun q hq hqa => pathNext_inj hL hq (List.getElem_mem (by omega)) hqa hs]
      exact hnew k hj


/-! ## Lemma C (need chains) -/

/-- The need digraph's edge `y → z` (`k4/c4x.md` §3): `B_y` is one good `g`, and `g ∈ N_z`. -/
def Edge (v : A → G → Nat) (goods : List G) (base : G → Option A) (y z : A) : Prop :=
  ∃ g, baseOf goods base y = [g] ∧ vbNeeds v goods base z g

/-- A need chain `x₀ → x₁ → … → x_s` (`s ≥ 1`): distinct listed agents joined by edges, the last one free (a
terminal: it needs the good of `x_{s−1}`). The agents `x₀, …, x_{s−1}` are frozen (`NeedChain.frozen`). -/
structure NeedChain (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (c : List A) :
    Prop where
  nodup : c.Nodup
  mem : ∀ a ∈ c, a ∈ agents
  two : 2 ≤ c.length
  edge : ∀ k (hk : k + 1 < c.length), Edge v goods base c[k] c[k + 1]
  free : ¬ Frozen agents goods base (vbNeeds v goods base) (c[c.length - 1]'(by omega))

/-- A need chain from `x` to `t`. -/
def ChainTo (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (x t : A) : Prop :=
  ∃ c, NeedChain v agents goods base c ∧ c.head? = some x ∧ c.getLast? = some t

/-- A terminal: a free listed agent with a need. -/
def Terminal (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (t : A) : Prop :=
  t ∈ agents ∧ ¬ Frozen agents goods base (vbNeeds v goods base) t ∧ ∃ g, vbNeeds v goods base t g

omit [DecidableEq G] in
/-- The tail of an edge is frozen when its head is listed. -/
theorem Edge.frozen {y z : A} (h : Edge v goods base y z) (hz : z ∈ agents) :
    Frozen agents goods base (vbNeeds v goods base) y := by
  obtain ⟨g, hB, hN⟩ := h
  exact ⟨g, hB, z, hz, hN⟩

omit [DecidableEq G] in
/-- The agents of a need chain but the last are frozen. -/
theorem NeedChain.frozen {c : List A} (h : NeedChain v agents goods base c) {k : Nat} (hk : k + 1 < c.length) :
    Frozen agents goods base (vbNeeds v goods base) c[k] :=
  (h.edge k hk).frozen (h.mem _ (List.getElem_mem hk))

omit [DecidableEq G] in
/-- The end of a need chain is a terminal. -/
theorem NeedChain.terminal {c : List A} (h : NeedChain v agents goods base c) :
    Terminal v agents goods base (c[c.length - 1]'(by have := h.two; omega)) := by
  have h2 := h.two
  obtain ⟨g, -, hN⟩ := h.edge (c.length - 2) (by omega)
  refine ⟨h.mem _ (List.getElem_mem _), h.free, g, ?_⟩
  have e : c.length - 2 + 1 = c.length - 1 := by omega
  simp only [e] at hN
  exact hN

omit [DecidableEq G] in
/-- **Lemma C, first half** (`k4/c4x.md` §3; any k). At a Pareto-maximum the need digraph has no cycle: no distinct
listed agents `L[0] → L[1] → … → L[n−1] → L[0]`. (Every agent takes its predecessor's good, which it needed.) -/
theorem no_edge_cycle (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) {L : List A} (hL : L.Nodup)
    (hne : L ≠ []) (hLa : ∀ a ∈ L, a ∈ agents)
    (hE : ∀ k (hk : k < L.length), Edge v goods base L[k] (L[(k + 1) % L.length]'(Nat.mod_lt _ (by omega)))) :
    False :=
  cycle_move hgd hP hL hne hLa (extra := fun _ => none) (by simp) fun k hk => by
    obtain ⟨g, hB, hg, hgb, hlt⟩ := hE k hk
    have hx : extrasOf goods base (fun _ => none) (L[(k + 1) % L.length]'(Nat.mod_lt _ (by omega))) = [] := by
      simp [extrasOf]
    rw [hB, hx]
    exact ⟨by simp, by simp; omega, by simpa [value] using hlt, by simp⟩

omit [DecidableEq G] in
/-- **Lemma C, second half** (`k4/c4x.md` §3; any k). At a Pareto-maximum every frozen listed agent `x` has a need
chain: following the edges from `x` through frozen agents reaches a terminal (it cannot close a cycle,
`no_edge_cycle`). -/
theorem exists_needChain (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) {x : A} (hx : x ∈ agents)
    (hF : Frozen agents goods base (vbNeeds v goods base) x) :
    ∃ c, NeedChain v agents goods base c ∧ c.head? = some x := by
  have walk : ∀ k, (∃ c, NeedChain v agents goods base c ∧ c.head? = some x) ∨
      ∃ w : List A, w.length = k + 1 ∧ w.Nodup ∧ w.head? = some x ∧
        (∀ a ∈ w, a ∈ agents ∧ Frozen agents goods base (vbNeeds v goods base) a) ∧
        ∀ i (hi : i + 1 < w.length), Edge v goods base w[i] w[i + 1] := by
    intro k
    induction k with
    | zero => exact Or.inr ⟨[x], rfl, by simp, rfl, by simp [hx, hF], fun i hi => by simp at hi⟩
    | succ k ih =>
      rcases ih with h | ⟨w, hlen, hnd, hhd, hfz, hed⟩
      · exact Or.inl h
      have hk : k < w.length := by omega
      obtain ⟨g, hB, z, hz, hN⟩ := (hfz _ (List.getElem_mem hk)).2
      have hyz : Edge v goods base w[k] z := ⟨g, hB, hN⟩
      -- the extended walk `w ++ [z]`
      have happ : ∀ i (hi : i < (w ++ [z]).length), (w ++ [z])[i] = if h : i < w.length then w[i] else z := by
        intro i hi
        split
        · rename_i h; exact List.getElem_append_left h
        · rename_i h
          rw [List.getElem_append_right (by omega)]
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          simp [show i - w.length = 0 by omega]
      have hed' : ∀ i (hi : i + 1 < (w ++ [z]).length), Edge v goods base (w ++ [z])[i] (w ++ [z])[i + 1] := by
        intro i hi
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        rw [happ i (by simp; omega), happ (i + 1) (by simp; omega)]
        by_cases h1 : i + 1 < w.length
        · simp only [show i < w.length by omega, h1, ↓reduceDIte]; exact hed i h1
        · have e : i = k := by omega
          subst e
          simp only [hk, ↓reduceDIte, show ¬ (i + 1 < w.length) by omega]
          exact hyz
      have hhd' : (w ++ [z]).head? = some x := by
        cases w with
        | nil => simp at hlen
        | cons a w => simpa using hhd
      by_cases hzF : Frozen agents goods base (vbNeeds v goods base) z
      · by_cases hzw : z ∈ w
        · -- a cycle `w[j] = z → … → w[k] → z`: excluded by `no_edge_cycle`
          exfalso
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hzw
          have hLl : (w.drop j).length = k + 1 - j := by simp [hlen]
          refine no_edge_cycle hgd hP (L := w.drop j) (hnd.sublist (List.drop_sublist _ _))
            (by simp; omega) (fun a ha => (hfz a (List.mem_of_mem_drop ha)).1) fun i hi => ?_
          rw [hLl] at hi
          by_cases h1 : i + 1 < k + 1 - j
          · have e : (i + 1) % (w.drop j).length = i + 1 := by rw [hLl]; exact Nat.mod_eq_of_lt h1
            simp only [e, List.getElem_drop]
            have := hed (j + i) (by omega)
            simp only [show j + i + 1 = j + (i + 1) by omega] at this
            exact this
          · have e : (i + 1) % (w.drop j).length = 0 := by
              rw [hLl, show i + 1 = k + 1 - j by omega, Nat.mod_self]
            simp only [e, List.getElem_drop, Nat.add_zero]
            simp only [show j + i = k by omega]
            exact hyz
        · refine Or.inr ⟨w ++ [z], by simp [hlen], ?_, hhd', fun a ha => ?_, hed'⟩
          · exact List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => by
              simp at hb; subst hb; exact fun e => hzw (e ▸ ha)⟩
          · rcases List.mem_append.mp ha with ha | ha
            · exact hfz a ha
            · simp at ha; subst ha; exact ⟨hz, hzF⟩
      · -- `z` is free: `w ++ [z]` is a need chain
        refine Or.inl ⟨w ++ [z], ⟨?_, fun a ha => ?_, by simp; omega, hed', ?_⟩, hhd'⟩
        · exact List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => by
            simp at hb; subst hb; exact fun e => hzF (e ▸ (hfz a ha).2)⟩
        · rcases List.mem_append.mp ha with ha | ha
          · exact (hfz a ha).1
          · simp at ha; subst ha; exact hz
        · rw [happ _ (by simp)]
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel, Nat.lt_irrefl,
            ↓reduceDIte]
          exact hzF
  rcases walk agents.length with h | ⟨w, hlen, hnd, -, hfz, -⟩
  · exact h
  · have := LB.length_le_of_subset hnd fun a ha => (hfz a ha).1
    omega


/-! ## Three goods: the facts of `k4/c4x.md` §3 -/

/-- The setting of Theorem K3 for the listed agents: exactly three relevant goods each, strictly balanced (each good
worth less than the other two together). Strict types are not needed by the proofs below. -/
structure Three (v : A → G → Nat) (agents : List A) (goods : List G) : Prop where
  three : ∀ i ∈ agents, (relevant v i goods).length = 3
  bal : ∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g < value v i goods

omit [DecidableEq A] [DecidableEq G] in
theorem mem_relevant {i : A} {g : G} : g ∈ relevant v i goods ↔ g ∈ goods ∧ 0 < v i g := by
  simp [relevant]

/-- A duplicate-free subset of a duplicate-free list that is at least as long is a permutation of it. -/
theorem perm_of_subset_length {S T : List G} (hS : S.Nodup) (hT : T.Nodup) (hsub : ∀ g ∈ S, g ∈ T)
    (hl : T.length ≤ S.length) : S.Perm T := by
  have hp : S.Perm (T.filter (fun g => g ∈ S)) :=
    (List.perm_ext_iff_of_nodup hS (hT.sublist List.filter_sublist)).mpr fun g => by
      simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => ⟨hsub g h, h⟩, fun h => h.2⟩
  have := (List.filter_sublist (p := fun g => decide (g ∈ S)) (l := T)).eq_of_length_le
    (by rw [← hp.length_eq]; exact hl)
  rw [this] at hp; exact hp

omit [DecidableEq A] in
/-- Values are monotone along duplicate-free subsets. -/
theorem value_le_of_subset {S T : List G} (hS : S.Nodup) (hT : T.Nodup) (hsub : ∀ g ∈ S, g ∈ T) (i : A) :
    value v i S ≤ value v i T := by
  have hp : S.Perm (T.filter (fun g => g ∈ S)) :=
    (List.perm_ext_iff_of_nodup hS (hT.sublist List.filter_sublist)).mpr fun g => by
      simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun h => ⟨hsub g h, h⟩, fun h => h.2⟩
  rw [value_perm hp]; exact value_sublist v i List.filter_sublist

omit [DecidableEq A] [DecidableEq G] in
theorem value_relevant (i : A) : value v i goods = value v i (relevant v i goods) :=
  LB4.value_filter_pos i goods

/-- **The threat facts (i)–(iii)** of `k4/c4x.md` §3, in one statement (`|R_x| = 3` only). Let `X` be a set of goods
disjoint from `B_x` and containing no good `x` needs. If `X` threatens `x` holding `B_x` alone
(`v_x(B_x) < v_x(X ∖ h)` for some `h ∈ X`), then `x` holds one good `a` and its two other relevant goods are in `X`. -/
theorem threat_shape (hgd : goods.Nodup) (hP : InP v agents goods base) {x : A}
    (h3 : (relevant v x goods).length = 3) {X : List G} (hX : X.Nodup) (hXg : ∀ g ∈ X, g ∈ goods)
    (hXB : ∀ g ∈ X, base g ≠ some x) (hXN : ∀ g ∈ X, ¬ vbNeeds v goods base x g) {h : G}
    (hth : value v x (baseOf goods base x) < value v x (X.erase h)) :
    ∃ a, baseOf goods base x = [a] ∧ ∀ g ∈ goods, 0 < v x g → g ≠ a → g ∈ X := by
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = X.filter (fun g => 0 < v x g) := ⟨_, rfl⟩
  have hYX : ∀ g ∈ Y, g ∈ X := fun g hg => (List.mem_filter.mp (hYdef ▸ hg)).1
  have hYpos : ∀ g ∈ Y, 0 < v x g := fun g hg => by
    rw [hYdef, List.mem_filter] at hg; exact of_decide_eq_true hg.2
  have hle : value v x (X.erase h) ≤ value v x Y := by
    rw [hYdef, show value v x (X.filter (fun g => 0 < v x g)) = value v x X from (LB4.value_filter_pos x X).symm]
    exact value_sublist v x (List.erase_sublist)
  have hYle : ∀ g ∈ Y, v x g ≤ value v x (baseOf goods base x) := fun g hg =>
    Nat.le_of_not_lt fun hlt => hXN g (hYX g hg) ⟨hXg g (hYX g hg), hXB g (hYX g hg), hlt⟩
  have hBY : (baseOf goods base x ++ Y).Nodup := List.nodup_append.mpr
    ⟨hgd.sublist List.filter_sublist, hYdef ▸ hX.sublist List.filter_sublist, fun a ha b hb e => by
      subst e; exact hXB a (hYX a hb) (mem_baseOf.mp ha).2⟩
  have hsub : ∀ g ∈ baseOf goods base x ++ Y, g ∈ relevant v x goods := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨hgg, hb⟩ := mem_baseOf.mp hg; exact mem_relevant.mpr ⟨hgg, hP.rel g hgg x hb⟩
    · exact mem_relevant.mpr ⟨hXg g (hYX g hg), hYpos g hg⟩
  have hcount := LB.length_le_of_subset hBY hsub
  rw [h3, List.length_append] at hcount
  clear hYdef
  rcases Y with _ | ⟨g1, _ | ⟨g2, rest⟩⟩
  · rw [value_nil] at hle; omega
  · have := hYle g1 (by simp); simp only [value_cons, value_nil] at hle; omega
  · simp only [List.length_cons] at hcount
    rcases base_le_one (by omega : (baseOf goods base x).length ≤ 1) with hB | ⟨a, hB⟩
    · have := hYle g1 (by simp); rw [hB] at this; simp [value] at this
      have := hYpos g1 (by simp); omega
    · refine ⟨a, hB, fun g hg hpos hga => ?_⟩
      have hperm := perm_of_subset_length (T := relevant v x goods) hBY (hgd.sublist List.filter_sublist) hsub
        (by rw [h3, List.length_append, hB]; simp; omega)
      have hgR := hperm.mem_iff.mpr (mem_relevant.mpr ⟨hg, hpos⟩)
      rw [hB] at hgR
      rcases List.mem_append.mp hgR with h1 | h1
      · simp at h1; exact absurd h1 hga
      · exact hYX g h1

/-- **Fact (i)** of `k4/c4x.md` §3: a base of two goods has no needs (the third good is worth less than the two). -/
theorem no_needs_two (hgd : goods.Nodup) (hP : InP v agents goods base) {x : A}
    (h3 : (relevant v x goods).length = 3) (hbal : ∀ g ∈ goods, 2 * v x g < value v x goods)
    (h2 : 2 ≤ (baseOf goods base x).length) {g : G} : ¬ vbNeeds v goods base x g := by
  rintro ⟨hg, hgb, hlt⟩
  have hnd : (baseOf goods base x ++ [g]).Nodup := List.nodup_append.mpr
    ⟨hgd.sublist List.filter_sublist, by simp, fun a ha b hb e => by
      simp at hb; subst hb; subst e; exact hgb (mem_baseOf.mp ha).2⟩
  have hsub : ∀ h ∈ baseOf goods base x ++ [g], h ∈ relevant v x goods := by
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · obtain ⟨hhg, hb⟩ := mem_baseOf.mp hh; exact mem_relevant.mpr ⟨hhg, hP.rel h hhg x hb⟩
    · simp at hh; subst hh; exact mem_relevant.mpr ⟨hg, by omega⟩
  have hperm := perm_of_subset_length (T := relevant v x goods) hnd (hgd.sublist List.filter_sublist) hsub
    (by rw [h3]; simp; omega)
  have hv := value_perm (v := v) (i := x) hperm
  rw [value_append, ← value_relevant] at hv
  have := hbal g hg
  simp [value] at hv
  simp [value] at hlt this
  omega

/-- A terminal holds at most one good (fact (i): a two-good base has no needs). -/
theorem Terminal.le_one (hgd : goods.Nodup) (hP : InP v agents goods base) (hT : Three v agents goods) {t : A}
    (ht : Terminal v agents goods base t) : (baseOf goods base t).length ≤ 1 := by
  obtain ⟨hta, -, g, hN⟩ := ht
  exact Nat.le_of_not_lt fun h2 => no_needs_two hgd hP (hT.three t hta) (hT.bal t hta) h2 hN

omit [DecidableEq G] in
/-- The goods of a free agent with at most one good are not in `NA`. -/
theorem not_NA_of_free_le_one {j : A} (h1 : (baseOf goods base j).length ≤ 1)
    (hF : ¬ Frozen agents goods base (vbNeeds v goods base) j) : ∀ g ∈ baseOf goods base j,
      ¬ NA agents (vbNeeds v goods base) g := by
  intro g hg
  rcases base_le_one h1 with hB | ⟨y, hB⟩
  · rw [hB] at hg; simp at hg
  · rw [hB] at hg; simp at hg; subst hg; exact not_NA_of_free hB hF

omit [DecidableEq A] in
/-- The two goods of `R_x` other than `a`, and `v_x(R_x) = v_x(a) + v_x(l₁) + v_x(l₂)`. -/
theorem low_pair (hgd : goods.Nodup) {x : A} (h3 : (relevant v x goods).length = 3) {a : G} (ha : a ∈ goods)
    (hpa : 0 < v x a) : ∃ l1 l2, l1 ∈ goods ∧ l2 ∈ goods ∧ 0 < v x l1 ∧ 0 < v x l2 ∧ l1 ≠ l2 ∧ l1 ≠ a ∧ l2 ≠ a ∧
      (∀ g ∈ goods, 0 < v x g → g = a ∨ g = l1 ∨ g = l2) ∧ value v x goods = v x a + v x l1 + v x l2 := by
  have haR : a ∈ relevant v x goods := mem_relevant.mpr ⟨ha, hpa⟩
  have hnd : (relevant v x goods).Nodup := hgd.sublist List.filter_sublist
  have hp := List.perm_cons_erase haR
  have hl : ((relevant v x goods).erase a).length = 2 := by rw [List.length_erase_of_mem haR, h3]
  match he : (relevant v x goods).erase a, hl with
  | [l1, l2], _ =>
    rw [he] at hp
    have hnd' := hp.nodup_iff.mp hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
    have hm : ∀ g, g ∈ relevant v x goods ↔ g = a ∨ g = l1 ∨ g = l2 := fun g => by
      rw [hp.mem_iff]; simp
    have h1 := mem_relevant.mp ((hm l1).mpr (Or.inr (Or.inl rfl)))
    have h2 := mem_relevant.mp ((hm l2).mpr (Or.inr (Or.inr rfl)))
    refine ⟨l1, l2, h1.1, h2.1, h1.2, h2.2, hnd'.2.1, Ne.symm hnd'.1.1, Ne.symm hnd'.1.2, fun g hg hpos =>
      (hm g).mp (mem_relevant.mpr ⟨hg, hpos⟩), ?_⟩
    rw [value_relevant, value_perm hp]; simp [value]; omega

omit [DecidableEq G] in
/-- The extras that `fun g => if P g then some x else none` gives: the junk goods of `P` to `x`, nothing to others. -/
theorem mem_extrasOf_if {P : G → Prop} [DecidablePred P] {x y : A} {g : G} :
    g ∈ extrasOf goods base (fun g => if P g then some x else none) y ↔
      g ∈ goods ∧ base g = none ∧ P g ∧ y = x := by
  unfold extrasOf
  rw [List.mem_filter, mem_junk]
  by_cases hP : P g <;> simp [hP, eq_comm, and_assoc]

omit [DecidableEq G] in
theorem extrasOf_if_ne {P : G → Prop} [DecidablePred P] {x y : A} (hxy : y ≠ x) :
    extrasOf goods base (fun g => if P g then some x else none) y = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun _ hg => hxy (mem_extrasOf_if.mp hg).2.2.2

omit [DecidableEq G] in
theorem extrasOf_if_perm (hgd : goods.Nodup) {P : G → Prop} [DecidablePred P] {x : A} {S : List G} (hS : S.Nodup)
    (h : ∀ g, g ∈ S ↔ g ∈ goods ∧ base g = none ∧ P g) :
    (extrasOf goods base (fun g => if P g then some x else none) x).Perm S :=
  (List.perm_ext_iff_of_nodup ((hgd.sublist List.filter_sublist).sublist List.filter_sublist) hS).mpr fun g => by
    show g ∈ extrasOf goods base (fun g => if P g then some x else none) x ↔ g ∈ S
    rw [mem_extrasOf_if, h g]; simp

/-- `extrasOf` for one extra good. -/
theorem extrasOf_single (hgd : goods.Nodup) {z : G} {x : A} (hz : z ∈ goods) (hzb : base z = none) :
    extrasOf goods base (fun g => if g = z then some x else none) x = [z] :=
  List.perm_singleton.mp (extrasOf_if_perm (P := fun g => g = z) hgd (by simp) fun g => by
    simp only [List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨hz, hzb, rfl⟩
    · exact fun h => h.2.2)

omit [DecidableEq G] in
/-- The new base of the receiver of an edge satisfies `GoodNew`. -/
theorem goodNew_edge {p a : A} (h : Edge v goods base p a) : GoodNew v agents goods base a (baseOf goods base p) := by
  obtain ⟨g, hB, -, -, hlt⟩ := h
  rw [hB]
  exact ⟨by simp, fun h hh => by simp at hh; subst hh; omega, by simpa [value] using hlt, by simp⟩

/-! ## Lemma R -/

/-- **Lemma R** (`k4/c4x.md` §3; k = 3). At a Pareto-maximum, if `x` holds one good `a` and heads a need chain ending
at `τ`, then not both other relevant goods of `x` are in `J ∪ B_τ`. (Otherwise LB⁺'s rotation — `x` takes them, the
chain rotates, `B_τ` goes to the junk or to `x` — dominates.) -/
theorem lemmaR (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods) {c : List A}
    (hc : NeedChain v agents goods base c) {x τ : A} {a : G} (hx : c.head? = some x) (hτ : c.getLast? = some τ)
    (hB : baseOf goods base x = [a]) :
    ¬ ∀ g ∈ goods, 0 < v x g → g ≠ a → base g = none ∨ base g = some τ := by
  intro hlow
  have h2 := hc.two
  have hne : c ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hx0 : c[0]'(by omega) = x := by
    cases c with
    | nil => simp at h2
    | cons y c => simpa using hx
  have hτn : c[c.length - 1]'(by omega) = τ := by
    rw [List.getLast?_eq_getElem?] at hτ
    exact (List.getElem?_eq_some_iff.mp hτ).2
  have hxa : x ∈ agents := hc.mem x (hx0 ▸ List.getElem_mem _)
  have haB : a ∈ goods ∧ base a = some x := mem_baseOf.mp (by rw [hB]; simp)
  have hpa := hP.1.rel a haB.1 x haB.2
  obtain ⟨l1, l2, hl1, hl2, hp1, hp2, h12, h1a, h2a, -, hsum⟩ := low_pair hgd (hT.three x hxa) haB.1 hpa
  have hbal := hT.bal x hxa a haB.1
  have hterm := hc.terminal
  simp only [hτn] at hterm
  have hτ1 := hterm.le_one hgd hP.1 hT
  have hτF := hterm.2.1
  have hxne : ∀ k (hk : k + 1 < c.length), c[k + 1] ≠ x := fun k hk e => by
    rw [← hx0, hc.nodup.getElem_inj] at e; omega
  -- the receivers after `x` get the good they needed
  have hedge : ∀ {extra : G → Option A}, (∀ k (hk : k + 1 < c.length), extrasOf goods base extra c[k + 1] = []) →
      ∀ k (hk : k + 1 < c.length), GoodNew v agents goods base c[k + 1]
        (baseOf goods base c[k] ++ extrasOf goods base extra c[k + 1]) := by
    intro extra hex k hk
    rw [hex k hk, List.append_nil]
    exact goodNew_edge (hc.edge k hk)
  by_cases hA : ∃ y z, ((y = l1 ∧ z = l2) ∨ (y = l2 ∧ z = l1)) ∧ baseOf goods base τ = [y]
  · -- `B_τ = {y}` with `y ∈ low(x)`: the cycle `x → … → τ → x`, `x` taking `{y, z}`
    obtain ⟨y, z, hyz, hBτ⟩ := hA
    have hy : y ∈ goods ∧ 0 < v x y ∧ y ≠ z := by
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hl1, hp1, h12⟩
      · exact ⟨hl2, hp2, Ne.symm h12⟩
    have hz : z ∈ goods ∧ 0 < v x z ∧ z ≠ a := by
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hl2, hp2, h2a⟩
      · exact ⟨hl1, hp1, h1a⟩
    have hzb : base z = none := by
      rcases hlow z hz.1 hz.2.1 hz.2.2 with h | h
      · exact h
      · have := (mem_single_base hBτ).mp ⟨hz.1, h⟩; exact absurd this.symm hy.2.2
    have hvyz : v x a < v x y + v x z := by
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    refine cycle_move hgd hP hc.nodup hne hc.mem (extra := fun g => if g = z then some x else none)
      (fun g _ b h => ?_) fun k hk => ?_
    · by_cases e : g = z
      · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst e; subst h
        exact ⟨hzb, hx0 ▸ List.getElem_mem _⟩
      · simp [e] at h
    by_cases hk1 : k + 1 < c.length
    · simp only [Nat.mod_eq_of_lt hk1]
      exact hedge (fun k hk => extrasOf_if_ne (hxne k hk)) k hk1
    · have ek : k = c.length - 1 := by omega
      subst ek
      simp only [show c.length - 1 + 1 = c.length by omega, Nat.mod_self, hx0, hτn, hBτ]
      rw [extrasOf_single hgd hz.1 hzb]
      refine ⟨by simp, fun g hg => ?_, ?_, fun _ g hg => ?_⟩
      · simp at hg; rcases hg with rfl | rfl
        · exact hy.2.1
        · exact hz.2.1
      · rw [hB]; simp [value]; omega
      · simp at hg; rcases hg with rfl | rfl
        · exact not_NA_of_free hBτ hτF
        · exact hP.1.valid.v1 g (mem_junk.mpr ⟨hz.1, hzb⟩)
  · -- otherwise both low goods are junk: the path `x → … → τ`, `x` taking `{l₁, l₂}`, `B_τ` to the junk
    have hjunk : ∀ l ∈ goods, 0 < v x l → l ≠ a → (l = l1 ∨ l = l2) → base l = none := by
      intro l hl hpl hla hl12
      rcases hlow l hl hpl hla with h | h
      · exact h
      · exfalso
        rcases base_le_one hτ1 with hBτ | ⟨y, hBτ⟩
        · have := mem_baseOf.mpr ⟨hl, h⟩; rw [hBτ] at this; simp at this
        · have := (mem_single_base hBτ).mp ⟨hl, h⟩
          subst this
          rcases hl12 with rfl | rfl
          · exact hA ⟨l, l2, Or.inl ⟨rfl, rfl⟩, hBτ⟩
          · exact hA ⟨l, l1, Or.inr ⟨rfl, rfl⟩, hBτ⟩
    have hb1 := hjunk l1 hl1 hp1 h1a (Or.inl rfl)
    have hb2 := hjunk l2 hl2 hp2 h2a (Or.inr rfl)
    refine path_move hgd hP hc.nodup (by omega) hc.mem (extra := fun g => if g = l1 ∨ g = l2 then some x else none)
      (fun g _ b h => ?_) ?_ ?_ (hedge fun k hk => extrasOf_if_ne (hxne k hk))
    · by_cases e : g = l1 ∨ g = l2
      · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
        refine ⟨?_, hx0 ▸ List.getElem_mem _⟩
        rcases e with rfl | rfl
        · exact hb1
        · exact hb2
      · simp [e] at h
    · simp only [hτn]; exact not_NA_of_free_le_one hτ1 hτF
    · simp only [hx0]
      have hperm := extrasOf_if_perm (x := x) (P := fun g => g = l1 ∨ g = l2) hgd (S := [l1, l2]) (by simp [h12])
        fun g => by
          constructor
          · intro hg; simp at hg
            rcases hg with rfl | rfl
            · exact ⟨hl1, hb1, Or.inl rfl⟩
            · exact ⟨hl2, hb2, Or.inr rfl⟩
          · rintro ⟨-, -, h⟩; simpa using h
      refine ⟨by rw [hperm.length_eq]; simp, fun g hg => ?_, ?_, fun _ g hg => ?_⟩
      · rw [hperm.mem_iff] at hg; simp at hg
        rcases hg with rfl | rfl
        · exact hp1
        · exact hp2
      · rw [value_perm hperm, hB]; simp [value]; omega
      · rw [hperm.mem_iff] at hg; simp at hg
        rcases hg with rfl | rfl
        · exact hP.1.valid.v1 g (mem_junk.mpr ⟨hl1, hb1⟩)
        · exact hP.1.valid.v1 g (mem_junk.mpr ⟨hl2, hb2⟩)

/-! ## Lemma E (who is exposed) -/

/-- `W_t = B_t ∪ J`. -/
def W (goods : List G) (base : G → Option A) (t : A) : List G :=
  goods.filter (fun g => base g = some t ∨ base g = none)

/-- `x` is exposed w.r.t. `t` (`k4/c4x.md` §3, `E_t`): `x ≠ t` is listed, and `W_t` threatens `x` holding its base
alone, `v_x(B_x) < v_x(W_t ∖ h)` for some `h ∈ W_t`. (Some `X ⊆ W_t` threatens `x` iff `W_t` does, values being
monotone: `exposed_of_sub`.) -/
def Exposed (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) (t x : A) : Prop :=
  x ∈ agents ∧ x ≠ t ∧ ∃ h ∈ W goods base t,
    value v x (baseOf goods base x) < value v x ((W goods base t).erase h)

omit [DecidableEq G] in
theorem mem_W {t : A} {g : G} : g ∈ W goods base t ↔ g ∈ goods ∧ (base g = some t ∨ base g = none) := by
  simp [W]

/-- A set `X ⊆ W_t` that threatens `x ≠ t` exposes `x`. -/
theorem exposed_of_sub (hgd : goods.Nodup) {t x : A} (hx : x ∈ agents) (hxt : x ≠ t) {X : List G} (hX : X.Nodup)
    (hXW : ∀ g ∈ X, g ∈ W goods base t) {h : G} (hh : h ∈ X)
    (hth : value v x (baseOf goods base x) < value v x (X.erase h)) : Exposed v agents goods base t x := by
  have hW : (W goods base t).Nodup := hgd.sublist List.filter_sublist
  refine ⟨hx, hxt, h, hXW h hh, Nat.lt_of_lt_of_le hth (value_le_of_subset (hX.erase h) (hW.erase h) ?_ x)⟩
  intro g hg
  have hgh : g ≠ h := fun e => by subst e; exact (List.Nodup.not_mem_erase hX) hg
  exact (List.mem_erase_of_ne hgh).mpr (hXW g (List.mem_of_mem_erase hg))

omit [DecidableEq G] in
/-- The goods of `W_t` are not in `NA` when `t` is free with at most one good (V1 for the junk). -/
theorem W_not_NA (hP : InP v agents goods base) {t : A} (ht1 : (baseOf goods base t).length ≤ 1)
    (htF : ¬ Frozen agents goods base (vbNeeds v goods base) t) :
    ∀ g ∈ W goods base t, ¬ NA agents (vbNeeds v goods base) g := by
  intro g hg
  obtain ⟨hgg, hb | hb⟩ := mem_W.mp hg
  · exact not_NA_of_free_le_one ht1 htF g (mem_baseOf.mpr ⟨hgg, hb⟩)
  · exact hP.valid.v1 g (mem_junk.mpr ⟨hgg, hb⟩)

/-- The shape of `x` threatened by a subset of `W_t`, for a terminal `t`: `x` holds one good `a`, and its two other
relevant goods are in the subset. -/
theorem threat_W (hgd : goods.Nodup) (hP : InP v agents goods base) (hT : Three v agents goods) {t x : A}
    (ht : Terminal v agents goods base t) (hx : x ∈ agents) (hxt : x ≠ t) {X : List G} (hX : X.Nodup)
    (hXW : ∀ g ∈ X, g ∈ W goods base t) {h : G}
    (hth : value v x (baseOf goods base x) < value v x (X.erase h)) :
    ∃ a, baseOf goods base x = [a] ∧ ∀ g ∈ goods, 0 < v x g → g ≠ a → g ∈ X := by
  refine threat_shape hgd hP (hT.three x hx) hX (fun g hg => (mem_W.mp (hXW g hg)).1) (fun g hg hb => ?_)
    (fun g hg hN => W_not_NA hP (ht.le_one hgd hP hT) ht.2.1 g (hXW g hg) ⟨x, hx, hN⟩) hth
  rcases (mem_W.mp (hXW g hg)).2 with e | e <;> rw [hb] at e
  · exact hxt (Option.some.inj e)
  · cases e

/-- **Lemma E** (`k4/c4x.md` §3; k = 3). Let `P` be Pareto-maximal and `t` a terminal. If `x` is exposed w.r.t. `t`,
then `x` is frozen and holds one good `a`, `B_t` is one good `y` relevant to `x`, the third good `z` of `x` is junk (its
*label*), and no need chain from `x` ends at `t`. -/
theorem lemmaE (hgd : goods.Nodup) (hP : ParetoMax v agents goods base) (hT : Three v agents goods) {t x : A}
    (ht : Terminal v agents goods base t) (hx : Exposed v agents goods base t x) :
    Frozen agents goods base (vbNeeds v goods base) x ∧ ∃ a y z, baseOf goods base x = [a] ∧
      baseOf goods base t = [y] ∧ z ∈ goods ∧ base z = none ∧ 0 < v x y ∧ 0 < v x z ∧ y ≠ z ∧
      (∀ g ∈ goods, 0 < v x g → g ≠ a → g = y ∨ g = z) ∧ ¬ ChainTo v agents goods base x t := by
  obtain ⟨hxa, hxt, h, -, hth⟩ := hx
  have hW : (W goods base t).Nodup := hgd.sublist List.filter_sublist
  obtain ⟨a, hB, hlowW⟩ := threat_W hgd hP.1 hT ht hxa hxt hW (fun g hg => hg) hth
  have haB : a ∈ goods ∧ base a = some x := mem_baseOf.mp (by rw [hB]; simp)
  obtain ⟨l1, l2, hl1, hl2, hp1, hp2, h12, h1a, h2a, hR, -⟩ :=
    low_pair hgd (hT.three x hxa) haB.1 (hP.1.rel a haB.1 x haB.2)
  have ht1 := ht.le_one hgd hP.1 hT
  -- both low goods in `B_t` is impossible: `B_t` has at most one good
  have hnot2 : ¬ (base l1 = some t ∧ base l2 = some t) := by
    rintro ⟨e1, e2⟩
    rcases base_le_one ht1 with hBt | ⟨y, hBt⟩
    · have := mem_baseOf.mpr ⟨hl1, e1⟩; rw [hBt] at this; simp at this
    · exact h12 (((mem_single_base hBt).mp ⟨hl1, e1⟩).trans ((mem_single_base hBt).mp ⟨hl2, e2⟩).symm)
  have hW1 := (mem_W.mp (hlowW l1 hl1 hp1 h1a)).2
  have hW2 := (mem_W.mp (hlowW l2 hl2 hp2 h2a)).2
  -- `x` is frozen: a free `x` would value no junk good (Lemma U)
  have hxF : Frozen agents goods base (vbNeeds v goods base) x := by
    refine Classical.byContradiction fun hF => hnot2 ?_
    have hU := lemmaU hgd hP hxa hF (by rw [hB]; simp)
    have hl : ∀ l ∈ goods, 0 < v x l → (base l = some t ∨ base l = none) → base l = some t := by
      intro l hl hpl hlw
      rcases hlw with e | e
      · exact e
      · have := hU l (mem_junk.mpr ⟨hl, e⟩); omega
    exact ⟨hl l1 hl1 hp1 hW1, hl l2 hl2 hp2 hW2⟩
  -- a need chain from `x` ends at a terminal `τ`; by Lemma R not both low goods are junk
  obtain ⟨c, hc, hcx⟩ := exists_needChain hgd hP hxa hxF
  have hlast : ∃ τ, c.getLast? = some τ := by
    cases h : c.getLast? with
    | none => have := hc.two; rw [List.getLast?_eq_none_iff] at h; subst h; simp at this
    | some τ => exact ⟨τ, rfl⟩
  obtain ⟨τ, hτ⟩ := hlast
  have hR' : ∀ τ', ChainTo v agents goods base x τ' →
      ¬ ((base l1 = some τ' ∨ base l1 = none) ∧ (base l2 = some τ' ∨ base l2 = none)) := by
    rintro τ' ⟨c', hc', hx', hτ'⟩ ⟨e1, e2⟩
    refine lemmaR hgd hP hT hc' hx' hτ' hB fun g hg hpg hga => ?_
    rcases hR g hg hpg with rfl | rfl | rfl
    · exact absurd rfl hga
    · exact e1.symm
    · exact e2.symm
  -- so exactly one low good is `B_t`'s good `y`, and the other one `z` is junk
  have key : ∀ y z, y ∈ goods → z ∈ goods → 0 < v x y → 0 < v x z → y ≠ z →
      (∀ g ∈ goods, 0 < v x g → g ≠ a → g = y ∨ g = z) → base y = some t → base z = none →
      Frozen agents goods base (vbNeeds v goods base) x ∧ ∃ a y z, baseOf goods base x = [a] ∧
        baseOf goods base t = [y] ∧ z ∈ goods ∧ base z = none ∧ 0 < v x y ∧ 0 < v x z ∧ y ≠ z ∧
        (∀ g ∈ goods, 0 < v x g → g ≠ a → g = y ∨ g = z) ∧ ¬ ChainTo v agents goods base x t := by
    intro y z hy hz hpy hpz hyz hyzR hby hbz
    have hBt : baseOf goods base t = [y] := by
      rcases base_le_one ht1 with hBt | ⟨y', hBt⟩
      · have := mem_baseOf.mpr ⟨hy, hby⟩; rw [hBt] at this; simp at this
      · rw [hBt, (mem_single_base hBt).mp ⟨hy, hby⟩]
    exact ⟨hxF, a, y, z, hB, hBt, hz, hbz, hpy, hpz, hyz, hyzR, fun hch => hR' t hch ⟨hW1, hW2⟩⟩
  have hcτ : ChainTo v agents goods base x τ := ⟨c, hc, hcx, hτ⟩
  have hRl : ∀ g ∈ goods, 0 < v x g → g ≠ a → g = l1 ∨ g = l2 := fun g hg hpg hga => by
    rcases hR g hg hpg with rfl | h | h
    · exact absurd rfl hga
    · exact Or.inl h
    · exact Or.inr h
  rcases hW1 with e1 | e1 <;> rcases hW2 with e2 | e2
  · exact absurd ⟨e1, e2⟩ hnot2
  · exact key l1 l2 hl1 hl2 hp1 hp2 h12 hRl e1 e2
  · exact key l2 l1 hl2 hl1 hp2 hp1 (Ne.symm h12) (fun g hg hpg hga => (hRl g hg hpg hga).symm) e2 e1
  · exact absurd ⟨Or.inr e1, Or.inr e2⟩ (hR' τ hcτ)

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.inP_of_gain
#print axioms EFX.C4min.lemmaU
#print axioms EFX.C4min.transfer_move
#print axioms EFX.C4min.transfer_inP_dominates
#print axioms EFX.C4min.cycle_move
#print axioms EFX.C4min.path_move
#print axioms EFX.C4min.no_edge_cycle
#print axioms EFX.C4min.exists_needChain
#print axioms EFX.C4min.threat_shape
#print axioms EFX.C4min.no_needs_two
#print axioms EFX.C4min.lemmaR
#print axioms EFX.C4min.exposed_of_sub
#print axioms EFX.C4min.lemmaE
