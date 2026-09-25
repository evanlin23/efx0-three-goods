import EFX.PreAlloc
import EFX.K4Ties

/-!
# Pre-allocations with bases and needs of any size (`k4/lb4.md` §1; ledger K4.LB4.S)

The k = 4 construction LB₄ builds *pre-allocations* in which an agent's base can have any number of
goods and its needs are any set between the goods worth more than the base and all goods outside it.
This file proves `k4/lb4.md` §1 for any number of relevant goods per agent (only additivity and
nonnegativity of the values are used), generalizing `EFX/PreAlloc.lean` (Theorem 1′ of
`proofs/lb_last_step.md`, k = 3), whose pre-allocations are ranking-based (picks and upgraded pairs).

Setting (over lists, as `EFX/Lists.lean`): agents `agents`, goods `goods`, values `v : A → G → Nat`.
- A pre-allocation is a map `base : G → Option A` (`base g = some i` iff `g ∈ B_i`, so bases are
  disjoint) and needs `N : A → G → Prop` (`N i g` iff `g ∈ N_i`). `baseOf goods base i` is `B_i`,
  `junk goods base` is `J`, `NA agents N` is `NA = ⋃ N_i`.
- `Needs`: the Definition's bounds `{g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)} ⊆ N_i ⊆ R_i ∖ B_i`. The pick
  needs (`g ≻_i Y`, for a strict order consistent with the values), the needs of an empty base (`R_i`)
  and the value-based needs are instances (`Needs.pick`, `Needs.empty`, `Needs.valueBased`).
- `Frozen`: the base is one good, and it is in `NA`. `Valid`: (V1) and (V2).
- `Completion`: owner `o` (a listed free agent) or none; every good goes to a listed agent, every base
  good to its base's agent, a frozen agent other than `o` gets no junk, a free agent `j ≠ o` gets
  junk `C_j` with `|C_j| ≤ cap(j) = 2 − |B_j|` (with its sign: `|C_j| + |B_j| ≤ 2`).
- `OC`: the owner constraint (OC₄), `v_j(X_o ∖ {h}) ≤ v_j(X_j)` for every `j ≠ o` and `h ∈ X_o`.
- `ownerNeeds`: the needs with the owner's replaced by `N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}`.

Main results:
- `efx0_of_needs`: the proof of Theorem 1′₄ with its hypotheses reduced to what it uses (every agent's
  needs contain the goods outside its bundle worth more than its bundle).
- `Valid.sound` (owner's needs from its base) and `Valid.sound_ownerNeeds` (owner's needs `N_o^X`):
  **Theorem 1′₄**. Every completion satisfying (OC₄) is EFX₀, for any values.
- `Completion.length_le_two`, `Completion.shape`: every bundle but the owner's has at most two goods
  (so the text's hypothesis "only `X_o` may have more than 2 goods" holds in every completion); in the
  model's terms (`d2_of_completion`) the allocation has the D2 shape, and `k4D_of_completion` states
  the chain "a completion satisfying (OC₄) exists ⟹ an EFX₀ allocation with at most one bundle of more
  than two goods exists". `target4_of_completions`: with K4.CORE and K4.TIE, TARGET₄ up to `N` agents
  follows if every connected strict k = 4 core with a 4-good agent has such a completion.
-/

set_option autoImplicit false

namespace EFX
namespace LB4

open LB (mem_bundle nodup_bundle length_le_one length_le_of_subset)

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Definitions -/

/-- `B_i`, agent `i`'s base: the goods of `goods` that `base` assigns to `i`. -/
def baseOf (goods : List G) (base : G → Option A) (i : A) : List G :=
  goods.filter (fun g => base g = some i)

/-- The junk `J`: the goods of `goods` in nobody's base. -/
def junk (goods : List G) (base : G → Option A) : List G :=
  goods.filter (fun g => base g = none)

/-- `C_j`: the junk goods in `j`'s bundle. -/
def junkOf (goods : List G) (base : G → Option A) (X : G → A) (j : A) : List G :=
  (bundle goods X j).filter (fun g => base g = none)

/-- `NA`, the needed-alone set: the goods that some listed agent needs. -/
def NA (agents : List A) (N : A → G → Prop) (g : G) : Prop := ∃ i ∈ agents, N i g

/-- `N i` is a set of needs of `i` (`k4/lb4.md` §1, Definition): it contains every good outside `B_i`
worth more to `i` than `B_i` (such a good is in `R_i`), and it is contained in `R_i ∖ B_i`. -/
structure Needs (v : A → G → Nat) (goods : List G) (base : G → Option A) (N : A → G → Prop) (i : A) :
    Prop where
  lower : ∀ g ∈ goods, base g ≠ some i → value v i (baseOf goods base i) < v i g → N i g
  upper : ∀ g, N i g → g ∈ goods ∧ 0 < v i g ∧ base g ≠ some i

/-- `j` is frozen: its base is a single good, and that good is in `NA`. -/
def Frozen (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) (j : A) :
    Prop :=
  ∃ y, baseOf goods base j = [y] ∧ NA agents N y

/-- A valid pre-allocation: (V1) no junk good is in `NA`; (V2) no good of a base of two or more goods is
in `NA`. -/
structure Valid (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) :
    Prop where
  v1 : ∀ g ∈ junk goods base, ¬ NA agents N g
  v2 : ∀ i, 2 ≤ (baseOf goods base i).length → ∀ g ∈ baseOf goods base i, ¬ NA agents N g

/-- A completion `X` with owner `o` (or none) of the pre-allocation `(base, N)`:
- `alloc`: every good goes to a listed agent;
- `onBase`: every base good goes to its base's agent (so `X_i = B_i ∪ C_i` with `C_i ⊆ J`);
- `owner`: the owner is a listed agent that is not frozen;
- `frozen`: a frozen agent other than the owner gets no junk (cap 0);
- `free`: a free agent `j` other than the owner gets at most `cap(j) = 2 − |B_j|` junk goods, the cap
  counted with its sign (`|C_j| + |B_j| ≤ 2`).
The owner gets the rest of the junk. -/
structure Completion (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop)
    (o : Option A) (X : G → A) : Prop where
  alloc : ∀ g ∈ goods, X g ∈ agents
  onBase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i
  owner : ∀ w, o = some w → w ∈ agents ∧ ¬ Frozen agents goods base N w
  frozen : ∀ j ∈ agents, o ≠ some j → Frozen agents goods base N j → junkOf goods base X j = []
  free : ∀ j ∈ agents, o ≠ some j → ¬ Frozen agents goods base N j →
    (junkOf goods base X j).length + (baseOf goods base j).length ≤ 2

/-- The owner constraint (OC₄): no listed agent other than the owner strongly envies the owner's bundle. -/
def OC (v : A → G → Nat) (agents : List A) (goods : List G) (X : G → A) (o : Option A) : Prop :=
  ∀ w, o = some w → ∀ j ∈ agents, j ≠ w → ∀ h ∈ bundle goods X w,
    value v j ((bundle goods X w).erase h) ≤ value v j (bundle goods X j)

/-- The needs with the owner's replaced by its needs from its bundle,
`N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}`. -/
def ownerNeeds (v : A → G → Nat) (goods : List G) (X : G → A) (N : A → G → Prop) (o : Option A) :
    A → G → Prop :=
  fun i g => if o = some i then g ∈ goods ∧ X g ≠ i ∧ value v i (bundle goods X i) < v i g else N i g

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}
  {N : A → G → Prop} {o : Option A} {X : G → A}

/-! ## Small lemmas -/

omit [DecidableEq G] in
theorem mem_baseOf {i : A} {g : G} : g ∈ baseOf goods base i ↔ g ∈ goods ∧ base g = some i := by
  simp [baseOf]

omit [DecidableEq A] [DecidableEq G] in
theorem mem_junk {g : G} : g ∈ junk goods base ↔ g ∈ goods ∧ base g = none := by
  simp [junk]

omit [DecidableEq G] in
theorem mem_junkOf {j : A} {g : G} :
    g ∈ junkOf goods base X j ↔ g ∈ goods ∧ X g = j ∧ base g = none := by
  simp only [junkOf, bundle, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

omit [DecidableEq A] in
/-- A value over a list containing `g` is `v g` plus the value of the rest. -/
theorem value_erase {i : A} {g : G} {S : List G} (h : g ∈ S) :
    value v i S = v i g + value v i (S.erase g) := by
  unfold value
  rw [(List.perm_cons_erase h).map (v i) |>.sum_nat]
  simp

omit [DecidableEq G] in
/-- The base goods of `i` are in `i`'s bundle, so the base is worth at most the bundle. -/
theorem value_baseOf_le (hbase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i) (i : A) :
    value v i (baseOf goods base i) ≤ value v i (bundle goods X i) := by
  apply value_sublist
  unfold baseOf bundle
  have : goods.filter (fun g => base g = some i) =
      (goods.filter (fun g => X g = i)).filter (fun g => base g = some i) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro g hg
    by_cases hb : base g = some i
    · simp [hb, hbase g hg i hb]
    · simp [hb]
  rw [this]
  exact List.filter_sublist

/-! ## Theorem 1′₄ -/

/-- **The proof of Theorem 1′₄, from what it uses.** Suppose every listed agent's needs contain the goods
outside its bundle worth more to it than its bundle (`hN`), (V1) and (V2) hold, every base good is with its
base's agent, a frozen agent holds only its base, every bundle but the owner's has at most two goods, and
(OC₄) holds. Then `X` is EFX₀. -/
theorem efx0_of_needs (hg : goods.Nodup)
    (hN : ∀ i ∈ agents, ∀ g ∈ goods, X g ≠ i → value v i (bundle goods X i) < v i g → N i g)
    (hV : Valid agents goods base N) (hbase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i)
    (hfz : ∀ j ∈ agents, Frozen agents goods base N j → ∀ g ∈ goods, X g = j → base g = some j)
    (hsmall : ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2) (hoc : OC v agents goods X o) :
    EFX0L v agents goods X := by
  intro i hi j hj hij g hgj
  -- singletons are never strongly envied
  by_cases hone : (bundle goods X j).length ≤ 1
  · have hlen : ((bundle goods X j).erase g).length = 0 := by
      rw [List.length_erase_of_mem hgj]; omega
    rw [List.length_eq_zero_iff.mp hlen]; simp
  -- the owner's bundle: (OC₄)
  by_cases hjo : o = some j
  · exact hoc j hjo i hi hij g hgj
  -- otherwise `X_j` has exactly two goods, and `X_j ∖ {g}` is one good `x`
  have h2 := hsmall j hj hjo
  have hl1 : ((bundle goods X j).erase g).length = 1 := by
    rw [List.length_erase_of_mem hgj]; omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
  have hxj : x ∈ bundle goods X j := List.mem_of_mem_erase (by rw [hx]; simp)
  obtain ⟨hxg, hXx⟩ := mem_bundle.mp hxj
  -- `x` is not in `NA`: it is junk (V1), or in `j`'s base, which has two goods (V2) or is `{x}` with `j`
  -- not frozen (a frozen agent holds only its base)
  have hnotNA : ¬ NA agents N x := by
    intro hna
    cases hbx : base x with
    | none => exact hV.v1 x (mem_junk.mpr ⟨hxg, hbx⟩) hna
    | some k =>
      have hkj : k = j := (hbase x hxg k hbx).symm.trans hXx
      subst hkj
      have hxb : x ∈ baseOf goods base k := mem_baseOf.mpr ⟨hxg, hbx⟩
      by_cases hb2 : 2 ≤ (baseOf goods base k).length
      · exact hV.v2 k hb2 x hxb hna
      · have hb1 : baseOf goods base k = [x] := by
          have hnd : (baseOf goods base k).Nodup := hg.sublist List.filter_sublist
          match hB : baseOf goods base k, hnd with
          | [], _ => rw [hB] at hxb; simp at hxb
          | [y], _ => rw [hB] at hxb; simp at hxb; rw [hxb]
          | _ :: _ :: _, _ => rw [hB] at hb2; simp at hb2
        have hF : Frozen agents goods base N k := ⟨x, hb1, hna⟩
        -- a frozen agent holds only its base `{x}`
        have := length_le_one (nodup_bundle hg X k) (y := x) (fun h hh => by
          obtain ⟨hhg, hXh⟩ := mem_bundle.mp hh
          have := mem_baseOf.mpr ⟨hhg, hfz k hj hF h hhg hXh⟩
          rw [hb1] at this; simpa using this)
        omega
  -- so `i` does not need `x`, and `x` is outside `i`'s bundle: it is worth at most `X_i`
  have hxi : X x ≠ i := fun e => hij (e.symm.trans hXx)
  have hle : v i x ≤ value v i (bundle goods X i) :=
    Nat.le_of_not_lt fun hlt => hnotNA ⟨i, hi, hN i hi x hxg hxi hlt⟩
  rw [hx]; simpa using hle

omit [DecidableEq G] in
/-- Needs in the Definition's sense contain the goods outside the bundle worth more than the bundle, when
every base good is with its base's agent. -/
theorem Needs.of_bundle {i : A} (hNi : Needs v goods base N i)
    (hbase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i) :
    ∀ g ∈ goods, X g ≠ i → value v i (bundle goods X i) < v i g → N i g := fun g hg hXg hlt =>
  hNi.lower g hg (fun hb => hXg (hbase g hg i hb))
    (Nat.lt_of_le_of_lt (value_baseOf_le hbase i) hlt)

/-- In a completion, every bundle but the owner's has at most two goods: `X_j = B_j ∪ C_j`, with
`|C_j| + |B_j| ≤ 2` for a free agent and `C_j = ∅`, `|B_j| = 1` for a frozen one. -/
theorem Completion.length_le_two (hC : Completion agents goods base N o X) (hg : goods.Nodup) :
    ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  intro j hj hjo
  -- the goods of `X_j` outside the junk are exactly `j`'s base goods
  have hsplit : (bundle goods X j).length ≤
      (junkOf goods base X j).length + (baseOf goods base j).length := by
    rw [List.length_eq_countP_add_countP (fun g => base g = none) (l := bundle goods X j),
      List.countP_eq_length_filter, List.countP_eq_length_filter]
    have : ((bundle goods X j).filter (fun g => ¬ (decide (base g = none)) = true)).length ≤
        (baseOf goods base j).length := by
      apply length_le_of_subset ((nodup_bundle hg X j).sublist List.filter_sublist)
      intro g hgf
      obtain ⟨hgb, hgn⟩ := List.mem_filter.mp hgf
      obtain ⟨hgg, hXg⟩ := mem_bundle.mp hgb
      cases hb : base g with
      | none => simp [hb] at hgn
      | some k =>
        have := hC.onBase g hgg k hb
        rw [hXg] at this; subst this
        exact mem_baseOf.mpr ⟨hgg, hb⟩
    unfold junkOf
    omega
  by_cases hF : Frozen agents goods base N j
  · obtain ⟨y, hy, -⟩ := id hF
    have := hC.frozen j hj hjo hF
    rw [this, hy] at hsplit
    simp at hsplit
    omega
  · exact Nat.le_trans hsplit (hC.free j hj hjo hF)

omit [DecidableEq G] in
/-- In a completion, a frozen agent other than the owner holds only its base. -/
theorem Completion.frozen_base (hC : Completion agents goods base N o X) :
    ∀ j ∈ agents, o ≠ some j → Frozen agents goods base N j → ∀ g ∈ goods, X g = j →
      base g = some j := by
  intro j hj hjo hF g hg hXg
  cases hb : base g with
  | none =>
    have : g ∈ junkOf goods base X j := mem_junkOf.mpr ⟨hg, hXg, hb⟩
    rw [hC.frozen j hj hjo hF] at this; simp at this
  | some k => rw [← hXg, hC.onBase g hg k hb]

/-- **Theorem 1′₄ (soundness, any k), owner's needs from its base.** Let `(base, N)` be a valid
pre-allocation in which every listed agent's needs are needs in the Definition's sense, and `X` a
completion with owner `o` (or none) satisfying (OC₄). Then `X` is EFX₀, and every bundle but the
owner's has at most two goods. Only additivity is used: no bound on `|R_i|`, no balance. -/
theorem Valid.sound (hg : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods base N i)
    (hV : Valid agents goods base N) (hC : Completion agents goods base N o X)
    (hoc : OC v agents goods X o) :
    EFX0L v agents goods X ∧ ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  refine ⟨efx0_of_needs hg (fun i hi => (hNd i hi).of_bundle hC.onBase) hV hC.onBase ?_
    (hC.length_le_two hg) hoc, hC.length_le_two hg⟩
  intro j hj hF g hg' hXg
  by_cases hjo : o = some j
  · exact absurd hF ((hC.owner j hjo).2)
  · exact hC.frozen_base j hj hjo hF g hg' hXg

/-- **Theorem 1′₄ (soundness, any k), owner's needs from its bundle.** The same with the owner's needs
replaced by `N_o^X` (`ownerNeeds`), and validity, the frozen agents and the caps computed with them. The
owner's own needs from its base are not used. -/
theorem Valid.sound_ownerNeeds (hg : goods.Nodup)
    (hNd : ∀ i ∈ agents, o ≠ some i → Needs v goods base N i)
    (hV : Valid agents goods base (ownerNeeds v goods X N o))
    (hC : Completion agents goods base (ownerNeeds v goods X N o) o X)
    (hoc : OC v agents goods X o) :
    EFX0L v agents goods X ∧ ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  refine ⟨efx0_of_needs hg (N := ownerNeeds v goods X N o) (fun i hi g hg' hXg hlt => ?_) hV hC.onBase
    ?_ (hC.length_le_two hg) hoc, hC.length_le_two hg⟩
  · by_cases hio : o = some i
    · simp only [ownerNeeds, hio, ↓reduceIte]
      exact ⟨hg', hXg, hlt⟩
    · simp only [ownerNeeds, hio, ↓reduceIte]
      exact (hNd i hi hio).of_bundle hC.onBase g hg' hXg hlt
  · intro j hj hF g hg' hXg
    by_cases hjo : o = some j
    · exact absurd hF ((hC.owner j hjo).2)
    · exact hC.frozen_base j hj hjo hF g hg' hXg

omit [DecidableEq G] in
/-- Taking the owner's needs from its bundle only shrinks them: `N_o^X ⊆ N_o` for needs in the
Definition's sense, so `NA` computed with `N_o^X` is contained in `NA`. -/
theorem ownerNeeds_le (hC : ∀ g ∈ goods, ∀ i, base g = some i → X g = i)
    (hNd : ∀ i ∈ agents, Needs v goods base N i) :
    ∀ i ∈ agents, ∀ g, ownerNeeds v goods X N o i g → N i g := by
  intro i hi g hN
  by_cases hio : o = some i
  · simp only [ownerNeeds, hio, ↓reduceIte] at hN
    exact (hNd i hi).of_bundle hC g hN.1 hN.2.1 hN.2.2
  · simpa [ownerNeeds, hio] using hN

omit [DecidableEq G] in
/-- Hence (V1) and (V2) with the owner's needs from its base imply them with its needs from its bundle. -/
theorem Valid.toOwnerNeeds (hV : Valid agents goods base N)
    (hC : ∀ g ∈ goods, ∀ i, base g = some i → X g = i) (hNd : ∀ i ∈ agents, Needs v goods base N i) :
    Valid agents goods base (ownerNeeds v goods X N o) := by
  have hNA : ∀ g, NA agents (ownerNeeds v goods X N o) g → NA agents N g := fun g ⟨i, hi, h⟩ =>
    ⟨i, hi, ownerNeeds_le hC hNd i hi g h⟩
  exact ⟨fun g hg h => hV.v1 g hg (hNA g h), fun i h2 g hg h => hV.v2 i h2 g hg (hNA g h)⟩


omit [DecidableEq G] in
/-- A completion with the owner's needs from its base is one with its needs from its bundle: `NA` only
shrinks, so fewer agents are frozen, and an agent that stops being frozen had base `{y}` and no junk. -/
theorem Completion.toOwnerNeeds (hC : Completion agents goods base N o X)
    (hNd : ∀ i ∈ agents, Needs v goods base N i) :
    Completion agents goods base (ownerNeeds v goods X N o) o X := by
  have hNA : ∀ g, NA agents (ownerNeeds v goods X N o) g → NA agents N g := fun g ⟨i, hi, h⟩ =>
    ⟨i, hi, ownerNeeds_le hC.onBase hNd i hi g h⟩
  have hF : ∀ j, Frozen agents goods base (ownerNeeds v goods X N o) j → Frozen agents goods base N j :=
    fun j ⟨y, hy, hna⟩ => ⟨y, hy, hNA y hna⟩
  refine ⟨hC.alloc, hC.onBase, fun w hw => ⟨(hC.owner w hw).1, fun h => (hC.owner w hw).2 (hF w h)⟩,
    fun j hj hjo h => hC.frozen j hj hjo (hF j h), fun j hj hjo _ => ?_⟩
  by_cases hFj : Frozen agents goods base N j
  · obtain ⟨y, hy, -⟩ := id hFj
    rw [hC.frozen j hj hjo hFj, hy]; simp
  · exact hC.free j hj hjo hFj

/-! ## The needs LB₄ uses -/

omit [DecidableEq G] in
/-- The value-based needs `{g ∉ B_i : v_i(g) > v_i(B_i)}` are needs. -/
theorem Needs.valueBased (i : A) :
    Needs v goods base (fun _ g => g ∈ goods ∧ base g ≠ some i ∧ value v i (baseOf goods base i) < v i g) i :=
  ⟨fun g hg hb hlt => ⟨hg, hb, hlt⟩, fun g ⟨hg, hb, hlt⟩ => ⟨hg, by omega, hb⟩⟩

omit [DecidableEq G] in
/-- The needs of an empty base: all of `R_i`. -/
theorem Needs.empty {i : A} (h0 : baseOf goods base i = []) :
    Needs v goods base (fun _ g => g ∈ goods ∧ 0 < v i g) i := by
  refine ⟨fun g hg _ hlt => ⟨hg, by omega⟩, fun g ⟨hg, hpos⟩ => ⟨hg, hpos, fun hb => ?_⟩⟩
  have := mem_baseOf.mpr ⟨hg, hb⟩
  rw [h0] at this; simp at this

/-- `pref i` is a strict order `≻_i` consistent with `i`'s values (`k4/lb4.md` §0): it is asymmetric, and
`v_i(g) > v_i(h) > 0` implies `g ≻_i h`. (Transitivity and totality are not needed.) -/
structure RankOK (v : A → G → Nat) (pref : A → G → G → Prop) (i : A) : Prop where
  asymm : ∀ g h, pref i g h → ¬ pref i h g
  consistent : ∀ g h, 0 < v i h → v i h < v i g → pref i g h

/-- The needs of a pick `y`: the goods of `R_i` ranked above `y`. -/
def pickNeeds (v : A → G → Nat) (goods : List G) (pref : A → G → G → Prop) (y : G) (i : A) (g : G) :
    Prop :=
  g ∈ goods ∧ 0 < v i g ∧ pref i g y

omit [DecidableEq G] in
/-- The needs of a pick are needs, for a relevant pick and a ranking consistent with the values. -/
theorem Needs.pick {pref : A → G → G → Prop} {i : A} {y : G} (hB : baseOf goods base i = [y])
    (hy : 0 < v i y) (hR : RankOK v pref i) :
    Needs v goods base (fun _ => pickNeeds v goods pref y i) i := by
  refine ⟨fun g hg _ hlt => ?_, fun g ⟨hg, hpos, hpref⟩ => ⟨hg, hpos, fun hb => ?_⟩⟩
  · rw [hB] at hlt
    simp only [value_cons, value_nil, Nat.add_zero] at hlt
    exact ⟨hg, by omega, hR.consistent g y hy hlt⟩
  · have := mem_baseOf.mpr ⟨hg, hb⟩
    rw [hB, List.mem_singleton] at this
    subst this
    exact hR.asymm g g hpref hpref

/-! ## The D2 shape and the chain to K4.D -/

/-- What every allocation LB₄ returns is (`k4/lb4.md` §2): a completion `X` with owner `o` (or none) of a
pre-allocation `(base, N)` whose non-owner agents have needs in the Definition's sense, valid and
completed with the owner's needs from its bundle, satisfying (OC₄). (With the owner's needs from its base
instead, `SoundCompletion.of_baseNeeds`.) -/
structure SoundCompletion (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A)
    (N : A → G → Prop) (o : Option A) (X : G → A) : Prop where
  needs : ∀ i ∈ agents, o ≠ some i → Needs v goods base N i
  valid : Valid agents goods base (ownerNeeds v goods X N o)
  completion : Completion agents goods base (ownerNeeds v goods X N o) o X
  oc : OC v agents goods X o

/-- The version with the owner's needs from its base is a special case. -/
theorem SoundCompletion.of_baseNeeds (hNd : ∀ i ∈ agents, Needs v goods base N i)
    (hV : Valid agents goods base N) (hC : Completion agents goods base N o X)
    (hoc : OC v agents goods X o) : SoundCompletion v agents goods base N o X :=
  ⟨fun i hi _ => hNd i hi, hV.toOwnerNeeds hC.onBase hNd, hC.toOwnerNeeds hNd, hoc⟩

/-- **The D2 shape, over lists.** A sound completion is a complete EFX₀ allocation of `goods` to
`agents` with at most one bundle of more than two goods (the owner's, or any agent's if there is no
owner). -/
theorem SoundCompletion.efx0_d2 (hS : SoundCompletion v agents goods base N o X) (hg : goods.Nodup)
    (hne : agents ≠ []) :
    IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ w ∈ agents, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 := by
  obtain ⟨hE, hlen⟩ := Valid.sound_ownerNeeds hg hS.needs hS.valid hS.completion hS.oc
  refine ⟨hS.completion.alloc, hE, ?_⟩
  cases ho : o with
  | some w =>
    exact ⟨w, (hS.completion.owner w ho).1, fun j hj hjw => hlen j hj (by rw [ho]; simpa using Ne.symm hjw)⟩
  | none =>
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil agents hne
    exact ⟨w, hw, fun j hj _ => hlen j hj (by rw [ho]; simp)⟩

/-- **Theorem 1′₄ in the model's terms.** A sound completion of an instance (agents `Fin n`, goods
`Fin m`) is EFX₀, and every bundle but the owner's has at most two goods. -/
theorem sound_model (I : Inst) {base : Fin I.m → Option (Fin I.n)} {N : Fin I.n → Fin I.m → Prop}
    {o : Option (Fin I.n)} {X : I.Alloc}
    (hS : SoundCompletion I.v (List.finRange I.n) (List.finRange I.m) base N o X) :
    I.EFX0 X ∧ ∀ j, o ≠ some j → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨hE, hlen⟩ := Valid.sound_ownerNeeds (List.nodup_finRange I.m) hS.needs hS.valid hS.completion hS.oc
  refine ⟨(Inst.efx0_iff I X).mpr hE, fun j hj => ?_⟩
  rw [LB.finSum_bundle_eq]
  exact hlen j (List.mem_finRange j) hj

/-- **The D2 shape, in the model's terms.** If every bundle except the owner's (if any) has at most two
goods, then at most one bundle has more than two goods. -/
theorem d2_shape (I : Inst) (hn : 0 < I.n) {X : I.Alloc} {o : Option (Fin I.n)}
    (h : ∀ j, o ≠ some j → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2) :
    ∃ w, ∀ j, j ≠ w → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  cases o with
  | some w => exact ⟨w, fun j hj => h j (by simpa using Ne.symm hj)⟩
  | none => exact ⟨⟨0, hn⟩, fun j _ => h j (by simp)⟩

/-- **LB₄ never fails ⟹ K4.D, for one instance.** If an instance with at least one agent has a sound
completion (every allocation LB₄ returns is one), it has an EFX₀ allocation with at most one bundle of
more than two goods: the conclusion of conjecture K4.D (and of `EFX.LB.corollaryD` at k = 3). -/
theorem k4D_of_completion (I : Inst) (hn : 0 < I.n)
    (h : ∃ (base : Fin I.m → Option (Fin I.n)) (N : Fin I.n → Fin I.m → Prop) (o : Option (Fin I.n))
      (X : I.Alloc), SoundCompletion I.v (List.finRange I.n) (List.finRange I.m) base N o X) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ w, ∀ j, j ≠ w → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨base, N, o, X, hS⟩ := h
  obtain ⟨hE, hlen⟩ := sound_model I hS
  exact ⟨X, hE, d2_shape I hn hlen⟩

/-- **LB₄ never fails ⟹ TARGET₄ (up to `Nn` agents).** With K4.CORE and K4.TIE
(`EFX.target4_of_strict_cores`): if every connected strict k = 4 core with at most `Nn` agents and a 4-good
agent has a sound completion (which LB₄ never failing on it would give), every instance with at most `Nn`
agents and at most four relevant goods per agent has an EFX₀ allocation. -/
theorem target4_of_completions (I : Inst) (hn : 0 < I.n) (Nn : Nat) (hN : I.n ≤ Nn)
    (hcore : ∀ (w : Fin I.n → Fin I.m → Nat) (agents : List (Fin I.n)) (goods : List (Fin I.m)),
      agents.Nodup → goods.Nodup → agents.length ≤ Nn → IsCore4 w agents goods →
      Connected w agents goods → Strict w agents goods → (∃ i ∈ agents, (relevant w i goods).length = 4) →
      ∃ (base : Fin I.m → Option (Fin I.n)) (N : Fin I.n → Fin I.m → Prop) (o : Option (Fin I.n))
        (X : Fin I.m → Fin I.n), SoundCompletion w agents goods base N o X)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn Nn hN (fun w agents goods hag hgd hl hc hconn hs h4 => by
    obtain ⟨base, N, o, X, hS⟩ := hcore w agents goods hag hgd hl hc hconn hs h4
    exact ⟨X, hS.completion.alloc,
      (Valid.sound_ownerNeeds hgd hS.needs hS.valid hS.completion hS.oc).1⟩) h


/-! ## Counting (`k4/lb4.md` §1, "Counting (any k)") -/

section counting

/-- Double counting: summing, over the agents, the number of goods related to each agent is summing,
over the goods, the number of agents related to each good. -/
theorem sum_countP_comm {α β : Type} (p : α → β → Bool) (as : List α) :
    ∀ gs : List β, (as.map (fun i => gs.countP (p i))).sum = (gs.map (fun g => as.countP (fun i => p i g))).sum
  | [] => by induction as <;> simp_all
  | g :: gs => by
    have ih := sum_countP_comm p as gs
    have e : ∀ bs : List α, (bs.map (fun i => (g :: gs).countP (p i))).sum =
        (bs.map (fun i => gs.countP (p i))).sum + bs.countP (fun i => p i g) := by
      intro bs
      induction bs with
      | nil => simp
      | cons b bs ihb =>
        have h1 : (g :: gs).countP (p b) = gs.countP (p b) + (if p b g then 1 else 0) := List.countP_cons
        have h2 : (b :: bs).countP (fun i => p i g) = bs.countP (fun i => p i g) + (if p b g then 1 else 0) :=
          List.countP_cons
        simp only [List.map_cons, List.sum_cons]
        rw [ihb, h1, h2]
        omega
    rw [e, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

omit [DecidableEq G] in
/-- In a list of distinct agents that contains every base's agent, exactly one agent (none) has `g` in its
base if `g` is (not) in a base. -/
theorem countP_base (as : List A) (has : as.Nodup) {b : Option A} (hb : ∀ k, b = some k → k ∈ as) :
    as.countP (fun i => decide (b = some i)) = if b = none then 0 else 1 := by
  cases b with
  | none => simp
  | some k =>
    have hk := hb k rfl
    simp only [reduceCtorEq, ↓reduceIte, Option.some.injEq]
    induction as with
    | nil => simp at hk
    | cons a as ih =>
      rw [List.countP_cons]
      obtain ⟨ha, has'⟩ := List.nodup_cons.mp has
      by_cases hka : k = a
      · subst hka
        have : as.countP (fun i => decide (k = i)) = 0 :=
          List.countP_eq_zero.mpr fun i hi hki => ha (by simp at hki; exact hki ▸ hi)
        simp [this]
      · have := ih has' (fun k' hk' => by cases hk'; exact (List.mem_cons.mp hk).resolve_left hka)
          ((List.mem_cons.mp hk).resolve_left hka)
        simp [hka, this]

/-- A sum over distinct agents in which every term but `w`'s vanishes is `w`'s term. -/
theorem sum_single (f : A → Int) {w : A} :
    ∀ {as : List A}, as.Nodup → w ∈ as → (∀ j ∈ as, j ≠ w → f j = 0) → (as.map f).sum = f w
  | [], _, hw, _ => by simp at hw
  | a :: as, has, hw, h0 => by
    obtain ⟨ha, has'⟩ := List.nodup_cons.mp has
    simp only [List.map_cons, List.sum_cons]
    by_cases haw : a = w
    · subst haw
      have : (as.map f).sum = 0 := by
        have : ∀ bs : List A, (∀ j ∈ bs, f j = 0) → (bs.map f).sum = 0 := by
          intro bs hbs
          induction bs with
          | nil => simp
          | cons b bs ih =>
            simp only [List.map_cons, List.sum_cons, hbs b (by simp),
              ih (fun j hj => hbs j (by simp [hj]))]
            simp
        exact this as (fun j hj => h0 j (by simp [hj]) (fun e => ha (e ▸ hj)))
      rw [this]; simp
    · rw [h0 a (by simp) haw, sum_single f has' ((List.mem_cons.mp hw).resolve_left (Ne.symm haw))
        (fun j hj hjw => h0 j (by simp [hj]) hjw)]
      simp

open Classical in
/-- `cap(i)`, counted with its sign: `0` for a frozen agent, `2 − |B_i|` for a free one (negative for a base
of three or more goods). -/
noncomputable def cap (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) (i : A) :
    Int :=
  if Frozen agents goods base N i then 0 else 2 - ((baseOf goods base i).length : Int)

/-- `S = Σ_i cap(i)`. -/
noncomputable def capSum (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) :
    Int :=
  (agents.map (cap agents goods base N)).sum

open Classical in
/-- `|NA|`: the number of goods (of `goods`) that some listed agent needs. -/
noncomputable def numNA (agents : List A) (goods : List G) (N : A → G → Prop) : Nat :=
  goods.countP (fun g => decide (NA agents N g))

open Classical in
/-- `|F|`: the number of frozen listed agents. -/
noncomputable def numFrozen (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) :
    Nat :=
  agents.countP (fun j => decide (Frozen agents goods base N j))

omit [DecidableEq G] in
open Classical in
/-- In a valid pre-allocation, an agent is frozen iff exactly one of its base goods is in `NA` (and
otherwise none is). -/
theorem frozen_count (hV : Valid agents goods base N) (hg : goods.Nodup) (j : A) :
    (if Frozen agents goods base N j then 1 else 0) =
      goods.countP (fun g => decide (base g = some j) && decide (NA agents N g)) := by
  have e : goods.countP (fun g => decide (base g = some j) && decide (NA agents N g)) =
      (baseOf goods base j).countP (fun g => decide (NA agents N g)) := by
    rw [baseOf, List.countP_filter]
    apply List.countP_congr
    intro g _
    simp [Bool.and_comm]
  rw [e]
  have hnd : (baseOf goods base j).Nodup := hg.sublist List.filter_sublist
  by_cases hF : Frozen agents goods base N j
  · obtain ⟨y, hy, hna⟩ := id hF
    simp only [hF, ↓reduceIte]
    rw [hy]; simp [hna]
  · simp only [hF, ↓reduceIte]
    symm
    apply List.countP_eq_zero.mpr
    intro g hg' hna
    simp only [decide_eq_true_eq] at hna
    by_cases h2 : 2 ≤ (baseOf goods base j).length
    · exact hV.v2 j h2 g hg' hna
    · apply hF
      refine ⟨g, ?_, hna⟩
      match hB : baseOf goods base j, hnd with
      | [], _ => rw [hB] at hg'; simp at hg'
      | [y], _ => rw [hB] at hg'; simp at hg'; rw [hg']
      | _ :: _ :: _, _ => rw [hB] at h2; simp at h2

/-- A count is a sum of indicators. -/
theorem countP_eq_sum {α : Type} (p : α → Bool) :
    ∀ l : List α, l.countP p = (l.map (fun a => if p a then 1 else 0)).sum
  | [] => by simp
  | a :: l => by rw [List.countP_cons, countP_eq_sum p l]; simp; omega

omit [DecidableEq G] in
/-- **`|F| = |NA|`.** In a valid pre-allocation every good of `NA` is the whole base of exactly one agent,
which is frozen, and every frozen agent's base is one good of `NA`. -/
theorem numFrozen_eq (hV : Valid agents goods base N) (hag : agents.Nodup) (hg : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) :
    numFrozen agents goods base N = numNA agents goods N := by
  classical
  unfold numFrozen numNA
  rw [countP_eq_sum, countP_eq_sum]
  have e1 : (agents.map (fun j => if decide (Frozen agents goods base N j) = true then 1 else 0)) =
      agents.map (fun j => goods.countP (fun g => decide (base g = some j) && decide (NA agents N g))) := by
    apply List.map_congr_left
    intro j _
    rw [← frozen_count hV hg j]
    simp
  rw [e1, sum_countP_comm (fun j g => decide (base g = some j) && decide (NA agents N g)) agents goods]
  congr 1
  apply List.map_congr_left
  intro g hgg
  by_cases hna : NA agents N g
  · have hb : base g ≠ none := fun hb => hV.v1 g (mem_junk.mpr ⟨hgg, hb⟩) hna
    have := countP_base agents hag (b := base g) (hmem g hgg)
    simp only [hb, ↓reduceIte] at this
    simp only [hna, decide_true, Bool.and_true, ↓reduceIte]
    exact this
  · simp [hna]

/-- Sums of integer differences. -/
theorem sum_map_sub_int {α : Type} (f h : α → Int) :
    ∀ l : List α, (l.map (fun a => f a - h a)).sum = (l.map f).sum - (l.map h).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_sub_int f h l]; omega

theorem sum_map_two {α : Type} : ∀ l : List α, (l.map (fun _ => (2 : Int))).sum = 2 * (l.length : Int)
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_two l]; omega

theorem sum_map_cast {α : Type} (f : α → Nat) :
    ∀ l : List α, (l.map (fun a => (f a : Int))).sum = ((l.map f).sum : Nat)
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_cast f l]; omega

omit [DecidableEq G] in
/-- The goods are the junk and the bases: `m = |J| + Σ_i |B_i|`. -/
theorem length_goods (hag : agents.Nodup) (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) :
    goods.length = (junk goods base).length + (agents.map (fun i => (baseOf goods base i).length)).sum := by
  have e : (agents.map (fun i => (baseOf goods base i).length)) =
      agents.map (fun i => goods.countP (fun g => decide (base g = some i))) := by
    apply List.map_congr_left
    intro i _
    rw [baseOf, List.countP_eq_length_filter]
  rw [e, sum_countP_comm (fun i g => decide (base g = some i)) agents goods]
  have e2 : (goods.map (fun g => agents.countP (fun i => decide (base g = some i)))) =
      goods.map (fun g => if decide (base g = none) = true then 0 else 1) := by
    apply List.map_congr_left
    intro g hg
    rw [countP_base agents hag (hmem g hg)]
    simp
  rw [e2, List.length_eq_countP_add_countP (fun g => decide (base g = none)), junk,
    List.countP_eq_length_filter, countP_eq_sum]
  have e3 : ∀ l : List G, (l.map (fun g => if decide (base g = none) = true then 0 else 1)).sum =
      (l.map (fun g => if (decide ¬ (decide (base g = none)) = true) = true then 1 else 0)).sum := by
    intro l
    congr 1
    apply List.map_congr_left
    intro g _
    by_cases hb : base g = none <;> simp [hb]
  rw [e3]

omit [DecidableEq G] in
open Classical in
/-- `cap(i) = 2 − |B_i| − [i frozen]`: a frozen agent has a base of one good. -/
theorem cap_eq (i : A) :
    cap agents goods base N i =
      2 - ((baseOf goods base i).length : Int) - ((if Frozen agents goods base N i then 1 else 0 : Nat) : Int) := by
  unfold cap
  by_cases hF : Frozen agents goods base N i
  · obtain ⟨y, hy, -⟩ := id hF
    simp only [hF, ↓reduceIte, hy]
    simp
  · simp [hF]

omit [DecidableEq G] in
/-- **Counting (any k).** With `cap(i) = 2 − |B_i|` counted with its sign (0 for frozen agents),
`S = Σ cap(i)` and `ω = |J| − S`: `ω = |NA| − σ`, where `σ = 2n − m` (`n` agents, `m` goods). -/
theorem omega_eq (hV : Valid agents goods base N) (hag : agents.Nodup) (hg : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) :
    ((junk goods base).length : Int) - capSum agents goods base N =
      (numNA agents goods N : Int) - (2 * (agents.length : Int) - (goods.length : Int)) := by
  classical
  have hm := length_goods (base := base) hag hmem
  have hF := numFrozen_eq hV hag hg hmem
  have hS : capSum agents goods base N = 2 * (agents.length : Int) -
      (((agents.map (fun i => (baseOf goods base i).length)).sum : Nat) : Int) -
      ((numFrozen agents goods base N : Nat) : Int) := by
    unfold capSum
    rw [List.map_congr_left (fun i _ => cap_eq (agents := agents) (goods := goods) (base := base) (N := N) i)]
    rw [sum_map_sub_int, sum_map_sub_int, sum_map_cast, sum_map_cast]
    unfold numFrozen
    rw [countP_eq_sum]
    rw [sum_map_two]
    have e : (agents.map (fun j => if Frozen agents goods base N j then 1 else 0)) =
        agents.map (fun j => if decide (Frozen agents goods base N j) = true then 1 else 0) := by
      apply List.map_congr_left; intro j _; simp
    rw [e]
  rw [hS, hF, hm]
  push_cast
  omega

omit [DecidableEq G] in
/-- In a completion, `|X_j| = |C_j| + |B_j|`. -/
theorem Completion.length_eq (hC : Completion agents goods base N o X) (j : A) :
    (bundle goods X j).length = (junkOf goods base X j).length + (baseOf goods base j).length := by
  rw [List.length_eq_countP_add_countP (fun g => base g = none) (l := bundle goods X j), junkOf,
    ← List.countP_eq_length_filter]
  congr 1
  rw [bundle, List.countP_filter, baseOf, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨hb, hX⟩
    cases hbg : base g with
    | none => exact absurd hbg hb
    | some k => rw [← hX, hC.onBase g hg k hbg]
  · intro hb
    exact ⟨by rw [hb]; simp, hC.onBase g hg j hb⟩

omit [DecidableEq G] in
/-- The junk is split among the listed agents: `|J| = Σ_j |C_j|`. -/
theorem Completion.junk_length (hC : Completion agents goods base N o X) (hag : agents.Nodup) :
    (junk goods base).length = (agents.map (fun j => (junkOf goods base X j).length)).sum := by
  have e : agents.map (fun j => (junkOf goods base X j).length) =
      agents.map (fun j => goods.countP (fun g => decide (X g = j) && decide (base g = none))) := by
    apply List.map_congr_left
    intro j _
    rw [junkOf, bundle, List.filter_filter, ← List.countP_eq_length_filter]
    apply List.countP_congr
    intro g _
    simp [And.comm]
  rw [e, sum_countP_comm (fun j g => decide (X g = j) && decide (base g = none)) agents goods, junk,
    ← List.countP_eq_length_filter, countP_eq_sum]
  congr 1
  apply List.map_congr_left
  intro g hg
  have hX := countP_base agents hag (b := some (X g)) (fun k hk => by cases hk; exact hC.alloc g hg)
  by_cases hb : base g = none
  · simp only [hb, decide_true, Bool.and_true, ↓reduceIte]
    simp only [reduceCtorEq, ↓reduceIte, Option.some.injEq] at hX
    exact hX.symm
  · simp [hb]

omit [DecidableEq G] in
open Classical in
/-- **The owner's bundle.** In a completion with a free owner `w` in which every other agent's slots are
filled (every free `j ≠ w` gets exactly `cap(j) = 2 − |B_j|` junk goods), the owner gets
`|X_w| = |B_w| + cap(w) + ω = ω + 2` goods, `ω = |J| − S`. -/
theorem Completion.owner_length {w : A} (hC : Completion agents goods base N (some w) X)
    (hag : agents.Nodup)
    (hfill : ∀ j ∈ agents, j ≠ w → ¬ Frozen agents goods base N j →
      (junkOf goods base X j).length + (baseOf goods base j).length = 2) :
    ((bundle goods X w).length : Int) = ((junk goods base).length : Int) - capSum agents goods base N + 2 := by
  have hw := hC.owner w rfl
  have hJ := hC.junk_length hag
  have hsum : (agents.map (fun j => ((junkOf goods base X j).length : Int) - cap agents goods base N j)).sum =
      ((junkOf goods base X w).length : Int) - cap agents goods base N w := by
    apply sum_single (fun j => ((junkOf goods base X j).length : Int) - cap agents goods base N j) hag hw.1
    intro j hj hjw
    have hjo : some w ≠ some j := fun e => hjw (Option.some.inj e).symm
    by_cases hF : Frozen agents goods base N j
    · rw [hC.frozen j hj hjo hF]; unfold cap; simp [hF]
    · have := hfill j hj hjw hF
      unfold cap; simp only [hF, ↓reduceIte]; omega
  rw [sum_map_sub_int, sum_map_cast] at hsum
  have hcw : cap agents goods base N w = 2 - ((baseOf goods base w).length : Int) := by
    unfold cap; simp [hw.2]
  rw [hC.length_eq w, hJ]
  unfold capSum
  omega

end counting

/-! ## Lemma 2₄ (self-protection) -/

section selfProtect

omit [DecidableEq A] [DecidableEq G] in
/-- Irrelevant goods add nothing: a value is the value of the relevant part. -/
theorem value_filter_pos (i : A) : ∀ S : List G, value v i S = value v i (S.filter (fun g => 0 < v i g))
  | [] => by simp
  | g :: S => by
    rw [value_cons, value_filter_pos i S]
    by_cases hg : 0 < v i g
    · simp [hg]
    · simp [hg]; omega

omit [DecidableEq A] in
/-- Two distinct goods of a bundle are worth together at most the bundle. -/
theorem two_le_value {i : A} {y t : G} {S : List G} (hy : y ∈ S) (ht : t ∈ S) (hyt : y ≠ t) :
    v i y + v i t ≤ value v i S := by
  rw [value_erase (v := v) (i := i) hy]
  have := le_value_of_mem v i ((List.mem_erase_of_ne (Ne.symm hyt)).mpr ht)
  omega

omit [DecidableEq A] in
/-- **Lemma 2₄, its core (values only).** Let `x` value at most four goods of `goods`, hold `y` with
`v_x(y) > 0`, and let `Xo` be a bundle disjoint from `x`'s in which every good is worth at most `v_x(y)` to
`x`. Suppose every good of `Xo` that `x` values lies in `Bo` (at most one good) or in `U`, and either `x`
values no good of `U`, or `x` also holds a good `t ≠ y` it values, worth at least every good of `U`.
Then `x` does not envy `Xo`. -/
theorem selfProtect_core {x : A} {Xx Xo Bo U : List G} {y : G}
    (hR : (relevant v x goods).length ≤ 4)
    (hXo : Xo.Nodup) (hXog : ∀ g ∈ Xo, g ∈ goods) (hdisj : ∀ g ∈ Xo, g ∉ Xx)
    (hy : y ∈ Xx) (hyg : y ∈ goods) (hypos : 0 < v x y) (hbelow : ∀ g ∈ Xo, v x g ≤ v x y)
    (hBo : Bo.length ≤ 1) (hcov : ∀ g ∈ Xo, 0 < v x g → g ∈ Bo ∨ g ∈ U)
    (hslot : (∀ g ∈ U, v x g = 0) ∨
      ∃ t ∈ Xx, t ≠ y ∧ t ∈ goods ∧ 0 < v x t ∧ ∀ g ∈ U, v x g ≤ v x t) :
    value v x Xo ≤ value v x Xx := by
  have hyX : v x y ≤ value v x Xx := le_value_of_mem v x hy
  -- `L`: the goods of `Xo` that `x` values
  rw [value_filter_pos (v := v) x Xo]
  have hL : (Xo.filter (fun g => 0 < v x g)).Nodup := hXo.sublist List.filter_sublist
  have hLmem : ∀ g ∈ Xo.filter (fun g => 0 < v x g), g ∈ Xo ∧ 0 < v x g := fun g hg' => by
    simpa using List.mem_filter.mp hg'
  -- a list of at most one such good is worth at most `v_x(y)`
  have hone : (Xo.filter (fun g => 0 < v x g)).length ≤ 1 →
      value v x (Xo.filter (fun g => 0 < v x g)) ≤ value v x Xx := by
    intro h1
    match hLe : Xo.filter (fun g => 0 < v x g), h1 with
    | [], _ => simp
    | [p], _ =>
      have hp := (hLmem p (by rw [hLe]; simp)).1
      simp only [value_cons, value_nil, Nat.add_zero]
      exact Nat.le_trans (hbelow p hp) hyX
  rcases hslot with hU0 | ⟨t, ht, hty, htg, htpos, htmax⟩
  · -- `x` values nothing in `U`: its valued goods of `Xo` are in `Bo`
    apply hone
    refine Nat.le_trans (length_le_of_subset hL fun g hg' => ?_) hBo
    obtain ⟨hgXo, hgpos⟩ := hLmem g hg'
    rcases hcov g hgXo hgpos with h | h
    · exact h
    · have := hU0 g h; omega
  · -- `x` holds `y` and `t`; at most two of its (at most four) valued goods remain for `Xo`
    have hlen : (Xo.filter (fun g => 0 < v x g)).length + 2 ≤ 4 := by
      have hnd : (y :: t :: Xo.filter (fun g => 0 < v x g)).Nodup := by
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hL⟩⟩
        · intro hm
          rcases List.mem_cons.mp hm with e | hm
          · exact hty e.symm
          · exact hdisj y (hLmem y hm).1 hy
        · intro hm; exact hdisj t (hLmem t hm).1 ht
      have := length_le_of_subset hnd (T := relevant v x goods) (fun g hg' => by
        unfold relevant
        rcases List.mem_cons.mp hg' with rfl | hg'
        · simpa using ⟨hyg, hypos⟩
        rcases List.mem_cons.mp hg' with rfl | hg'
        · simpa using ⟨htg, htpos⟩
        · obtain ⟨hgXo, hgpos⟩ := hLmem g hg'
          simpa using ⟨hXog g hgXo, hgpos⟩)
      simp only [List.length_cons] at this
      omega
    by_cases h1 : (Xo.filter (fun g => 0 < v x g)).length ≤ 1
    · exact hone h1
    -- two goods `p`, `q`: not both in `Bo`, so one is in `U` and worth at most `t`
    have hyt := two_le_value (v := v) (i := x) hy ht (Ne.symm hty)
    match hLe : Xo.filter (fun g => 0 < v x g), hlen, h1, hL with
    | [], _, h1, _ => simp at h1
    | [_], _, h1, _ => simp at h1
    | _ :: _ :: _ :: _, hlen, _, _ => simp at hlen
    | [p, q], _, _, hpq =>
      have hp := hLmem p (by rw [hLe]; simp)
      have hq := hLmem q (by rw [hLe]; simp)
      have hpq' : p ≠ q := by simp at hpq; exact hpq
      simp only [value_cons, value_nil, Nat.add_zero]
      have hbp := hbelow p hp.1
      have hbq := hbelow q hq.1
      rcases hcov p hp.1 hp.2 with hpB | hpU
      · rcases hcov q hq.1 hq.2 with hqB | hqU
        · have := length_le_of_subset (S := [p, q]) (by simp [hpq']) (fun g hg' => by
            rcases List.mem_cons.mp hg' with rfl | hg'
            · exact hpB
            · simp at hg'; rw [hg']; exact hqB)
          simp at this; omega
        · have := htmax q hqU; omega
      · have := htmax p hpU; omega

/-- **Lemma 2₄ (self-protection, `|R_x| ≤ 4`).** Let `(base, N)` be a valid pre-allocation (`N` the needs
used, so the owner's may be `N_o^X`) and `X` a completion with owner `w` whose base has at most one good.
Let `x ≠ w` be a listed agent with at most four relevant goods whose base is a pick `{y}` it values, and
whose needs contain the goods it ranks above `y` (its needs are those of a pick, for a strict order `≻_x`
consistent with its values). Let `U` be the junk not yet placed when `x` fills its slot: it contains every
junk good that ends in the owner's bundle (goods placed earlier went into other agents' slots, goods placed
later only leave the owner's bundle). Suppose `x` takes its `≻_x`-best good of `U` it values, if there is
one. Then `x` does not envy the owner's bundle; in particular it is not threatened by it. -/
theorem selfProtect {w : A} (hV : Valid agents goods base N)
    (hC : Completion agents goods base N (some w) X) (hBo : (baseOf goods base w).length ≤ 1)
    {x : A} (hx : x ∈ agents) (hxw : x ≠ w) (hR : (relevant v x goods).length ≤ 4)
    {y : G} (hBx : baseOf goods base x = [y]) (hy : 0 < v x y)
    {pref : A → G → G → Prop} (hrank : RankOK v pref x)
    (hNx : ∀ g, pickNeeds v goods pref y x g → N x g)
    {U : List G} (hUJ : ∀ g ∈ U, g ∈ junk goods base)
    (hU : ∀ g ∈ junk goods base, X g = w → g ∈ U)
    (hslot : (∃ g ∈ U, 0 < v x g) →
      ∃ t ∈ U, X t = x ∧ 0 < v x t ∧ ∀ g ∈ U, 0 < v x g → g ≠ t → pref x t g) (hg : goods.Nodup) :
    value v x (bundle goods X w) ≤ value v x (bundle goods X x) ∧
      ∀ h ∈ bundle goods X w, value v x ((bundle goods X w).erase h) ≤ value v x (bundle goods X x) := by
  have hyb : y ∈ baseOf goods base x := by rw [hBx]; simp
  obtain ⟨hyg, hby⟩ := mem_baseOf.mp hyb
  have hyX : y ∈ bundle goods X x := mem_bundle.mpr ⟨hyg, hC.onBase y hyg x hby⟩
  -- a good of the owner's bundle is junk or the owner's base good
  have hsrc : ∀ g ∈ bundle goods X w, g ∈ junk goods base ∨ g ∈ baseOf goods base w := by
    intro g hgb
    obtain ⟨hgg, hXg⟩ := mem_bundle.mp hgb
    cases hb : base g with
    | none => exact Or.inl (mem_junk.mpr ⟨hgg, hb⟩)
    | some k =>
      have := hC.onBase g hgg k hb
      rw [hXg] at this; subst this
      exact Or.inr (mem_baseOf.mpr ⟨hgg, hb⟩)
  -- no good of the owner's bundle is in `NA`: not junk (V1), and the owner's base good would freeze it
  have hnotNA : ∀ g ∈ bundle goods X w, ¬ NA agents N g := by
    intro g hgb hna
    rcases hsrc g hgb with hJ | hB
    · exact hV.v1 g hJ hna
    · have hB1 : baseOf goods base w = [g] := by
        match hB' : baseOf goods base w, hBo with
        | [], _ => rw [hB'] at hB; simp at hB
        | [z], _ => rw [hB'] at hB; simp at hB; rw [hB]
      exact (hC.owner w rfl).2 ⟨g, hB1, hna⟩
  have hmain : value v x (bundle goods X w) ≤ value v x (bundle goods X x) := by
    refine selfProtect_core (Bo := baseOf goods base w) (U := U) hR (nodup_bundle hg X w)
      (fun g hgb => (mem_bundle.mp hgb).1) (fun g hgw hgx => hxw ((mem_bundle.mp hgx).2.symm.trans
        (mem_bundle.mp hgw).2)) hyX hyg hy (fun g hgb => ?_) hBo (fun g hgb hpos => ?_) ?_
    · -- the goods `x` ranks above `y` are in `NA`, so not in the owner's bundle
      refine Nat.le_of_not_lt fun hlt => hnotNA g hgb ⟨x, hx, hNx g ⟨(mem_bundle.mp hgb).1, ?_, ?_⟩⟩
      · omega
      · exact hrank.consistent g y hy hlt
    · rcases hsrc g hgb with hJ | hB
      · exact Or.inr (hU g hJ (mem_bundle.mp hgb).2)
      · exact Or.inl hB
    · by_cases hex : ∃ g ∈ U, 0 < v x g
      · obtain ⟨t, htU, hXt, htpos, hbest⟩ := hslot hex
        obtain ⟨htg, hbt⟩ := mem_junk.mp (hUJ t htU)
        refine Or.inr ⟨t, mem_bundle.mpr ⟨htg, hXt⟩, fun e => ?_, htg, htpos, fun g hgU => ?_⟩
        · rw [e, hby] at hbt; cases hbt
        · by_cases hgpos : 0 < v x g
          · by_cases hgt : g = t
            · rw [hgt]; exact Nat.le_refl _
            · exact Nat.le_of_not_lt fun hlt =>
                hrank.asymm t g (hbest g hgU hgpos hgt) (hrank.consistent g t htpos hlt)
          · omega
      · exact Or.inl fun g hgU => Nat.eq_zero_of_not_pos fun hpos => hex ⟨g, hgU, hpos⟩
  exact ⟨hmain, fun h _ => Nat.le_trans (value_sublist v x List.erase_sublist) hmain⟩

/-- `|R_x| ≤ 4` is needed in Lemma 2₄ (`k4/lb4.md` §1): `x` values goods `0, …, 4` at `10, 9, 8, 7, 6` and
good `5` at `0`, holds `{0, 1}` (its pick `0` and its best junk good `1`), and the owner holds
`{2, 3, 4, 5}`. The other hypotheses of `selfProtect_core` hold (`Bo = []`, `U = [2, 3, 4, 5]`, `t = 1`:
every good of the owner's bundle is worth at most `x`'s pick and at most `t`), `x` values five goods, and
`x` is threatened: without good `5` the owner's bundle is worth `21 > 19`. -/
theorem selfProtect_five :
    let v : Unit → Fin 6 → Nat := fun _ g => if g.val < 5 then 10 - g.val else 0
    (relevant v () (List.finRange 6)).length = 5 ∧
      (∀ g ∈ ([2, 3, 4, 5] : List (Fin 6)), v () g ≤ v () 0 ∧ v () g ≤ v () 1) ∧
      value v () [0, 1] < value v () (([2, 3, 4, 5] : List (Fin 6)).erase 5) := by
  decide

end selfProtect

end LB4
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4.efx0_of_needs
#print axioms EFX.LB4.Valid.sound
#print axioms EFX.LB4.Valid.sound_ownerNeeds
#print axioms EFX.LB4.Completion.length_le_two
#print axioms EFX.LB4.Needs.pick
#print axioms EFX.LB4.SoundCompletion.of_baseNeeds
#print axioms EFX.LB4.SoundCompletion.efx0_d2
#print axioms EFX.LB4.sound_model
#print axioms EFX.LB4.d2_shape
#print axioms EFX.LB4.k4D_of_completion
#print axioms EFX.LB4.target4_of_completions
#print axioms EFX.LB4.numFrozen_eq
#print axioms EFX.LB4.omega_eq
#print axioms EFX.LB4.selfProtect_core
#print axioms EFX.LB4.selfProtect
#print axioms EFX.LB4.Completion.owner_length
#print axioms EFX.LB4.selfProtect_five
