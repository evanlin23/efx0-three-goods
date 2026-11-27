import EFX.SDE
import EFX.T6

/-!
# Theorem REC-S: the two-move proof skeleton (`k4/oc1max_multi.md` §8, §12)

Theorem REC-S (K4.MULTI.RECS, `proof/k4-oc1max-multi`; refereed CORRECT, `k4/referee/oc1max_multi.md` §11) proves
OC₂ at a perfect start by two moves:
1. the earliest-wanter chain `E(k)`, in which `k` takes an improving set `T` of at most two goods from `J ∪ {Y_z}`;
2. one move `P′` of the smaller instance `I⁻` (without `k` and `T`), from its perfect serial-dictatorship start
   (Lemma SD-E), followed by a completion `X⁻` of `I⁻` in which no bundle threatens `k` at `v_k(T)` ((K));
and Lemma LIFT lifts `P′` and `X⁻ ∪ {k : T}` to the whole instance.

This file machine-checks that skeleton, with **Theorem S's conclusion as a hypothesis** (`ThmSHolds SHyp`: whenever
an abstract condition `SHyp` holds at a perfect start, some move reaches a state with a one-absorber completion that
threatens the extra agent `k` at `v_k(T)` with no bundle; `SHyp` stands for "(R) some `(k′, P′, h)` meets Theorem
S's hypotheses, and (K)").
- `echain_isChain`: `E(k)` with `k` taking `T` is an official chain (`EFX.OC1Max.IsChain`).
- `recs_L`: Lemma LIFT's hypothesis (L) is automatic (the referee's remark): every other agent values each good of
  `T` at most its value after `E(k)`.
- `junk_reduce`, `oneMove_lift` (**LIFT 1**), `oneMove_congr`, `oneAbsorber_lift` (**LIFT 2**).
- `ConjRECS SHyp`: at every perfect start of every strict instance with at most four relevant goods per agent, the
  picks complete, or one move gives a completion, or REC-S's data exist (`RECSData`: an earliest-wanter chain
  `k :: rest`, an improving `T`, and `SHyp` in the reduced instance).
- **`conjOC2perf_of_recs`: Theorem S's conclusion and REC-S existence imply OC₂ᵖᵉʳᶠ**, hence
  **`target4_of_recs`: TARGET₄** (through `EFX.OC1Max.target4_of_conjOC2perf`, Lemma RED and MAXSD).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

open LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section recs
variable {v : A → G → Nat}

omit [DecidableEq A] [DecidableEq G] in
theorem value_toList (i : A) (o : Option G) : value v i o.toList = match o with | none => 0 | some g => v i g := by
  cases o <;> simp

omit [DecidableEq A] [DecidableEq G] in
theorem value_toList_eq_mval (Y : A → Option G) (i a : A) :
    value v i (Y a).toList = match Y a with | none => 0 | some g => v i g := value_toList i (Y a)

omit [DecidableEq A] [DecidableEq G] in
theorem value_pick (Y : A → Option G) (i : A) : value v i (Y i).toList = mval v Y i := by
  cases h : Y i <;> simp [mval, h]

omit [DecidableEq A] in
/-- The end of a list has no successor. -/
theorem getLast_no_succ : ∀ {l : List A} (hne : l ≠ []), l.Nodup → ∀ q, (l.getLast hne, q) ∉ l.zip l.tail
  | [], hne, _, _, _ => absurd rfl hne
  | [_], _, _, _, h => by simp at h
  | a :: b :: rest, _, hnd, q, h => by
    rw [List.getLast_cons (List.cons_ne_nil _ _)] at h
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨h1, -⟩ | h
    · exact (List.nodup_cons.mp hnd).1 (h1 ▸ List.getLast_mem _)
    · exact getLast_no_succ (List.cons_ne_nil b rest) (List.nodup_cons.mp hnd).2 q h

/-- The picks form a valid state. -/
theorem validState_pickBase {agents : List A} {goods : List G} {σ : List A} (hσ : σ.Perm agents)
    (hgd : goods.Nodup) : ValidState agents goods (pickBase v goods σ) := by
  have hm := isMatching_sdPick (v := v) hσ hgd
  refine ⟨fun i _ => ⟨?_, fun g hg => ?_⟩, fun i _ j _ hij g hi hj => ?_⟩
  · simp only [pickBase]; cases sdPick v σ goods i <;> simp
  · simp only [pickBase] at hg
    cases h : sdPick v σ goods i with
    | none => rw [h] at hg; simp at hg
    | some y => rw [h] at hg; simp at hg; subst hg; exact (hm.mem i _ h).2.1
  · simp only [pickBase] at hi hj
    cases h1 : sdPick v σ goods i <;> cases h2 : sdPick v σ goods j <;> rw [h1] at hi <;> rw [h2] at hj <;>
      simp at hi hj
    subst hi; subst hj
    exact hij (hm.inj i j _ h1 h2)

/-- The state after the earliest-wanter chain `k :: rest` in which `k` takes `T`. -/
def afterE (Y : A → Option G) (k : A) (rest : List A) (T : List G) (a : A) : List G :=
  if a = k then T else (Y (src (k :: rest) a)).toList

section echain
variable {agents : List A} {goods : List G} {σ : List A}

/-- **`E(k)` with `k` taking `T` is an official chain**: `k` takes `T` (from the junk and the end's pick, improving),
each later agent its predecessor's pick (which it wants). -/
theorem echain_isChain (hσ : σ.Perm agents) {k : A} {rest : List A}
    (hch : EChain v agents σ (sdPick v σ goods) (k :: rest)) {T : List G} (hTnd : T.Nodup)
    (hTg : ∀ g ∈ T, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨
      sdPick v σ goods ((k :: rest).getLast (List.cons_ne_nil _ _)) = some g))
    (himp : mval v (sdPick v σ goods) k < value v k T) :
    IsChain v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) k rest T) := by
  have hnd := hch.nodup
  have hk : k ∉ rest := (List.nodup_cons.mp hnd).1
  have hne : ∀ x ∈ rest, x ≠ k := fun x hx e => hk (e ▸ hx)
  refine ⟨k, rest, fun a => if a = k then T else [], hch.tail_ne, hnd, hch.mem, fun x _ => ?_,
    fun x _ y _ hxy g hg hg' => ?_, fun g hg => ?_, fun x hx g hg => ?_, ?_, fun p hp => ?_, ?_,
    fun p hp => ?_, fun y hy => ?_⟩
  · by_cases hxk : x = k
    · subst hxk; simp only [ite_true]; exact ⟨hTnd, fun g hg => (hTg g hg).2.1⟩
    · simp [hxk]
  · by_cases hxk : x = k
    · have hyk : y ≠ k := fun e => hxy (hxk.trans e.symm)
      simp [hyk] at hg'
    · simp [hxk] at hg
  · simp only [ite_true] at hg
    obtain ⟨hgG, -, h⟩ := hTg g hg
    rcases h with h | h
    · exact Or.inl ((mem_junkOf_pickBase hσ).mpr ⟨hgG, h⟩)
    · exact Or.inr (by simp [pickBase, h])
  · simp [hne x hx] at hg
  · simp only [ite_true]; rw [pickBase, value_pick]; exact himp
  · have hp2 : p.2 ∈ rest := (List.of_mem_zip hp).2
    obtain ⟨y, hy, hlt⟩ := hch.wants p hp
    simp only [hne p.2 hp2, ite_false, List.append_nil]
    refine ⟨by simp [pickBase, hy], ?_⟩
    rw [pickBase, pickBase, value_pick, hy]; simpa using hlt
  · simp [afterE]
  · have hp2 : p.2 ∈ rest := (List.of_mem_zip hp).2
    simp only [afterE, hne p.2 hp2, ite_false, List.append_nil, pickBase]
    rw [src_of_pair hnd (by simpa using hp)]
  · have hyk : y ≠ k := fun e => hy (e ▸ List.mem_cons_self)
    have hyr : y ∉ rest := fun h => hy (List.mem_cons_of_mem _ h)
    simp only [afterE, hyk, ite_false, pickBase]
    rw [src_of_not_tail (by simpa using hyr)]

/-- **(L) is automatic** (the referee's remark on REC-S): every listed agent other than `k` values each good of `T`
at most its value after `E(k)`. -/
theorem recs_L (hσ : σ.Perm agents) (hag : agents.Nodup) (hgd : goods.Nodup) {k : A} {rest : List A}
    (hch : EChain v agents σ (sdPick v σ goods) (k :: rest)) {T : List G}
    (hTg : ∀ g ∈ T, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨
      sdPick v σ goods ((k :: rest).getLast (List.cons_ne_nil _ _)) = some g)) :
    ∀ i ∈ agents, i ≠ k → ∀ g ∈ T, v i g ≤ value v i (afterE (sdPick v σ goods) k rest T i) := by
  intro i hi hik g hg
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hm := isMatching_sdPick (v := v) hσ hgd
  -- the value after the chain is at least the pick value
  have hup : mval v (sdPick v σ goods) i ≤ value v i (afterE (sdPick v σ goods) k rest T i) := by
    simp only [afterE, hik, ite_false]
    by_cases hir : i ∈ rest
    · obtain ⟨p, hp⟩ := (mem_tail_iff_pair (l := k :: rest)).mp hir
      rw [src_of_pair hch.nodup hp]
      obtain ⟨y, hy, hlt⟩ := hch.wants _ hp
      simp only at hy hlt; rw [hy]; simpa using Nat.le_of_lt hlt
    · rw [src_of_not_tail hir, value_pick]; exact Nat.le_refl _
  obtain ⟨hgG, -, h⟩ := hTg g hg
  rcases h with h | h
  · -- a junk good: worth at most the pick
    refine Nat.le_trans ?_ hup
    by_cases hpos : 0 < v i g
    · obtain ⟨y, hy, hle⟩ := sdPick_turn v σ goods hnd hgd i (hσ.mem_iff.mpr hi) g hgG (fun c _ => h c) hpos
      rw [mval_some hy]; exact hle
    · omega
  · -- the end's pick
    by_cases hiz : i = (k :: rest).getLast (List.cons_ne_nil _ _)
    · -- `z` holds its predecessor's pick, worth more to it than its own
      have hzmem : (k :: rest).getLast (List.cons_ne_nil _ _) ∈ k :: rest := List.getLast_mem _
      have hir : i ∈ rest := (List.mem_cons.mp (hiz ▸ hzmem)).resolve_left hik
      obtain ⟨p, hp⟩ := (mem_tail_iff_pair (l := k :: rest)).mp hir
      obtain ⟨y, hy, hlt⟩ := hch.wants _ hp
      simp only at hy hlt
      have hYi : sdPick v σ goods i = some g := by rw [hiz]; exact h
      rw [mval_some hYi] at hlt
      simp only [afterE, hik, ite_false]
      rw [src_of_pair hch.nodup hp, hy]
      simpa using Nat.le_of_lt hlt
    · refine Nat.le_trans ?_ hup
      have := hch.last _ (List.getLast_mem (List.cons_ne_nil k rest))
        (getLast_no_succ (List.cons_ne_nil k rest) hch.nodup) i hi
      exact Nat.le_of_not_lt fun hlt => this ⟨g, h, hlt⟩

end echain

/-! ## Lemma LIFT -/

section lift
variable {agents : List A} {goods : List G}

/-- When `k` holds `T`, the junk of the whole instance is the junk of the instance without `k` and `T`. -/
theorem junk_reduce (hag : agents.Nodup) {k : A} (hk : k ∈ agents) {T : List G} {B : A → List G} (hBk : B k = T)
    (g : G) : g ∈ junkOf agents goods B ↔ g ∈ junkOf (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) B := by
  rw [mem_junkOf, mem_junkOf, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hg, hno⟩
    exact ⟨⟨hg, fun hT => hno k hk (hBk ▸ hT)⟩, fun i hi => hno i (List.mem_of_mem_erase hi)⟩
  · rintro ⟨⟨hg, hT⟩, hno⟩
    refine ⟨hg, fun i hi hgi => ?_⟩
    by_cases hik : i = k
    · subst hik; exact hT (hBk ▸ hgi)
    · exact hno i ((List.Nodup.mem_erase_iff hag).mpr ⟨hik, hi⟩) hgi

/-- **LIFT 1**: a move of the instance without `k` and `T`, at a state where `k` holds `T`, is a move of the whole
instance (leaving `k`'s base unchanged). -/
theorem oneMove_lift (hag : agents.Nodup) {k : A} (hk : k ∈ agents) {T : List G} {B C : A → List G} (hBk : B k = T)
    (h : OneMove v (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) B C) : OneMove v agents goods B C := by
  have hJ := junk_reduce (goods := goods) hag hk hBk
  rcases h with ⟨x, H, hx, hHne, hHnd, hHJ, h1, h2⟩ | ⟨x₀, xs, H, hxs, hnd, hagx, hH, hdis, hH0, hHJ, hg0, hp, h0,
    hp', ho⟩ | ⟨w₀, ws, H, hws, hnd, hagw, hH, hdis, hp, ho⟩
  · exact Or.inl ⟨x, H, List.mem_of_mem_erase hx, hHne, hHnd, fun g hg => ⟨(hJ g).mpr (hHJ g hg).1, (hHJ g hg).2⟩,
      h1, h2⟩
  · refine Or.inr (Or.inl ⟨x₀, xs, H, hxs, hnd, fun x hx => List.mem_of_mem_erase (hagx x hx), hH, hdis,
      fun g hg => ?_, fun x hx g hg => (hJ g).mpr (hHJ x hx g hg), hg0, hp, h0, hp', ho⟩)
    rcases hH0 g hg with h | h
    · exact Or.inl ((hJ g).mpr h)
    · exact Or.inr h
  · exact Or.inr (Or.inr ⟨w₀, ws, H, hws, hnd, fun x hx => List.mem_of_mem_erase (hagw x hx),
      fun x hx => ⟨(hH x hx).1, fun g hg => ⟨(hJ g).mpr ((hH x hx).2 g hg).1, ((hH x hx).2 g hg).2⟩⟩, hdis, hp, ho⟩)

omit [DecidableEq A] in
theorem junk_congr {B B' : A → List G} (h : ∀ a ∈ agents, B a = B' a) (g : G) :
    g ∈ junkOf agents goods B ↔ g ∈ junkOf agents goods B' := by
  rw [mem_junkOf, mem_junkOf]
  exact and_congr_right fun _ => ⟨fun hno i hi => h i hi ▸ hno i hi, fun hno i hi => (h i hi).symm ▸ hno i hi⟩

/-- A move only depends on the bases of the listed agents. -/
theorem oneMove_congr {B B' C : A → List G} (hB : ∀ a ∈ agents, B a = B' a) (h : OneMove v agents goods B C) :
    OneMove v agents goods B' (fun a => if a ∈ agents then C a else B' a) := by
  classical
  have hJ := junk_congr (goods := goods) hB
  rcases h with ⟨x, H, hx, hHne, hHnd, hHJ, h1, h2⟩ | ⟨x₀, xs, H, hxs, hnd, hagx, hH, hdis, hH0, hHJ, hg0, hp, h0,
    hp', ho⟩ | ⟨w₀, ws, H, hws, hnd, hagw, hH, hdis, hp, ho⟩
  · refine Or.inl ⟨x, H, hx, hHne, hHnd, fun g hg => ⟨(hJ g).mp (hHJ g hg).1, (hHJ g hg).2⟩, ?_, fun y hy => ?_⟩
    · simp only [hx, ite_true]; rw [h1, hB x hx]
    · by_cases hya : y ∈ agents
      · simp only [hya, ite_true]; rw [h2 y hy, hB y hya]
      · simp [hya]
  · have hl := hagx _ (List.getLast_mem (List.cons_ne_nil x₀ xs))
    refine Or.inr (Or.inl ⟨x₀, xs, H, hxs, hnd, hagx, hH, hdis, fun g hg => ?_, fun x hx g hg => (hJ g).mp
      (hHJ x hx g hg), ?_, fun p hpp => ?_, ?_, fun p hpp => ?_, fun y hy => ?_⟩)
    · rcases hH0 g hg with h | h
      · exact Or.inl ((hJ g).mp h)
      · exact Or.inr (hB _ hl ▸ h)
    · rw [← hB x₀ (hagx x₀ List.mem_cons_self)]; exact hg0
    · have h1 := hagx _ (List.of_mem_zip hpp).1
      have h2 := hagx _ (List.mem_cons_of_mem _ (List.of_mem_zip hpp).2)
      rw [← hB _ h1, ← hB _ h2]; exact hp p hpp
    · simp only [hagx x₀ List.mem_cons_self, ite_true]; exact h0
    · have h1 := hagx _ (List.of_mem_zip hpp).1
      have h2 := hagx _ (List.mem_cons_of_mem _ (List.of_mem_zip hpp).2)
      simp only [h2, ite_true]; rw [hp' p hpp, hB _ h1]
    · by_cases hya : y ∈ agents
      · simp only [hya, ite_true]; rw [ho y hy, hB y hya]
      · simp [hya]
  · refine Or.inr (Or.inr ⟨w₀, ws, H, hws, hnd, hagw, fun x hx => ⟨(hH x hx).1, fun g hg =>
      ⟨(hJ g).mp ((hH x hx).2 g hg).1, ((hH x hx).2 g hg).2⟩⟩, hdis, fun p hpp => ?_, fun y hy => ?_⟩)
    · have h1 := hagw _ (List.of_mem_zip hpp).1
      have h2 : p.2 ∈ agents := by
        have := (List.of_mem_zip hpp).2
        rcases List.mem_append.mp this with h | h
        · exact hagw _ (List.mem_cons_of_mem _ h)
        · rw [List.mem_singleton] at h; rw [h]; exact hagw _ List.mem_cons_self
      obtain ⟨hne, hgain, hC⟩ := hp p hpp
      refine ⟨hB _ h1 ▸ hne, by rw [← hB _ h1, ← hB _ h2]; exact hgain, ?_⟩
      simp only [h2, ite_true]; rw [hC, hB _ h1]
    · by_cases hya : y ∈ agents
      · simp only [hya, ite_true]; rw [ho y hy, hB y hya]
      · simp [hya]

/-- **LIFT 2**: a one-absorber completion `X⁻` of a state `C` of the instance without `k` and `T`, in which no
bundle threatens `k` at `v_k(T)` ((K)) and every other agent values each good of `T` at most its own bundle, gives,
with `T` to `k`, a one-absorber completion of `C` (where `k` holds `T`) in the whole instance. -/
theorem oneAbsorber_lift (hag : agents.Nodup) (hgd : goods.Nodup) {k : A} (hk : k ∈ agents) {T : List G}
    (hTnd : T.Nodup) (hT2 : T.length ≤ 2) (hTg : ∀ g ∈ T, g ∈ goods) {C : A → List G} (hCk : C k = T)
    (hCsub : ∀ i ∈ agents.erase k, ∀ g ∈ C i, g ∉ T) {X' : G → A}
    (hX' : IsAllocation (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) X')
    (hE' : EFX0L v (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) X')
    (hb' : ∀ i ∈ agents.erase k, ∀ g ∈ C i, X' g = i)
    (ha' : ∃ a, ∀ i ∈ agents.erase k, i ≠ a →
      ((junkOf (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) C).filter (fun g => X' g = i)).length ≤ 1)
    (hL : ∀ i ∈ agents.erase k, ∀ g ∈ T,
      v i g ≤ value v i (bundle (goods.filter (fun g => decide (g ∉ T))) X' i))
    (hK : ∀ j ∈ agents.erase k,
      ¬ Threat v k (bundle (goods.filter (fun g => decide (g ∉ T))) X' j) (value v k T)) :
    OneAbsorber v agents goods C := by
  classical
  let goods' := goods.filter (fun g => decide (g ∉ T))
  have hgd' : goods'.Nodup := hgd.sublist List.filter_sublist
  have hmem' : ∀ g, g ∈ goods' ↔ g ∈ goods ∧ g ∉ T := fun g => by simp [goods']
  have hmemE : ∀ i, i ∈ agents.erase k ↔ i ≠ k ∧ i ∈ agents := fun i => List.Nodup.mem_erase_iff hag
  let X : G → A := fun g => if g ∈ T then k else X' g
  have hXk : ∀ g ∈ goods, (X g = k ↔ g ∈ T) := fun g hg => by
    by_cases hgT : g ∈ T
    · simp [X, hgT]
    · simp only [X, hgT, ite_false, iff_false]
      intro e
      have := hX' g ((hmem' g).mpr ⟨hg, hgT⟩)
      rw [e] at this; exact List.Nodup.not_mem_erase hag this
  have hbk : ∀ g, g ∈ bundle goods X k ↔ g ∈ T := fun g => by
    rw [mem_bundle]
    exact ⟨fun ⟨hg, hX⟩ => (hXk g hg).mp hX, fun hgT => ⟨hTg g hgT, (hXk g (hTg g hgT)).mpr hgT⟩⟩
  have hbj : ∀ j, j ≠ k → ∀ g, g ∈ bundle goods X j ↔ g ∈ bundle goods' X' j := fun j hjk g => by
    rw [mem_bundle, mem_bundle, hmem']
    by_cases hgT : g ∈ T
    · simp only [X, hgT, ite_true]
      constructor
      · rintro ⟨-, e⟩; exact absurd e.symm hjk
      · rintro ⟨⟨-, h⟩, -⟩; exact absurd trivial h
    · simp [X, hgT]
  have hvalj : ∀ i j, j ≠ k → value v i (bundle goods X j) = value v i (bundle goods' X' j) := fun i j hjk =>
    value_eq_of_mem_iff (nodup_bundle hgd X j) (nodup_bundle hgd' X' j) (hbj j hjk)
  have hvalk : value v k (bundle goods X k) = value v k T := value_eq_of_mem_iff (nodup_bundle hgd X k) hTnd hbk
  refine ⟨X, fun g hg => ?_, efx0L_iff.mpr fun i hi j hj hij => ?_, fun i hi g hg => ?_, ?_⟩
  · by_cases hgT : g ∈ T
    · simp only [X, hgT, ite_true]; exact hk
    · simp only [X, hgT, ite_false]
      exact List.mem_of_mem_erase (hX' g ((hmem' g).mpr ⟨hg, hgT⟩))
  · by_cases hjk : j = k
    · -- `k`'s bundle `T`: at most two goods, each worth at most `i`'s bundle
      subst hjk
      have hik : i ≠ j := hij
      have hiE : i ∈ agents.erase j := (hmemE i).mpr ⟨hik, hi⟩
      rw [threat_congr (nodup_bundle hgd X j) hTnd hbk, hvalj i i hik]
      exact not_threat_small hTnd (fun y hy => hy) hT2 fun y hy => hL i hiE y hy
    · have hjE : j ∈ agents.erase k := (hmemE j).mpr ⟨hjk, hj⟩
      rw [threat_congr (nodup_bundle hgd X j) (nodup_bundle hgd' X' j) (hbj j hjk)]
      by_cases hik : i = k
      · subst hik; rw [hvalk]; exact hK j hjE
      · rw [hvalj i i hik]
        exact efx0L_iff.mp hE' i ((hmemE i).mpr ⟨hik, hi⟩) j hjE hij
  · by_cases hik : i = k
    · subst hik; rw [hCk] at hg; simp [X, hg]
    · have hiE : i ∈ agents.erase k := (hmemE i).mpr ⟨hik, hi⟩
      have hgT := hCsub i hiE g hg
      simp only [X, hgT, ite_false]; exact hb' i hiE g hg
  · obtain ⟨a, ha⟩ := ha'
    have hJ := junk_reduce (goods := goods) hag hk hCk
    refine ⟨a, fun i hi hia => ?_⟩
    by_cases hik : i = k
    · -- `k` receives no junk
      subst hik
      have h0 : (junkOf agents goods C).filter (fun g => X g = i) = [] :=
        List.eq_nil_iff_forall_not_mem.mpr fun g hg => by
          obtain ⟨hgJ, hXg⟩ := List.mem_filter.mp hg
          have hgT := (hXk g (mem_junkOf.mp hgJ).1).mp (by simpa using hXg)
          exact (mem_junkOf.mp hgJ).2 i hi (hCk ▸ hgT)
      rw [h0]; exact Nat.zero_le _
    · have hiE : i ∈ agents.erase k := (hmemE i).mpr ⟨hik, hi⟩
      refine Nat.le_trans ?_ (ha i hiE hia)
      refine ((hgd.sublist List.filter_sublist).sublist List.filter_sublist).length_le_of_subset fun g hg => ?_
      obtain ⟨hgJ, hXg⟩ := List.mem_filter.mp hg
      have hgJ' := (hJ g).mp hgJ
      have hgT : g ∉ T := ((hmem' g).mp (mem_junkOf.mp hgJ').1).2
      refine List.mem_filter.mpr ⟨hgJ', ?_⟩
      simpa [X, hgT] using hXg

end lift

omit [DecidableEq A] in
theorem junkOf_congr_eq {agents : List A} {goods : List G} {B B' : A → List G} (h : ∀ a ∈ agents, B a = B' a) :
    junkOf agents goods B = junkOf agents goods B' := by
  unfold junkOf
  refine List.filter_congr fun g _ => ?_
  refine Bool.eq_iff_iff.mpr ?_
  simp only [List.all_eq_true]
  exact ⟨fun hh i hi => h i hi ▸ hh i hi, fun hh i hi => (h i hi).symm ▸ hh i hi⟩

end recs

/-! ## The frame: REC-S existence ⟹ OC₂ᵖᵉʳᶠ ⟹ TARGET₄ -/

/-- The type of Theorem S's hypothesis: a condition on an instance, an order, an extra agent `k` and its set `T`. -/
abbrev SHypRel (A G : Type) : Type := (A → G → Nat) → List A → List G → List A → A → List G → Prop

/-- **Theorem S's conclusion, as a hypothesis** (with REC-S's (K)). Whenever `SHyp` holds at a perfect start of a
strict instance, some move reaches a state with a one-absorber completion in which no bundle threatens `k` at
`v_k(T)`. Theorem S (K4.MULTI.S, refereed CORRECT) is the intended instance: `SHyp` = "some `(k′, P′, h)` meets
Theorem S's (relaxed) hypotheses, and its allocation satisfies (K)". Theorem S is not formalized here. -/
def ThmSHolds (A G : Type) [DecidableEq A] [DecidableEq G] (SHyp : SHypRel A G) : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) (k : A) (T : List G),
    agents.Nodup → goods.Nodup → Strict v agents goods → σ.Perm agents →
    PerfectStart v agents goods (sdPick v σ goods) → SHyp v agents goods σ k T →
    ∃ (C : A → List G) (X : G → A), OneMove v agents goods (pickBase v goods σ) C ∧
      IsAllocation agents goods X ∧ EFX0L v agents goods X ∧ (∀ i ∈ agents, ∀ g ∈ C i, X g = i) ∧
      (∃ a, ∀ i ∈ agents, i ≠ a → ((junkOf agents goods C).filter (fun g => X g = i)).length ≤ 1) ∧
      ∀ j ∈ agents, ¬ Threat v k (bundle goods X j) (value v k T)

/-- **REC-S's data** at the start of `σ`: an earliest-wanter chain `k :: rest`, a set `T` of at most two goods of
`J ∪ {Y_z}` that `k` values and that improves on its pick, and Theorem S's hypothesis in the instance without `k`
and `T`, at the order without `k`. -/
def RECSData (SHyp : SHypRel A G) (v : A → G → Nat) (agents : List A) (goods : List G) (σ : List A) : Prop :=
  ∃ (k : A) (rest : List A) (T : List G), EChain v agents σ (sdPick v σ goods) (k :: rest) ∧ T.Nodup ∧
    T.length ≤ 2 ∧ (∀ g ∈ T, g ∈ goods ∧ 0 < v k g ∧ ((∀ x, sdPick v σ goods x ≠ some g) ∨
      sdPick v σ goods ((k :: rest).getLast (List.cons_ne_nil _ _)) = some g)) ∧
    mval v (sdPick v σ goods) k < value v k T ∧
    SHyp v (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) (σ.erase k) k T

/-- **REC-S existence**: at every perfect start of every strict instance with at least one agent and at most four
relevant goods per agent, the picks have a one-absorber completion, or one move gives a state that has one, or
REC-S's data exist. A `Prop`. -/
def ConjRECS (A G : Type) [DecidableEq A] [DecidableEq G] (SHyp : SHypRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents ≠ [] → agents.Nodup → goods.Nodup →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 4) → Strict v agents goods → ∀ σ : List A, σ.Perm agents →
      PerfectStart v agents goods (sdPick v σ goods) →
      OneAbsorber v agents goods (pickBase v goods σ) ∨
        (∃ B', OneMove v agents goods (pickBase v goods σ) B' ∧ OneAbsorber v agents goods B') ∨
        RECSData SHyp v agents goods σ

/-- **Theorem REC-S, the skeleton**: at a perfect start with REC-S's data, Theorem S's conclusion gives a repair by
two moves: `E(k)` with `k` taking `T`, then the lifted move of the smaller instance, completed by the lifted
completion. -/
theorem recs_two_moves {SHyp : SHypRel A G} (hS : ThmSHolds A G SHyp) {v : A → G → Nat} {agents : List A}
    {goods : List G} (hag : agents.Nodup) (hgd : goods.Nodup) (hs : Strict v agents goods) {σ : List A}
    (hσ : σ.Perm agents) (hperf : PerfectStart v agents goods (sdPick v σ goods))
    (hdata : RECSData SHyp v agents goods σ) :
    ∃ B₂, movesUpTo (fun v agents goods => OneMove v agents goods) 2 v agents goods (pickBase v goods σ) B₂ ∧
      OneAbsorber v agents goods B₂ := by
  classical
  obtain ⟨k, rest, T, hch, hTnd, hT2, hTg, himp, hSH⟩ := hdata
  have hk : k ∈ agents := hch.mem k List.mem_cons_self
  have hsv := strictVals_of_strict hs
  have hnd : σ.Nodup := hσ.nodup_iff.mpr hag
  have hm := isMatching_sdPick (v := v) hσ hgd
  -- the reduced instance
  have hag' : (agents.erase k).Nodup := hag.erase k
  have hgd' : (goods.filter (fun g => decide (g ∉ T))).Nodup := hgd.sublist List.filter_sublist
  have hs' : Strict v (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) := fun i hi S T' hS hT hd he =>
    hs i (List.mem_of_mem_erase hi) S T' (hS.trans List.filter_sublist) (hT.trans List.filter_sublist) hd he
  have hσ' : (σ.erase k).Perm (agents.erase k) := hσ.erase k
  have hTsde : ∀ g ∈ T, ∀ x ∈ agents, sdPick v σ goods x = some g →
      x ∈ k :: rest ∧ ∀ q, (x, q) ∉ (k :: rest).zip rest := fun g hg x hx hxg => by
    rcases (hTg g hg).2.2 with h | h
    · exact absurd hxg (h x)
    · have hl := hch.mem _ (List.getLast_mem (List.cons_ne_nil k rest))
      have := hm.inj x _ g hxg h
      subst this
      exact ⟨List.getLast_mem _, getLast_no_succ _ hch.nodup⟩
  have hperf' := sdE_perfect hσ hag hgd hsv hch hTsde hperf
  obtain ⟨C, X', hmv, hX', hE', hb', ha', hK⟩ := hS v _ _ _ k T hag' hgd' hs' hσ' hperf' hSH
  -- the reduced picks are the state after `E(k)`
  have hagree : ∀ a ∈ agents.erase k, pickBase v (goods.filter (fun g => decide (g ∉ T))) (σ.erase k) a =
      afterE (sdPick v σ goods) k rest T a := fun a ha => by
    have hak : a ≠ k := fun e => by subst e; exact List.Nodup.not_mem_erase hag ha
    have haσ : a ∈ σ.erase k := hσ'.mem_iff.mpr ha
    simp only [pickBase, afterE, hak, ite_false]
    rw [sdE hσ hag hgd hsv hch hTsde a haσ]
  let C' : A → List G := fun a => if a ∈ agents.erase k then C a else afterE (sdPick v σ goods) k rest T a
  have hmv' := oneMove_congr hagree hmv
  have hBk : afterE (sdPick v σ goods) k rest T k = T := by simp [afterE]
  have hmv'' : OneMove v agents goods (afterE (sdPick v σ goods) k rest T) C' := oneMove_lift hag hk hBk hmv'
  have hm1 : OneMove v agents goods (pickBase v goods σ) (afterE (sdPick v σ goods) k rest T) :=
    Or.inr (Or.inl (echain_isChain hσ hch hTnd hTg himp))
  -- the lifted completion
  have hkE : k ∉ agents.erase k := List.Nodup.not_mem_erase hag
  have hCk : C' k = T := by simp only [C', hkE, ite_false]; exact hBk
  have hvalid' := validState_pickBase (v := v) hσ' hgd'
  have hCsub : ∀ i ∈ agents.erase k, ∀ g ∈ C' i, g ∉ T := fun i hi g hg => by
    simp only [C', hi, ite_true] at hg
    have hgin : g ∈ goods.filter (fun g => decide (g ∉ T)) := by
      rcases move_local (fun j hj => (hvalid'.1 j hj).1) hmv i hi with he | ⟨j, hj, -, hmem, -⟩
      · rw [he] at hg; exact (hvalid'.1 i hi).2 g hg
      · rcases hmem g hg with h | h
        · exact (hvalid'.1 j hj).2 g h
        · exact (mem_junkOf.mp h).1
    simpa using (List.mem_filter.mp hgin).2
  have hb'' : ∀ i ∈ agents.erase k, ∀ g ∈ C' i, X' g = i := fun i hi g hg => by
    simp only [C', hi, ite_true] at hg; exact hb' i hi g hg
  have hjunk : junkOf (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) C' =
      junkOf (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) C :=
    junkOf_congr_eq fun a ha => by simp [C', ha]
  have ha'' : ∃ a, ∀ i ∈ agents.erase k, i ≠ a →
      ((junkOf (agents.erase k) (goods.filter (fun g => decide (g ∉ T))) C').filter
        (fun g => X' g = i)).length ≤ 1 := by
    rw [hjunk]; exact ha'
  have hL' : ∀ i ∈ agents.erase k, ∀ g ∈ T,
      v i g ≤ value v i (bundle (goods.filter (fun g => decide (g ∉ T))) X' i) := fun i hi g hg => by
    have hik : i ≠ k := fun e => hkE (e ▸ hi)
    have h1 := recs_L hσ hag hgd hch hTg i (List.mem_of_mem_erase hi) hik g hg
    rw [← hagree i hi] at h1
    exact Nat.le_trans h1 (t6_dominate hvalid' hmv hb' i hi)
  have hT : ∀ g ∈ T, g ∈ goods := fun g hg => (hTg g hg).1
  exact ⟨C', Or.inr ⟨_, hm1, Or.inr ⟨C', hmv'', rfl⟩⟩,
    oneAbsorber_lift hag hgd hk hTnd hT2 hT hCk hCsub hX' hE' hb'' ha'' hL' hK⟩

/-- **Theorem S's conclusion and REC-S existence imply OC₂ at perfect starts.** -/
theorem conjOC2perf_of_recs {SHyp : SHypRel A G} (hS : ThmSHolds A G SHyp) (h : ConjRECS A G SHyp) :
    ConjOC2perf A G := by
  intro agents goods v hne hag hgd h4 hs σ hσ hperf
  rcases h agents goods v hne hag hgd h4 hs σ hσ hperf with h0 | ⟨B', hm, hB'⟩ | hdata
  · exact Or.inl h0
  · exact Or.inr ⟨B', movesUpTo_mono (by omega : 1 ≤ 2) (movesUpTo_one hm), hB'⟩
  · exact Or.inr (recs_two_moves hS hag hgd hs hσ hperf hdata)

/-- **REC-S existence ⟹ TARGET₄** (with Theorem S's conclusion as a hypothesis): through OC₂ᵖᵉʳᶠ, Lemma RED and
MAXSD. -/
theorem target4_of_recs (I : Inst) (hn : 0 < I.n) {SHyp : SHypRel (Fin I.n) (Fin I.m)}
    (hS : ThmSHolds (Fin I.n) (Fin I.m) SHyp) (h : ConjRECS (Fin I.n) (Fin I.m) SHyp)
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC2perf I hn (conjOC2perf_of_recs hS h) hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.echain_isChain
#print axioms EFX.OC1Max.recs_L
#print axioms EFX.OC1Max.junk_reduce
#print axioms EFX.OC1Max.oneMove_lift
#print axioms EFX.OC1Max.oneMove_congr
#print axioms EFX.OC1Max.oneAbsorber_lift
#print axioms EFX.OC1Max.recs_two_moves
#print axioms EFX.OC1Max.conjOC2perf_of_recs
#print axioms EFX.OC1Max.target4_of_recs
