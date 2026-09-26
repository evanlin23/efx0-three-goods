import EFX.K3CostBound
import EFX.K3Examples
import EFX.RealValues
import EFX.PreAllocK

/-!
# Four results of the k = 3 paper (`paper/k3/long.tex`, `paper/k3/main.tex`)

Four statements the paper proves in writing, machine-checked here.

1. **`r` lies in the last block** (the remark after Lemma 10, "the candidate `r`", of the long version).
   `EFX.LB.blk_le_lastOut`: in Phase 1 in any order, if no upgraded agent picks its top, every agent's
   block is at most the block of `r = lastOut up order`. `EFX.LB.lastOut_lastBlock`: in the paper's setting
   (a run of Phase 1 and a valid pre-allocation, `EFX.LB.State`, as in `EFX.LB.lastOut_terminal`) `r`'s
   block is the largest block number and the block of the last processed agent. Blocks are numbered by
   `EFX.LB.blkAux` (the number of insertion steps up to and including the agent's turn), so this is "r's
   block `B*` is the last block". R1 priority is not needed.
2. **The size of the large bundle** (Proposition "size of the large bundle" in both versions).
   For a valid pre-allocation (`EFX.LB.Valid`) of distinct agents and goods:
   - `EFX.LB.numFrozen_eq_numNA`: `|F| = |NA|` (`NA` counted over the goods);
   - `EFX.LB.omega_eq`: `ω = |J| − S = m − 2n + |NA|` (as integers);
   - `EFX.LB.Completion.owner_length_ge`: every completion (`EFX.LB.Completion`, the notion `complete` produces)
     with an owner `o` that is a listed terminal or upgraded agent gives `o` at least `ω + 2` goods;
   - `EFX.LB.Completion.owner_length_eq`: exactly `ω + 2` when the slots of the other terminals are full;
   - `EFX.LB.largeBundle_size`: the three together, the Proposition. The paper assumes `ω ≥ 1`; the Lean
     statements hold for every `ω` (for `ω ≤ 0` the bound `ω + 2 ≤ |X_o|` still holds for a completion with
     an owner).
   - For K3ALG's completion `EFX.LB.complete` (`Complete(o, H)` in the paper): `EFX.LB.complete_owner_length`,
     if `H` lists no good twice (and `ω ≥ 1`), the other terminals' slots are full and the owner gets exactly
     `ω + 2` goods. Equality fails in general: `EFX.K3.Examples.repeatedGood` is the four-agent instance of the
     paper's remark "a repeated good", run through K3ALG (`EFX.K3.algo`) by `decide`: `HitSet` is `(g₀, g₀)`,
     `ω = 1`, the owner gets `4 = ω + 3` goods, and the output is EFX₀.
3. **At most two relevant goods** (Corollary "two relevant goods", `cor:k2` of the long version): serial
   dictatorship in any order, each agent taking *a* favourite remaining good (any good of largest value to
   it) and the last agent everything left, returns an EFX₀ allocation. `EFX.SDRun` is the set of runs (any
   order, any favourite at every step); `EFX.sdRun_efx0` (over lists) and `EFX.Inst.sdRun_efx0` (model) prove
   that every run is EFX₀. `EFX.serialDict` is one run, computable (index-order favourite, `EFX.favorite`);
   `EFX.Inst.serialDict_efx0`: it is EFX₀ for every order of all agents. The existence form was already
   `EFX.exists_efx0_of_count`.
4. **Rational values** (Corollary "rational values"). `OrderedValue Rat` (core Lean's `Rat`); `EFX.ratScale`
   multiplies agent `i`'s values by the product `EFX.denProd` of their denominators and takes the results as
   natural numbers (`EFX.ratScale_val`: `w i g = v i g · D_i`). `EFX.ratScale_agree`: this preserves every
   comparison between two subset sums of one agent's values (`EFX.Agree`), hence EFX₀
   (`EFX.ratScale_efx0_iff`) and the relevant goods (`EFX.ratScale_relevant`, `EFX.ratScale_numRelevant`).
   `EFX.K3.algoRat` is K3ALG on the scaled instance, and `EFX.K3.algoRat_efx0` is the Corollary: its output is
   EFX₀ for the rational values whenever every agent positively values at most three goods.
-/

set_option autoImplicit false

namespace EFX

/-! ## Counting over lists -/

section listcount
variable {α : Type}

theorem sum_map_add' (f g : α → Nat) : ∀ l : List α,
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add' f g l]; omega

theorem sum_map_le' {f g : α → Nat} : ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := sum_map_le' (l := l) (fun x hx => h x (by simp [hx]))
    omega

theorem sum_map_congr' {f g : α → Nat} {l : List α} (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem sum_map_const (c : Nat) : ∀ l : List α, (l.map (fun _ => c)).sum = c * l.length
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_const c l, List.length_cons]; rw [Nat.mul_succ]; omega

/-- A count splits as a sum of two counts when the indicators do, pointwise on the list. -/
theorem countP_eq_add {p q r : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, (if p x then 1 else 0) = (if q x then 1 else 0) + (if r x then 1 else 0)) →
    l.countP p = l.countP q + l.countP r
  | [], _ => by simp
  | a :: l, h => by
    have ha := h a (by simp)
    have ih := countP_eq_add (l := l) (fun x hx => h x (by simp [hx]))
    simp only [List.countP_cons]
    omega

/-- The same with three counts. -/
theorem countP_eq_add3 {p q r s : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, (if p x then 1 else 0) =
      (if q x then 1 else 0) + (if r x then 1 else 0) + (if s x then 1 else 0)) →
    l.countP p = l.countP q + l.countP r + l.countP s
  | [], _ => by simp
  | a :: l, h => by
    have ha := h a (by simp)
    have ih := countP_eq_add3 (l := l) (fun x hx => h x (by simp [hx]))
    simp only [List.countP_cons]
    omega

/-- In a list without repetition, a predicate that holds for at most one member is counted at most once. -/
theorem countP_le_one {p : α → Bool} : ∀ {l : List α}, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) → l.countP p ≤ 1
  | [], _, _ => by simp
  | a :: l, hnd, h => by
    rw [List.countP_cons]
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    by_cases hpa : p a = true
    · have : l.countP p = 0 := List.countP_eq_zero.mpr fun x hx hpx =>
        ha (by rw [h a (by simp) x (by simp [hx]) hpa hpx]; exact hx)
      simp [hpa, this]
    · have := countP_le_one hl (fun x hx y hy => h x (by simp [hx]) y (by simp [hy]))
      simp [hpa]; omega

/-- ... and exactly once if it holds for some member. -/
theorem countP_eq_one {p : α → Bool} {l : List α} (hnd : l.Nodup)
    (h : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) {a : α} (ha : a ∈ l) (hpa : p a = true) :
    l.countP p = 1 := by
  have h1 := countP_le_one hnd h
  have h2 : 0 < l.countP p := List.countP_pos_iff.mpr ⟨a, ha, hpa⟩
  omega

/-- Counting the members equal to `a` in a list without repetition. -/
theorem countP_eq_self [DecidableEq α] {l : List α} (hnd : l.Nodup) (a : α) :
    l.countP (fun x => decide (a = x)) = if a ∈ l then 1 else 0 := by
  by_cases ha : a ∈ l
  · simp only [ha, ↓reduceIte]
    exact countP_eq_one hnd (fun x _ y _ hx hy => by simp at hx hy; rw [← hx, ← hy]) ha (by simp)
  · simp only [ha, ↓reduceIte]
    exact List.countP_eq_zero.mpr fun x hx hax => ha (by simp at hax; rw [hax]; exact hx)

/-- Summing over a list without repetition that contains `o`: split off `o`'s term. -/
theorem sum_split [DecidableEq α] (f : α → Nat) {o : α} : ∀ {l : List α}, l.Nodup → o ∈ l →
    (l.map f).sum = f o + (l.map (fun j => if j = o then 0 else f j)).sum
  | [], _, h => by simp at h
  | a :: l, hnd, h => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hao : a = o
    · subst hao
      have : (l.map (fun j => if j = a then 0 else f j)).sum = (l.map f).sum :=
        sum_map_congr' (fun x hx => by
          have : x ≠ a := fun e => ha (e ▸ hx)
          simp [this])
      simp only [↓reduceIte, this]; omega
    · have := sum_split f hl ((List.mem_cons.mp h).resolve_left (Ne.symm hao))
      simp only [hao, ↓reduceIte]
      omega

/-- Two lists without repetition that agree on the members satisfying `p` count `p` equally. -/
theorem countP_eq_of_mem_iff [DecidableEq α] {p : α → Bool} {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ x, p x = true → (x ∈ l₁ ↔ x ∈ l₂)) : l₁.countP p = l₂.countP p := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have a := LB.length_le_of_subset (G := α) (h₁.sublist List.filter_sublist)
    (T := l₂.filter p) (fun x hx => by
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      exact List.mem_filter.mpr ⟨(h x hx2).mp hx1, hx2⟩)
  have b := LB.length_le_of_subset (G := α) (h₂.sublist List.filter_sublist)
    (T := l₁.filter p) (fun x hx => by
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      exact List.mem_filter.mpr ⟨(h x hx2).mpr hx1, hx2⟩)
  omega

end listcount

/-! ## 1. `r` lies in the last block -/

namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

section lastBlock
variable {P : Profile A G}

omit [DecidableEq A] in
/-- An agent all of whose goods remain (a leader) picks its top. -/
theorem fav_of_full {pool : List G} {i : A} (h : full P pool i = true) : fav P pool i = some (P.a i) := by
  simp only [full, decide_eq_true_eq] at h
  simp [fav, h.1]

/-- If no agent of `order` picks its top, no insertion step happens: every agent is in block `n`. -/
theorem blkAux_const : ∀ {order : List A} {pool : List G} {n : Nat}, order.Nodup →
    (∀ x ∈ order, phase1 P order pool x ≠ some (P.a x)) → ∀ x ∈ order, blkAux P order pool n x = n
  | [], _, _, _, _, x, hx => by simp at hx
  | i :: order, pool, n, hnd, h, x, hx => by
    have hi : i ∉ order := (List.nodup_cons.mp hnd).1
    have hnf : full P pool i = false := by
      cases hfi : full P pool i with
      | false => rfl
      | true => exact absurd (by rw [phase1_cons]; simp [fav_of_full hfi]) (h i (by simp))
    rw [blkAux_cons]
    simp only [hnf, Bool.false_eq_true, ↓reduceIte]
    by_cases hxi : x = i
    · simp [hxi]
    · simp only [hxi, ↓reduceIte]
      refine blkAux_const (List.nodup_cons.mp hnd).2 (fun y hy => ?_) x
        ((List.mem_cons.mp hx).resolve_left hxi)
      have hyi : y ≠ i := fun e => hi (e ▸ hy)
      have := h y (List.mem_cons_of_mem _ hy)
      rw [phase1_cons] at this
      simpa only [hyi, ↓reduceIte] using this

/-- Blocks never decrease along the processing order: every agent's block is at most the last agent's. -/
theorem blk_le_getLast : ∀ {order : List A} {pool : List G} {n : Nat}, order.Nodup → (hne : order ≠ []) →
    ∀ x ∈ order, blkAux P order pool n x ≤ blkAux P order pool n (order.getLast hne)
  | [], _, _, _, hne, _, _ => absurd rfl hne
  | [i], pool, n, _, _, x, hx => by
    simp only [List.mem_singleton] at hx
    subst hx; exact Nat.le_refl _
  | i :: j :: rest, pool, n, hnd, _, x, hx => by
    have hi : i ∉ j :: rest := (List.nodup_cons.mp hnd).1
    have hlast : (i :: j :: rest).getLast (by simp) = (j :: rest).getLast (by simp) :=
      List.getLast_cons (by simp)
    have hL := List.getLast_mem (l := j :: rest) (by simp)
    have hLi : (j :: rest).getLast (by simp) ≠ i := fun e => hi (e ▸ hL)
    rw [hlast, blkAux_cons i (j :: rest) pool n x, blkAux_cons i (j :: rest) pool n _]
    simp only [hLi, ↓reduceIte]
    by_cases hxi : x = i
    · simp only [hxi, ↓reduceIte]
      exact blk_ge hL
    · simp only [hxi, ↓reduceIte]
      exact blk_le_getLast (List.nodup_cons.mp hnd).2 (by simp) x
        ((List.mem_cons.mp hx).resolve_left hxi)

/-- **`r` lies in the last block (general form).** In Phase 1 in any order of distinct agents, if no upgraded
agent picks its top, then no agent's block exceeds the block of `r`, the last agent of `order` not upgraded:
a later block would start with a leader, which picks its top, so is not upgraded, yet comes after `r`. -/
theorem blk_le_lastOut {up : List A} : ∀ {order : List A} {pool : List G} {n : Nat} {r : A}, order.Nodup →
    (∀ u ∈ up, u ∈ order → phase1 P order pool u ≠ some (P.a u)) → lastOut up order = some r →
    ∀ x ∈ order, blkAux P order pool n x ≤ blkAux P order pool n r
  | [], _, _, _, _, _, hr, _, _ => by simp [lastOut] at hr
  | i :: order, pool, n, r, hnd, hup, hr, x, hx => by
    have hi : i ∉ order := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    -- the hypothesis on the rest of the order
    have hup' : ∀ u ∈ up, u ∈ order →
        phase1 P order (removePick pool (fav P pool i)) u ≠ some (P.a u) := by
      intro u hu huo
      have hui : u ≠ i := fun e => hi (e ▸ huo)
      have := hup u hu (List.mem_cons_of_mem _ huo)
      rw [phase1_cons] at this
      simpa only [hui, ↓reduceIte] using this
    unfold lastOut at hr
    cases hl : lastOut up order with
    | some r' =>
      rw [hl] at hr
      have e : r' = r := Option.some.inj hr
      rw [e] at hl
      have hro := (lastOut_some hnd' hl).1
      have hri : r ≠ i := fun e => hi (e ▸ hro)
      rw [blkAux_cons i order pool n x, blkAux_cons i order pool n r]
      simp only [hri, ↓reduceIte]
      by_cases hxi : x = i
      · simp only [hxi, ↓reduceIte]
        exact blk_ge hro
      · simp only [hxi, ↓reduceIte]
        exact blk_le_lastOut hnd' hup' hl x ((List.mem_cons.mp hx).resolve_left hxi)
    | none =>
      rw [hl] at hr
      simp only at hr
      by_cases hiu : i ∈ up
      · simp [hiu] at hr
      simp only [hiu, ↓reduceIte, Option.some.injEq] at hr
      rw [← hr]
      -- every agent after `r` is upgraded, so none of them is a leader
      rw [blkAux_cons i order pool n x, blkAux_cons i order pool n i]
      by_cases hxi : x = i
      · simp [hxi]
      · simp only [hxi, ↓reduceIte]
        have hxo := (List.mem_cons.mp hx).resolve_left hxi
        rw [blkAux_const hnd' (fun y hy => hup' y (lastOut_none hl y hy) hy) x hxo]
        exact Nat.le_refl _

/-- **`r` lies in the last block** (the remark after the long version's Lemma 10). After a run of Phase 1 (its
blocks numbered by `blkAux`) and with a valid pre-allocation (`State`, as in `lastOut_terminal`), let `r` be
the last-processed agent that is not upgraded. Then every agent's block is at most `r`'s, and `r`'s block is
the block of the last processed agent: `r` lies in the last block `B*`. -/
theorem lastOut_lastBlock {agents : List A} {goods : List G} {order : List A} {lead : A → Prop}
    {up : List A} (hS : State P agents goods order (phase1 P order goods) (blkAux P order goods 0) lead up)
    {r : A} (hr : lastOut up order = some r) :
    (∀ x ∈ agents, blkAux P order goods 0 x ≤ blkAux P order goods 0 r) ∧
    ∀ hne : order ≠ [], blkAux P order goods 0 (order.getLast hne) = blkAux P order goods 0 r := by
  have hup : ∀ u ∈ up, u ∈ order → phase1 P order goods u ≠ some (P.a u) := by
    intro u hu _ he
    rw [hS.valid.up_b u hu] at he
    exact (hS.wf u (hS.valid.up_mem u hu)).2.2.2.1 (Option.some.inj he).symm
  have hle := blk_le_lastOut (n := 0) hS.run.order_nodup hup hr
  refine ⟨fun x hx => hle x ((hS.run.mem_order x).mpr hx), fun hne => ?_⟩
  have h1 := hle _ (List.getLast_mem hne)
  have h2 := blk_le_getLast (P := P) (pool := goods) (n := 0) hS.run.order_nodup hne r
    (lastOut_some hS.run.order_nodup hr).1
  omega

end lastBlock

/-! ## 2. The size of the large bundle -/

section size
variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

/-- The junk test of `junkList`: nobody's pick and not the `c` of an upgraded agent. -/
def isJunk (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) : Bool :=
  (picker agents Y g).isNone && (upOf P up g).isNone

omit [DecidableEq A] in
theorem junkList_eq_filter : junkList P agents up Y goods = goods.filter (isJunk P agents up Y) := rfl

/-- `|NA|`: the number of goods (of `goods`) needed alone. -/
def numNA (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) : Nat :=
  goods.countP (naB P agents up Y)

/-- `|F|`: the number of frozen agents (not upgraded, and their pick is in `NA`). -/
def numFrozen (P : Profile A G) (agents up : List A) (Y : A → Option G) : Nat :=
  agents.countP (fun k => frozenB P agents up Y k && !up.contains k)

/-- The number of junk goods that `X` gives to `j`. -/
def junkCount (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (X : G → A)
    (j : A) : Nat :=
  goods.countP (fun g => decide (X g = j) && isJunk P agents up Y g)

omit [DecidableEq A] in
theorem isJunk_pick {k : A} {y : G} (hk : k ∈ agents) (hy : Y k = some y) : isJunk P agents up Y y = false := by
  cases hp : picker agents Y y with
  | none => exact absurd hy (picker_none hp k hk)
  | some _ => simp [isJunk, hp]

omit [DecidableEq A] in
theorem isJunk_upc {u : A} (hu : u ∈ up) : isJunk P agents up Y (P.c u) = false := by
  cases hp : upOf P up (P.c u) with
  | none => exact absurd rfl (upOf_none hp u hu)
  | some _ => simp [isJunk, hp]

omit [DecidableEq A] in
theorem isJunk_true {g : G} (h : isJunk P agents up Y g = true) :
    (∀ k ∈ agents, Y k ≠ some g) ∧ ∀ u ∈ up, P.c u ≠ g := by
  simp only [isJunk, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨picker_none h.1, upOf_none h.2⟩

/-- Per agent: `cap(k) + [k has a pick] + [k upgraded] + [k frozen] = 2`. -/
theorem cap_add (hV : Valid P agents goods Y up) (k : A) :
    cap P agents up Y k + (if (Y k).isSome then 1 else 0) + (if up.contains k then 1 else 0) +
      (if frozenB P agents up Y k && !up.contains k then 1 else 0) = 2 := by
  by_cases hu : k ∈ up
  · simp [cap, hu, hV.up_b k hu]
  · cases hf : frozenB P agents up Y k with
    | false =>
      cases hy : Y k with
      | none => simp [cap, hf, hu, hy]
      | some y => simp [cap, hf, hu, hy]
    | true =>
      cases hy : Y k with
      | none => simp [frozenB, hy] at hf
      | some y => simp [cap, hf, hu]

/-- Per good: a good is somebody's pick, or the `c` of an upgraded agent, or junk, exactly one of these. -/
theorem good_split (hV : Valid P agents goods Y up) (hag : agents.Nodup) {g : G} :
    agents.countP (fun k => decide (Y k = some g)) + agents.countP (fun k => up.contains k && decide (P.c k = g)) +
      (if isJunk P agents up Y g then 1 else 0) = 1 := by
  have uniqY : ∀ x ∈ agents, ∀ y ∈ agents, decide (Y x = some g) = true → decide (Y y = some g) = true → x = y :=
    fun x _ y _ hx hy => hV.pick_inj x y g (by simpa using hx) (by simpa using hy)
  have uniqC : ∀ x ∈ agents, ∀ y ∈ agents, (up.contains x && decide (P.c x = g)) = true →
      (up.contains y && decide (P.c y = g)) = true → x = y := by
    intro x _ y _ hx hy
    simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hx hy
    exact hV.up_c_inj x hx.1 y hy.1 (hx.2.trans hy.2.symm)
  cases hp : picker agents Y g with
  | some k =>
    obtain ⟨hk, hYk⟩ := picker_some hp
    have h1 := countP_eq_one hag uniqY hk (by simp [hYk])
    have h2 : agents.countP (fun k => up.contains k && decide (P.c k = g)) = 0 :=
      List.countP_eq_zero.mpr fun x _ hx => by
        simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hx
        exact (hV.up_c x hx.1).2 k (hx.2 ▸ hYk)
    have h3 : isJunk P agents up Y g = false := by simp [isJunk, hp]
    rw [h1, h2, h3]; rfl
  | none =>
    have h1 : agents.countP (fun k => decide (Y k = some g)) = 0 :=
      List.countP_eq_zero.mpr fun x hx hxg => picker_none hp x hx (by simpa using hxg)
    cases hu : upOf P up g with
    | some u =>
      obtain ⟨hu', hc⟩ := upOf_some hu
      have h2 := countP_eq_one hag uniqC (hV.up_mem u hu') (by simp [hu', hc])
      have h3 : isJunk P agents up Y g = false := by simp [isJunk, hu]
      rw [h1, h2, h3]; rfl
    | none =>
      have h2 : agents.countP (fun k => up.contains k && decide (P.c k = g)) = 0 :=
        List.countP_eq_zero.mpr fun x _ hx => by
          simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hx
          exact upOf_none hu x hx.1 hx.2
      have h3 : isJunk P agents up Y g = true := by simp [isJunk, hp, hu]
      rw [h1, h2, h3]; rfl

/-- The goods are the picks, the goods `c u` of the upgraded agents, and the junk:
`m = #picks + |U| + |J|`. -/
theorem length_goods (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup) :
    goods.length = agents.countP (fun k => (Y k).isSome) + agents.countP (fun k => up.contains k) +
      (junkList P agents up Y goods).length := by
  have e1 : goods.length = (goods.map (fun g => agents.countP (fun k => decide (Y k = some g)) +
      agents.countP (fun k => up.contains k && decide (P.c k = g)) +
      (if isJunk P agents up Y g then 1 else 0))).sum := by
    rw [sum_map_congr' (fun g _ => good_split hV hag (g := g)), sum_map_const]; omega
  rw [sum_map_add', sum_map_add'] at e1
  rw [← LB4.sum_countP_comm (fun k g => decide (Y k = some g)) agents goods,
    ← LB4.sum_countP_comm (fun k g => up.contains k && decide (P.c k = g)) agents goods,
    ← LB4.countP_eq_sum] at e1
  rw [e1, junkList_eq_filter, ← List.countP_eq_length_filter, LB4.countP_eq_sum (fun k => (Y k).isSome),
    LB4.countP_eq_sum (fun k => up.contains k)]
  congr 2
  · apply sum_map_congr'
    intro k hk
    have := LB4.countP_base goods hgd (b := Y k) (fun y hy => (hV.pick k y hy).2.1)
    rw [this]
    cases Y k <;> simp
  · apply sum_map_congr'
    intro k hk
    by_cases hu : k ∈ up
    · have : goods.countP (fun g => up.contains k && decide (P.c k = g)) =
          goods.countP (fun g => decide (P.c k = g)) := List.countP_congr (fun g _ => by simp [hu])
      rw [this, countP_eq_self hgd]
      simp [hu, (hV.up_c k hu).1]
    · have : goods.countP (fun g => up.contains k && decide (P.c k = g)) = 0 :=
        List.countP_eq_zero.mpr fun g _ h => hu (by simp at h; exact h.1)
      rw [this]; simp [hu]

/-- The slots: `S + #picks + |U| + |F| = 2n`. -/
theorem slotSum_add (hV : Valid P agents goods Y up) :
    slotSum P agents up Y + agents.countP (fun k => (Y k).isSome) + agents.countP (fun k => up.contains k) +
      numFrozen P agents up Y = 2 * agents.length := by
  unfold slotSum numFrozen
  rw [LB4.countP_eq_sum (fun k => (Y k).isSome), LB4.countP_eq_sum (fun k => up.contains k),
    LB4.countP_eq_sum (fun k => frozenB P agents up Y k && !up.contains k), ← sum_map_add', ← sum_map_add',
    ← sum_map_add', sum_map_congr' (fun k _ => cap_add hV k), sum_map_const]

/-- **`|F| = |NA|`.** In a valid pre-allocation every good of `NA` is the pick of exactly one agent, which is
frozen, and every frozen agent's pick is in `NA`. -/
theorem numFrozen_eq_numNA (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup) :
    numFrozen P agents up Y = numNA P agents up Y goods := by
  unfold numFrozen numNA
  have e1 : agents.countP (fun k => frozenB P agents up Y k && !up.contains k) =
      (agents.map (fun k => goods.countP
        (fun g => decide (Y k = some g) && naB P agents up Y g && !up.contains k))).sum := by
    rw [LB4.countP_eq_sum]
    apply sum_map_congr'
    intro k hk
    cases hy : Y k with
    | none =>
      have : frozenB P agents up Y k = false := by simp [frozenB, hy]
      rw [this, List.countP_eq_zero.mpr (fun g _ h => by simp at h)]
      simp
    | some y =>
      have hfz : frozenB P agents up Y k = naB P agents up Y y := by simp [frozenB, hy]
      have hyg := (hV.pick k y hy).2.1
      rw [hfz]
      by_cases hb : (naB P agents up Y y && !up.contains k) = true
      · simp only [hb, ↓reduceIte]
        refine (countP_eq_one hgd (fun x _ z _ hx hz => ?_) hyg ?_).symm
        · simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at hx hz
          exact hx.1.1.symm.trans hz.1.1
        · simp only [Bool.and_eq_true] at hb
          have hku : k ∉ up := by simpa using hb.2
          simp [hb.1, hku]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        refine (List.countP_eq_zero.mpr fun g _ h => hb ?_).symm
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at h
        have hku : k ∉ up := by simpa using h.2
        rw [h.1.1]; simp [h.1.2, hku]
  rw [e1, LB4.sum_countP_comm (fun k g => decide (Y k = some g) && naB P agents up Y g && !up.contains k),
    LB4.countP_eq_sum]
  apply sum_map_congr'
  intro g hg
  by_cases hna : naB P agents up Y g = true
  · obtain ⟨k, hk⟩ := hV.na_picked hg (naB_iff.mp hna)
    have hka := (hV.pick k g hk).1
    have hku : k ∉ up := fun hku => by
      rw [hV.up_b k hku] at hk
      cases hk
      exact (hV.v2 k hku).1 (naB_iff.mp hna)
    simp only [hna, ↓reduceIte]
    refine countP_eq_one hag (fun x _ z _ hx hz => ?_) hka ?_
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx hz
      exact hV.pick_inj x z g hx.1.1 hz.1.1
    · simp [hk, hku]
  · simp only [hna, Bool.false_eq_true, ↓reduceIte]
    exact List.countP_eq_zero.mpr fun k _ h => by simp at h

/-- **`ω = m − 2n + |NA|`.** In a valid pre-allocation of distinct agents and goods, the overflow
`ω = |J| − S` equals `m − 2n + |NA|` (`m` goods, `n` agents, `NA` counted over the goods). -/
theorem omega_eq (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup) :
    ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y =
      (goods.length : Int) - 2 * (agents.length : Int) + numNA P agents up Y goods := by
  have h1 := length_goods hV hag hgd
  have h2 := slotSum_add hV
  have h3 := numFrozen_eq_numNA hV hag hgd
  omega

variable {o : A} {X : G → A}

/-- The junk goods are split among the listed agents: `|J| = Σ_j #(junk in X_j)`. -/
theorem junkCount_sum {oo : Option A} (hC : Completion P agents goods Y up oo X) (hag : agents.Nodup) :
    (agents.map (junkCount P agents up Y goods X)).sum = (junkList P agents up Y goods).length := by
  unfold junkCount
  rw [LB4.sum_countP_comm (fun j g => decide (X g = j) && isJunk P agents up Y g), junkList_eq_filter,
    ← List.countP_eq_length_filter, LB4.countP_eq_sum (isJunk P agents up Y)]
  apply sum_map_congr'
  intro g hg
  by_cases hj : isJunk P agents up Y g = true
  · simp only [hj, Bool.and_true, ↓reduceIte]
    rw [countP_eq_self hag (X g)]
    simp [hC.alloc g hg]
  · simp only [hj, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact List.countP_eq_zero.mpr (fun _ _ h => by simp at h)

/-- An agent `j ∉ up` receives as junk exactly the goods of its bundle other than its pick. -/
theorem junkCount_eq_filter {oo : Option A} (hC : Completion P agents goods Y up oo X) {j : A}
    (hj : j ∈ agents) (hju : j ∉ up) :
    junkCount P agents up Y goods X j = ((bundle goods X j).filter (fun g => Y j ≠ some g)).length := by
  unfold junkCount bundle
  rw [← List.countP_eq_length_filter, List.countP_filter]
  apply List.countP_congr
  intro g _
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  constructor
  · rintro ⟨hX, hJ⟩
    exact ⟨fun hy => (isJunk_true hJ).1 j hj hy, hX⟩
  · rintro ⟨hy, hX⟩
    refine ⟨hX, ?_⟩
    cases hp : picker agents Y g with
    | some k =>
      obtain ⟨-, hYk⟩ := picker_some hp
      have := hC.pick k g hYk
      rw [hX] at this
      subst this
      exact absurd hYk hy
    | none =>
      cases hu : upOf P up g with
      | some u =>
        obtain ⟨hu', hc⟩ := upOf_some hu
        have := hC.upc u hu'
        rw [hc, hX] at this
        subst this
        exact absurd hu' hju
      | none => simp [isJunk, hp, hu]

/-- An agent other than the owner receives no junk if it is upgraded or frozen (it has no slot), and as many
junk goods as its bundle has beyond its pick if it is a terminal. -/
theorem junkCount_other (hV : Valid P agents goods Y up) (hC : Completion P agents goods Y up (some o) X)
    {j : A} (hj : j ∈ agents) (hjo : j ≠ o) :
    ((j ∈ up ∨ frozenB P agents up Y j = true) → junkCount P agents up Y goods X j = 0 ∧
        cap P agents up Y j = 0) ∧
    (j ∉ up → frozenB P agents up Y j = false →
      junkCount P agents up Y goods X j = ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ∧
      cap P agents up Y j = if Y j = none then 2 else 1) := by
  have hoj : some o ≠ some j := fun e => hjo (Option.some.inj e).symm
  refine ⟨fun h => ⟨List.countP_eq_zero.mpr fun g hg hgj => ?_, ?_⟩, fun hju hf =>
    ⟨junkCount_eq_filter hC hj hju, ?_⟩⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hgj
    rcases h with hu | hf
    · rcases hC.upOnly j hu hoj g hg hgj.1 with rfl | rfl
      · rw [isJunk_pick hj (hV.up_b j hu)] at hgj; cases hgj.2
      · rw [isJunk_upc hu] at hgj; cases hgj.2
    · obtain ⟨y, hy, hna⟩ := frozenB_iff.mp hf
      have hju : j ∉ up := fun hu => (hV.v2 j hu).1 (by rw [hV.up_b j hu] at hy; cases hy; exact hna)
      have := hC.frozen j hj hju y hy hna g hg hgj.1
      subst this
      rw [isJunk_pick hj hy] at hgj; cases hgj.2
  · rcases h with hu | hf
    · simp [cap, hu]
    · simp [cap, hf]
  · simp [cap, hf, hju]

/-- The owner's bundle: its base (its pick, and its `c` if it is upgraded) and its junk. -/
theorem owner_bundle_length (hV : Valid P agents goods Y up) (hC : Completion P agents goods Y up (some o) X)
    (hgd : goods.Nodup) (ho : o ∈ agents) :
    (bundle goods X o).length = junkCount P agents up Y goods X o + (if (Y o).isSome then 1 else 0) +
      (if up.contains o then 1 else 0) := by
  unfold bundle junkCount
  rw [← List.countP_eq_length_filter]
  rw [countP_eq_add3 (q := fun g => decide (X g = o) && isJunk P agents up Y g)
    (r := fun g => decide (Y o = some g)) (s := fun g => up.contains o && decide (P.c o = g)) ?_]
  · congr 1
    · congr 1
      have := LB4.countP_base goods hgd (b := Y o) (fun y hy => (hV.pick o y hy).2.1)
      rw [this]; cases Y o <;> simp
    · by_cases hu : o ∈ up
      · have : goods.countP (fun g => up.contains o && decide (P.c o = g)) =
            goods.countP (fun g => decide (P.c o = g)) := List.countP_congr (fun g _ => by simp [hu])
        rw [this, countP_eq_self hgd]
        simp [hu, (hV.up_c o hu).1]
      · rw [List.countP_eq_zero.mpr fun g _ h => hu (by simp at h; exact h.1)]
        simp [hu]
  · intro g hg
    have hcpick : ∀ k, Y k = some g → ¬ (o ∈ up ∧ P.c o = g) := fun k hk h =>
      (hV.up_c o h.1).2 k (h.2 ▸ hk)
    cases hp : picker agents Y g with
    | some k =>
      obtain ⟨hk, hYk⟩ := picker_some hp
      have hX := hC.pick k g hYk
      have hJ : isJunk P agents up Y g = false := by simp [isJunk, hp]
      have hc := hcpick k hYk
      have hc' : (up.contains o && decide (P.c o = g)) = false := by
        cases h : up.contains o && decide (P.c o = g)
        · rfl
        · simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h; exact absurd h hc
      simp only [hc']
      by_cases hko : k = o
      · subst hko
        simp [hX, hJ, hYk]
      · have hYo : Y o ≠ some g := fun h => hko (hV.pick_inj k o g hYk h)
        simp [hX, hJ, hko, hYo]
    | none =>
      have hYo : Y o ≠ some g := picker_none hp o ho
      cases hu : upOf P up g with
      | some u =>
        obtain ⟨hu', hc⟩ := upOf_some hu
        have hX : X g = u := hc ▸ hC.upc u hu'
        have hJ : isJunk P agents up Y g = false := by simp [isJunk, hu]
        by_cases huo : u = o
        · subst huo
          simp [hX, hJ, hYo, hu', hc]
        · have hc' : (up.contains o && decide (P.c o = g)) = false := by
            cases h : up.contains o && decide (P.c o = g)
            · rfl
            · simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
              exact absurd (hV.up_c_inj u hu' o h.1 (hc.trans h.2.symm)) huo
          simp only [hc']
          simp [hX, hJ, hYo, huo]
      | none =>
        have hJ : isJunk P agents up Y g = true := by simp [isJunk, hp, hu]
        have hc' : (up.contains o && decide (P.c o = g)) = false := by
          cases h : up.contains o && decide (P.c o = g)
          · rfl
          · simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
            exact absurd h.2 (upOf_none hu o h.1)
        simp only [hc']
        simp [hJ, hYo]

/-- **Every completion gives the owner at least `ω + 2` goods.** For a completion of a valid pre-allocation
with an owner `o` that is a listed terminal or upgraded agent: `|X_o| ≥ |J| − S + 2`. -/
theorem Completion.owner_length_ge (hV : Valid P agents goods Y up)
    (hC : Completion P agents goods Y up (some o) X) (hag : agents.Nodup) (hgd : goods.Nodup)
    (ho : o ∈ agents) (hoT : o ∈ up ∨ ∀ y, Y o = some y → ¬ P.NA agents (· ∈ up) Y y) :
    ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y + 2 ≤ (bundle goods X o).length := by
  have hsum := junkCount_sum hC hag
  have hsplit := sum_split (junkCount P agents up Y goods X) hag ho
  have hS := sum_split (cap P agents up Y) hag ho
  have hle : (agents.map (fun j => if j = o then 0 else junkCount P agents up Y goods X j)).sum ≤
      (agents.map (fun j => if j = o then 0 else cap P agents up Y j)).sum := by
    apply sum_map_le'
    intro j hj
    by_cases hjo : j = o
    · simp [hjo]
    · simp only [hjo, ↓reduceIte]
      obtain ⟨h1, h2⟩ := junkCount_other hV hC hj hjo
      by_cases hsl : j ∈ up ∨ frozenB P agents up Y j = true
      · rw [(h1 hsl).1]; exact Nat.zero_le _
      · have hju : j ∉ up := fun h => hsl (Or.inl h)
        have hf : frozenB P agents up Y j = false := by simpa using fun h => hsl (Or.inr h)
        rw [(h2 hju hf).1, (h2 hju hf).2]
        exact hC.slots j hj (fun e => hjo (Option.some.inj e).symm) hju (not_frozen_iff.mp hf)
  have hlen := owner_bundle_length hV hC hgd ho
  have hcap := cap_add hV o
  have hfo : (if frozenB P agents up Y o && !up.contains o then 1 else 0) = 0 := by
    rcases hoT with hu | hT
    · simp [hu]
    · simp [not_frozen_iff.mpr hT]
  unfold slotSum
  omega

/-- **Exactly `ω + 2` goods when the other slots are full.** If moreover every terminal other than the owner
has its slots full (one good beyond its pick, or two if it has none), the owner gets exactly `|J| − S + 2`
goods. -/
theorem Completion.owner_length_eq (hV : Valid P agents goods Y up)
    (hC : Completion P agents goods Y up (some o) X) (hag : agents.Nodup) (hgd : goods.Nodup)
    (ho : o ∈ agents) (hoT : o ∈ up ∨ ∀ y, Y o = some y → ¬ P.NA agents (· ∈ up) Y y)
    (hfull : ∀ j ∈ agents, j ≠ o → j ∉ up → (∀ y, Y j = some y → ¬ P.NA agents (· ∈ up) Y y) →
      ((bundle goods X j).filter (fun g => Y j ≠ some g)).length = if Y j = none then 2 else 1) :
    ((bundle goods X o).length : Int) = ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y + 2 := by
  have hsum := junkCount_sum hC hag
  have hsplit := sum_split (junkCount P agents up Y goods X) hag ho
  have hS := sum_split (cap P agents up Y) hag ho
  have heq : (agents.map (fun j => if j = o then 0 else junkCount P agents up Y goods X j)).sum =
      (agents.map (fun j => if j = o then 0 else cap P agents up Y j)).sum := by
    apply sum_map_congr'
    intro j hj
    by_cases hjo : j = o
    · simp [hjo]
    · simp only [hjo, ↓reduceIte]
      obtain ⟨h1, h2⟩ := junkCount_other hV hC hj hjo
      by_cases hsl : j ∈ up ∨ frozenB P agents up Y j = true
      · rw [(h1 hsl).1, (h1 hsl).2]
      · have hju : j ∉ up := fun h => hsl (Or.inl h)
        have hf : frozenB P agents up Y j = false := by simpa using fun h => hsl (Or.inr h)
        rw [(h2 hju hf).1, (h2 hju hf).2]
        exact hfull j hj hjo hju (not_frozen_iff.mp hf)
  have hlen := owner_bundle_length hV hC hgd ho
  have hcap := cap_add hV o
  have hfo : (if frozenB P agents up Y o && !up.contains o then 1 else 0) = 0 := by
    rcases hoT with hu | hT
    · simp [hu]
    · simp [not_frozen_iff.mpr hT]
  unfold slotSum
  omega

/-- **Proposition (size of the large bundle).** Let `(Y, up)` be a valid pre-allocation of distinct agents
and goods, `ω = |J| − S`. Then `ω = m − 2n + |NA|`; every completion with an owner `o` (a listed terminal or
upgraded agent) gives `o` at least `ω + 2` goods; and exactly `ω + 2` when the slots of the other terminals
are full. (The paper assumes `ω ≥ 1`, which is not needed here.) -/
theorem largeBundle_size (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup) :
    ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y =
      (goods.length : Int) - 2 * (agents.length : Int) + numNA P agents up Y goods ∧
    ∀ (o : A) (X : G → A), o ∈ agents → (o ∈ up ∨ ∀ y, Y o = some y → ¬ P.NA agents (· ∈ up) Y y) →
      Completion P agents goods Y up (some o) X →
      ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y + 2 ≤ (bundle goods X o).length ∧
      ((∀ j ∈ agents, j ≠ o → j ∉ up → (∀ y, Y j = some y → ¬ P.NA agents (· ∈ up) Y y) →
          ((bundle goods X j).filter (fun g => Y j ≠ some g)).length = if Y j = none then 2 else 1) →
        ((bundle goods X o).length : Int) =
          ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y + 2) :=
  ⟨omega_eq hV hag hgd, fun _ _ ho hoT hC =>
    ⟨Completion.owner_length_ge hV hC hag hgd ho hoT, Completion.owner_length_eq hV hC hag hgd ho hoT⟩⟩

/-! ### K3ALG's completion fills every other slot when `H` lists no good twice -/

omit [DecidableEq A] in
/-- `fill` gives every agent exactly its slots when the list is long enough and has no repeated good. -/
theorem fill_count_eq {s : A → Nat} [DecidableEq A] : ∀ {ks : List A} {rest : List G}, ks.Nodup → rest.Nodup →
    (ks.map s).sum ≤ rest.length → ∀ j ∈ ks, rest.countP (fun g => decide (fill s ks rest g = some j)) = s j
  | [], _, _, _, _, j, hj => by simp at hj
  | k :: ks, rest, hks, hr, hsum, j, hj => by
    obtain ⟨hk, hks'⟩ := List.nodup_cons.mp hks
    simp only [List.map_cons, List.sum_cons] at hsum
    have hdisj := (List.nodup_append.mp ((List.take_append_drop (s k) rest).symm ▸ hr)).2.2
    have hdrop : (rest.drop (s k)).Nodup := hr.sublist (List.drop_sublist _ _)
    have htake : (rest.take (s k)).Nodup := hr.sublist (List.take_sublist _ _)
    have e : ∀ g, fill s (k :: ks) rest g =
        if g ∈ rest.take (s k) then some k else fill s ks (rest.drop (s k)) g := fun g => rfl
    by_cases hjk : j = k
    · subst hjk
      have : rest.countP (fun g => decide (fill s (j :: ks) rest g = some j)) =
          rest.countP (fun g => decide (g ∈ rest.take (s j))) := by
        apply List.countP_congr
        intro g _
        rw [e]
        by_cases hg : g ∈ rest.take (s j)
        · simp [hg]
        · simp only [hg, ↓reduceIte, decide_eq_true_eq, iff_false]
          intro hf
          exact hk (fill_some hf).1
      rw [this, countP_eq_of_mem_iff hr htake (fun g hg => by
        simp only [decide_eq_true_eq] at hg
        exact ⟨fun _ => hg, fun _ => List.mem_of_mem_take hg⟩)]
      rw [List.countP_eq_length_filter, List.filter_eq_self.mpr (fun g hg => by simp [hg]),
        List.length_take]
      omega
    · have hj' := (List.mem_cons.mp hj).resolve_left hjk
      have : rest.countP (fun g => decide (fill s (k :: ks) rest g = some j)) =
          rest.countP (fun g => decide (fill s ks (rest.drop (s k)) g = some j)) := by
        apply List.countP_congr
        intro g _
        rw [e]
        by_cases hg : g ∈ rest.take (s k)
        · simp only [hg, ↓reduceIte, decide_eq_true_eq, Option.some.injEq]
          constructor
          · intro h; exact absurd h.symm hjk
          · intro hf
            exact absurd rfl (hdisj g hg g (fill_some hf).2.1)
        · simp [hg]
      rw [this, countP_eq_of_mem_iff hr hdrop (fun g hg => by
        simp only [decide_eq_true_eq] at hg
        exact ⟨fun _ => (fill_some hg).2.1, fun h => List.mem_of_mem_drop h⟩)]
      exact fill_count_eq hks' hdrop (by rw [List.length_drop]; omega) j hj'

/-- **K3ALG's completion, when `H` lists no good twice.** For `complete` (`Complete(o, H)`) with owner `o` under
the hypotheses of Lemma 1 (`complete_some`) and `ω ≥ 1`: if `H` has no repeated good, the terminals other than
`o` get their slots full, so the owner gets exactly `ω + 2 = |J| − S + 2` goods. -/
theorem complete_owner_length (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup)
    {o : A} (ho : o ∈ agents) (hoT : o ∈ up ∨ ∀ y, Y o = some y → ¬ P.NA agents (· ∈ up) Y y)
    {H : List G} (hH : ∀ h ∈ H, h ∈ junkList P agents up Y goods) (hHnd : H.Nodup)
    (hHfit : H.length ≤ (agents.map (slotsExcept (cap P agents up Y) (some o))).sum)
    (hhit : ∀ x ∈ agents, x ≠ o → x ∉ up → Y x = some (P.a x) →
      (P.b x ∈ junkList P agents up Y goods ∨ InBase P up Y o (P.b x)) →
      (P.c x ∈ junkList P agents up Y goods ∨ InBase P up Y o (P.c x)) → P.b x ∈ H ∨ P.c x ∈ H)
    (hω : slotSum P agents up Y < (junkList P agents up Y goods).length) (d : A) :
    ((bundle goods (complete P agents up Y goods (some o) H d) o).length : Int) =
      ((junkList P agents up Y goods).length : Int) - slotSum P agents up Y + 2 := by
  have hC := complete_some (d := d) hV hag hgd ho hoT hH hHfit hhit
  refine Completion.owner_length_eq hV hC hag hgd ho hoT (fun j hj hjo hju hT => ?_)
  -- the list of junk goods `fill` distributes
  have hJnd : (junkList P agents up Y goods).Nodup := hgd.sublist List.filter_sublist
  have hLnd : (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)).Nodup := by
    refine List.nodup_append.mpr ⟨hHnd, hJnd.sublist List.filter_sublist, fun a _ b hb e => ?_⟩
    subst e
    exact (by simpa using (List.mem_filter.mp hb).2 : a ∉ H) (by assumption)
  have hLlen : (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)).length =
      (junkList P agents up Y goods).length := by
    rw [List.length_append, List.length_eq_countP_add_countP (fun g => decide (g ∈ H))
      (l := junkList P agents up Y goods), ← List.countP_eq_length_filter]
    have : H.length = (junkList P agents up Y goods).countP (fun g => decide (g ∈ H)) := by
      rw [← countP_eq_of_mem_iff hHnd hJnd (p := fun g => decide (g ∈ H)) (fun g hg => by
        simp only [decide_eq_true_eq] at hg
        exact ⟨fun _ => hH g hg, fun _ => hg⟩)]
      rw [List.countP_eq_length_filter, List.filter_eq_self.mpr (fun g hg => by simp [hg])]
    rw [this]
    congr 1
    exact List.countP_congr (fun g _ => by simp)
  have hsl : (agents.map (slotsExcept (cap P agents up Y) (some o))).sum + cap P agents up Y o =
      slotSum P agents up Y := by
    have := sum_split (cap P agents up Y) hag ho
    have e : (agents.map (slotsExcept (cap P agents up Y) (some o))).sum =
        (agents.map (fun j => if j = o then 0 else cap P agents up Y j)).sum :=
      sum_map_congr' (fun j _ => by
        by_cases hjo : j = o
        · simp [slotsExcept, hjo]
        · have : some o ≠ some j := fun e => hjo (Option.some.inj e).symm
          simp [slotsExcept, hjo, this])
    unfold slotSum; omega
  have hcnt := fill_count_eq (s := slotsExcept (cap P agents up Y) (some o)) hag hLnd
    (by rw [hLlen]; omega) j hj
  have hoj : some o ≠ some j := fun e => hjo (Option.some.inj e).symm
  have hfz : frozenB P agents up Y j = false := not_frozen_iff.mpr hT
  have hsj : slotsExcept (cap P agents up Y) (some o) j = if Y j = none then 2 else 1 := by
    simp [slotsExcept, hoj, cap, hfz, hju]
  rw [← hsj, ← hcnt, ← List.countP_eq_length_filter, bundle, List.countP_filter]
  -- the goods `j` gets beyond its pick are exactly those `fill` places with it
  have hmemJ : ∀ g, g ∈ H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H) →
      g ∈ junkList P agents up Y goods := by
    intro g hgL
    rcases List.mem_append.mp hgL with h | h
    · exact hH g h
    · exact (List.mem_filter.mp h).1
  rw [List.countP_congr (l := goods) (q := fun g => decide (fill (slotsExcept (cap P agents up Y) (some o))
      agents (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = some j)) (fun g _ => ?_)]
  · refine countP_eq_of_mem_iff hgd hLnd (fun g hf => ?_)
    simp only [decide_eq_true_eq] at hf
    have hgL := (fill_some hf).2.1
    exact ⟨fun _ => hgL, fun _ => (mem_junkList.mp (hmemJ g hgL)).1⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hy, hX⟩
      rcases complete_cases (P := P) (agents := agents) (up := up) (Y := Y) (goods := goods) (o := some o)
        (H := H) (d := d) g with ⟨k, hp, hX'⟩ | ⟨-, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨-, -, -, hX'⟩
      · rw [hX'] at hX; subst hX; exact absurd (picker_some hp).2 hy
      · rw [hX'] at hX; subst hX; exact absurd (upOf_some hu).1 hju
      · rw [hX'] at hX; subst hX; exact hf
      · rw [hX'] at hX; simp only [Option.getD_some] at hX; exact absurd hX.symm hjo
    · intro hf
      obtain ⟨-, hp, hu⟩ := mem_junkList.mp (hmemJ g (fill_some hf).2.1)
      refine ⟨fun hy => picker_none hp j hj hy, ?_⟩
      unfold complete; rw [hp, hu]; dsimp only; rw [hf]; rfl
end size

end LB

/-! ### The remark "a repeated good": K3ALG's owner can get more than `ω + 2` goods -/

namespace K3
namespace Examples

/-- The instance of the paper's remark "a repeated good" (`paper/k3/examples/`): four agents value `g₀` at 3,
and agent `i` also values `g_{2i+1}` at 4 and `g_{2i+2}` at 2 (nine goods). -/
def repeatedGood : Inst := mkInst 4 9 [[3, 4, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 4, 2, 0, 0, 0, 0],
  [3, 0, 0, 0, 0, 4, 2, 0, 0], [3, 0, 0, 0, 0, 0, 0, 4, 2]]

/-- Stage L of K3ALG on `repeatedGood` (nobody is peeled): the rankings, Phase 1's order and picks, and the
upgraded agents (none). -/
def rgP : LB.Profile (Fin 4) (Fin 9) := profileOf repeatedGood.v (List.finRange 9) 0
def rgOrder : List (Fin 4) := LB.r1Order rgP 4 (List.finRange 4) (List.finRange 9)
def rgY : Fin 4 → Option (Fin 9) := LB.phase1 rgP rgOrder (List.finRange 9)
def rgUp : List (Fin 4) := LB.lbUp rgP (List.finRange 4) (List.finRange 9) rgY

theorem repeatedGood_relevant : ∀ i, numRelevant repeatedGood i ≤ 3 := by decide

/-- **The state.** K3ALG's output is Stage L's (LB⁺ on all agents and goods). All four agents pick their tops
(`g₁, g₃, g₅, g₇`), nobody is upgraded, `NA = ∅`, `|J| = 5` and `S = 4`, so `ω = 1 = m − 2n + |NA|`. The owner
is `r = 3`, and `HitSet(E₃)` is `(g₀, g₀)`: it lists `g₀` twice. -/
theorem repeatedGood_state :
    (∀ g, algoSpec repeatedGood (by decide) g = lbStage repeatedGood.v (List.finRange 4) (List.finRange 9)
      (⟨0, by decide⟩ : Fin repeatedGood.m) (⟨0, by decide⟩ : Fin repeatedGood.n) g) ∧
    (List.finRange 4).map rgY = [some 1, some 3, some 5, some 7] ∧ rgUp = [] ∧
    LB.numNA rgP (List.finRange 4) rgUp rgY (List.finRange 9) = 0 ∧
    (LB.junkList rgP (List.finRange 4) rgUp rgY (List.finRange 9)).length = 5 ∧
    LB.slotSum rgP (List.finRange 4) rgUp rgY = 4 ∧
    LB.lastOut rgUp rgOrder = some 3 ∧
    LB.hitSet rgP (LB.junkList rgP (List.finRange 4) rgUp rgY (List.finRange 9))
      (LB.exposedL rgP (List.finRange 4) rgUp rgY (List.finRange 9) 3) = [0, 0] := by
  decide

/-- **The owner gets `ω + 3` goods.** K3ALG's output on `repeatedGood`: agent 1's slot stays empty (its window
holds the repeated `g₀`), and the owner, agent 3, gets `g₄, g₆, g₇, g₈`: four goods, while `ω + 2 = 3`. The output
is EFX₀ (`algo_efx0`). So `Completion.owner_length_eq` needs its hypothesis that the other slots are full, and
`complete_owner_length` its hypothesis that `H` repeats no good. -/
theorem repeatedGood_algo :
    (List.finRange 9).map (fun g => (algo repeatedGood (by decide) g).val) = [0, 0, 2, 1, 3, 2, 3, 3, 3] ∧
    (bundle (List.finRange 9) (algo repeatedGood (by decide)) (⟨3, by decide⟩ : Fin repeatedGood.n)).length = 4 ∧
    ((LB.junkList rgP (List.finRange 4) rgUp rgY (List.finRange 9)).length : Int) -
      LB.slotSum rgP (List.finRange 4) rgUp rgY + 3 = 4 ∧
    repeatedGood.EFX0 (algo repeatedGood (by decide)) := by
  refine ⟨?_, ?_, ?_, algo_efx0 repeatedGood (by decide) repeatedGood_relevant⟩
  · simp only [algo_eq_spec]; decide
  · simp only [algo_eq_spec]; decide
  · have := repeatedGood_state
    rw [this.2.2.2.2.1, this.2.2.2.2.2.1]; rfl

end Examples
end K3

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.blk_le_lastOut
#print axioms EFX.LB.lastOut_lastBlock
#print axioms EFX.LB.numFrozen_eq_numNA
#print axioms EFX.LB.omega_eq
#print axioms EFX.LB.Completion.owner_length_ge
#print axioms EFX.LB.Completion.owner_length_eq
#print axioms EFX.LB.largeBundle_size
#print axioms EFX.LB.complete_owner_length
#print axioms EFX.K3.Examples.repeatedGood_state
#print axioms EFX.K3.Examples.repeatedGood_algo
