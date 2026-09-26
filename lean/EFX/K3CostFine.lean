import EFX.K3Real

/-!
# The finer operation count of K3ALG: `O(n⁴ + n²m)` (`proofs/k3_algorithm.md` §5)

`EFX.K3.algoC_cost` bounds the counted operations of `EFX.K3.algoC` by `400 (n + m + 1)⁴`, with one number
`N = n + m + 1` for every list. This file re-derives the cost of every stage with two numbers: `a`, a bound on the
lists of agents (the agents left, the upgraded agents, the order, the exposed agents, the hitting set, the chain,
the peeled goods), and `b`, a bound on the lists of goods (the goods left, the pools, the junk). The upgraded
agents after the rotation, `k :: up`, have at most `a + 1` elements. At the top, `a = n` and `b = m`.

- `algoC_cost_fine`: **the finer bound.** On every instance with `n ≥ 1` agents and `m` goods,
  `(algoC I hn).cost ≤ n⁴ + 20 n³ + 25 n²m + 124 n² + 47 nm + 119 n + 22 m + 3`.
- `algoC_cost_fine'`: hence `≤ 145 n⁴ + 72 n²m + 119 n + 22 m + 3`, and `algoC_cost_fine''`: `≤ 270 (n⁴ + n²m)`.
- `algoOrdC_cost_fine`: the same for K3ALG on ordered values (`EFX.K3Real`), plus the surrogate's
  `n (m + 12) + 10 nm + 971 n`.

Where the degree-4 terms come from (the per-stage lemmas below, `a = n`, `b = m`):
- `a⁴ + 17 a³ + a²b`: LB's upgrade loop (`lbUpC_cost_fine`): at most `a` rounds, each testing every agent, and
  each test computes `NA` for one good by scanning the agents with a membership test in the upgraded agents
  (`a²` per test) and tests `c_k ∈ J` (`b` per test);
- `a³` terms: the slot tables (`a` agents × frozen test `a²`) and the need chain (`a` agents × frozen test);
- `a²b` terms: Stage R (`a` rounds × `a` agents × R1 test `6b`), the processing order (`a` steps × `a` agents ×
  three pool memberships), Phase 1's picks and the blocks (tables over `a` agents, each replaying Phase 1:
  `a` turns × pool scans), and `meet` in the owner tests (`a²` pairs × membership in `J`).
No stage costs more than the written total: every term is `O(n⁴ + n²m)`, and there is no `nm²` or `m²` term.
Every loop over the goods does `O(n)` work per good (a scan of the agents, of the upgraded agents, of the peeled
goods, or of the hitting set, which has at most `n` goods) or `O(1)`; goods lists are scanned inside loops over
agents only. One row of the written table (`proofs/k3_algorithm.md` §5, "rotated state, second owner test,
completion", `O(n³ + nm)`) leaves out that the second owner test runs `hitSetC`, hence `meetC` (pairs of exposed
agents × membership in the junk); counted by the program's loops this is `2 a²b + …` (`hitSetC_cost_fine`), so the
row is `O(n²m + n³)` here, as is the first owner test's row; the total is unaffected.
-/

set_option autoImplicit false

namespace EFX
namespace K3

open Timed LB

/-! ## Arithmetic: multiplying a bound by a list length -/

section arith

/-- A loop over at most `a` elements: multiply a bound in `1, a, b, ab, a², a³` by `a`. -/
theorem mulA_le {len x a b : Nat} (c0 cA cB cAB cA2 cA3 : Nat) (hl : len ≤ a)
    (hx : x ≤ c0 + cA * a + cB * b + cAB * (a * b) + cA2 * (a * a) + cA3 * (a * a * a)) :
    len * x ≤ c0 * a + cA * (a * a) + cB * (a * b) + cAB * (a * a * b) + cA2 * (a * a * a) +
      cA3 * (a * a * a * a) :=
  calc len * x ≤ a * (c0 + cA * a + cB * b + cAB * (a * b) + cA2 * (a * a) + cA3 * (a * a * a)) :=
        Nat.mul_le_mul hl hx
    _ = _ := by simp only [Nat.mul_add]; ac_rfl

/-- A loop over at most `b` elements: multiply a bound in `1, a, a²` by `b`. -/
theorem mulB_le {len x a b : Nat} (c0 cA cA2 : Nat) (hl : len ≤ b) (hx : x ≤ c0 + cA * a + cA2 * (a * a)) :
    len * x ≤ c0 * b + cA * (a * b) + cA2 * (a * a * b) :=
  calc len * x ≤ b * (c0 + cA * a + cA2 * (a * a)) := Nat.mul_le_mul hl hx
    _ = _ := by simp only [Nat.mul_add]; ac_rfl

end arith

/-! ## Polynomial bounds, added syntactically

The bound of LB⁺ sums about thirty stage bounds along its longest path. As in `EFX.K3.lbPlusC_cost` (whose
`cost_sum` adds bounds of the form `K · N⁴`), the sum is formed syntactically, here with bounds of the form
`p.ev a b` for a polynomial `p` given by its coefficients, and compared coefficientwise by `decide`. -/

/-- The polynomial `c0 + cA a + cB b + cAB ab + cA2 a² + cA2B a²b + cA3 a³ + cA4 a⁴` (coefficients default to 0). -/
structure Poly where
  c0 : Nat := 0
  cA : Nat := 0
  cB : Nat := 0
  cAB : Nat := 0
  cA2 : Nat := 0
  cA2B : Nat := 0
  cA3 : Nat := 0
  cA4 : Nat := 0

namespace Poly

/-- Its value at `a`, `b`. -/
def ev (p : Poly) (a b : Nat) : Nat :=
  p.c0 + p.cA * a + p.cB * b + p.cAB * (a * b) + p.cA2 * (a * a) + p.cA2B * (a * a * b) + p.cA3 * (a * a * a) +
    p.cA4 * (a * a * a * a)

/-- The sum of two polynomials. -/
def add (p q : Poly) : Poly :=
  ⟨p.c0 + q.c0, p.cA + q.cA, p.cB + q.cB, p.cAB + q.cAB, p.cA2 + q.cA2, p.cA2B + q.cA2B, p.cA3 + q.cA3,
    p.cA4 + q.cA4⟩

/-- Coefficientwise comparison. -/
def le (p q : Poly) : Bool :=
  decide (p.c0 ≤ q.c0) && decide (p.cA ≤ q.cA) && decide (p.cB ≤ q.cB) && decide (p.cAB ≤ q.cAB) &&
    decide (p.cA2 ≤ q.cA2) && decide (p.cA2B ≤ q.cA2B) && decide (p.cA3 ≤ q.cA3) && decide (p.cA4 ≤ q.cA4)

theorem ev_add (p q : Poly) (a b : Nat) : (p.add q).ev a b = p.ev a b + q.ev a b := by
  simp only [ev, add, Nat.add_mul]; omega

theorem ev_le {p q : Poly} (h : p.le q = true) (a b : Nat) : p.ev a b ≤ q.ev a b := by
  simp only [le, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have := Nat.mul_le_mul_right a h1
  have := Nat.mul_le_mul_right b h2
  have := Nat.mul_le_mul_right (a * b) h3
  have := Nat.mul_le_mul_right (a * a) h4
  have := Nat.mul_le_mul_right (a * a * b) h5
  have := Nat.mul_le_mul_right (a * a * a) h6
  have := Nat.mul_le_mul_right (a * a * a * a) h7
  simp only [ev]
  omega

end Poly

theorem psum {x y a b : Nat} {p q : Poly} (hx : x ≤ p.ev a b) (hy : y ≤ q.ev a b) : x + y ≤ (p.add q).ev a b := by
  rw [Poly.ev_add]; exact Nat.add_le_add hx hy

theorem pweaken {x a b : Nat} {p q : Poly} (h : x ≤ p.ev a b) (hpq : p.le q = true) : x ≤ q.ev a b :=
  Nat.le_trans h (Poly.ev_le hpq a b)

/-- Bound a sum `c₀ + (c₁ + …)` by `q.ev a b`: bound each summand by a hypothesis `cᵢ ≤ pᵢ.ev a b`, add the
polynomials (`psum`), and check `Σ pᵢ ≤ q` coefficientwise by `decide`. -/
macro "poly_sum" : tactic =>
  `(tactic| (apply pweaken
             (repeat (first | with_reducible assumption | with_reducible apply psum))
             decide))

/-! ## Phase 1 -/

section generic
variable {A G : Type} [DecidableEq A] [DecidableEq G] {a b : Nat}

theorem phase1C_cost_fine (P : Profile A G) : ∀ (order : List A) (pool : List G) (k : A),
    pool.length ≤ b → (phase1C P order pool k).cost ≤ order.length * (4 * b + 4)
  | [], _, _, _ => by simp [phase1C]
  | i :: order, pool, k, hp => by
    have hf := favC_cost P pool i
    have hr := removePickC_cost pool (fav P pool i)
    rw [List.length_cons, Nat.succ_mul]
    unfold phase1C
    simp only [bind_cost, tick_cost]
    split
    · omega
    · have ih := phase1C_cost_fine P order (removePick pool (fav P pool i)) k
        (Nat.le_trans (length_removePick pool _) hp)
      simp only [bind_cost, favC_val, removePickC_val]
      omega

theorem blkAuxC_cost_fine (P : Profile A G) : ∀ (order : List A) (pool : List G) (cnt : Nat) (k : A),
    pool.length ≤ b → (blkAuxC P order pool cnt k).cost ≤ order.length * (7 * b + 8)
  | [], _, _, _, _ => by simp [blkAuxC]
  | i :: order, pool, cnt, k, hp => by
    have hfu := fullC_cost P pool i
    have hf := favC_cost P pool i
    have hr := removePickC_cost pool (fav P pool i)
    rw [List.length_cons, Nat.succ_mul]
    unfold blkAuxC
    simp only [bind_cost, tick_cost]
    split
    · simp only [pure_cost]; omega
    · have ih := blkAuxC_cost_fine P order (removePick pool (fav P pool i))
        (if (fullC P pool i).val = true then cnt + 1 else cnt) k (Nat.le_trans (length_removePick pool _) hp)
      simp only [bind_cost, favC_val, removePickC_val]
      omega

theorem r1OrderC_cost_fine (P : Profile A G) : ∀ (fuel : Nat) (rem : List A) (pool : List G),
    rem.length ≤ a → pool.length ≤ b →
      (r1OrderC P fuel rem pool).cost ≤ fuel * (3 * (a * b) + 5 * a + 4 * b + 3)
  | 0, _, _, _, _ => by simp [r1OrderC]
  | fuel + 1, rem, pool, hr, hp => by
    have hfind : (findC (fun j => do let b ← fullC P pool j; pure (!b)) rem).cost ≤ 4 * a + 3 * (a * b) := by
      have h1 := findC_cost (fun j => do let b ← fullC P pool j; pure (!b)) (3 + 3 * b) rem (fun j _ => by
        have := fullC_cost P pool j; simp only [bind_cost, pure_cost]; omega)
      have h2 := mulA_le (b := b) (x := 3 + 3 * b + 1) 4 0 3 0 0 0 hr (by omega)
      omega
    rw [Nat.succ_mul]
    unfold r1OrderC
    simp only [bind_cost]
    split
    · rename_i i hi
      have he := eraseC_cost i rem
      have hf := favC_cost P pool i
      have hrp := removePickC_cost pool (fav P pool i)
      have ih := r1OrderC_cost_fine P fuel (rem.erase i) (removePick pool (fav P pool i))
        (Nat.le_trans List.length_erase_le hr) (Nat.le_trans (length_removePick pool _) hp)
      simp only [bind_cost, eraseC_val, favC_val, removePickC_val, pure_cost]
      omega
    · cases rem with
      | nil => simp [findC]
      | cons i rest =>
        have hf := favC_cost P pool i
        have hrp := removePickC_cost pool (fav P pool i)
        have ih := r1OrderC_cost_fine P fuel rest (removePick pool (fav P pool i))
          (by simp at hr; omega) (Nat.le_trans (length_removePick pool _) hp)
        simp only [bind_cost, favC_val, removePickC_val, pure_cost]
        omega

/-! ## Phase 2 -/

theorem naBC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) (g : G)
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) : (naBC P agents up Y g).cost ≤ a * a + 16 * a := by
  have h1 := anyC_cost (fun i => do
    let u ← memC i up
    let p ← prefersC P Y i g
    pure (!u && p)) (up.length + 14) agents (fun i _ => by
      have := memC_cost i up
      have := prefersC_cost P Y i g
      simp only [bind_cost, pure_cost]
      omega)
  have h2 := mulA_le (b := 0) (x := up.length + 14 + 1) 16 1 0 0 0 0 ha (by omega)
  unfold naBC
  omega

theorem frozenBC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) (k : A)
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) : (frozenBC P agents up Y k).cost ≤ a * a + 16 * a + 1 := by
  unfold frozenBC
  cases hy : Y k with
  | none => simp
  | some y =>
    have := naBC_cost_fine P Y y ha hu
    simp only [bind_cost, tick_cost]
    omega

theorem capC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) (k : A)
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) : (capC P agents up Y k).cost ≤ a * a + 17 * a + 4 := by
  have h1 := frozenBC_cost_fine P Y k ha hu
  have h2 := memC_cost k up
  simp only [capC, bind_cost, tick_cost, pure_cost]
  omega

theorem canUpC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) {J : List G}
    (k : A) (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) (hJ : J.length ≤ b) :
    (canUpC P agents up Y J k).cost ≤ a * a + 17 * a + b + 11 := by
  have h1 := memC_cost k up
  have h2 := pickRankC_cost P Y k
  have h3 := memC_cost (P.c k) J
  have h4 := naBC_cost_fine P Y (P.b k) ha hu
  simp only [canUpC, bind_cost, tick_cost, pure_cost]
  omega

/-- The upgrade loop: each round tests every agent (`a (a² + 17a + b + 12)`) and removes one junk good. -/
theorem upgradesC_cost_fine (P : Profile A G) {agents : List A} (Y : A → Option G)
    (ha : agents.length ≤ a) : ∀ (fuel : Nat) (up : List A) (J : List G),
      up.length + fuel ≤ a → J.length ≤ b →
        (upgradesC P agents Y fuel up J).cost ≤ fuel * (a * a * a + 17 * (a * a) + a * b + 12 * a + b + 1)
  | 0, _, _, _, _ => by simp [upgradesC]
  | fuel + 1, up, J, hu, hJ => by
    have h1 := findC_cost (canUpC P agents up Y J) (a * a + 17 * a + b + 11) agents
      (fun k _ => canUpC_cost_fine P Y k ha (by omega) hJ)
    have h2 := mulA_le (b := b) (x := a * a + 17 * a + b + 11 + 1) 12 17 1 0 1 0 ha (by omega)
    rw [Nat.succ_mul]
    unfold upgradesC
    simp only [bind_cost]
    split
    · simp only [pure_cost]; omega
    · rename_i k _
      have he := eraseC_cost (P.c k) J
      have ih := upgradesC_cost_fine P Y ha fuel (k :: up) (J.erase (P.c k)) (by simp; omega)
        (Nat.le_trans List.length_erase_le hJ)
      simp only [bind_cost, tick_cost, eraseC_val]
      omega

omit [DecidableEq A] in
theorem junk0C_cost_fine {agents : List A} (Y : A → Option G) {goods : List G}
    (ha : agents.length ≤ a) (hg : goods.length ≤ b) : (junk0C agents Y goods).cost ≤ 3 * (a * b) + b := by
  have h1 := filterC_cost (fun g => do let p ← pickerC agents Y g; pure p.isNone) (3 * a) goods
    (fun g _ => by have := pickerC_cost Y g ha; simp only [bind_cost, pure_cost]; omega)
  have h2 := mulB_le (a := a) (x := 3 * a + 1) 1 3 0 hg (by omega)
  unfold junk0C; omega

/-- LB's upgrades: `a⁴ + 17a³ + a²b + …`, the dominant term. -/
theorem lbUpC_cost_fine (P : Profile A G) {agents : List A} {goods : List G} (Y : A → Option G)
    (ha : agents.length ≤ a) (hg : goods.length ≤ b) :
    (lbUpC P agents goods Y).cost ≤ a * a * a * a + 17 * (a * a * a) + a * a * b + 12 * (a * a) +
      4 * (a * b) + 2 * a + b := by
  have h1 := junk0C_cost_fine Y ha hg
  have h2 := lengthC_cost agents
  have h3 := upgradesC_cost_fine P Y ha agents.length [] (junk0 agents Y goods) (by simpa using ha)
    (Nat.le_trans (List.length_filter_le _ _) hg)
  have h4 := mulA_le (b := b) (x := a * a * a + 17 * (a * a) + a * b + 12 * a + b + 1) 1 12 1 1 17 1 ha (by omega)
  simp only [lbUpC, bind_cost, junk0C_val, lengthC_val, pure_cost]
  omega

omit [DecidableEq A] in
theorem junkListC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) {goods : List G}
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) (hg : goods.length ≤ b) :
    (junkListC P agents up Y goods).cost ≤ 6 * (a * b) + 5 * b := by
  have h1 := filterC_cost (fun g => do
    let p ← pickerC agents Y g
    let u ← upOfC P up g
    tick 1
    pure (p.isNone && u.isNone)) (6 * a + 4) goods (fun g _ => by
      have := pickerC_cost Y g ha
      have := upOfC_cost P g hu
      simp only [bind_cost, tick_cost, pure_cost]
      omega)
  have h2 := mulB_le (a := a) (x := 6 * a + 4 + 1) 5 6 0 hg (by omega)
  unfold junkListC; omega

/-! ## The owner test -/

theorem exposedLC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) {J : List G}
    (w : A) (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) (hJ : J.length ≤ b) :
    (exposedLC P agents up Y J w).cost ≤ 3 * (a * a) + 2 * (a * b) + 18 * a := by
  have h1 := filterC_cost (exposedC P up Y J w) (3 * a + 2 * b + 17) agents (fun x _ => by
    have := memC_cost x up
    have := memC_cost (P.b x) J
    have := memC_cost (P.c x) J
    have := inBaseC_cost P Y w (P.b x) hu
    have := inBaseC_cost P Y w (P.c x) hu
    simp only [exposedC, bind_cost, tick_cost, pure_cost]
    omega)
  have h2 := mulA_le (b := b) (x := 3 * a + 2 * b + 17 + 1) 18 3 2 0 0 0 ha (by omega)
  unfold exposedLC; omega

theorem meetC_cost_fine (P : Profile A G) {J : List G} {E : List A} (hJ : J.length ≤ b) (hE : E.length ≤ a) :
    (meetC P J E).cost ≤ 2 * (a * a * b) + 14 * (a * a) + a := by
  have hin : ∀ x y : A, (do
      tick 3
      if x = y then pure none else do
        let r ← findC (fun g => do
          let mj ← memC g J
          tick 4
          pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) [P.b x, P.c x]
        pure (r.map (fun g => (x, y, g))) : Timed (Option (A × A × G))).cost ≤ 2 * b + 13 := by
    intro x y
    have := findC_cost (fun g => do
          let mj ← memC g J
          tick 4
          pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) (b + 4) [P.b x, P.c x]
      (fun g _ => by have := memC_cost g J; simp only [bind_cost, tick_cost, pure_cost]; omega)
    simp only [bind_cost, tick_cost]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, pure_cost, List.length_cons, List.length_nil] at this ⊢; omega
  have hinner : ∀ x : A, (findSomeC (fun y => (do
      tick 3
      if x = y then pure none else do
        let r ← findC (fun g => do
          let mj ← memC g J
          tick 4
          pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) [P.b x, P.c x]
        pure (r.map (fun g => (x, y, g))) : Timed (Option (A × A × G)))) E).cost ≤ 14 * a + 2 * (a * b) := by
    intro x
    have := findSomeC_cost _ (2 * b + 13) E (fun y _ => hin x y)
    have := mulA_le (b := b) (x := 2 * b + 13 + 1) 14 0 2 0 0 0 hE (by omega)
    omega
  have := findSomeC_cost _ (14 * a + 2 * (a * b)) E (fun x _ => hinner x)
  have := mulA_le (b := b) (x := 14 * a + 2 * (a * b) + 1) 1 14 0 2 0 0 hE (by omega)
  unfold meetC; omega

omit [DecidableEq A] in
theorem pickOneC_cost_fine (P : Profile A G) {J : List G} (x : A) (hJ : J.length ≤ b) :
    (pickOneC P J x).cost ≤ b + 2 := by
  have := memC_cost (P.b x) J
  simp only [pickOneC, bind_cost, tick_cost, pure_cost]
  omega

theorem hitSetC_cost_fine (P : Profile A G) {J : List G} {E : List A} (hJ : J.length ≤ b)
    (hE : E.length ≤ a) : (hitSetC P J E).cost ≤ 2 * (a * a * b) + 14 * (a * a) + a * b + 7 * a := by
  have h1 := meetC_cost_fine P hJ hE
  have hmap : ∀ E' : List A, E'.length ≤ a → (mapC (pickOneC P J) E').cost ≤ 3 * a + a * b := fun E' hE' => by
    have := mapC_cost (pickOneC P J) (b + 2) E' (fun x _ => pickOneC_cost_fine P x hJ)
    have := mulA_le (b := b) (x := b + 2 + 1) 3 0 1 0 0 0 hE' (by omega)
    omega
  unfold hitSetC
  simp only [bind_cost]
  split
  · rename_i x y g _
    have h2 := filterC_cost (fun z => do tick 2; pure (decide (z ≠ x ∧ z ≠ y))) 2 E (fun _ _ => by simp)
    have h3 := hmap (E.filter (fun z => (do tick 2; pure (decide (z ≠ x ∧ z ≠ y)) : Timed Bool).val))
      (Nat.le_trans (List.length_filter_le _ _) hE)
    simp only [bind_cost, filterC_val, pure_cost]
    omega
  · have := hmap E hE
    omega

/-! ## The rotation -/

theorem isNextC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G) (cur j : A)
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) : (isNextC P agents up Y cur j).cost ≤ a * a + 17 * a + 17 := by
  have h1 := frozenBC_cost_fine P Y cur ha hu
  have h2 := memC_cost j up
  unfold isNextC
  cases hy : Y cur with
  | none => simp only [bind_cost, tick_cost, pure_cost]; omega
  | some y =>
    have := prefersC_cost P Y j y
    simp only [bind_cost, tick_cost, pure_cost]; omega

theorem chainFromC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G)
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) : ∀ (cur : A) (rest : List A),
      (chainFromC P agents up Y cur rest).cost ≤ rest.length * (a * a + 17 * a + 18)
  | _, [] => by simp [chainFromC]
  | cur, j :: rest => by
    have h1 := isNextC_cost_fine P Y cur j ha hu
    rw [List.length_cons, Nat.succ_mul]
    unfold chainFromC
    simp only [bind_cost, tick_cost]
    split
    · have := chainFromC_cost_fine P Y ha hu j rest
      simp only [bind_cost, pure_cost]; omega
    · have := chainFromC_cost_fine P Y ha hu cur rest
      omega

omit [DecidableEq G] in
theorem rotPicksC_cost_fine (P : Profile A G) (Y : A → Option G) (k : A) (c : List A) (x : A) :
    (rotPicksC P Y k c x).cost ≤ 2 * c.length + 3 := by
  have := rotYC_cost Y k c x
  unfold rotPicksC
  simp only [bind_cost, tick_cost]
  split
  · simp only [pure_cost]; omega
  · omega

/-! ## The completion -/

omit [DecidableEq A] in
theorem completeOneC_cost_fine (P : Profile A G) {agents up : List A} (Y : A → Option G)
    (o : Option A) (d : A) (s : A → Nat) (hs : ∀ k, s k ≤ 2) (L : List G) (g : G)
    (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) : (completeOneC P agents up Y o d s L g).cost ≤ 14 * a + 4 := by
  have h1 := pickerC_cost Y g ha
  have h2 := upOfC_cost P g hu
  have h3 := fillC_cost s hs g agents L
  unfold completeOneC
  simp only [bind_cost]
  split
  · simp only [pure_cost]; omega
  · simp only [bind_cost]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, tick_cost, pure_cost]; omega

omit [DecidableEq A] in
theorem placeListC_cost_fine {H J : List G} (hH : H.length ≤ a) (hJ : J.length ≤ b) :
    (placeListC H J).cost ≤ a * b + a + b := by
  have h1 := filterC_cost (fun g => do let b ← memC g H; pure (!b)) a J
    (fun g _ => by have := memC_cost g H; simp only [bind_cost, pure_cost]; omega)
  have h2 := mulB_le (a := a) (x := a + 1) 1 1 0 hJ (by omega)
  have h3 := appendC_cost H (J.filter (fun g => (do let b ← memC g H; pure (!b) : Timed Bool).val))
  simp only [placeListC, bind_cost, filterC_val]
  omega

/-! ## Rule R1 -/

omit [DecidableEq A] in
theorem r1StepC_cost_fine (v : A → G → Nat) (goods : List G) (i : A) :
    (r1StepC v goods i).cost ≤ 6 * goods.length + 4 := by
  have h1 := favoriteC_cost (fun g => do tick 1; pure (v i g)) (fun _ => by simp) goods
  unfold r1StepC
  simp only [bind_cost]
  split
  · simp only [pure_cost]; omega
  · rename_i p _
    simp only [bind_cost, tick_cost]
    split
    · simp only [pure_cost]; omega
    · have h2 := eraseC_cost p goods
      have h3 := valueC_cost v i (goods.erase p)
      have h4 := List.length_erase_le (a := p) (l := goods)
      simp only [bind_cost, eraseC_val, tick_cost, pure_cost]; omega

omit [DecidableEq A] in
theorem findR1C_cost_fine (v : A → G → Nat) {agents : List A} {goods : List G}
    (ha : agents.length ≤ a) (hg : goods.length ≤ b) : (findR1C v agents goods).cost ≤ 6 * (a * b) + 5 * a := by
  have h1 := findSomeC_cost (fun i => do
    let s ← r1StepC v goods i
    pure (s.map (fun s => (i, s)))) (6 * b + 4) agents
    (fun i _ => by have := r1StepC_cost_fine v goods i; simp only [bind_cost, pure_cost]; omega)
  have h2 := mulA_le (b := b) (x := 6 * b + 4 + 1) 5 0 6 0 0 0 ha (by omega)
  unfold findR1C; omega

end generic

/-! ## The algorithm -/

section fin
variable {n m a b : Nat}

theorem profTabC_cost_fine (v : Fin n → Fin m → Nat) {goods : List (Fin m)} (g0 : Fin m)
    (hn : n ≤ a) (hg : goods.length ≤ b) : (profTabC v goods g0).cost ≤ 3 * (a * b) + 11 * a := by
  have h1 := mkTable_cost n (fun i => do
    let rel ← filterC (fun g => do tick 2; pure (decide (0 < v i g))) goods
    sort3C (v i) g0 rel) (3 * b + 10) (fun i => by
      have := filterC_cost (fun g => do tick 2; pure (decide (0 < v i g))) 2 goods (fun _ _ => by simp)
      simp only [bind_cost, sort3C, tick_cost, pure_cost]
      omega)
  have h2 := mulA_le (b := b) (x := 3 * b + 10 + 1) 11 0 3 0 0 0 hn (by omega)
  simp only [profTabC, bind_cost, pure_cost]
  omega

theorem completeTabC_cost_fine (P : Profile (Fin n) (Fin m)) {agents up : List (Fin n)}
    (Y : Fin n → Option (Fin m)) (capT : Fin n → Nat) (hc : ∀ k, capT k ≤ 2) {J : List (Fin m)}
    (o : Option (Fin n)) {H : List (Fin m)} (d : Fin n) (hm : m ≤ b) (ha : agents.length ≤ a)
    (hu : up.length ≤ a + 1) (hJ : J.length ≤ b) (hH : H.length ≤ a) :
    (completeTabC P agents up Y capT J o H d).cost ≤ 15 * (a * b) + a + 6 * b := by
  have h1 := placeListC_cost_fine hH hJ
  have h2 := mkTable_cost m (fun g => completeOneC P agents up Y o d (slotsExcept capT o)
    (placeListC H J).val g) (14 * a + 4)
    (fun g => completeOneC_cost_fine P Y o d _ (slotsExcept_le capT hc o) _ g ha hu)
  have h3 := mulB_le (a := a) (x := 14 * a + 4 + 1) 5 14 0 hm (by omega)
  simp only [completeTabC, bind_cost]
  omega

/-! ### The stage bounds of LB⁺ as polynomials -/

theorem one_costP : (1 : Nat) ≤ Poly.ev { c0 := 1 } a b := by simp only [Poly.ev]; omega

theorem phase1TabC_costP (P : Profile (Fin n) (Fin m)) {order : List (Fin n)} {goods : List (Fin m)}
    (hn : n ≤ a) (hg : goods.length ≤ b) (ho : order.length ≤ a) :
    (mkTable n (fun k => phase1C P order goods k)).cost ≤ Poly.ev { cA := 1, cA2 := 4, cA2B := 4 } a b := by
  have h1 := mkTable_cost n (fun k => phase1C P order goods k) (4 * (a * b) + 4 * a) (fun k => by
    have h1 := phase1C_cost_fine P order goods k hg
    have h2 := mulA_le (b := b) (x := 4 * b + 4) 4 0 4 0 0 0 ho (by omega)
    omega)
  have h2 := mulA_le (b := b) (x := 4 * (a * b) + 4 * a + 1) 1 4 0 4 0 0 hn (by omega)
  simp only [Poly.ev]; omega

theorem blkTabC_costP (P : Profile (Fin n) (Fin m)) {order : List (Fin n)} {goods : List (Fin m)}
    (hn : n ≤ a) (hg : goods.length ≤ b) (ho : order.length ≤ a) :
    (mkTable n (fun k => blkAuxC P order goods 0 k)).cost ≤ Poly.ev { cA := 1, cA2 := 8, cA2B := 7 } a b := by
  have h1 := mkTable_cost n (fun k => blkAuxC P order goods 0 k) (7 * (a * b) + 8 * a) (fun k => by
    have h1 := blkAuxC_cost_fine P order goods 0 k hg
    have h2 := mulA_le (b := b) (x := 7 * b + 8) 8 0 7 0 0 0 ho (by omega)
    omega)
  have h2 := mulA_le (b := b) (x := 7 * (a * b) + 8 * a + 1) 1 8 0 7 0 0 hn (by omega)
  simp only [Poly.ev]; omega

theorem lbUpC_costP (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {goods : List (Fin m)}
    (Y : Fin n → Option (Fin m)) (ha : agents.length ≤ a) (hg : goods.length ≤ b) :
    (lbUpC P agents goods Y).cost ≤
      Poly.ev { cA := 2, cB := 1, cAB := 4, cA2 := 12, cA2B := 1, cA3 := 17, cA4 := 1 } a b := by
  have := lbUpC_cost_fine P Y ha hg
  simp only [Poly.ev]; omega

theorem junkListC_costP (P : Profile (Fin n) (Fin m)) {agents up : List (Fin n)} (Y : Fin n → Option (Fin m))
    {goods : List (Fin m)} (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) (hg : goods.length ≤ b) :
    (junkListC P agents up Y goods).cost ≤ Poly.ev { cB := 5, cAB := 6 } a b := by
  have := junkListC_cost_fine P Y ha hu hg
  simp only [Poly.ev]; omega

theorem capTabC_costP (P : Profile (Fin n) (Fin m)) {agents up : List (Fin n)} (Y : Fin n → Option (Fin m))
    (hn : n ≤ a) (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) :
    (mkTable n (capC P agents up Y)).cost ≤ Poly.ev { cA := 5, cA2 := 17, cA3 := 1 } a b := by
  have h1 := mkTable_cost n (capC P agents up Y) (a * a + 17 * a + 4) (fun k => capC_cost_fine P Y k ha hu)
  have h2 := mulA_le (b := b) (x := a * a + 17 * a + 4 + 1) 5 17 0 0 1 0 hn (by omega)
  simp only [Poly.ev]; omega

theorem sumTabC_costP (s : Fin n → Nat) {agents : List (Fin n)} (ha : agents.length ≤ a) :
    (sumTabC s agents).cost ≤ Poly.ev { cA := 2 } a b := by
  have := sumTabC_cost s ha
  simp only [Poly.ev]; omega

theorem sumExceptC_costP (s : Fin n → Nat) (o : Option (Fin n)) {agents : List (Fin n)} (ha : agents.length ≤ a) :
    (sumExceptC s o agents).cost ≤ Poly.ev { cA := 3 } a b := by
  have := sumExceptC_cost s o ha
  simp only [Poly.ev]; omega

theorem lengthC_costPA {α : Type} {l : List α} (hl : l.length ≤ a) : (lengthC l).cost ≤ Poly.ev { cA := 1 } a b := by
  rw [lengthC_cost]; simp only [Poly.ev]; omega

theorem lengthC_costPB {α : Type} {l : List α} (hl : l.length ≤ b) : (lengthC l).cost ≤ Poly.ev { cB := 1 } a b := by
  rw [lengthC_cost]; simp only [Poly.ev]; omega

theorem completeTabC_costP (P : Profile (Fin n) (Fin m)) {agents up : List (Fin n)}
    (Y : Fin n → Option (Fin m)) (capT : Fin n → Nat) (hc : ∀ k, capT k ≤ 2) {J : List (Fin m)}
    (o : Option (Fin n)) {H : List (Fin m)} (d : Fin n) (hm : m ≤ b) (ha : agents.length ≤ a)
    (hu : up.length ≤ a + 1) (hJ : J.length ≤ b) (hH : H.length ≤ a) :
    (completeTabC P agents up Y capT J o H d).cost ≤ Poly.ev { cA := 1, cB := 6, cAB := 15 } a b := by
  have := completeTabC_cost_fine P Y capT hc o d hm ha hu hJ hH
  simp only [Poly.ev]; omega

theorem lastOutC_costP {up order : List (Fin n)} (hu : up.length ≤ a + 1) (ho : order.length ≤ a) :
    (lastOutC up order).cost ≤ Poly.ev { cA := 2, cA2 := 1 } a b := by
  have h1 := lastOutC_cost up hu order
  have h2 := mulA_le (b := b) (x := a + 1 + 1) 2 1 0 0 0 0 ho (by omega)
  simp only [Poly.ev]; omega

theorem exposedLC_costP (P : Profile (Fin n) (Fin m)) {agents up : List (Fin n)} (Y : Fin n → Option (Fin m))
    {J : List (Fin m)} (w : Fin n) (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) (hJ : J.length ≤ b) :
    (exposedLC P agents up Y J w).cost ≤ Poly.ev { cA := 18, cAB := 2, cA2 := 3 } a b := by
  have := exposedLC_cost_fine P Y w ha hu hJ
  simp only [Poly.ev]; omega

theorem hitSetC_costP (P : Profile (Fin n) (Fin m)) {J : List (Fin m)} {E : List (Fin n)} (hJ : J.length ≤ b)
    (hE : E.length ≤ a) : (hitSetC P J E).cost ≤ Poly.ev { cA := 7, cAB := 1, cA2 := 14, cA2B := 2 } a b := by
  have := hitSetC_cost_fine P hJ hE
  simp only [Poly.ev]; omega

theorem kstarC_costP (blk : Fin n → Nat) {E : List (Fin n)} (r : Fin n) (hE : E.length ≤ a) :
    (kstarC blk E r).cost ≤ Poly.ev { cA := 4 } a b := by
  have := kstarC_cost blk r hE
  simp only [Poly.ev]; omega

theorem afterC_costP {order : List (Fin n)} (k : Fin n) (ho : order.length ≤ a) :
    (afterC order k).cost ≤ Poly.ev { cA := 1 } a b := by
  have := afterC_cost order k
  simp only [Poly.ev]; omega

theorem chainC_costP (P : Profile (Fin n) (Fin m)) {agents up order : List (Fin n)} (Y : Fin n → Option (Fin m))
    (k : Fin n) (ha : agents.length ≤ a) (hu : up.length ≤ a + 1) (ho : order.length ≤ a) :
    (chainFromC P agents up Y k (after order k)).cost ≤ Poly.ev { cA := 18, cA2 := 17, cA3 := 1 } a b := by
  have h1 := chainFromC_cost_fine P Y ha hu k (after order k)
  have h2 := mulA_le (b := b) (x := a * a + 17 * a + 18) 18 17 0 0 1 0
    (Nat.le_trans (length_after order k) ho) (by omega)
  simp only [Poly.ev]; omega

theorem rotTabC_costP (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (k : Fin n) {ch : List (Fin n)}
    (hn : n ≤ a) (hc : ch.length ≤ a) :
    (mkTable n (fun x => rotPicksC P Y k ch x)).cost ≤ Poly.ev { cA := 4, cA2 := 2 } a b := by
  have h1 := mkTable_cost n (fun x => rotPicksC P Y k ch x) (2 * a + 3) (fun x => by
    have := rotPicksC_cost_fine P Y k ch x; omega)
  have h2 := mulA_le (b := b) (x := 2 * a + 3 + 1) 4 2 0 0 0 0 hn (by omega)
  simp only [Poly.ev]; omega

/-- **LB⁺, finer**: at most `a⁴ + 20a³ + 16a²b + 112a² + 37ab + 102a + 19b + 3` counted operations. -/
theorem lbPlusC_cost_fine (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {goods : List (Fin m)}
    {order : List (Fin n)} (d : Fin n) (hn : n ≤ a) (hm : m ≤ b) (ha : agents.length ≤ a)
    (hg : goods.length ≤ b) (ho : order.length ≤ a) :
    (lbPlusC P agents goods order d).cost ≤
      Poly.ev { c0 := 3, cA := 102, cB := 19, cAB := 37, cA2 := 112, cA2B := 16, cA3 := 20, cA4 := 1 } a b := by
  have h1 : (1 : Nat) ≤ Poly.ev { c0 := 1 } a b := one_costP
  have hY := phase1TabC_costP P hn hg ho (a := a) (b := b)
  have hblk := blkTabC_costP P hn hg ho (a := a) (b := b)
  generalize hYd : (mkTable n (fun k => phase1C P order goods k)).val = Y
  have hup := lbUpC_costP P Y ha hg
  have hupl : (lbUp P agents goods Y).length ≤ agents.length := by
    have := (length_upgrades P agents Y agents.length [] (junk0 agents Y goods)).1
    simpa [lbUp] using this
  generalize hupd : lbUp P agents goods Y = up at hupl
  have hu : up.length ≤ a + 1 := by omega
  have hu' : ∀ k : Fin n, (k :: up).length ≤ a + 1 := fun k => by simp; omega
  clear hupl
  have hJl : (junkList P agents up Y goods).length ≤ b := Nat.le_trans (List.length_filter_le _ _) hg
  have hJ := junkListC_costP P Y ha hu hg
  have hcapT := capTabC_costP P Y hn ha hu (b := b)
  have hcap2 : ∀ k, (mkTable n (capC P agents up Y)).val k ≤ 2 := fun k => by
    simp only [mkTable_val, capC_val]; exact cap_le_two P agents up Y k
  have hS := sumTabC_costP (mkTable n (capC P agents up Y)).val ha (b := b)
  have hlJ := lengthC_costPB hJl (a := a)
  have hct := fun (o : Option (Fin n)) (H : List (Fin m)) (hH : H.length ≤ a) =>
    completeTabC_costP P (up := up) Y _ hcap2 (J := junkList P agents up Y goods) o d hm ha hu hJl hH
  have hlo := lastOutC_costP hu ho (b := b)
  unfold lbPlusC
  simp only [bind_cost, hYd, lbUpC_val, hupd, junkListC_val, tick_cost]
  clear hYd hupd
  split
  · rename_i hc; clear hc; have := hct none [] (by simp); poly_sum
  rename_i hc; clear hc
  simp only [bind_cost]
  split
  · rename_i hc; clear hc; have := hct none [] (by simp); poly_sum
  rename_i r hc; clear hc
  have hEl : (exposedL P agents up Y goods r).length ≤ a := Nat.le_trans (List.length_filter_le _ _) ha
  have hE := exposedLC_costP P Y (J := junkList P agents up Y goods) r ha hu hJl
  simp only [bind_cost, exposedLC_val]
  have hH := hitSetC_costP P (J := junkList P agents up Y goods) hJl hEl
  have hHl : (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)).length ≤ a :=
    Nat.le_trans hitSet_length.1 hEl
  have hlH := lengthC_costPA hHl (b := b)
  have hSr := sumExceptC_costP (mkTable n (capC P agents up Y)).val (some r) ha (b := b)
  simp only [hitSetC_val, tick_cost]
  split
  · rename_i hc; clear hc; have := hct (some r) _ hHl; poly_sum
  rename_i hc; clear hc
  simp only [bind_cost]
  have hks := kstarC_costP (mkTable n (fun k => blkAuxC P order goods 0 k)).val r hEl (b := b)
  split
  · rename_i hc; clear hc; have := hct (some r) _ hHl; poly_sum
  rename_i k hc; clear hc hct hHl hEl
  simp only [bind_cost]
  -- the rotation
  have haf := afterC_costP k ho (b := b)
  have hch := chainC_costP P Y k ha hu ho (b := b)
  have hchl : (chainFrom P agents up Y k (after order k)).length ≤ a :=
    Nat.le_trans (chainFrom_sublist k (after order k)).length_le (Nat.le_trans (length_after order k) ho)
  simp only [afterC_val, chainFromC_val]
  generalize chainFrom P agents up Y k (after order k) = ch at hchl hch
  have hY2 := rotTabC_costP P Y k hn hchl (b := b)
  generalize (mkTable n (fun x => rotPicksC P Y k ch x)).val = Y'
  have hJl' : (junkList P agents (k :: up) Y' goods).length ≤ b := Nat.le_trans (List.length_filter_le _ _) hg
  have hJ' := junkListC_costP P Y' ha (hu' k) hg
  have hcapT2 := capTabC_costP P Y' hn ha (hu' k) (b := b)
  have hcap22 : ∀ x, (mkTable n (capC P agents (k :: up) Y')).val x ≤ 2 := fun x => by
    simp only [mkTable_val, capC_val]; exact cap_le_two P agents (k :: up) Y' x
  have hS' := sumTabC_costP (mkTable n (capC P agents (k :: up) Y')).val ha (b := b)
  have hlJ' := lengthC_costPB hJl' (a := a)
  have hct' := fun (o : Option (Fin n)) (H : List (Fin m)) (hH : H.length ≤ a) =>
    completeTabC_costP P (up := k :: up) Y' _ hcap22 (J := junkList P agents (k :: up) Y' goods) o d hm ha
      (hu' k) hJl' hH
  simp only [junkListC_val, tick_cost]
  split
  · rename_i hc; clear hc; have := hct' none [] (by simp); poly_sum
  rename_i hc; clear hc
  have hEl' : (exposedL P agents (k :: up) Y' goods k).length ≤ a := Nat.le_trans (List.length_filter_le _ _) ha
  have hE' := exposedLC_costP P Y' (J := junkList P agents (k :: up) Y' goods) k ha (hu' k) hJl'
  have hH' := hitSetC_costP P (J := junkList P agents (k :: up) Y' goods) hJl' hEl'
  have hHl' := Nat.le_trans (hitSet_length (P := P) (J := junkList P agents (k :: up) Y' goods)
    (E := exposedL P agents (k :: up) Y' goods k)).1 hEl'
  have := hct' (some k) _ hHl'
  simp only [bind_cost, exposedLC_val, hitSetC_val]
  poly_sum

/-- The peeling loop: at most `6ab + 7a + b + 1` per round, and the LB stage (rankings, order, LB⁺) once. -/
theorem reduceC_cost_fine (v : Fin n → Fin m → Nat) (d : Fin n) (hn : n ≤ a) (hm : m ≤ b) :
    ∀ (fuel : Nat) (agents : List (Fin n)) (goods : List (Fin m)), agents.length ≤ a → goods.length ≤ b →
      (reduceC v d fuel agents goods).cost ≤ fuel * (6 * (a * b) + 7 * a + b + 1) +
        (a * a * a * a + 20 * (a * a * a) + 19 * (a * a * b) + 117 * (a * a) + 44 * (a * b) + 117 * a +
          19 * b + 3)
  | 0, _, _, _, _ => by simp [reduceC]
  | fuel + 1, agents, goods, ha, hg => by
    have hl := lengthC_cost agents
    rw [Nat.succ_mul]
    unfold reduceC
    simp only [bind_cost, lengthC_val, tick_cost]
    split
    · simp only [pure_cost]; omega
    cases goods with
    | nil => simp only [pure_cost]; omega
    | cons g0 gs =>
      have hR := findR1C_cost_fine v (goods := g0 :: gs) ha hg
      simp only [bind_cost]
      split
      · rename_i i _
        have h1 := eraseC_cost i agents
        have ih := reduceC_cost_fine v d hn hm fuel ((eraseC i agents).val) (g0 :: gs)
          (by rw [eraseC_val]; have := List.length_erase_le (a := i) (l := agents); omega) hg
        simp only [bind_cost]; omega
      · rename_i i p _
        have h1 := eraseC_cost i agents
        have h2 := eraseC_cost p (g0 :: gs)
        have ih := reduceC_cost_fine v d hn hm fuel ((eraseC i agents).val) ((eraseC p (g0 :: gs)).val)
          (by rw [eraseC_val]; have := List.length_erase_le (a := i) (l := agents); omega)
          (by rw [eraseC_val]; have := List.length_erase_le (a := p) (l := g0 :: gs); omega)
        simp only [bind_cost, pure_cost]; omega
      · have hP := profTabC_cost_fine v (goods := g0 :: gs) g0 hn hg
        have hl' := lengthC_cost agents
        have hO := r1OrderC_cost_fine (profTabC v (g0 :: gs) g0).val agents.length agents (g0 :: gs) ha hg
        have hO' := mulA_le (b := b) (x := 3 * (a * b) + 5 * a + 4 * b + 3) 3 5 4 3 0 0 ha (by omega)
        have hL := lbPlusC_cost_fine (profTabC v (g0 :: gs) g0).val (agents := agents) (goods := g0 :: gs)
          (order := (r1OrderC (profTabC v (g0 :: gs) g0).val agents.length agents (g0 :: gs)).val) d hn hm ha hg
          (by rw [r1OrderC_val]; exact Nat.le_trans (length_r1Order _ _ _ _) ha)
        simp only [Poly.ev] at hL
        simp only [bind_cost, lengthC_val, pure_cost]
        omega

end fin

/-- **The finer running-time theorem.** Algorithm K3ALG (`algo`) performs at most
`n⁴ + 20 n³ + 25 n²m + 124 n² + 47 nm + 119 n + 22 m + 3` counted operations on every instance with `n ≥ 1`
agents and `m` goods (same program and cost model as `EFX.K3.algoC_cost`; any number of relevant goods). -/
theorem algoC_cost_fine (I : Inst) (hn : 0 < I.n) :
    (algoC I hn).cost ≤ I.n ^ 4 + 20 * I.n ^ 3 + 25 * (I.n ^ 2 * I.m) + 124 * I.n ^ 2 + 47 * (I.n * I.m) +
      119 * I.n + 22 * I.m + 3 := by
  have hR := reduceC_cost_fine I.v ⟨0, hn⟩ (a := I.n) (b := I.m) (Nat.le_refl _) (Nat.le_refl _) I.n
    (List.finRange I.n) (List.finRange I.m) (by simp) (by simp)
  have hR' := mulA_le (b := I.m) (x := 6 * (I.n * I.m) + 7 * I.n + I.m + 1) 1 7 1 6 0 0 (Nat.le_refl I.n) (by omega)
  have hpl := length_reduceC_peels I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)
  simp only [algoC, bind_cost, finRangeC, tick_cost, pure_cost, bind_val, pure_val]
  generalize reduceC I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m) = R at hR hpl ⊢
  have hT := mkTable_cost I.m (fun g => do
    let q ← findC (fun q => do tick 1; pure (q.2 == g)) R.val.1
    tick 1
    pure ((q.map Prod.fst).getD (R.val.2 g))) (2 * I.n + 1) (fun g => by
      have := findC_cost (fun q => do tick 1; pure (q.2 == g)) 1 R.val.1 (fun _ _ => by simp)
      simp only [bind_cost, tick_cost, pure_cost]
      omega)
  have hT' := mulB_le (a := I.n) (x := 2 * I.n + 1 + 1) 2 2 0 (Nat.le_refl I.m) (by omega)
  have e4 : I.n ^ 4 = I.n * I.n * I.n * I.n := by simp [Nat.pow_succ]
  have e3 : I.n ^ 3 = I.n * I.n * I.n := by simp [Nat.pow_succ]
  have e2 : I.n ^ 2 * I.m = I.n * I.n * I.m := by simp [Nat.pow_succ]
  have e2' : I.n ^ 2 = I.n * I.n := by simp [Nat.pow_succ]
  rw [e4, e3, e2, e2']
  omega

/-- The finer bound in the form `a n⁴ + b n²m + c n + d m + e`: at most `145 n⁴ + 72 n²m + 119 n + 22 m + 3`
(from `algoC_cost_fine`, as `n³, n² ≤ n⁴` and `nm ≤ n²m` when `n ≥ 1`). -/
theorem algoC_cost_fine' (I : Inst) (hn : 0 < I.n) :
    (algoC I hn).cost ≤ 145 * I.n ^ 4 + 72 * (I.n ^ 2 * I.m) + 119 * I.n + 22 * I.m + 3 := by
  have h := algoC_cost_fine I hn
  have h1 : I.n ^ 3 ≤ I.n ^ 4 := Nat.pow_le_pow_right hn (by omega)
  have h2 : I.n ^ 2 ≤ I.n ^ 4 := Nat.pow_le_pow_right hn (by omega)
  have h3 : I.n * I.m ≤ I.n ^ 2 * I.m := Nat.mul_le_mul_right _ (by
    have := Nat.pow_le_pow_right hn (show 1 ≤ 2 by omega); simpa using this)
  omega

/-- **`O(n⁴ + n²m)`**: at most `270 (n⁴ + n²m)` counted operations (from `algoC_cost_fine'`, as `1, n ≤ n⁴` and
`m ≤ n²m` when `n ≥ 1`). -/
theorem algoC_cost_fine'' (I : Inst) (hn : 0 < I.n) :
    (algoC I hn).cost ≤ 270 * (I.n ^ 4 + I.n ^ 2 * I.m) := by
  have h := algoC_cost_fine' I hn
  have h1 : 1 ≤ I.n ^ 4 := by have := Nat.pow_le_pow_left hn 4; simpa using this
  have h2 : I.n ≤ I.n ^ 4 := by
    have := Nat.pow_le_pow_right hn (show 1 ≤ 4 by omega); simpa using this
  have h3 : I.m ≤ I.n ^ 2 * I.m := by
    have : 1 ≤ I.n ^ 2 := by have := Nat.pow_le_pow_left hn 2; simpa using this
    have := Nat.mul_le_mul_right I.m this; simpa using this
  rw [Nat.mul_add]
  omega

/-- **K3ALG on ordered values, finer**: the surrogate (`EFX.K3.surrogateC_cost`, `n (m + 12)` oracle calls) plus
`algoC_cost_fine'` for K3ALG on it. -/
theorem algoOrdC_cost_fine {V : Type} [OrderedValue V] (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) :
    (algoOrdC le I hn).cost ≤ I.n * (I.m + 12) + 10 * (I.n * I.m) + 971 * I.n +
      (145 * I.n ^ 4 + 72 * (I.n ^ 2 * I.m) + 119 * I.n + 22 * I.m + 3) := by
  have h1 := surrogateC_cost 1 le I
  have h2 := algoC_cost_fine' ⟨I.n, I.m, (surrogateC 1 le I).val⟩ hn
  simp only at h2
  simp only [algoOrdC, bind_cost]
  omega

end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.mulA_le
#print axioms EFX.K3.lbUpC_cost_fine
#print axioms EFX.K3.lbPlusC_cost_fine
#print axioms EFX.K3.reduceC_cost_fine
#print axioms EFX.K3.algoC_cost_fine
#print axioms EFX.K3.algoC_cost_fine'
#print axioms EFX.K3.algoC_cost_fine''
#print axioms EFX.K3.algoOrdC_cost_fine
