import EFX.C4min

/-!
# DL_R ⟹ C₄ᵐⁱⁿ (removal-only) ⟹ TARGET₄ by finite descent (`k4/strategy.md` §3, step 4; ledger K4.STRAT.DL2.LEAN)

Conjecture DL₂ of `k4/strategy.md` §3 (K4.STRAT.DL2) says that the deficit has no local minimum above 0 for changes of
at most two bases at the fewest frozen agents. This file states it for an arbitrary neighbourhood relation `R` on
pre-allocations (`DefLocal R`, "DL_R"), so that the reduction survives a widening of DL₂ (more agents, other moves),
and proves by finite descent that DL_R implies C₄ᵐⁱⁿ in removal-only form on connected cores (`C4minROConn`), hence
TARGET₄. DL_R is a hypothesis of every theorem here, never an axiom. Everything is stated with the definitions of
`EFX/C4min.lean` (`InP`, `nFrozen`, `MinFrozen`, `omegaP`, `DeficitLE`, `RemovalOnly`); nothing of the model is redefined.

**Definitions.**
- `Nbhd A G`: a neighbourhood relation, `R v agents goods P P′` ("`P′` is a neighbour of `P`"); it may depend on the
  instance.
- `DeficitLT v agents goods P′ P`: `def(P′) < def(P)`, with `def ∈ ℤ ∪ {+∞}`, read through `DeficitLE` ("def ≤ d"):
  some integer `d` has `def(P′) ≤ d` and not `def(P) ≤ d`. `deficitLE_mono`, `deficitLE_lower` and
  `exists_least_deficit` show that `{d | DeficitLE P d}` is empty (`def(P) = +∞`) or the integers from a least one on
  (`def(P)`), so this is the strict order of `ℤ ∪ {+∞}` (`deficitLT_iff`: `def(P′) < def(P)` iff `def(P′)` is an
  integer `d₀` and not `def(P) ≤ d₀`).
- `DefLocalAt R v agents goods` (one instance): if `ω = f − (2n − m) ≥ 1` (`f` the fewest frozen agents, here
  `nFrozen` of a min-frozen `P`; `n`, `m` the lengths of `agents`, `goods`), every min-frozen `P` with `def(P) > 0`
  (`¬ DeficitLE P 0`, including `def(P) = +∞`) has a min-frozen `P′` with `R P P′` and `def(P′) < def(P)`.
- `DefLocal R` (DL_R, the scope of DL₂): `DefLocalAt R` on every strict profile of every connected k = 4 core.
  `DefLocalAll R`: the same on every strict profile of every k = 4 core, connected or not.
- `BasesDiffer k`: `P′` differs from `P` in the bases of at most `k` agents (a list `S` of at most `k` agents outside
  of which every listed agent has the same base). `DefLocal2 A G := DefLocal (BasesDiffer 2)` is DL₂.

**Results.**
- `exists_removalOnly_of_defLocalAt` (the descent, on one instance): DL_R on an instance gives a min-frozen `P` with
  `def(P) ≤ 0`. A min-frozen `P₀` exists (`exists_minFrozen`); while `def(P) > 0`, DL_R gives a min-frozen `P′` with
  `def(P′) ≤ d < def(P)` for an integer `d`. After the first step every deficit is finite, and the deficits before the
  last step are positive integers that strictly decrease, so the descent stops.
- `C4minROConn_of_defLocal`, `target4_of_defLocal`: DL_R ⟹ `C4minROConn` ⟹ TARGET₄ (`target4_of_C4minROConn`), for
  every relation `R`; `C4minROConn_of_defLocal2`, `target4_of_defLocal2`: in particular DL₂ ⟹ TARGET₄.
- `C4minRO_of_defLocalAll`: DL_R on every core ⟹ `TheoremC4minRO` (the form named in step 4 of the strategy).
- `defLocalAt_top_iff`: for the full relation (`R` always true), DL_R on an instance is equivalent to C₄ᵐⁱⁿ's
  conclusion (removal-only) there, so the reduction loses nothing; `DefLocal.mono`, `basesDiffer_mono`: widening `R`
  (e.g. from two agents to `k ≥ 2`) weakens DL_R.
- `omegaP_eq`, `omegaP_minFrozen_eq`, `omegaP_pos`: on 𝒫, `ω(P) = |J| − S = nFrozen(P) − (2n − m)`, the same for every
  min-frozen `P` (the parenthetical of DL₂), and `def(P) > 0` forces `ω(P) ≥ 1`; so DL₂'s restriction to `ω ≥ 1`
  excludes no `P` with `def(P) > 0`.

**Where the Lean statement differs from the prose.**
1. The strategy's descent says "the min-frozen class is finite and nonempty, take a pre-allocation of least deficit".
   A pre-allocation here is a base map `G → Option A`, and finiteness of the class would need a quotient by agreement
   on `goods`. The proof instead descends on the deficit: after the first step (from a possible `+∞`) every deficit
   in the chain except the last is a positive integer, and each step lowers it, so the chain is finite. Only
   nonemptiness (`exists_minFrozen`) is used, not finiteness.
2. DL₂ is stated on connected cores, so DL_R yields `C4minROConn` (whose extra hypothesis, a 4-good agent, is not
   used), and TARGET₄ through `target4_of_C4minROConn`. Step 4 of the strategy names `TheoremC4minRO`, which needs the
   statement on every core: that is `DefLocalAll` and `C4minRO_of_defLocalAll`.
3. "The bases of at most two agents differ" compares bases on `goods` (`baseOf goods P i = baseOf goods P′ i`) for the
   listed agents outside a list of at most two agents; the values of a base map outside `goods` do not matter.
-/

set_option autoImplicit false

namespace EFX
namespace C4min

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Neighbourhoods, the strict order of deficits, and the statements -/

/-- A neighbourhood relation on pre-allocations: `R v agents goods P P′` says that `P′` is a neighbour of `P` on the
instance `(agents, goods, v)`. -/
abbrev Nbhd (A G : Type) : Type := (A → G → Nat) → List A → List G → (G → Option A) → (G → Option A) → Prop

/-- **`def(P′) < def(P)`**, with `def ∈ ℤ ∪ {+∞}` given by `DeficitLE` (`def(P) ≤ d`): some integer `d` has
`def(P′) ≤ d` and not `def(P) ≤ d`. If `def(P) = +∞` this says that `def(P′)` is finite. -/
def DeficitLT (v : A → G → Nat) (agents : List A) (goods : List G) (base' base : G → Option A) : Prop :=
  ∃ d : Int, DeficitLE v agents goods base' d ∧ ¬ DeficitLE v agents goods base d

/-- **The deficit has no local minimum above 0 for `R`, on one instance.** If `ω = f − (2n − m) ≥ 1` (`f`: the fewest
frozen agents, the `nFrozen` of the min-frozen `P`), every pre-allocation `P` of 𝒫 with the fewest frozen agents and
`def(P) > 0` (`+∞` included) has a pre-allocation `P′` of 𝒫 with the fewest frozen agents, `R P P′` and
`def(P′) < def(P)`. -/
def DefLocalAt (R : Nbhd A G) (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ base, MinFrozen v agents goods base →
    1 ≤ (nFrozen v agents goods base : Int) - (2 * (agents.length : Int) - (goods.length : Int)) →
    ¬ DeficitLE v agents goods base 0 →
      ∃ base', MinFrozen v agents goods base' ∧ R v agents goods base base' ∧ DeficitLT v agents goods base' base

/-- **DL_R** (`k4/strategy.md` §3, with the relation `R` in place of "at most two bases differ"): `DefLocalAt R` on
every strict profile of every connected k = 4 core, the scope of DL₂. A hypothesis, never an axiom. -/
def DefLocal (R : Nbhd A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → DefLocalAt R v agents goods

/-- DL_R on every strict profile of every k = 4 core, connected or not. -/
def DefLocalAll (R : Nbhd A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → DefLocalAt R v agents goods

/-- **`P′` differs from `P` in the bases of at most `k` agents**: some list `S` of at most `k` agents such that every
listed agent outside `S` has the same base (on `goods`) in `P` and `P′`. -/
def BasesDiffer (k : Nat) : Nbhd A G := fun _ agents goods base base' =>
  ∃ S : List A, S.length ≤ k ∧ ∀ i ∈ agents, i ∉ S → baseOf goods base i = baseOf goods base' i

/-- **Conjecture DL₂** (`k4/strategy.md` §3, K4.STRAT.DL2): DL_R for "the bases of at most two agents differ". -/
def DefLocal2 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  DefLocal (BasesDiffer (A := A) (G := G) 2)

/-! ## The deficit is an element of `ℤ ∪ {+∞}` -/

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}

/-- `def(P) ≤ d` is upward closed in `d`. -/
theorem deficitLE_mono {d d' : Int} (h : DeficitLE v agents goods base d) (hd : d ≤ d') :
    DeficitLE v agents goods base d' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, o, ho, hF, C, hU, hle⟩
  · exact Or.inl ⟨h1, Int.le_trans h2 hd⟩
  · exact Or.inr ⟨h1, o, ho, hF, C, hU, Int.le_trans hle hd⟩

theorem sum_le_two_mul_int {α : Type} (f : α → Int) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ 2) → (l.map f).sum ≤ 2 * (l.length : Int)
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := sum_le_two_mul_int f l (fun b hb => h b (by simp [hb]))
    have := h a (by simp)
    omega

theorem sum_le_two_mul_nat {α : Type} (f : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ 2) → (l.map f).sum ≤ 2 * l.length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := sum_le_two_mul_nat f l (fun b hb => h b (by simp [hb]))
    have := h a (by simp)
    omega

/-- **The deficit is bounded below**: `def(P) ≥ −2n`, since `S ≤ 2n` and every `S_o(C) ≤ 2n`. -/
theorem deficitLE_lower {d : Int} (h : DeficitLE v agents goods base d) : -(2 * (agents.length : Int)) ≤ d := by
  rcases h with ⟨-, h2⟩ | ⟨-, o, -, -, C, -, hle⟩
  · have hS : capSum agents goods base (vbNeeds v goods base) ≤ 2 * (agents.length : Int) := by
      unfold capSum
      refine sum_le_two_mul_int _ agents fun i _ => ?_
      unfold cap
      split <;> omega
    unfold omegaP at h2
    omega
  · have hS : otherSlots agents goods base (roNeeds v goods base o C) o ≤ 2 * agents.length := by
      unfold otherSlots
      refine sum_le_two_mul_nat _ agents fun j _ => ?_
      split <;> omega
    omega

/-- **A finite deficit is attained**: if `def(P) ≤ d` for some integer `d`, there is a least such integer, `def(P)`. -/
theorem exists_least_deficit {d : Int} (h : DeficitLE v agents goods base d) :
    ∃ d₀, DeficitLE v agents goods base d₀ ∧ ∀ d', DeficitLE v agents goods base d' → d₀ ≤ d' := by
  have key : ∀ n : Nat, ∀ d : Int, d + 2 * (agents.length : Int) ≤ n → DeficitLE v agents goods base d →
      ∃ d₀, DeficitLE v agents goods base d₀ ∧ ∀ d', DeficitLE v agents goods base d' → d₀ ≤ d' := by
    intro n
    induction n with
    | zero =>
      intro d hn hd
      exact ⟨d, hd, fun d' hd' => by have := deficitLE_lower hd'; omega⟩
    | succ n ih =>
      intro d hn hd
      by_cases h1 : DeficitLE v agents goods base (d - 1)
      · exact ih (d - 1) (by omega) h1
      · refine ⟨d, hd, fun d' hd' => Classical.byContradiction fun hlt => h1 (deficitLE_mono hd' ?_)⟩
        omega
  exact key (d + 2 * (agents.length : Int)).toNat d (Int.self_le_toNat _) h

/-- **`DeficitLT` is the order of `ℤ ∪ {+∞}`**: `def(P′) < def(P)` iff `def(P′)` is an integer `d₀` (the least `d`
with `def(P′) ≤ d`) and not `def(P) ≤ d₀`. -/
theorem deficitLT_iff {base' : G → Option A} :
    DeficitLT v agents goods base' base ↔
      ∃ d₀, (DeficitLE v agents goods base' d₀ ∧ ∀ d, DeficitLE v agents goods base' d → d₀ ≤ d) ∧
        ¬ DeficitLE v agents goods base d₀ := by
  constructor
  · rintro ⟨d, hd, hnd⟩
    obtain ⟨d₀, hd₀, hleast⟩ := exists_least_deficit hd
    exact ⟨d₀, ⟨hd₀, hleast⟩, fun h => hnd (deficitLE_mono h (hleast d hd))⟩
  · rintro ⟨d₀, ⟨hd₀, -⟩, hnd⟩
    exact ⟨d₀, hd₀, hnd⟩

/-! ## `ω` on 𝒫 -/

/-- **`def(P) > 0` forces `ω(P) ≥ 1`**: if `ω(P) ≤ 0`, then `def(P) = ω(P) ≤ 0`. -/
theorem omegaP_pos (h : ¬ DeficitLE v agents goods base 0) : 0 < omegaP v agents goods base :=
  Classical.byContradiction fun hle => h (Or.inl ⟨by omega, by omega⟩)

omit [DecidableEq G] in
/-- **`ω(P) = f(P) − (2n − m)` on 𝒫** (`EFX.LB4.omega_eq` with `|F| = |NA|`, `EFX.LB4.numFrozen_eq`). -/
theorem omegaP_eq (hag : agents.Nodup) (hgd : goods.Nodup) (hP : InP v agents goods base) :
    omegaP v agents goods base =
      (nFrozen v agents goods base : Int) - (2 * (agents.length : Int) - (goods.length : Int)) := by
  unfold omegaP nFrozen
  rw [LB4.omega_eq hP.valid hag hgd hP.mem, LB4.numFrozen_eq hP.valid hag hgd hP.mem]

omit [DecidableEq G] in
/-- **`ω` is the same for every pre-allocation with the fewest frozen agents** (the parenthetical of DL₂). -/
theorem omegaP_minFrozen_eq {base' : G → Option A} (hag : agents.Nodup) (hgd : goods.Nodup)
    (hM : MinFrozen v agents goods base) (hM' : MinFrozen v agents goods base') :
    omegaP v agents goods base = omegaP v agents goods base' := by
  have h1 := hM.2 base' hM'.1
  have h2 := hM'.2 base hM.1
  rw [omegaP_eq hag hgd hM.1, omegaP_eq hag hgd hM'.1]
  omega

/-! ## The descent -/

/-- **DL_R ⟹ C₄ᵐⁱⁿ's conclusion (removal-only), on one instance, by finite descent.** Some pre-allocation of 𝒫 has
the fewest frozen agents (`exists_minFrozen`). From a min-frozen `P` with `def(P) > 0`, DL_R gives a min-frozen `P′`
and an integer `d` with `def(P′) ≤ d < def(P)`; after the first step (from a possible `+∞`) the deficits met before
the last step are positive integers that strictly decrease, so the descent ends at a min-frozen pre-allocation with
`def ≤ 0`. -/
theorem exists_removalOnly_of_defLocalAt {R : Nbhd A G} (hag : agents.Nodup) (hgd : goods.Nodup)
    (h : DefLocalAt R v agents goods) :
    ∃ base, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base := by
  -- one step: `ω ≥ 1` is forced by `def(P) > 0`
  have step : ∀ base, MinFrozen v agents goods base → ¬ DeficitLE v agents goods base 0 →
      ∃ base' d, MinFrozen v agents goods base' ∧ DeficitLE v agents goods base' d ∧
        ¬ DeficitLE v agents goods base d := by
    intro base hM hpos
    have hω := omegaP_pos hpos
    rw [omegaP_eq hag hgd hM.1] at hω
    obtain ⟨base', hM', -, d, hd, hnd⟩ := h base hM (by omega) hpos
    exact ⟨base', d, hM', hd, hnd⟩
  -- the descent, on a natural bound `n` of `def(P)`
  have key : ∀ n : Nat, ∀ base, MinFrozen v agents goods base → DeficitLE v agents goods base n →
      ∃ base, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro base hM hn
      by_cases h0 : DeficitLE v agents goods base 0
      · exact ⟨base, hM, h0⟩
      obtain ⟨base', d, hM', hd, hnd⟩ := step base hM h0
      have hdn : d < n := Classical.byContradiction fun hc => hnd (deficitLE_mono hn (by omega))
      have hn0 : (0 : Int) < n := Classical.byContradiction fun hc => h0 (deficitLE_mono hn (by omega))
      exact ih d.toNat (by omega) base' hM' (deficitLE_mono hd (Int.self_le_toNat d))
  obtain ⟨base, hM⟩ := exists_minFrozen (v := v) hag hgd
  by_cases h0 : DeficitLE v agents goods base 0
  · exact ⟨base, hM, h0⟩
  obtain ⟨base', d, hM', hd, -⟩ := step base hM h0
  exact key d.toNat base' hM' (deficitLE_mono hd (Int.self_le_toNat d))

/-- **For the full relation, DL_R is exactly C₄ᵐⁱⁿ's conclusion (removal-only)** on an instance: the reduction loses
nothing. -/
theorem defLocalAt_top_iff (hag : agents.Nodup) (hgd : goods.Nodup) :
    DefLocalAt (fun _ _ _ _ _ => True) v agents goods ↔
      ∃ base, MinFrozen v agents goods base ∧ RemovalOnly v agents goods base := by
  constructor
  · exact exists_removalOnly_of_defLocalAt hag hgd
  · rintro ⟨b, hM, hR⟩ base _ _ hpos
    exact ⟨b, hM, trivial, 0, hR, hpos⟩

/-- Widening the relation weakens DL_R, on one instance. -/
theorem DefLocalAt.mono {R R' : Nbhd A G}
    (hR : ∀ b b', R v agents goods b b' → R' v agents goods b b') (h : DefLocalAt R v agents goods) :
    DefLocalAt R' v agents goods := fun base hM hω hpos => by
  obtain ⟨b', hM', hr, hlt⟩ := h base hM hω hpos
  exact ⟨b', hM', hR base b' hr, hlt⟩

/-- **Widening the relation weakens DL_R.** -/
theorem DefLocal.mono {R R' : Nbhd A G}
    (hR : ∀ v agents goods b b', R v agents goods b b' → R' v agents goods b b') (h : DefLocal R) : DefLocal R' :=
  fun agents goods v hag hgd hc hconn hs =>
    (h agents goods v hag hgd hc hconn hs).mono (hR v agents goods)

omit [DecidableEq G] in
/-- At most `k` differing bases are at most `k'` differing bases for `k ≤ k'` (so DL₂ implies DL_k for `k ≥ 2`). -/
theorem basesDiffer_mono {k k' : Nat} (hk : k ≤ k') {b b' : G → Option A}
    (h : BasesDiffer (A := A) k v agents goods b b') : BasesDiffer k' v agents goods b b' := by
  obtain ⟨S, hS, hb⟩ := h
  exact ⟨S, Nat.le_trans hS hk, hb⟩

/-- DL_R on every core implies DL_R on connected cores. -/
theorem defLocal_of_defLocalAll {R : Nbhd A G} (h : DefLocalAll R) : DefLocal R :=
  fun agents goods v hag hgd hc _ hs => h agents goods v hag hgd hc hs

/-! ## DL_R ⟹ C₄ᵐⁱⁿ (removal-only) ⟹ TARGET₄ -/

/-- **DL_R ⟹ C₄ᵐⁱⁿ (removal-only) on connected cores with a 4-good agent**, for every relation `R` (the 4-good agent is
not used). -/
theorem C4minROConn_of_defLocal {R : Nbhd A G} (h : DefLocal R) : C4minROConn A G :=
  fun agents goods v hag hgd hc hconn hs _ =>
    exists_removalOnly_of_defLocalAt hag hgd (h agents goods v hag hgd hc hconn hs)

/-- **DL_R on every core ⟹ C₄ᵐⁱⁿ (removal-only)** (`TheoremC4minRO`), for every relation `R`. -/
theorem C4minRO_of_defLocalAll {R : Nbhd A G} (h : DefLocalAll R) : TheoremC4minRO A G :=
  fun agents goods v hag hgd hc hs => exists_removalOnly_of_defLocalAt hag hgd (h agents goods v hag hgd hc hs)

/-- **DL_R ⟹ TARGET₄**, for every relation `R` (`target4_of_C4minROConn`): every instance with at least one agent and
at most four relevant goods per agent has an EFX₀ allocation. DL_R is a hypothesis, not an axiom. -/
theorem target4_of_defLocal (I : Inst) (hn : 0 < I.n) {R : Nbhd (Fin I.n) (Fin I.m)} (hDL : DefLocal R)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4minROConn I hn (C4minROConn_of_defLocal hDL) h

/-- **DL₂ ⟹ C₄ᵐⁱⁿ (removal-only) on connected cores with a 4-good agent.** -/
theorem C4minROConn_of_defLocal2 (h : DefLocal2 A G) : C4minROConn A G :=
  C4minROConn_of_defLocal h

/-- **DL₂ ⟹ TARGET₄.** DL₂ is a hypothesis, not an axiom. -/
theorem target4_of_defLocal2 (I : Inst) (hn : 0 < I.n) (hDL : DefLocal2 (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_defLocal I hn hDL h

end C4min
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.C4min.deficitLE_mono
#print axioms EFX.C4min.deficitLE_lower
#print axioms EFX.C4min.exists_least_deficit
#print axioms EFX.C4min.deficitLT_iff
#print axioms EFX.C4min.omegaP_pos
#print axioms EFX.C4min.omegaP_eq
#print axioms EFX.C4min.omegaP_minFrozen_eq
#print axioms EFX.C4min.exists_removalOnly_of_defLocalAt
#print axioms EFX.C4min.defLocalAt_top_iff
#print axioms EFX.C4min.DefLocalAt.mono
#print axioms EFX.C4min.DefLocal.mono
#print axioms EFX.C4min.basesDiffer_mono
#print axioms EFX.C4min.defLocal_of_defLocalAll
#print axioms EFX.C4min.C4minROConn_of_defLocal
#print axioms EFX.C4min.C4minRO_of_defLocalAll
#print axioms EFX.C4min.target4_of_defLocal
#print axioms EFX.C4min.C4minROConn_of_defLocal2
#print axioms EFX.C4min.target4_of_defLocal2
