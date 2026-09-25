import EFX.PreAllocK

/-!
# Construction LB₄ʳ and Theorem C₄ (`k4/lb4.md` §2, §5; ledger K4.C4.FRAME)

LB₄ʳ(τ) (`k4/lb4.md` §5, "LB₄ʳ(τ), precisely", with LB₄'s steps of §2) defined over the pre-allocations of
`EFX/PreAllocK.lean`, the statement of Theorem C₄ (LB₄ʳ never fails on a strict profile of a k = 4 core), and the
reduction "C₄ ⟹ K4.D ⟹ TARGET₄" (`target4_of_C4`).

**Representation.** A state `LState` records the bases (`base : G → Option A`), the picks (`pick`, used by the need
chains) and the agents *marked* as upgraded or rotated. Needs are not stored but derived (`needsOf`):
- an unmarked agent with pick `y` has the needs of a pick, the goods it values more than `y` (`v_i(g) > v_i(y)`);
- an unmarked agent without a pick needs all its relevant goods;
- a marked agent has the value-based needs of its base, `{g ∉ B_i : v_i(g) > v_i(B_i)}`.
For an upgrade `B_k = {Y_k, g}` of an agent with pick needs, the text's `N′ = {x ∈ N_k : v_k(x) > v_k(Y_k) + v_k(g)}`
is exactly this set, and a rotated agent has value-based needs by §2.

**The steps.**
- `phase1`: Phase 1(τ) as a function (P-steps by LB's key, insertion steps by τ).
- `UpStep pol`, `UpRun pol`: one upgrade of the policy `pol` (need-shrinking, envy-free only, none), and a run of
  upgrades until none applies.
- `RotStep`: one rotation along a need chain with a base `O`, kept only if the result passes the checks of §5
  ((V1), (V2) for every marked agent, at most one base of three or more goods).
- `Output`: the owner step's result: a completion with the owner's needs from its bundle that satisfies (OC₄), with
  no owner exactly when `ω ≤ 0`, unless some base has three or more goods (then its agent is the owner).
- `Succeeds τ`: some policy, some run of upgrades, at most three rotations, and an output.

**Choices where the prose leaves room** (to be pinned down by the proof of C₄; see the module README entry):
1. The order `≻_i` is by value (`v_i(g) > v_i(h)`); the text breaks ties by index. On strict profiles (C₄'s domain)
   relevant goods have distinct values, so the two agree.
2. τ is a list of numbers; the j-th insertion step takes the `(τ_j mod u)`-th unprocessed agent in index order (`u`
   the number of unprocessed agents; `τ_j = 0` once τ is used up). τ = [] is index order.
3. The search order (owners latest-processed first, chains, sizes of `C` and `O`) is not modeled: the relations allow
   every choice the search tries, so "LB₄ʳ succeeds" means "some tried configuration succeeds".
4. The owner step allows every completion that satisfies (OC₄), not only those with `|C| ≥ min(|J|, S − cap(o))`;
   by Lemma 3₄ this loses nothing except for a rotated owner with a one-good base.
5. A rotated agent follows the text's rule `cap(k) = 2 − |O|` (it gets a slot when `|O| = 1`), but (V2) is required of
   `O` even when `|O| = 1`, as in `lb4.c`. `ω` is computed with the text's signed caps.
6. A state reached by a rotation is used whether or not the owner step failed before it (for "succeeds" this is the
   same: an earlier success is a success).
7. A chain may end at any agent that is not frozen: with a base of at most one good, upgraded, or rotated earlier
   (§5); the end releases its whole base to the junk and takes the previous agent's pick.
-/

set_option autoImplicit false

namespace EFX
namespace LB4R

open LB4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## States and needs -/

/-- A state of LB₄ʳ: bases, picks, and the agents marked as upgraded or rotated. -/
structure LState (A G : Type) where
  base : G → Option A
  pick : A → Option G
  marked : A → Prop

/-- The needs of agent `i` in a state (derived, see the module doc). -/
def needsOf (v : A → G → Nat) (goods : List G) (s : LState A G) (i : A) (g : G) : Prop :=
  (s.marked i ∧ g ∈ goods ∧ s.base g ≠ some i ∧ value v i (baseOf goods s.base i) < v i g) ∨
  (¬ s.marked i ∧ g ∈ goods ∧ 0 < v i g ∧ ∀ y, s.pick i = some y → v i y < v i g)

/-- `ω = |J| − S`, with the caps counted with their sign and the needs of the state. -/
noncomputable def omega (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) : Int :=
  ((LB4.junk goods s.base).length : Int) - capSum agents goods s.base (needsOf v goods s)

/-! ## Phase 1(τ) -/

/-- `i`'s favourite good among `S`: of largest value, the first in `S` on ties. -/
def fav (v : A → G → Nat) (i : A) (S : List G) : Option G := favorite (v i) (relevant v i S)

/-- The rank of `f` among `i`'s relevant goods: the number of them `i` values more. -/
def rankOf (v : A → G → Nat) (goods : List G) (i : A) (f : G) : Nat :=
  ((relevant v i goods).filter (fun h => decide (v i f < v i h))).length

/-- LB's key for a P-step, encoded as one number ordered lexicographically: the rank of the favourite good of
`R_i ∩ G` (`d_i` if none), then `|R_i ∩ G|`, then the index of `i`. -/
def key (v : A → G → Nat) (agents : List A) (goods : List G) (G0 : List G) (i : A) : Nat :=
  let K := agents.length + goods.length + 5
  let r := match fav v i G0 with
    | some f => rankOf v goods i f
    | none => (relevant v i goods).length
  (r * K + (relevant v i G0).length) * K + agents.idxOf i

/-- `i` has lost a good: some good it values is no longer available. -/
def lost (v : A → G → Nat) (goods : List G) (G0 : List G) (i : A) : Bool :=
  (relevant v i goods).any (fun g => !G0.contains g)

/-- The first element of a list with the smallest `f`. -/
def argmin (f : A → Nat) : List A → Option A
  | [] => none
  | a :: l =>
    match argmin f l with
    | none => some a
    | some b => if f a ≤ f b then some a else some b

/-- Remove a pick from the available goods. -/
def takeOut (G0 : List G) : Option G → List G
  | none => G0
  | some y => G0.erase y

/-- **Phase 1(τ)**: serial dictatorship with priority to agents that lost a good. `U` are the unprocessed agents in
index order, `G0` the available goods; each step processes one agent, which picks its favourite available good. The
result lists the agents in processing order with their picks. -/
def phase1 (v : A → G → Nat) (agents : List A) (goods : List G) :
    Nat → List A → List G → List Nat → List (A × Option G)
  | 0, _, _, _ => []
  | fuel + 1, U, G0, τ =>
    match U with
    | [] => []
    | u :: us =>
      let L := (u :: us).filter (lost v goods G0)
      let next : A × List Nat :=
        match argmin (key v agents goods G0) L with
        | some x => (x, τ)
        | none => (((u :: us).getD (τ.headD 0 % (u :: us).length) u), τ.tail)
      let y := fav v next.1 G0
      (next.1, y) :: phase1 v agents goods fuel ((u :: us).erase next.1) (takeOut G0 y) next.2

/-- The state after Phase 1(τ): each agent's pick is its base, nobody is marked. -/
def phase1State (v : A → G → Nat) (agents : List A) (goods : List G) (τ : List Nat) : LState A G :=
  let run := phase1 v agents goods agents.length agents goods τ
  { base := fun g => (run.find? (fun p => p.2 == some g)).map Prod.fst
    pick := fun i => ((run.find? (fun p => p.1 == i)).map Prod.snd).join
    marked := fun _ => False }

/-! ## Upgrades -/

/-- The three upgrade policies of LB₄ʳ. -/
inductive Policy
  | shrink
  | envyFree
  | none

/-- `k` may take the junk good `g` into its base under the policy: `k` is unmarked with base `{Y}`, `Y ∉ NA`,
`N_k ≠ ∅`, `g` is junk and relevant to `k`, and `g` shrinks `N_k` (some good of `N_k` is worth at most
`v_k(Y) + v_k(g)`); with `envyFree`, also `v_k(R_k ∖ {Y, g}) ≤ v_k(Y) + v_k(g)`. -/
def UpEligible (v : A → G → Nat) (agents : List A) (goods : List G) (pol : Policy) (s : LState A G) (k : A)
    (g : G) : Prop :=
  k ∈ agents ∧ ¬ s.marked k ∧ ∃ y, s.pick k = some y ∧ baseOf goods s.base k = [y] ∧
    ¬ NA agents (needsOf v goods s) y ∧ (∃ x, needsOf v goods s k x) ∧ g ∈ LB4.junk goods s.base ∧ 0 < v k g ∧
    (∃ x, needsOf v goods s k x ∧ v k x ≤ v k y + v k g) ∧
    (match pol with
      | .shrink => True
      | .envyFree => value v k ((relevant v k goods).filter (fun h => h ≠ y ∧ h ≠ g)) ≤ v k y + v k g
      | .none => False)

/-- The state after `k` takes `g`: `g` joins `k`'s base and `k` is marked. -/
def upgrade (s : LState A G) (k : A) (g : G) : LState A G :=
  { base := fun h => if h = g then some k else s.base h
    pick := s.pick
    marked := fun i => i = k ∨ s.marked i }

/-- One upgrade: the smallest-index eligible agent takes its best eligible good (first in `goods` on ties). -/
def UpStep (v : A → G → Nat) (agents : List A) (goods : List G) (pol : Policy) (s s' : LState A G) : Prop :=
  ∃ k g, UpEligible v agents goods pol s k g ∧
    (∀ k' g', UpEligible v agents goods pol s k' g' → agents.idxOf k ≤ agents.idxOf k') ∧
    (∀ g', UpEligible v agents goods pol s k g' → v k g' < v k g ∨ (v k g' = v k g ∧ goods.idxOf g ≤ goods.idxOf g')) ∧
    s' = upgrade s k g

/-- A run of upgrades that stops when none applies. -/
inductive UpRun (v : A → G → Nat) (agents : List A) (goods : List G) (pol : Policy) :
    LState A G → LState A G → Prop
  | done (s : LState A G) : (∀ k g, ¬ UpEligible v agents goods pol s k g) → UpRun v agents goods pol s s
  | step (s s' s'' : LState A G) : UpStep v agents goods pol s s' → UpRun v agents goods pol s' s'' →
      UpRun v agents goods pol s s''

/-! ## Rotations -/

/-- The predecessor of `x` along the chain. -/
def prevOf (chain : List A) (x : A) : Option A :=
  ((chain.zip chain.tail).find? (fun p => p.2 == x)).map Prod.fst

/-- The rotation along `chain = k :: …` (at least two agents) with base `O` for `k`: every later agent of the chain
takes its predecessor's pick as its base (and pick), the last agent's old base returns to the junk, `k` takes `O`
and is marked; the agents of the chain after `k` are unmarked (they hold picks). -/
def rotate (s : LState A G) (chain : List A) (O : List G) : LState A G :=
  { base := fun g =>
      if g ∈ O then chain.head?
      else match (chain.zip chain.tail).find? (fun p => s.pick p.1 == some g) with
        | some p => some p.2
        | none => if s.base g = chain.getLast? then none else s.base g
    pick := fun x => if x ∈ chain.tail then ((prevOf chain x).map s.pick).join
      else if some x = chain.head? then none else s.pick x
    marked := fun x => some x = chain.head? ∨ (s.marked x ∧ x ∉ chain) }

/-- A state is *frozen at* `x`: `x` is unmarked with a one-good base in `NA`. -/
def FrozenAt (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (x : A) : Prop :=
  ¬ s.marked x ∧ Frozen agents goods s.base (needsOf v goods s) x

/-- The checks of §5 on the result of a rotation: (V1), (V2) for every marked agent (even with one good), and at
most one base of three or more goods. -/
def RotChecks (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) : Prop :=
  Valid agents goods s.base (needsOf v goods s) ∧
  (∀ i ∈ agents, s.marked i → ∀ g ∈ baseOf goods s.base i, ¬ NA agents (needsOf v goods s) g) ∧
  (∀ i ∈ agents, ∀ j ∈ agents, 3 ≤ (baseOf goods s.base i).length → 3 ≤ (baseOf goods s.base j).length → i = j)

/-- **One rotation** (§5, R(d)): a frozen agent `k`, a need chain `k = x₀, x₁, …, x_t` of distinct agents (`t ≥ 1`;
`x₁, …, x_{t−1}` frozen; each `x_i` needs `x_{i−1}`'s pick; `x_t` not frozen), and a nonempty base
`O ⊆ R_k ∩ (J ∪ B_{x_t})`; the result must pass `RotChecks`. -/
def RotStep (v : A → G → Nat) (agents : List A) (goods : List G) (s s' : LState A G) : Prop :=
  ∃ (k : A) (xs : List A) (O : List G),
    (k :: xs).Nodup ∧ xs ≠ [] ∧ (∀ x ∈ k :: xs, x ∈ agents) ∧
    FrozenAt v agents goods s k ∧
    (∀ x ∈ xs.dropLast, FrozenAt v agents goods s x) ∧
    (∀ x, xs.getLast? = some x → ¬ FrozenAt v agents goods s x) ∧
    (∀ p ∈ (k :: xs).zip xs, ∃ y, s.pick p.1 = some y ∧ needsOf v goods s p.2 y) ∧
    O ≠ [] ∧ O.Nodup ∧
    (∀ g ∈ O, g ∈ goods ∧ 0 < v k g ∧ (s.base g = none ∨ s.base g = xs.getLast?)) ∧
    s' = rotate s (k :: xs) O ∧ RotChecks v agents goods s'

/-- States reachable by at most `d` rotations. -/
inductive RotReach (v : A → G → Nat) (agents : List A) (goods : List G) :
    Nat → LState A G → LState A G → Prop
  | refl (d : Nat) (s : LState A G) : RotReach v agents goods d s s
  | step (d : Nat) (s s' s'' : LState A G) : RotStep v agents goods s s' → RotReach v agents goods d s' s'' →
      RotReach v agents goods (d + 1) s s''

/-! ## The owner step and success -/

/-- **An output** of the owner step on the state `s`: a completion `X` with owner `o`, the owner's needs taken from
its bundle, that satisfies (OC₄); with no owner exactly when `ω ≤ 0`, unless some base has three or more goods (then
`Completion` forces its agent to be the owner). -/
def Output (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (o : Option A) (X : G → A) :
    Prop :=
  Completion agents goods s.base (ownerNeeds v goods X (needsOf v goods s) o) o X ∧ OC v agents goods X o ∧
  ((∀ i ∈ agents, (baseOf goods s.base i).length ≤ 2) → (o = none ↔ omega v agents goods s ≤ 0))

/-- **LB₄ʳ(τ) succeeds**: for some upgrade policy, the run of upgrades from Phase 1(τ) followed by at most three
rotations reaches a state with an output. -/
def Succeeds (v : A → G → Nat) (agents : List A) (goods : List G) (τ : List Nat) : Prop :=
  ∃ (pol : Policy) (s₁ s : LState A G) (o : Option A) (X : G → A),
    UpRun v agents goods pol (phase1State v agents goods τ) s₁ ∧ RotReach v agents goods 3 s₁ s ∧
    Output v agents goods s o X

/-- **Theorem C₄** (conjecture, `k4/lb4.md` §5): for every strict profile of every k = 4 core and every insertion
sequence τ, LB₄ʳ(τ) succeeds. -/
def TheoremC4 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → ∀ τ : List Nat, Succeeds v agents goods τ

/-- **Theorem C₄ for the index order** (τ = []: every insertion step takes the first unprocessed agent). -/
def TheoremC4index (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → Succeeds v agents goods []

theorem theoremC4index_of_C4 (h : TheoremC4 A G) : TheoremC4index A G :=
  fun agents goods v hag hgd hc hs => h agents goods v hag hgd hc hs []

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.theoremC4index_of_C4
