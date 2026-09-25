import EFX.PreAllocK

/-!
# Construction LB₄ʳ and Theorem C₄ (`k4/lb4.md` §2, §5; ledger K4.C4.FRAME)

LB₄ʳ(τ) (`k4/lb4.md` §5, "LB₄ʳ(τ), precisely", with LB₄'s steps of §2) defined over the pre-allocations of
`EFX/PreAllocK.lean`, the statement of Theorem C₄ (LB₄ʳ never fails on a strict profile of a k = 4 core), its
route-agnostic form C₄∃ (`TheoremC4exists`: every strict profile of every k = 4 core has a sound completion of some
valid pre-allocation), and the reductions "C₄ ⟹ C₄∃ ⟹ K4.D ⟹ TARGET₄" (`C4exists_of_C4`, `k4D_of_C4exists`,
`target4_of_C4exists`, `target4_of_C4`).

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
8. In a rotation, `x_{i+1}` takes the base of `x_i` (for `i < t`); these agents are frozen, so their base is their pick
   `Y_{x_i}` alone (an invariant proved below), which is the text's rule.
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

/-- The next agent of Phase 1 among the unprocessed agents `U` (with fallback `d`), and the rest of τ: by a P-step
the agent with the smallest key among those that lost a good, else by an insertion step the `(τ₀ mod |U|)`-th
unprocessed agent in index order (consuming `τ₀`). -/
def nextAgent (v : A → G → Nat) (agents : List A) (goods : List G) (U : List A) (G0 : List G) (τ : List Nat)
    (d : A) : A × List Nat :=
  match argmin (key v agents goods G0) (U.filter (lost v goods G0)) with
  | some x => (x, τ)
  | none => (U.getD (τ.headD 0 % U.length) d, τ.tail)

/-- **Phase 1(τ)**: serial dictatorship with priority to agents that lost a good. `U` are the unprocessed agents in
index order, `G0` the available goods; each step processes one agent (`nextAgent`), which picks its favourite
available good. The result lists the agents in processing order with their picks. -/
def phase1 (v : A → G → Nat) (agents : List A) (goods : List G) :
    Nat → List A → List G → List Nat → List (A × Option G)
  | 0, _, _, _ => []
  | _ + 1, [], _, _ => []
  | fuel + 1, u :: us, G0, τ =>
    let nx := nextAgent v agents goods (u :: us) G0 τ u
    (nx.1, fav v nx.1 G0) ::
      phase1 v agents goods fuel ((u :: us).erase nx.1) (takeOut G0 (fav v nx.1 G0)) nx.2

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

/-- The rotation along the chain `c = k :: …` (at least two distinct agents) with base `O` for `k`: every good of
the base of an agent `x_i` of the chain moves to the next agent `x_{i+1}` (the frozen agents of the chain hold their
pick alone, so `x_{i+1}` takes `Y_{x_i}`), the last agent's base returns to the junk, and `k` takes `O`; every agent
of the chain after `k` takes its predecessor's pick, `k` has none and is marked, and the others of the chain are
unmarked. -/
def rotate (s : LState A G) (c : List A) (O : List G) : LState A G :=
  { base := fun g =>
      if g ∈ O then c.head?
      else match s.base g with
        | none => none
        | some a => if a ∈ c then c[c.idxOf a + 1]? else some a
    pick := fun x => if x ∈ c then (if c.idxOf x = 0 then none else (c[c.idxOf x - 1]?).bind s.pick)
      else s.pick x
    marked := fun x => c.head? = some x ∨ (s.marked x ∧ x ∉ c) }

/-- A state is *frozen at* `x`: `x` is unmarked with a one-good base in `NA`. -/
def FrozenAt (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) (x : A) : Prop :=
  ¬ s.marked x ∧ Frozen agents goods s.base (needsOf v goods s) x

/-- The checks of §5 on the result of a rotation: (V1), (V2) for every marked agent (even with one good), and at
most one base of three or more goods. -/
def RotChecks (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) : Prop :=
  Valid agents goods s.base (needsOf v goods s) ∧
  (∀ i ∈ agents, s.marked i → ∀ g ∈ baseOf goods s.base i, ¬ NA agents (needsOf v goods s) g) ∧
  (∀ i ∈ agents, ∀ j ∈ agents, 3 ≤ (baseOf goods s.base i).length → 3 ≤ (baseOf goods s.base j).length → i = j)

/-- **One rotation** (§5, R(d)): a need chain `c = k :: …` of at least two distinct listed agents in which every agent
but the last is frozen and holds a pick needed by the next one (so `k` is frozen), the last is not frozen, and a
nonempty base `O ⊆ R_k ∩ (J ∪ B_{x_t})` for `k`; the result must pass `RotChecks`. -/
def RotStep (v : A → G → Nat) (agents : List A) (goods : List G) (s s' : LState A G) : Prop :=
  ∃ (c : List A) (k last : A) (O : List G),
    c.Nodup ∧ 2 ≤ c.length ∧ (∀ x ∈ c, x ∈ agents) ∧ c.head? = some k ∧ c.getLast? = some last ∧
    (∀ i a b, c[i]? = some a → c[i + 1]? = some b →
      FrozenAt v agents goods s a ∧ ∃ y, s.pick a = some y ∧ needsOf v goods s b y) ∧
    ¬ FrozenAt v agents goods s last ∧
    O ≠ [] ∧ O.Nodup ∧ (∀ g ∈ O, g ∈ goods ∧ 0 < v k g ∧ (s.base g = none ∨ s.base g = some last)) ∧
    s' = rotate s c O ∧ RotChecks v agents goods s'

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

/-! ## The invariant of reachable states -/

/-- The invariant: a valid pre-allocation (with the derived needs) in which every unmarked listed agent's base is
exactly its pick, a good it values. -/
structure Inv (v : A → G → Nat) (agents : List A) (goods : List G) (s : LState A G) : Prop where
  valid : Valid agents goods s.base (needsOf v goods s)
  unmarked : ∀ i ∈ agents, ¬ s.marked i → baseOf goods s.base i = (s.pick i).toList
  pickRel : ∀ i ∈ agents, ¬ s.marked i → ∀ y, s.pick i = some y → 0 < v i y

omit [DecidableEq G] in
/-- In a state satisfying the invariant, every listed agent's needs are needs in the Definition's sense. -/
theorem Inv.needs {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G}
    (h : Inv v agents goods s) : ∀ i ∈ agents, Needs v goods s.base (needsOf v goods s) i := by
  intro i hi
  by_cases hm : s.marked i
  · refine ⟨fun g hg hb hlt => Or.inl ⟨hm, hg, hb, hlt⟩, fun g hN => ?_⟩
    rcases hN with ⟨_, hg, hb, hlt⟩ | ⟨hm', _⟩
    · exact ⟨hg, by omega, hb⟩
    · exact absurd hm hm'
  · have hB := h.unmarked i hi hm
    refine ⟨fun g hg hb hlt => Or.inr ⟨hm, hg, ?_, fun y hy => ?_⟩, fun g hN => ?_⟩
    · omega
    · rw [hB, hy] at hlt; simpa using hlt
    · rcases hN with ⟨hm', _⟩ | ⟨_, hg, hpos, hlt⟩
      · exact absurd hm' hm
      · refine ⟨hg, hpos, fun hb => ?_⟩
        have hgB : g ∈ baseOf goods s.base i := mem_baseOf.mpr ⟨hg, hb⟩
        rw [hB] at hgB
        cases hy : s.pick i with
        | none => rw [hy] at hgB; simp at hgB
        | some y =>
          rw [hy] at hgB
          simp at hgB; subst hgB
          have := hlt g hy; omega

/-- **Outputs are sound completions.** In a state satisfying the invariant, every output of the owner step is a
completion satisfying (OC₄) of a valid pre-allocation with needs in the Definition's sense (`EFX.LB4.SoundCompletion`),
hence EFX₀ with at most one bundle of more than two goods (Theorem 1′₄). -/
theorem Inv.sound {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G} {o : Option A}
    {X : G → A} (h : Inv v agents goods s) (hO : Output v agents goods s o X) :
    SoundCompletion v agents goods s.base (needsOf v goods s) o X :=
  ⟨fun i hi _ => h.needs i hi, h.valid.toOwnerNeeds hO.1.onBase h.needs, hO.1, hO.2.1⟩

/-! ### Phase 1 -/

omit [DecidableEq A] [DecidableEq G] in
theorem argmin_mem {f : A → Nat} : ∀ {l : List A} {a : A}, argmin f l = some a → a ∈ l
  | [], _, h => by simp [argmin] at h
  | b :: l, a, h => by
    unfold argmin at h
    split at h
    · cases h; simp
    · rename_i c hc
      split at h
      · cases h; simp
      · cases h; exact List.mem_cons_of_mem _ (argmin_mem hc)

omit [DecidableEq A] [DecidableEq G] in
theorem fav_some {v : A → G → Nat} {i : A} {S : List G} {y : G} (h : fav v i S = some y) :
    y ∈ S ∧ 0 < v i y ∧ ∀ g ∈ S, 0 < v i g → v i g ≤ v i y := by
  obtain ⟨hy, hmax⟩ := favorite_spec (v i) h
  obtain ⟨hyS, hpos⟩ := List.mem_filter.mp hy
  exact ⟨hyS, by simpa using hpos, fun g hg hg' => hmax g (List.mem_filter.mpr ⟨hg, by simpa using hg'⟩)⟩

omit [DecidableEq A] [DecidableEq G] in
theorem fav_none {v : A → G → Nat} {i : A} {S : List G} (h : fav v i S = none) : ∀ g ∈ S, ¬ 0 < v i g := by
  intro g hg hpos
  have := (favorite_eq_none_iff (v i)).mp h
  have hmem : g ∈ relevant v i S := List.mem_filter.mpr ⟨hg, by simpa using hpos⟩
  rw [this] at hmem; simp at hmem

theorem nextAgent_mem {v : A → G → Nat} {agents : List A} {goods : List G} {U : List A} {G0 : List G}
    {τ : List Nat} {d : A} (hd : d ∈ U) : (nextAgent v agents goods U G0 τ d).1 ∈ U := by
  unfold nextAgent
  split
  · rename_i x hx
    exact (List.mem_filter.mp (argmin_mem hx)).1
  · have hlen : 0 < U.length := List.length_pos_of_mem hd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hlen)]
    exact List.getElem_mem _

/-- What Phase 1's run satisfies: its agents are distinct agents of `U`, all of them when the fuel suffices; its
picks are distinct available goods their agents value; and a good available at the start that nobody picks is worth
at most the pick of every agent of the run (so that agent has a pick). -/
structure RunSpec (v : A → G → Nat) (U : List A) (G0 : List G) (fuel : Nat) (run : List (A × Option G)) : Prop where
  mem : ∀ p ∈ run, p.1 ∈ U
  nodup : (run.map Prod.fst).Nodup
  cover : U.length ≤ fuel → ∀ x ∈ U, ∃ p ∈ run, p.1 = x
  pickMem : ∀ p ∈ run, ∀ y, p.2 = some y → y ∈ G0 ∧ 0 < v p.1 y
  pickInj : ∀ p ∈ run, ∀ q ∈ run, ∀ y, p.2 = some y → q.2 = some y → p = q
  best : ∀ p ∈ run, ∀ g ∈ G0, 0 < v p.1 g → (∀ q ∈ run, q.2 ≠ some g) → ∃ y, p.2 = some y ∧ v p.1 g ≤ v p.1 y

theorem phase1_spec (v : A → G → Nat) (agents : List A) (goods : List G) :
    ∀ fuel (U : List A) (G0 : List G) (τ : List Nat), U.Nodup → G0.Nodup →
      RunSpec v U G0 fuel (phase1 v agents goods fuel U G0 τ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro U G0 τ _ _
    refine ⟨by simp [phase1], by simp [phase1], fun h x hx => ?_, by simp [phase1], by simp [phase1],
      by simp [phase1]⟩
    have := List.length_pos_of_mem hx; omega
  | succ fuel ih =>
    intro U G0 τ hU hG
    cases U with
    | nil => exact ⟨by simp [phase1], by simp [phase1], fun _ x hx => by simp at hx, by simp [phase1],
        by simp [phase1], by simp [phase1]⟩
    | cons u us =>
      -- the step: `x` picks `y`, the rest runs on the other agents and goods
      have hx := nextAgent_mem (v := v) (agents := agents) (goods := goods) (G0 := G0) (τ := τ)
        (List.mem_cons_self (a := u) (l := us))
      generalize hnx : nextAgent v agents goods (u :: us) G0 τ u = nx at hx
      obtain ⟨x, τ'⟩ := nx
      simp only at hx
      have hrun : phase1 v agents goods (fuel + 1) (u :: us) G0 τ =
          (x, fav v x G0) :: phase1 v agents goods fuel ((u :: us).erase x) (takeOut G0 (fav v x G0)) τ' := by
        simp only [phase1, hnx]
      rw [hrun]
      have hG' : (takeOut G0 (fav v x G0)).Nodup := by
        cases fav v x G0 with
        | none => exact hG
        | some y => exact hG.erase y
      have T := ih ((u :: us).erase x) (takeOut G0 (fav v x G0)) τ' (hU.erase x) hG'
      have hsub : ∀ g, g ∈ takeOut G0 (fav v x G0) → g ∈ G0 := by
        intro g hg
        cases hf : fav v x G0 with
        | none => rw [hf] at hg; exact hg
        | some y => rw [hf] at hg; exact List.mem_of_mem_erase hg
      have hxT : ∀ p ∈ phase1 v agents goods fuel ((u :: us).erase x) (takeOut G0 (fav v x G0)) τ', p.1 ≠ x :=
        fun p hp e => (List.Nodup.not_mem_erase hU) (e ▸ T.mem p hp)
      -- the head's pick is not available to the rest
      have hyT : ∀ y, fav v x G0 = some y → y ∉ takeOut G0 (fav v x G0) := by
        intro y hy
        rw [hy]
        exact List.Nodup.not_mem_erase hG
      refine ⟨fun p hp => ?_, ?_, fun hlen z hz => ?_, fun p hp y hpy => ?_, fun p hp q hq y hpy hqy => ?_,
        fun p hp g hg hpos hnone => ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact hx
        · exact List.mem_of_mem_erase (T.mem p hp)
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨fun hm => by
          obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
          exact hxT p hp hpx, T.nodup⟩
      · by_cases hzx : z = x
        · exact ⟨_, List.mem_cons_self, hzx.symm⟩
        · have hzE : z ∈ (u :: us).erase x := (List.mem_erase_of_ne hzx).mpr hz
          have hlen' : ((u :: us).erase x).length ≤ fuel := by
            rw [List.length_erase_of_mem hx]; simp at hlen ⊢; omega
          obtain ⟨p, hp, hpz⟩ := T.cover hlen' z hzE
          exact ⟨p, List.mem_cons_of_mem _ hp, hpz⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · obtain ⟨h1, h2, -⟩ := fav_some hpy
          exact ⟨h1, h2⟩
        · obtain ⟨h1, h2⟩ := T.pickMem p hp y hpy
          exact ⟨hsub y h1, h2⟩
      · rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
        · rfl
        · exact absurd (T.pickMem q hq y hqy).1 (hyT y hpy)
        · exact absurd (T.pickMem p hp y hpy).1 (hyT y hqy)
        · exact T.pickInj p hp q hq y hpy hqy
      · rcases List.mem_cons.mp hp with rfl | hp
        · -- the head: `g` was available, so `x`'s favourite is worth at least `g`
          cases hf : fav v x G0 with
          | none => exact absurd hpos (fav_none hf g hg)
          | some y => exact ⟨y, rfl, (fav_some hf).2.2 g hg hpos⟩
        · -- the rest: `g` was not picked by the head, so it stays available
          have hgT : g ∈ takeOut G0 (fav v x G0) := by
            cases hf : fav v x G0 with
            | none => exact hg
            | some y =>
              have hne : g ≠ y := fun e => hnone (x, fav v x G0) List.mem_cons_self (by rw [hf, e])
              exact (List.mem_erase_of_ne hne).mpr hg
          exact T.best p hp g hgT hpos fun q hq => hnone q (List.mem_cons_of_mem _ hq)

omit [DecidableEq A] [DecidableEq G] in
theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, h, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with ha1 | ha1 <;> rcases List.mem_cons.mp hb with hb1 | hb1
    · rw [ha1, hb1]
    · subst ha1; exact absurd (List.mem_map.mpr ⟨b, hb1, hab.symm⟩) h.1
    · subst hb1; exact absurd (List.mem_map.mpr ⟨a, ha1, hab⟩) h.1
    · exact eq_of_mem_of_nodup_map h.2 ha1 hb1 hab

omit [DecidableEq A] in
theorem filter_eq_single {P : G → Bool} : ∀ {l : List G}, l.Nodup → ∀ {y : G}, y ∈ l →
    (∀ g ∈ l, P g = true ↔ g = y) → l.filter P = [y]
  | [], _, _, hy, _ => by simp at hy
  | c :: l, hl, y, hy, hP => by
    obtain ⟨hc, hl'⟩ := List.nodup_cons.mp hl
    by_cases hcy : c = y
    · subst hcy
      have hrest : l.filter P = [] := List.filter_eq_nil_iff.mpr fun g hg hPg => by
        have := (hP g (List.mem_cons_of_mem _ hg)).mp hPg
        subst this; exact hc hg
      simp [(hP c List.mem_cons_self).mpr rfl, hrest]
    · have hPc : ¬ P c = true := fun h => hcy ((hP c List.mem_cons_self).mp h)
      simp only [List.filter_cons, hPc, Bool.false_eq_true, ↓reduceIte]
      exact filter_eq_single hl' ((List.mem_cons.mp hy).resolve_left (Ne.symm hcy))
        fun g hg => hP g (List.mem_cons_of_mem _ hg)

section phase1State
variable {v : A → G → Nat} {agents : List A} {goods : List G} {τ : List Nat}

theorem phase1State_pick (hR : RunSpec v agents goods agents.length (phase1 v agents goods agents.length agents goods τ))
    {p : A × Option G} (hp : p ∈ phase1 v agents goods agents.length agents goods τ) :
    (phase1State v agents goods τ).pick p.1 = p.2 := by
  simp only [phase1State]
  cases hq : (phase1 v agents goods agents.length agents goods τ).find? (fun q => q.1 == p.1) with
  | none =>
    exact absurd (List.find?_eq_none.mp hq p hp) (by simp)
  | some q =>
    have hqm := List.mem_of_find?_eq_some hq
    have hq1 : q.1 = p.1 := by simpa using List.find?_some hq
    rw [eq_of_mem_of_nodup_map hR.nodup hqm hp hq1]
    simp

theorem phase1State_pick_none {i : A}
    (h : ∀ p ∈ phase1 v agents goods agents.length agents goods τ, p.1 ≠ i) :
    (phase1State v agents goods τ).pick i = none := by
  simp only [phase1State]
  rw [List.find?_eq_none.mpr fun p hp => by simpa using h p hp]
  simp

theorem phase1State_base (hR : RunSpec v agents goods agents.length (phase1 v agents goods agents.length agents goods τ))
    {g : G} {i : A} : (phase1State v agents goods τ).base g = some i ↔
      ∃ p ∈ phase1 v agents goods agents.length agents goods τ, p.1 = i ∧ p.2 = some g := by
  simp only [phase1State]
  constructor
  · intro h
    cases hq : (phase1 v agents goods agents.length agents goods τ).find? (fun q => q.2 == some g) with
    | none => rw [hq] at h; simp at h
    | some q =>
      rw [hq] at h; simp at h
      exact ⟨q, List.mem_of_find?_eq_some hq, h, by simpa using List.find?_some hq⟩
  · rintro ⟨p, hp, hpi, hpg⟩
    cases hq : (phase1 v agents goods agents.length agents goods τ).find? (fun q => q.2 == some g) with
    | none => exact absurd (List.find?_eq_none.mp hq p hp) (by simp [hpg])
    | some q =>
      have hqg : q.2 = some g := by simpa using List.find?_some hq
      rw [hR.pickInj q (List.mem_of_find?_eq_some hq) p hp g hqg hpg]
      simp [hpi]

theorem phase1State_baseOf (hR : RunSpec v agents goods agents.length (phase1 v agents goods agents.length agents goods τ))
    (hgd : goods.Nodup) (i : A) :
    baseOf goods (phase1State v agents goods τ).base i = ((phase1State v agents goods τ).pick i).toList := by
  by_cases hi : ∃ p ∈ phase1 v agents goods agents.length agents goods τ, p.1 = i
  · obtain ⟨p, hp, rfl⟩ := hi
    rw [phase1State_pick hR hp]
    have hb : ∀ g, (phase1State v agents goods τ).base g = some p.1 ↔ p.2 = some g := fun g => by
      rw [phase1State_base hR]
      constructor
      · rintro ⟨q, hq, hq1, hq2⟩
        rw [← eq_of_mem_of_nodup_map hR.nodup hq hp hq1]; exact hq2
      · intro h; exact ⟨p, hp, rfl, h⟩
    cases hp2 : p.2 with
    | none =>
      simp only [Option.toList_none]
      exact List.filter_eq_nil_iff.mpr fun g _ h => by
        have := (hb g).mp (by simpa using h); rw [hp2] at this; cases this
    | some y =>
      simp only [Option.toList_some]
      exact filter_eq_single hgd (hR.pickMem p hp y hp2).1 fun g _ => by
        rw [decide_eq_true_iff, hb g, hp2]; simp [eq_comm]
  · rw [phase1State_pick_none fun p hp e => hi ⟨p, hp, e⟩]
    exact List.filter_eq_nil_iff.mpr fun g _ h => by
      obtain ⟨p, hp, hpi, -⟩ := (phase1State_base hR).mp (by simpa using h)
      exact hi ⟨p, hp, hpi⟩

/-- **The invariant holds after Phase 1** (for any τ). -/
theorem phase1State_inv (hag : agents.Nodup) (hgd : goods.Nodup) :
    Inv v agents goods (phase1State v agents goods τ) := by
  have hR := phase1_spec v agents goods agents.length agents goods τ hag hgd
  have hbo := phase1State_baseOf hR hgd (τ := τ)
  refine ⟨⟨fun g hg hna => ?_, fun i h2 => ?_⟩, fun i _ _ => hbo i, fun i _ _ y hy => ?_⟩
  · -- (V1): an unpicked good needed by `i` was available at `i`'s turn
    obtain ⟨hgg, hgb⟩ := mem_junk.mp hg
    obtain ⟨i, hi, hN⟩ := hna
    rcases hN with ⟨hm, -⟩ | ⟨-, -, hpos, hlt⟩
    · exact hm
    obtain ⟨p, hp, rfl⟩ := hR.cover (Nat.le_refl _) i hi
    have hnone : ∀ q ∈ phase1 v agents goods agents.length agents goods τ, q.2 ≠ some g := fun q hq hqg => by
      have := (phase1State_base hR (g := g) (i := q.1)).mpr ⟨q, hq, rfl, hqg⟩
      rw [hgb] at this; cases this
    obtain ⟨y, hy, hle⟩ := hR.best p hp g hgg hpos hnone
    have := hlt y (by rw [phase1State_pick hR hp, hy])
    omega
  · -- (V2): every base has at most one good
    rw [hbo i] at h2
    cases hp : (phase1State v agents goods τ).pick i <;> rw [hp] at h2 <;> simp at h2
  · by_cases hi : ∃ p ∈ phase1 v agents goods agents.length agents goods τ, p.1 = i
    · obtain ⟨p, hp, rfl⟩ := hi
      rw [phase1State_pick hR hp] at hy
      exact (hR.pickMem p hp y hy).2
    · rw [phase1State_pick_none fun p hp e => hi ⟨p, hp, e⟩] at hy; cases hy

end phase1State

/-! ### Upgrades -/

section upgrades
variable {v : A → G → Nat} {agents : List A} {goods : List G}

theorem baseOf_upgrade_ne {s : LState A G} {k i : A} {g : G} (hg : s.base g = none) (hik : i ≠ k) :
    baseOf goods (upgrade s k g).base i = baseOf goods s.base i := by
  unfold baseOf upgrade
  apply List.filter_congr
  intro h _
  by_cases hh : h = g
  · subst hh; simp [hg, Ne.symm hik]
  · simp [hh]

theorem needsOf_upgrade_ne {s : LState A G} {k i : A} {g : G} (hg : s.base g = none) (hik : i ≠ k) (h : G) :
    needsOf v goods (upgrade s k g) i h ↔ needsOf v goods s i h := by
  have hb : (upgrade s k g).base h ≠ some i ↔ s.base h ≠ some i := by
    simp only [upgrade]
    by_cases hh : h = g
    · subst hh; simp [hg, Ne.symm hik]
    · simp [hh]
  unfold needsOf
  rw [baseOf_upgrade_ne hg hik, hb]
  simp [upgrade, hik]

/-- **An upgrade keeps the invariant**: `NA` only shrinks, the new base `{Y_k, g}` is not in it (`Y_k ∉ NA` by
eligibility, `g` was junk), and the other agents keep their bases and needs. -/
theorem upgrade_inv {pol : Policy} {s : LState A G} {k : A} {g : G}
    (hI : Inv v agents goods s) (hE : UpEligible v agents goods pol s k g) :
    Inv v agents goods (upgrade s k g) := by
  obtain ⟨hk, hkm, y, hy, hBk, hyNA, -, hgJ, hgpos, -, -⟩ := hE
  obtain ⟨hgg, hgb⟩ := mem_junk.mp hgJ
  have hyb : s.base y = some k := (mem_baseOf.mp (by rw [hBk]; simp : y ∈ baseOf goods s.base k)).2
  -- the new needs are contained in the old ones
  have hsub : ∀ i h, needsOf v goods (upgrade s k g) i h → needsOf v goods s i h := by
    intro i h hN
    by_cases hik : i = k
    · subst hik
      rcases hN with ⟨-, hh, -, hlt⟩ | ⟨hm, -⟩
      · refine Or.inr ⟨hkm, hh, ?_, fun y' hy' => ?_⟩
        · omega
        · rw [hy] at hy'; cases hy'
          have hyB : y ∈ baseOf goods (upgrade s i g).base i := mem_baseOf.mpr ⟨(mem_baseOf.mp
            (by rw [hBk]; simp : y ∈ baseOf goods s.base i)).1, by
              simp only [upgrade]; have : y ≠ g := fun e => by rw [e, hgb] at hyb; cases hyb
              simp [this, hyb]⟩
          have := le_value_of_mem v i hyB
          omega
      · exact absurd (Or.inl rfl) hm
    · exact (needsOf_upgrade_ne hgb hik h).mp hN
  have hNA : ∀ h, NA agents (needsOf v goods (upgrade s k g)) h → NA agents (needsOf v goods s) h :=
    fun h ⟨i, hi, hN⟩ => ⟨i, hi, hsub i h hN⟩
  refine ⟨⟨fun h hh hna => ?_, fun i h2 h hh hna => ?_⟩, fun i hi hm => ?_, fun i hi hm => ?_⟩
  · obtain ⟨hhg, hhb⟩ := mem_junk.mp hh
    have hne : h ≠ g := fun e => by subst e; simp [upgrade] at hhb
    have : s.base h = none := by simpa [upgrade, hne] using hhb
    exact hI.valid.v1 h (mem_junk.mpr ⟨hhg, this⟩) (hNA h hna)
  · by_cases hik : i = k
    · subst hik
      obtain ⟨hhg, hhb⟩ := mem_baseOf.mp hh
      by_cases hhg' : h = g
      · subst hhg'; exact hI.valid.v1 h hgJ (hNA h hna)
      · have : s.base h = some i := by simpa [upgrade, hhg'] using hhb
        have hmem : h ∈ baseOf goods s.base i := mem_baseOf.mpr ⟨hhg, this⟩
        rw [hBk] at hmem; simp at hmem; subst hmem
        exact hyNA (hNA h hna)
    · rw [baseOf_upgrade_ne hgb hik] at h2 hh
      exact hI.valid.v2 i h2 h hh (hNA h hna)
  · have hik : i ≠ k := fun e => hm (Or.inl e)
    have hm' : ¬ s.marked i := fun h => hm (Or.inr h)
    rw [baseOf_upgrade_ne hgb hik]
    exact hI.unmarked i hi hm'
  · exact hI.pickRel i hi fun h => hm (Or.inr h)

theorem upRun_inv {pol : Policy} {s s' : LState A G} (hR : UpRun v agents goods pol s s')
    (hI : Inv v agents goods s) : Inv v agents goods s' := by
  induction hR with
  | done => exact hI
  | step s s' s'' hstep _ ih =>
    obtain ⟨k, g, hE, -, -, rfl⟩ := hstep
    exact ih (upgrade_inv hI hE)

end upgrades

/-! ### Rotations -/

theorem getElem?_idxOf {c : List A} {a : A} (h : a ∈ c) : c[c.idxOf a]? = some a := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h), List.getElem_idxOf]

theorem idxOf_of_getElem? {c : List A} (hc : c.Nodup) {j : Nat} {a : A} (h : c[j]? = some a) :
    c.idxOf a = j := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.Nodup.idxOf_getElem hc j hj

section rotations
variable {v : A → G → Nat} {agents : List A} {goods : List G}

/-- **A rotation keeps the invariant**: validity is checked; every agent of the chain after `k` holds exactly its
predecessor's pick (the predecessor is frozen, so its base is its pick alone, and that pick is not in `O`); an
agent outside the chain keeps its base. -/
theorem rotStep_inv {s s' : LState A G} (hgd : goods.Nodup) (hI : Inv v agents goods s) (hR : RotStep v agents goods s s') :
    Inv v agents goods s' := by
  obtain ⟨c, k, last, O, hc, hlen, hcA, hk, hlast, hchain, -, -, -, hO, rfl, hchk⟩ := hR
  have hkc : k ∈ c := List.mem_of_mem_head? hk
  have hlc : last ∈ c := List.mem_of_getLast? hlast
  refine ⟨hchk.1, fun i hi hm => ?_, fun i hi hm y hy => ?_⟩
  all_goals simp only [rotate] at hm
  -- unmarked after the rotation: not `k`, and unmarked before unless in the chain
  all_goals have hik : c.head? ≠ some i := fun h => hm (Or.inl h)
  · by_cases hic : i ∈ c
    · -- `i = x_{j+1}`: it holds the pick of `x_j`
      have hi0 : c.idxOf i ≠ 0 := fun h0 => hik (by
        have := getElem?_idxOf hic; rw [h0] at this; rw [List.head?_eq_getElem?]; exact this)
      obtain ⟨a, ha⟩ : ∃ a, c[c.idxOf i - 1]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by have := List.idxOf_lt_length_of_mem hic; omega)⟩
      have hai : c[c.idxOf i - 1 + 1]? = some i := by
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0), List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hic),
          List.getElem_idxOf]
      obtain ⟨⟨ham, y', hy'B, -⟩, y, hya, hNy⟩ := hchain _ a i ha hai
      have hBa := hI.unmarked a (hcA a (List.mem_of_getElem? ha)) ham
      rw [hya] at hBa
      simp only [Option.toList_some] at hBa
      have hyb : s.base y = some a := (mem_baseOf.mp (by rw [hBa]; simp : y ∈ baseOf goods s.base a)).2
      have hyg : y ∈ goods := (mem_baseOf.mp (by rw [hBa]; simp : y ∈ baseOf goods s.base a)).1
      -- `a` is not the last agent (it has a successor), so `y` is not in `O`
      have hal : a ≠ last := by
        intro e; subst e
        have h1 := idxOf_of_getElem? hc ha
        have h2 : c.idxOf a = c.length - 1 := by
          rw [List.getLast?_eq_getElem?] at hlast
          exact idxOf_of_getElem? hc hlast
        have := List.idxOf_lt_length_of_mem hic
        omega
      have hyO : y ∉ O := fun hm' => by
        rcases (hO y hm').2.2 with h | h <;> rw [hyb] at h <;> simp at h; exact hal h
      simp only [rotate, hic, hi0, ↓reduceIte, ha, Option.bind_some, hya, Option.toList_some]
      refine filter_eq_single hgd hyg fun g hg => ?_
      simp only [decide_eq_true_eq]
      constructor
      · intro hg'
        by_cases hgO : g ∈ O
        · simp only [hgO, ↓reduceIte] at hg'; exact absurd hg' (Ne.symm hik ∘ Eq.symm)
        · simp only [hgO, ↓reduceIte] at hg'
          cases hgb : s.base g with
          | none => rw [hgb] at hg'; cases hg'
          | some b =>
            rw [hgb] at hg'
            by_cases hbc : b ∈ c
            · simp only [hbc, ↓reduceIte] at hg'
              have := idxOf_of_getElem? hc hg'
              have hb : b = a := by
                have hb1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hbc)
                have : c.idxOf b = c.idxOf i - 1 := by omega
                rw [← hb1] at ⊢
                exact Option.some.inj (by rw [← ha, ← this, List.getElem?_eq_getElem]) 
              subst hb
              have : g ∈ baseOf goods s.base b := mem_baseOf.mpr ⟨hg, hgb⟩
              rw [hBa] at this; simpa using this
            · simp only [hbc, ↓reduceIte] at hg'; cases hg'; exact absurd hi (fun _ => hbc hic)
      · intro e; subst e
        simp only [hyO, ↓reduceIte, hyb, show a ∈ c from List.mem_of_getElem? ha]
        rw [idxOf_of_getElem? hc ha]; exact hai
    · -- outside the chain: the base is unchanged
      have hm' : ¬ s.marked i := fun h => hm (Or.inr ⟨h, hic⟩)
      simp only [rotate, hic, ↓reduceIte]
      rw [← hI.unmarked i hi hm']
      apply List.filter_congr
      intro g _
      simp only [decide_eq_decide]
      by_cases hgO : g ∈ O
      · simp only [hgO, ↓reduceIte]
        constructor
        · intro h; rw [hk] at h; cases h; exact absurd hkc hic
        · intro h
          rcases (hO g hgO).2.2 with h' | h' <;> rw [h] at h' <;> simp at h'; subst h'; exact absurd hlc hic
      · simp only [hgO, ↓reduceIte]
        cases hgb : s.base g with
        | none => simp
        | some b =>
          by_cases hbc : b ∈ c
          · simp only [hbc, ↓reduceIte]
            constructor
            · intro h; exact absurd (List.mem_of_getElem? h) hic
            · intro h; cases h; exact absurd hbc hic
          · simp [hbc]
  · -- the pick of `i` after the rotation is a good it values
    by_cases hic : i ∈ c
    · have hi0 : c.idxOf i ≠ 0 := fun h0 => hik (by
        have := getElem?_idxOf hic; rw [h0] at this; rw [List.head?_eq_getElem?]; exact this)
      simp only [rotate, hic, hi0, ↓reduceIte] at hy
      cases ha : c[c.idxOf i - 1]? with
      | none => rw [ha] at hy; cases hy
      | some a =>
        rw [ha] at hy
        have hai : c[c.idxOf i - 1 + 1]? = some i := by
          rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0), List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hic),
            List.getElem_idxOf]
        obtain ⟨-, y', hya, hN⟩ := hchain _ a i ha hai
        simp only [Option.bind_some, hya] at hy; cases hy
        rcases hN with ⟨-, -, -, hlt⟩ | ⟨-, -, hpos, -⟩ <;> omega
    · simp only [rotate, hic, ↓reduceIte] at hy
      exact hI.pickRel i hi (fun h => hm (Or.inr ⟨h, hic⟩)) y hy

theorem rotReach_inv {d : Nat} {s s' : LState A G} (hgd : goods.Nodup) (hR : RotReach v agents goods d s s')
    (hI : Inv v agents goods s) : Inv v agents goods s' := by
  induction hR with
  | refl => exact hI
  | step d s s' s'' hstep _ ih => exact ih (rotStep_inv hgd hI hstep)

end rotations

/-- **A base of three or more goods is the owner's** in every output (a completion gives every other agent at most
two goods), and every other bundle has at most two goods. -/
theorem output_big_base {v : A → G → Nat} {agents : List A} {goods : List G} {s : LState A G} {o : Option A}
    {X : G → A} (hgd : goods.Nodup) (hO : Output v agents goods s o X) :
    (∀ i ∈ agents, 3 ≤ (baseOf goods s.base i).length → o = some i) ∧
      ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  have hlen := hO.1.length_le_two hgd
  refine ⟨fun i hi h3 => Classical.byContradiction fun hio => ?_, hlen⟩
  have h2 := hlen i hi hio
  have hsub : (baseOf goods s.base i).length ≤ (bundle goods X i).length := by
    have := hO.1.length_eq i
    omega
  omega

/-- (V1) and (V2) after a rotation: they are among the checks a rotation must pass (§5), so they hold in every
state a rotation reaches; (V2) holds for every marked agent, even with a one-good base. -/
theorem rotStep_valid {v : A → G → Nat} {agents : List A} {goods : List G} {s s' : LState A G}
    (hR : RotStep v agents goods s s') :
    Valid agents goods s'.base (needsOf v goods s') ∧
      ∀ i ∈ agents, s'.marked i → ∀ g ∈ baseOf goods s'.base i, ¬ NA agents (needsOf v goods s') g := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hchk⟩ := hR
  exact ⟨hchk.1, hchk.2.1⟩

/-! ## Theorem C₄ ⟹ K4.D ⟹ TARGET₄ -/

/-- **Every output of LB₄ʳ is sound.** If LB₄ʳ(τ) succeeds, some sound completion exists: an EFX₀ allocation with
at most one bundle of more than two goods (Theorem 1′₄ and the shape, `EFX.LB4.SoundCompletion.efx0_d2`). -/
theorem sound_of_succeeds {v : A → G → Nat} {agents : List A} {goods : List G} {τ : List Nat}
    (hag : agents.Nodup) (hgd : goods.Nodup) (h : Succeeds v agents goods τ) :
    ∃ (base : G → Option A) (N : A → G → Prop) (o : Option A) (X : G → A),
      SoundCompletion v agents goods base N o X := by
  obtain ⟨pol, s₁, s, o, X, hup, hrot, hout⟩ := h
  have hinv := rotReach_inv hgd hrot (upRun_inv hup (phase1State_inv (τ := τ) hag hgd))
  exact ⟨s.base, needsOf v goods s, o, X, hinv.sound hout⟩

/-- **Theorem C₄∃** (route-agnostic): every strict profile of every k = 4 core has a valid pre-allocation (bases of
any size, needs in the Definition's sense for the agents other than the owner) with a completion satisfying (OC₄),
the owner's needs taken from its bundle (`EFX.LB4.SoundCompletion`: frozen agents hold exactly their base, and only the
owner's bundle may have more than two goods). A witness with the owner's needs from its base is one too
(`EFX.LB4.SoundCompletion.of_baseNeeds`). -/
def TheoremC4exists (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods →
      ∃ (base : G → Option A) (N : A → G → Prop) (o : Option A) (X : G → A),
        SoundCompletion v agents goods base N o X

/-- **C₄ (LB₄ʳ, index order) ⟹ C₄∃**: every output of LB₄ʳ is a sound completion. -/
theorem C4exists_of_C4index (h : TheoremC4index A G) : TheoremC4exists A G :=
  fun agents goods v hag hgd hc hs => sound_of_succeeds hag hgd (h agents goods v hag hgd hc hs)

/-- **C₄ (LB₄ʳ) ⟹ C₄∃.** -/
theorem C4exists_of_C4 (h : TheoremC4 A G) : TheoremC4exists A G :=
  C4exists_of_C4index (theoremC4index_of_C4 h)

/-- **C₄∃ ⟹ K4.D.** Every k = 4 core (strict or not) has an EFX₀ allocation with at most one bundle of more than
two goods: a strict core directly (Theorem 1′₄ and the shape, `EFX.LB4.SoundCompletion.efx0_d2`), a core with ties
through its strict perturbation (K4.TIE, `EFX.tieBreak`), whose allocation is EFX₀ for the original values. -/
theorem k4D_of_C4exists (hC4 : TheoremC4exists A G) {agents : List A} {goods : List G} {v : A → G → Nat}
    (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ w ∈ agents, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 := by
  have hne : agents ≠ [] := fun h => by have := hc.1; rw [h] at this; simp at this
  obtain ⟨base, N, o, X, hS⟩ :=
    hC4 agents goods (tieBreak v goods) hag hgd (isCore4_tieBreak v goods hgd hc) (strict_tieBreak v goods hgd)
  obtain ⟨hX, hE, hd2⟩ := hS.efx0_d2 hgd hne
  exact ⟨X, hX, efx0_of_tieBreak v goods hgd hE, hd2⟩

/-- **C₄∃ ⟹ TARGET₄.** With K4.CORE and K4.TIE (`EFX.LB4.target4_of_completions`): every instance with at least one
agent and at most four relevant goods per agent has an EFX₀ allocation. C₄∃ is a hypothesis, not an axiom. -/
theorem target4_of_C4exists (I : Inst) (hn : 0 < I.n) (hC4 : TheoremC4exists (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_completions I hn I.n (Nat.le_refl _)
    (fun w agents goods hag hgd _ hc _ hs _ => hC4 agents goods w hag hgd hc hs) h

/-- **C₄ (LB₄ʳ, index order) ⟹ K4.D.** -/
theorem k4D_of_C4index (hC4 : TheoremC4index A G) {agents : List A} {goods : List G} {v : A → G → Nat}
    (hag : agents.Nodup) (hgd : goods.Nodup) (hc : IsCore4 v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ w ∈ agents, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 :=
  k4D_of_C4exists (C4exists_of_C4index hC4) hag hgd hc

/-- **C₄ (LB₄ʳ, index order) ⟹ TARGET₄**: `target4_of_C4exists` after `C4exists_of_C4index`. -/
theorem target4_of_C4index (I : Inst) (hn : 0 < I.n) (hC4 : TheoremC4index (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4exists I hn (C4exists_of_C4index hC4) h

/-- **Theorem C₄ (LB₄ʳ) ⟹ TARGET₄** (every insertion sequence; the index order suffices). -/
theorem target4_of_C4 (I : Inst) (hn : 0 < I.n) (hC4 : TheoremC4 (Fin I.n) (Fin I.m))
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4index I hn (theoremC4index_of_C4 hC4) h

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.theoremC4index_of_C4
#print axioms EFX.LB4R.phase1State_inv
#print axioms EFX.LB4R.Inv.sound
#print axioms EFX.LB4R.upgrade_inv
#print axioms EFX.LB4R.rotStep_inv
#print axioms EFX.LB4R.sound_of_succeeds
#print axioms EFX.LB4R.k4D_of_C4index
#print axioms EFX.LB4R.target4_of_C4index
#print axioms EFX.LB4R.target4_of_C4
#print axioms EFX.LB4R.output_big_base
#print axioms EFX.LB4R.rotStep_valid
#print axioms EFX.LB4R.C4exists_of_C4index
#print axioms EFX.LB4R.C4exists_of_C4
#print axioms EFX.LB4R.k4D_of_C4exists
#print axioms EFX.LB4R.target4_of_C4exists
