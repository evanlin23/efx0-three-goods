import EFX.K4One

/-!
# Rule F's target statement (`k4/rulef.md` §7; ledger K4.RF.LEAN)

Rule F (`k4/adaptive.md` §1, ledger K4.AD.F) runs LB₄ʳ with the insertion sequence "a first, then index order" for
some agent `a`. In `lean/EFX/LB4R.lean` that sequence is the list `[a]` (choice 2 of its module doc: the first insertion
step takes the `a`-th unprocessed agent in index order, and every later step the first one, since `τ` is used up). This
file states what a proof of rule F (or of any explicit first-agent rule, `k4/rulef.md` §4) has to deliver, and proves
that it gives C₄∃, hence K4.D and TARGET₄:

- `SucceedsR d`: LB₄ʳ(τ) succeeds with at most `d` rotations (`Succeeds` is the case `d = 3`,
  `succeeds_iff_succeedsR3`), and `succeeds_of_succeedsR`: at most `d ≤ 3` rotations is a success of `Succeeds`
  (`rotReach_mono`);
- `TheoremRuleF`: every strict profile of every k = 4 core has a first agent `a` with `SucceedsR 1 … [a]` (rule F with
  at most one rotation succeeds); `RuleFConn`: the same for connected cores with a 4-good agent; `RuleFOne`: for
  connected cores with at most one 4-good agent;
- `C4exists_of_ruleF`, `C4existsConn_of_ruleFConn`, `C4existsOne_of_ruleFOne`, and the corollaries
  `target4_of_ruleF`, `target4_of_ruleFConn` (TARGET₄), `target4one_of_ruleFOne` (TARGET₄ with at most one 4-good
  agent), through `EFX.LB4R.sound_of_succeeds` (K4.C4.FRAME) and K4.ONE.FRAME.

`TheoremRuleF`, `RuleFConn` and `RuleFOne` are hypotheses of these theorems, not axioms, and all three are open
(K4.AD.F, CONJECTURE). An explicit rule (a function choosing `a` from the profile) is a witness for the `∃ a`; the
statement does not depend on how `a` is found.
-/

set_option autoImplicit false

namespace EFX
namespace LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- **LB₄ʳ(τ) succeeds with at most `d` rotations**: for some upgrade policy, the run of upgrades from Phase 1(τ)
followed by at most `d` rotations reaches a state with an output. `Succeeds` is `SucceedsR 3`. -/
def SucceedsR (d : Nat) (v : A → G → Nat) (agents : List A) (goods : List G) (τ : List Nat) : Prop :=
  ∃ (pol : Policy) (s₁ s : LState A G) (o : Option A) (X : G → A),
    UpRun v agents goods pol (phase1State v agents goods τ) s₁ ∧ RotReach v agents goods d s₁ s ∧
    Output v agents goods s o X

/-- States reachable with at most `d` rotations are reachable with at most `e ≥ d`. -/
theorem rotReach_mono {v : A → G → Nat} {agents : List A} {goods : List G} {d : Nat} {s s' : LState A G}
    (h : RotReach v agents goods d s s') : ∀ {e : Nat}, d ≤ e → RotReach v agents goods e s s' := by
  induction h with
  | refl d s => intro e _; exact .refl e s
  | step d s s' s'' hs _ ih =>
    intro e hde
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact .step e' s s' s'' hs (ih (by omega))

/-- A success with at most `d ≤ 3` rotations is a success of LB₄ʳ (`Succeeds`). -/
theorem succeeds_of_succeedsR {v : A → G → Nat} {agents : List A} {goods : List G} {d : Nat} {τ : List Nat}
    (hd : d ≤ 3) (h : SucceedsR d v agents goods τ) : Succeeds v agents goods τ := by
  obtain ⟨pol, s₁, s, o, X, hup, hrot, hout⟩ := h
  exact ⟨pol, s₁, s, o, X, hup, rotReach_mono hrot hd, hout⟩

/-- `Succeeds` is `SucceedsR 3` (the same proposition, by unfolding). -/
theorem succeeds_iff_succeedsR3 {v : A → G → Nat} {agents : List A} {goods : List G} {τ : List Nat} :
    Succeeds v agents goods τ ↔ SucceedsR 3 v agents goods τ :=
  Iff.rfl

/-- **Rule F's target** (`k4/rulef.md` §7): for every strict profile of every k = 4 core some agent `a` makes
LB₄ʳ([a]) (`a` first, then index order) succeed with at most one rotation. Open (K4.AD.F). -/
def TheoremRuleF (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Strict v agents goods → ∃ a, a < agents.length ∧ SucceedsR 1 v agents goods [a]

/-- Rule F's target on connected cores with a 4-good agent, the cores TARGET₄ needs (`C4existsConn`). -/
def RuleFConn (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup →
    IsCore4 v agents goods → Connected v agents goods → Strict v agents goods →
    (∃ i ∈ agents, (relevant v i goods).length = 4) → ∃ a, a < agents.length ∧ SucceedsR 1 v agents goods [a]

/-- Rule F's target on connected cores with at most one 4-good agent (the cores of `C4existsOne`). -/
def RuleFOne (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup →
    IsCore4 v agents goods → Connected v agents goods → Strict v agents goods → AtMostOne4 v agents goods →
    ∃ a, a < agents.length ∧ SucceedsR 1 v agents goods [a]

/-- **Rule F ⟹ C₄∃**: LB₄ʳ's output is a sound completion (`sound_of_succeeds`). -/
theorem C4exists_of_ruleF (h : TheoremRuleF A G) : TheoremC4exists A G :=
  fun agents goods v hag hgd hc hs => by
    obtain ⟨a, -, ha⟩ := h agents goods v hag hgd hc hs
    exact sound_of_succeeds hag hgd (succeeds_of_succeedsR (by omega) ha)

/-- **Rule F on connected cores with a 4-good agent ⟹ `C4existsConn`.** -/
theorem C4existsConn_of_ruleFConn (h : RuleFConn A G) : C4existsConn A G :=
  fun agents goods v hag hgd hc hconn hs h4 => by
    obtain ⟨a, -, ha⟩ := h agents goods v hag hgd hc hconn hs h4
    exact sound_of_succeeds hag hgd (succeeds_of_succeedsR (by omega) ha)

/-- **Rule F with at most one 4-good agent ⟹ `C4existsOne`.** -/
theorem C4existsOne_of_ruleFOne (h : RuleFOne A G) : C4existsOne A G :=
  fun agents goods v hag hgd hc hconn hs h1 => by
    obtain ⟨a, -, ha⟩ := h agents goods v hag hgd hc hconn hs h1
    exact sound_of_succeeds hag hgd (succeeds_of_succeedsR (by omega) ha)

/-- **Rule F ⟹ TARGET₄**: every instance with at least one agent and at most four relevant goods per agent has an
EFX₀ allocation. `TheoremRuleF` is a hypothesis, not an axiom. -/
theorem target4_of_ruleF (I : Inst) (hn : 0 < I.n) (h : TheoremRuleF (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4exists I hn (C4exists_of_ruleF h) h4

/-- **Rule F on connected cores with a 4-good agent ⟹ TARGET₄.** -/
theorem target4_of_ruleFConn (I : Inst) (hn : 0 < I.n) (h : RuleFConn (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4existsConn I hn (C4existsConn_of_ruleFConn h) h4

/-- **Rule F with at most one 4-good agent ⟹ TARGET₄ for instances with at most one 4-good agent.** -/
theorem target4one_of_ruleFOne (I : Inst) (hn : 0 < I.n) (h : RuleFOne (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) (h1 : ∀ i j, numRelevant I i = 4 → numRelevant I j = 4 → i = j) :
    ∃ X : I.Alloc, I.EFX0 X :=
  target4one_of_C4existsOne I hn (C4existsOne_of_ruleFOne h) h4 h1

end LB4R
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4R.rotReach_mono
#print axioms EFX.LB4R.succeeds_of_succeedsR
#print axioms EFX.LB4R.succeeds_iff_succeedsR3
#print axioms EFX.LB4R.C4exists_of_ruleF
#print axioms EFX.LB4R.C4existsConn_of_ruleFConn
#print axioms EFX.LB4R.C4existsOne_of_ruleFOne
#print axioms EFX.LB4R.target4_of_ruleF
#print axioms EFX.LB4R.target4_of_ruleFConn
#print axioms EFX.LB4R.target4one_of_ruleFOne
