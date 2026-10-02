import EFX.RuleF

/-!
# Adaptive Lemma M's target statement (`k4/lemmam_x.md` §7.2, §7.4; ledger K4.LMX.AD.LEAN)

Lemma M (`k4/rulef.md`, ledger K4.RF.M) chooses only the first agent of LB₄ʳ's insertion sequence; it is false if
Proposition HH of `k4/lemmam_bt.md` §3 (PR #83) holds. The repair of `k4/lemmam_x.md` §7 chooses the inserted agent
at every insertion step. In `lean/EFX/LB4R.lean` any insertion sequence is a list `τ` (choice 2 of its module doc:
the j-th insertion step takes the `(τ_j mod u)`-th unprocessed agent in index order), so the repaired target is

- `TheoremAdaptive` (M_ad): every strict profile of every k = 4 core has an insertion sequence `τ` with
  `SucceedsR 1 … τ` (LB₄ʳ(τ) succeeds with at most one rotation);
- `C4exists_of_adaptive`: M_ad gives C₄∃ (hence K4.D) through `EFX.LB4R.sound_of_succeeds` and
  `EFX.LB4R.succeeds_of_succeedsR`, as `C4exists_of_ruleF` does;
- `adaptive_of_ruleF`: rule F's target is the special case `τ = [a]`;
- `target4_of_adaptive`: M_ad gives TARGET₄.

`TheoremAdaptive` is a hypothesis of these theorems, not an axiom, and open (K4.LMX.AD). The text was compiled first
by the PR #77 referee.
-/

set_option autoImplicit false

namespace EFX
namespace LB4R

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- Adaptive Lemma M's target (`k4/lemmam_x.md` §7.2): for every strict profile of every k = 4 core some insertion
sequence `τ` makes LB₄ʳ(τ) succeed with at most one rotation. Open (K4.LMX.AD). -/
def TheoremAdaptive (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup →
    IsCore4 v agents goods → Strict v agents goods → ∃ τ : List Nat, SucceedsR 1 v agents goods τ

/-- **M_ad ⟹ C₄∃**: LB₄ʳ's output is a sound completion (`sound_of_succeeds`). -/
theorem C4exists_of_adaptive (h : TheoremAdaptive A G) : TheoremC4exists A G :=
  fun agents goods v hag hgd hc hs => by
    obtain ⟨τ, hτ⟩ := h agents goods v hag hgd hc hs
    exact sound_of_succeeds hag hgd (succeeds_of_succeedsR (by omega) hτ)

/-- **Rule F ⟹ M_ad**: rule F's target is the case `τ = [a]`. -/
theorem adaptive_of_ruleF (h : TheoremRuleF A G) : TheoremAdaptive A G :=
  fun agents goods v hag hgd hc hs => by
    obtain ⟨a, -, ha⟩ := h agents goods v hag hgd hc hs
    exact ⟨[a], ha⟩

/-- **M_ad ⟹ TARGET₄**: every instance with at least one agent and at most four relevant goods per agent has an EFX₀
allocation. `TheoremAdaptive` is a hypothesis, not an axiom. -/
theorem target4_of_adaptive (I : Inst) (hn : 0 < I.n) (h : TheoremAdaptive (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_C4exists I hn (C4exists_of_adaptive h) h4

end LB4R
end EFX

#print axioms EFX.LB4R.C4exists_of_adaptive
#print axioms EFX.LB4R.adaptive_of_ruleF
#print axioms EFX.LB4R.target4_of_adaptive
