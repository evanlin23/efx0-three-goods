import EFX.DE4

/-!
# DE4ᵛ³: DE4 with the lower pair only while b is held (`k4/de4.md` §8; ledger K4.DE4V3)

**Definitions.**
- `V3` (**(V3)**): every listed agent holding its lower pair has every relevant good worth less than its top (its b,
  on a strict profile) held by some agent.
- `ValidV3`, `IsMaximumV3`: (V1), (V2) and (V3); a maximum of the order of `k4/de4.md` §1 among those states.
- `ConjDE4V3` (**Conjecture DE4ᵛ³**, a hypothesis, never an axiom): every such maximum is completable.

**Results.**
- `draft_v3`: the draft satisfies (V3) (it holds single goods only); `exists_maximumV3`: maxima exist.
- `target4_of_conjDE4V3`: Conjecture DE4ᵛ³ implies TARGET₄ (with K4.CORE and K4.TIE, as in Lemma 3).

**Faithfulness.** On a strict profile a 4-good agent's relevant goods outside its lower pair are its a and its b, and
only b is worth less than the top, so (V3) says exactly "its b is held"; `k4/de4/de4v.c` and `k4/de4/ss_screen.py`
test the same rule.
-/

set_option autoImplicit false

namespace EFX
namespace DE4

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- (V3): a holder of its lower pair has its b held. -/
def V3 (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ∀ i ∈ agents, IsLowerPair v i goods (hold goods base i) →
    ∀ g ∈ relevant v i goods, g ∉ hold goods base i → v i g < topV v i goods → base g ≠ none

/-- A valid state that satisfies (V3). -/
def ValidV3 (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  Valid v agents goods base ∧ V3 v agents goods base

/-- A maximum among the states satisfying (V1), (V2) and (V3). -/
def IsMaximumV3 (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A) : Prop :=
  ValidV3 v agents goods base ∧ ∀ base', ValidV3 v agents goods base' → ¬ Better v agents goods base' base

/-- **Conjecture DE4ᵛ³** (`k4/de4.md` §8): on every strict R1-core with at most four relevant goods per agent, every
maximum of the (V3)-valid states is completable. A hypothesis, never an axiom. -/
def ConjDE4V3 (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ∀ (v : A → G → Nat) (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
    R1Core4 v agents goods → Strict v agents goods →
    ∀ base, IsMaximumV3 v agents goods base → Completable v agents goods base

section v3
variable (v : A → G → Nat) {agents : List A} {goods : List G}

/-- The draft satisfies (V3): its holdings are single goods, never a lower pair. -/
theorem draft_v3 (hag : agents.Nodup) (hgd : goods.Nodup) : V3 v agents goods (draft v goods agents) := by
  intro i _ hlp
  have h1 := draft_hold_length (v := v) hag hgd i
  have h2 := hlp.2.1
  omega

/-- From any (V3)-valid state, descent along `Better` reaches a maximum of the (V3)-valid states. -/
theorem exists_maximumV3_of_valid {base : G → Option A} (hb : ValidV3 v agents goods base) :
    ∃ m, IsMaximumV3 v agents goods m := by
  let M := 5 * agents.length * (bigV v agents goods + 1) + bigV v agents goods
  suffices key : ∀ k, ∀ b, ValidV3 v agents goods b → M - measure v agents goods b ≤ k →
      ∃ m, IsMaximumV3 v agents goods m from key _ base hb (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro b hb hk
    refine ⟨b, hb, fun b' _ hbet => ?_⟩
    have := measure_lt_of_better v agents goods hbet
    have := measure_le v agents goods b'
    omega
  | succ k ih =>
    intro b hb hk
    by_cases hmax : ∀ b', ValidV3 v agents goods b' → ¬ Better v agents goods b' b
    · exact ⟨b, hb, hmax⟩
    · obtain ⟨b', hb'⟩ := Classical.not_forall.mp hmax
      have hv' : ValidV3 v agents goods b' := Classical.byContradiction fun hn => hb' fun h => absurd h hn
      have hbet : Better v agents goods b' b := Classical.byContradiction fun hn => hb' fun _ => hn
      have := measure_lt_of_better v agents goods hbet
      have := measure_le v agents goods b'
      exact ih b' hv' (by omega)

/-- Every instance has a maximum of the (V3)-valid states. -/
theorem exists_maximumV3 (hag : agents.Nodup) (hgd : goods.Nodup) : ∃ base, IsMaximumV3 v agents goods base :=
  exists_maximumV3_of_valid v ⟨draft_valid hag hgd, draft_v3 v hag hgd⟩

end v3

/-- Conjecture DE4ᵛ³ gives an EFX₀ allocation of every strict R1-core with at most four relevant goods per agent. -/
theorem exists_efx0_of_conjDE4V3 (h : ConjDE4V3 A G) (v : A → G → Nat) {agents : List A} {goods : List G}
    (hne : agents ≠ []) (hag : agents.Nodup) (hgd : goods.Nodup) (hc : R1Core4 v agents goods)
    (hs : Strict v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨base, hmax⟩ := exists_maximumV3 v hag hgd
  obtain ⟨X, hX, -, hE⟩ := h v agents goods hne hag hgd hc hs base hmax
  exact ⟨X, hX, hE⟩

/-- **Conjecture DE4ᵛ³ implies TARGET₄** (with K4.CORE and K4.TIE, as in Lemma 3). -/
theorem target4_of_conjDE4V3 (I : Inst) (hn : 0 < I.n) (h : ConjDE4V3 (Fin I.n) (Fin I.m))
    (h4 : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _)
    (fun w agents _ hag hgd _ hcore _ hs _ =>
      exists_efx0_of_conjDE4V3 h w (fun he => by have := hcore.1; rw [he] at this; simp at this) hag hgd
        (fun i hi => ⟨(hcore.2.1 i hi).1, (hcore.2.1 i hi).2, hcore.2.2.1 i hi⟩) hs) h4

end DE4
end EFX

#print axioms EFX.DE4.draft_v3
#print axioms EFX.DE4.exists_maximumV3
#print axioms EFX.DE4.exists_efx0_of_conjDE4V3
#print axioms EFX.DE4.target4_of_conjDE4V3
