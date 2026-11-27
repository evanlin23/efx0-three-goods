import EFX.OC1Perf

/-!
# Variants of OC₁^max after its refutation (`k4/sdc.md` §31)

OC₁^max is false at k = 4 (ledger K4.SDC.OC1MAX; `EFX/OC1MaxCex.lean`). The frames of `EFX/OC1Max.lean` and
`EFX/OC1Perf.lean` are implications parametrized by the move relation, so they carry over to the candidates that
survive (`k4/sdc.md` §31, "What survives"):

- `movesUpTo Move k`: at most `k` sequential moves (`movesUpTo Move 0` is "no move").
- **OC_k^max** (`ConjOCkmax k`: from every maximum-matching start of every strict connected k = 4 core, at most `k`
  sequential improving moves reach bases with a one-absorber completion) and **OC₂^max** (`ConjOC2max`, k = 2);
  `target4_of_conjOCkmax`, **`target4_of_conjOC2max`**.
- The perfect-start forms (`ConjOCkperf`, `ConjOC2perf`) over all strict instances; `target4_of_conjOCkperf`,
  **`target4_of_conjOC2perf`**.
- **The ∃-order form** (`ConjOC1exmaxWith`, `ConjOC1exmax`): every strict connected k = 4 core has *some* order whose
  picks form a maximum matching and satisfy OC₁. `conjOC1exmaxWith_of_conjOC1maxWith` (the every-order form implies
  it, by MAXSD) and **`target4_of_conjOC1exmax`**.
- Monotonicity: `conjOC1maxWith_mono`, `movesUpTo_mono`, `conjOCkmax_of_conjOC1max` (OC₁^max ⟹ OC_k^max for k ≥ 1).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Several moves -/

/-- At most `k` sequential moves of `Move`. -/
def movesUpTo (Move : MoveRel A G) : Nat → MoveRel A G
  | 0 => fun _ _ _ B B' => B' = B
  | k + 1 => fun v agents goods B B'' =>
      B'' = B ∨ ∃ B', Move v agents goods B B' ∧ movesUpTo Move k v agents goods B' B''

omit [DecidableEq A] [DecidableEq G] in
/-- One move is at most one move. -/
theorem movesUpTo_one {Move : MoveRel A G} {v : A → G → Nat} {agents : List A} {goods : List G}
    {B B' : A → List G} (h : Move v agents goods B B') : movesUpTo Move 1 v agents goods B B' :=
  Or.inr ⟨B', h, rfl⟩

omit [DecidableEq A] [DecidableEq G] in
/-- At most `k` moves are at most `k + 1` moves. -/
theorem movesUpTo_succ {Move : MoveRel A G} : ∀ (k : Nat) {v : A → G → Nat} {agents : List A} {goods : List G}
    {B B' : A → List G}, movesUpTo Move k v agents goods B B' → movesUpTo Move (k + 1) v agents goods B B'
  | 0, _, _, _, _, _, h => Or.inl h
  | k + 1, _, _, _, _, _, h => by
    rcases h with h | ⟨B₁, hm, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨B₁, hm, movesUpTo_succ k hr⟩

omit [DecidableEq A] [DecidableEq G] in
theorem movesUpTo_mono {Move : MoveRel A G} {k l : Nat} (hkl : k ≤ l) {v : A → G → Nat} {agents : List A}
    {goods : List G} {B B' : A → List G} (h : movesUpTo Move k v agents goods B B') :
    movesUpTo Move l v agents goods B B' := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact movesUpTo_succ _ ih

/-- A weaker move relation gives a weaker conjecture. -/
theorem conjOC1maxWith_mono {M M' : MoveRel A G}
    (hM : ∀ v agents goods B B', M v agents goods B B' → M' v agents goods B B') (h : ConjOC1maxWith A G M) :
    ConjOC1maxWith A G M' := by
  intro agents goods v hag hgd hc hconn hs ord hperm hmax
  rcases h agents goods v hag hgd hc hconn hs ord hperm hmax with h0 | ⟨B', hm, hB'⟩
  · exact Or.inl h0
  · exact Or.inr ⟨B', hM _ _ _ _ _ hm, hB'⟩

theorem conjOC1perfWith_mono {M M' : MoveRel A G}
    (hM : ∀ v agents goods B B', M v agents goods B B' → M' v agents goods B B') (h : ConjOC1perfWith A G M) :
    ConjOC1perfWith A G M' := by
  intro agents goods v hne hag hgd h4 hs ord hperm hperf
  rcases h agents goods v hne hag hgd h4 hs ord hperm hperf with h0 | ⟨B', hm, hB'⟩
  · exact Or.inl h0
  · exact Or.inr ⟨B', hM _ _ _ _ _ hm, hB'⟩

/-- **Conjecture OC_k^max**: from every maximum-matching start of every strict connected k = 4 core, at most `k`
sequential improving moves (additions, chains, rings) reach bases with a one-absorber completion. A `Prop`. -/
def ConjOCkmax (A G : Type) [DecidableEq A] [DecidableEq G] (k : Nat) : Prop :=
  ConjOC1maxWith A G (movesUpTo (fun v agents goods => OneMove v agents goods) k)

/-- **Conjecture OC₂^max** (`k4/sdc.md` §31): at most two sequential moves. -/
def ConjOC2max (A G : Type) [DecidableEq A] [DecidableEq G] : Prop := ConjOCkmax A G 2

/-- OC₁^max is OC_k^max with `k = 1`, and it implies OC_k^max for every `k ≥ 1`. -/
theorem conjOCkmax_of_conjOC1max {k : Nat} (hk : 1 ≤ k) (h : ConjOC1max A G) : ConjOCkmax A G k :=
  conjOC1maxWith_mono (fun _ _ _ _ _ hm => movesUpTo_mono hk (movesUpTo_one hm)) h

/-- **OC_k^max ⟹ TARGET₄.** -/
theorem target4_of_conjOCkmax (I : Inst) (hn : 0 < I.n) {k : Nat} (h : ConjOCkmax (Fin I.n) (Fin I.m) k)
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1maxWith I hn h hk

/-- **OC₂^max ⟹ TARGET₄.** -/
theorem target4_of_conjOC2max (I : Inst) (hn : 0 < I.n) (h : ConjOC2max (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOCkmax I hn h hk

/-- **OC_k at perfect starts**, over all strict instances with at most four relevant goods per agent. A `Prop`. -/
def ConjOCkperf (A G : Type) [DecidableEq A] [DecidableEq G] (k : Nat) : Prop :=
  ConjOC1perfWith A G (movesUpTo (fun v agents goods => OneMove v agents goods) k)

/-- **OC₂ at perfect starts.** -/
def ConjOC2perf (A G : Type) [DecidableEq A] [DecidableEq G] : Prop := ConjOCkperf A G 2

/-- OC₁ᵖᵉʳᶠ implies OC_kᵖᵉʳᶠ for every `k ≥ 1`. -/
theorem conjOCkperf_of_conjOC1perf {k : Nat} (hk : 1 ≤ k) (h : ConjOC1perf A G) : ConjOCkperf A G k :=
  conjOC1perfWith_mono (fun _ _ _ _ _ hm => movesUpTo_mono hk (movesUpTo_one hm)) h

/-- **OC_kᵖᵉʳᶠ ⟹ TARGET₄**, without the core reduction (Lemma RED). -/
theorem target4_of_conjOCkperf (I : Inst) (hn : 0 < I.n) {k : Nat} (h : ConjOCkperf (Fin I.n) (Fin I.m) k)
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1perfWith I hn h hk

/-- **OC₂ᵖᵉʳᶠ ⟹ TARGET₄.** -/
theorem target4_of_conjOC2perf (I : Inst) (hn : 0 < I.n) (h : ConjOC2perf (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOCkperf I hn h hk

/-! ## Some maximum-matching order -/

/-- **The ∃-order form, for any move relation**: every strict connected k = 4 core has some order of its agents whose
picks form a maximum matching and have a one-absorber completion, at the picks or after one `Move`. A `Prop`. -/
def ConjOC1exmaxWith (A G : Type) [DecidableEq A] [DecidableEq G] (Move : MoveRel A G) : Prop :=
  ∀ (agents : List A) (goods : List G) (v : A → G → Nat), agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → ∃ ord : List A, ord.Perm agents ∧
      IsMaximum v agents goods (sdPick v ord goods) ∧
      (OneAbsorber v agents goods (pickBase v goods ord) ∨
        ∃ B', Move v agents goods (pickBase v goods ord) B' ∧ OneAbsorber v agents goods B')

/-- **Conjecture OC₁^∃max**: some maximum-matching order satisfies OC₁ (one move of `OneMove`). -/
def ConjOC1exmax (A G : Type) [DecidableEq A] [DecidableEq G] : Prop :=
  ConjOC1exmaxWith A G (fun v agents goods => OneMove v agents goods)

/-- The every-order form implies the ∃-order form (MAXSD gives a maximum-matching order). -/
theorem conjOC1exmaxWith_of_conjOC1maxWith {Move : MoveRel A G} (h : ConjOC1maxWith A G Move) :
    ConjOC1exmaxWith A G Move := by
  intro agents goods v hag hgd hc hconn hs
  obtain ⟨ord, hperm, hmax⟩ := exists_order_maximum hag hgd (strictVals_of_strict hs)
  exact ⟨ord, hperm, hmax, h agents goods v hag hgd hc hconn hs ord hperm hmax⟩

/-- **The ∃-order form (any move relation) ⟹ TARGET₄.** -/
theorem target4_of_conjOC1exmaxWith (I : Inst) (hn : 0 < I.n) {Move : MoveRel (Fin I.n) (Fin I.m)}
    (h : ConjOC1exmaxWith (Fin I.n) (Fin I.m) Move) (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn I.n (Nat.le_refl _) (fun _ _ _ hag hgd _ hc hconn hs _ => by
    obtain ⟨_, -, -, h0 | ⟨_, -, hB⟩⟩ := h _ _ _ hag hgd hc hconn hs
    · obtain ⟨X, hX, hE, -⟩ := h0; exact ⟨X, hX, hE⟩
    · obtain ⟨X, hX, hE, -⟩ := hB; exact ⟨X, hX, hE⟩) hk

/-- **Conjecture OC₁^∃max ⟹ TARGET₄.** -/
theorem target4_of_conjOC1exmax (I : Inst) (hn : 0 < I.n) (h : ConjOC1exmax (Fin I.n) (Fin I.m))
    (hk : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_conjOC1exmaxWith I hn h hk

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.movesUpTo_mono
#print axioms EFX.OC1Max.conjOC1maxWith_mono
#print axioms EFX.OC1Max.conjOC1perfWith_mono
#print axioms EFX.OC1Max.conjOCkmax_of_conjOC1max
#print axioms EFX.OC1Max.target4_of_conjOCkmax
#print axioms EFX.OC1Max.target4_of_conjOC2max
#print axioms EFX.OC1Max.conjOCkperf_of_conjOC1perf
#print axioms EFX.OC1Max.target4_of_conjOCkperf
#print axioms EFX.OC1Max.target4_of_conjOC2perf
#print axioms EFX.OC1Max.conjOC1exmaxWith_of_conjOC1maxWith
#print axioms EFX.OC1Max.target4_of_conjOC1exmaxWith
#print axioms EFX.OC1Max.target4_of_conjOC1exmax
