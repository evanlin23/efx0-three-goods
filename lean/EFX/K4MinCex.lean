import EFX.K4Ties
import EFX.Target

/-!
# A minimal counterexample to TARGET₄ (`k4/MINCEX.md`; ledger K4.MC0–K4.MC7)

The minimal-counterexample route of `proofs/min_counterexample.md`, carried to k = 4 in `k4/MINCEX.md`. This
file machine-checks its mathematical steps; the computational facts it rests on (reduction certificates, core
enumerations, core certificates) and the literature (the multigraph theorem) enter as explicit hypotheses.

## K4.MC1: local reductions are sound (Lemmas M1 and M1(b))

`proofs/min_counterexample.md` §2, used verbatim at k = 4 (`k4/MINCEX.md` §2). A configuration `(S, I)` of `H` is
replaced by a gadget `(S′, I′)`; the outside agents `out` belong to both `H` (agents `ag`, goods `gs`) and the
smaller instance `H′` (agents `ag'`, goods `gs'`), and value no good of `I ∪ I′` (`inner`). One value function
`v` serves both instances. For an EFX₀ allocation `Y` of `H′`, an *extension* is an allocation `X` of `H` in which
- every outside agent keeps the goods of its bundle outside `I ∪ I′`, or held only goods of `I′` (`keep`);
- every agent of `H` that is not an outside agent (an agent of `S`) is safe (`safe`);
- every bundle of `X` is dominated by a bundle of `Y` (`dom`), or, for M1(b), its goods outside `I ∪ I′` lie in the
  bundle `Y_z` of an agent `z` that no outside agent envies (a bundle of `X` equal to a bundle of `Y` is dominated by
  it, so this is (ii) of M1).

Here `U(B)` is the part of `B` outside `I ∪ I′` (`uPart`), `B` is *inner* if it meets `I ∪ I′`, and `B` is
*dominated* by `B′` (`Dominated`) if `|B| ≤ 1`, or `U(B) = ∅`, or `U(B) ⊆ U(B′)` and (`B` is not inner, or `B′` is
inner, or `U(B) ≠ U(B′)`).

- `threat_le_of_dominated`: the claim `θ_j(B) ≤ θ_j(B′)` of M1's proof, in the form "every good removal".
- `m1_efx0`: **Lemmas M1 and M1(b)**: an extension of an EFX₀ allocation of `H′` is EFX₀ for `H`.
- `m1_reduce`: as used on a minimal counterexample: if `H′` has an EFX₀ allocation and every EFX₀ allocation of
  `H′` with an unenvied agent (F2, `EFX.exists_unenvied`) has an extension, `H` has an EFX₀ allocation.

What the certificates of K4.MC2, K4.MC3 and K4.MC5 check is the hypothesis of `m1_reduce` through *local
states* (`k4/check_reductions4.py`: every admissible local state has a stored extension); that an extension of the
local state gives an extension of `Y` in the sense above is the construction in M1's proof, not formalized here.
-/

set_option autoImplicit false

namespace EFX
namespace MinCex

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Lemmas on values -/

omit [DecidableEq A] in
/-- A value over a list containing `g` is `v g` plus the value of the rest. -/
theorem value_erase' (v : A → G → Nat) (i : A) {g : G} {S : List G} (h : g ∈ S) :
    value v i S = v i g + value v i (S.erase g) := by
  unfold value
  rw [(List.perm_cons_erase h).map (v i) |>.sum_nat]
  simp

omit [DecidableEq A] in
/-- A list without repeated goods, all of them in `T`, is worth at most `T`. -/
theorem value_le_of_subset (v : A → G → Nat) (i : A) :
    ∀ {S T : List G}, S.Nodup → (∀ x ∈ S, x ∈ T) → value v i S ≤ value v i T
  | [], _, _, _ => by simp
  | x :: S, T, hS, h => by
    obtain ⟨hx, hS'⟩ := List.nodup_cons.mp hS
    have hxT := h x (by simp)
    have ih := value_le_of_subset v i (T := T.erase x) hS' fun y hy =>
      (List.mem_erase_of_ne (fun (e : y = x) => hx (e ▸ hy))).mpr (h y (by simp [hy]))
    rw [value_cons, value_erase' v i hxT]
    omega

/-! ## Domination (`proofs/min_counterexample.md` §2) -/

/-- `U(B)`: the goods of `B` outside `I ∪ I′`. -/
def uPart (inner : G → Bool) (B : List G) : List G := B.filter (fun g => !inner g)

/-- `B` is *dominated* by `B′`: `|B| ≤ 1`, or `U(B) = ∅`, or `U(B) ⊆ U(B′)` and (`B` is not inner, or `B′` is
inner, or `U(B) ≠ U(B′)`). -/
def Dominated (inner : G → Bool) (B B' : List G) : Prop :=
  B.length ≤ 1 ∨ uPart inner B = [] ∨
    ((∀ g ∈ uPart inner B, g ∈ uPart inner B') ∧
      ((∀ g ∈ B, inner g = false) ∨ (∃ w ∈ B', inner w = true) ∨ ∃ h ∈ uPart inner B', h ∉ uPart inner B))

omit [DecidableEq A] [DecidableEq G] in
theorem mem_uPart {inner : G → Bool} {B : List G} {g : G} : g ∈ uPart inner B ↔ g ∈ B ∧ inner g = false := by
  simp [uPart]

omit [DecidableEq A] [DecidableEq G] in
/-- An agent that values no good of `I ∪ I′` values a bundle as its part `U(B)`. -/
theorem value_uPart (v : A → G → Nat) {j : A} {inner : G → Bool} (hj : ∀ g, inner g = true → v j g = 0) :
    ∀ B : List G, value v j (uPart inner B) = value v j B
  | [] => by simp [uPart]
  | g :: B => by
    have ih := value_uPart v hj B
    by_cases hg : inner g = true
    · simp only [uPart, List.filter_cons, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      rw [value_cons, hj g hg, ← ih]; simp
    · simp only [uPart, List.filter_cons, Bool.not_eq_true] at hg ih ⊢
      simp only [hg, Bool.not_false, ↓reduceIte, value_cons]
      rw [ih]

omit [DecidableEq A] in
/-- **The claim of M1's proof.** If an agent `j` that values no good of `I ∪ I′` does not strongly envy `B′`
(with bound `c`), it does not strongly envy a bundle `B` dominated by `B′`. -/
theorem threat_le_of_dominated (v : A → G → Nat) {j : A} {inner : G → Bool}
    (hj : ∀ g, inner g = true → v j g = 0) {B B' : List G} (hB : B.Nodup) {c : Nat}
    (hdom : Dominated inner B B') (hc : ∀ g' ∈ B', value v j (B'.erase g') ≤ c) :
    ∀ g ∈ B, value v j (B.erase g) ≤ c := by
  intro g hg
  have hU : (uPart inner B).Nodup := hB.sublist List.filter_sublist
  have hBe : value v j (B.erase g) ≤ value v j B := value_sublist v j List.erase_sublist
  rcases hdom with h1 | h0 | ⟨hsub, hni | ⟨w, hw, hwi⟩ | ⟨h, hh, hhB⟩⟩
  · have : (B.erase g).length = 0 := by rw [List.length_erase_of_mem hg]; omega
    rw [List.length_eq_zero_iff.mp this]; simp
  · have := value_uPart v hj B
    rw [h0] at this; simp at this; omega
  · -- `B` is not inner: `B = U(B) ⊆ B′`, and removing the same good keeps the inclusion
    have hgB' : g ∈ B' := (mem_uPart.mp (hsub g (mem_uPart.mpr ⟨hg, hni g hg⟩))).1
    refine Nat.le_trans (value_le_of_subset v j (hB.sublist List.erase_sublist) fun x hx => ?_) (hc g hgB')
    have hxB := (List.Nodup.mem_erase_iff hB).mp hx
    exact (List.mem_erase_of_ne hxB.1).mpr (mem_uPart.mp (hsub x (mem_uPart.mpr ⟨hxB.2, hni x hxB.2⟩))).1
  · -- `B′` is inner: removing its worthless good `w` costs `j` nothing
    have h1 := value_uPart v hj B
    have h2 := value_uPart v hj B'
    have h3 := value_le_of_subset v j hU hsub
    have h4 := value_erase' v j hw
    rw [hj w hwi] at h4
    have := hc w hw
    omega
  · -- `U(B) ⊊ U(B′)`: remove from `B′` a good `h` of `U(B′)` outside `U(B)`
    have hhB' := (mem_uPart.mp hh).1
    have h1 := value_uPart v hj B
    have h3 := value_le_of_subset v j hU (T := B'.erase h) fun x hx =>
      (List.mem_erase_of_ne (fun (e : x = h) => hhB (e ▸ hx))).mpr (mem_uPart.mp (hsub x hx)).1
    have := hc h hhB'
    omega

/-! ## Lemmas M1 and M1(b) -/

/-- An *extension* `X` of the allocation `Y` of `H′` (agents `ag'`, goods `gs'`) to `H` (agents `ag`, goods
`gs`), with outside agents `out` and the goods `I ∪ I′` marked by `inner` (M1's conditions, with M1(b)'s
relaxation through an agent `z` of `H′` whose bundle no outside agent envies):
- `keep`: an outside agent keeps the goods of its bundle outside `I ∪ I′`, or held only goods of `I ∪ I′`;
- `safe`: every agent of `H` other than the outside agents is safe in `X`;
- `dom`: every bundle of `X` is dominated by a bundle of `Y`, or its goods outside `I ∪ I′` are in `Y_z`. -/
structure Extension (v : A → G → Nat) (out ag ag' : List A) (gs gs' : List G) (inner : G → Bool)
    (Y X : G → A) (z : A) : Prop where
  keep : ∀ j ∈ out, (∀ g ∈ bundle gs' Y j, inner g = false → g ∈ bundle gs X j) ∨
    (∀ g ∈ bundle gs' Y j, inner g = true)
  safe : ∀ s ∈ ag, s ∉ out → ∀ k ∈ ag, k ≠ s → ∀ g ∈ bundle gs X k,
    value v s ((bundle gs X k).erase g) ≤ value v s (bundle gs X s)
  dom : ∀ k ∈ ag, (∃ k' ∈ ag', Dominated inner (bundle gs X k) (bundle gs' Y k')) ∨
    ((∀ j ∈ out, value v j (bundle gs' Y z) ≤ value v j (bundle gs' Y j)) ∧
      ∀ g ∈ uPart inner (bundle gs X k), g ∈ uPart inner (bundle gs' Y z))

/-- **Lemmas M1 and M1(b) (K4.MC1).** Let the outside agents `out` be agents of `H′` that value no good of
`I ∪ I′`. If `Y` is EFX₀ for `H′`, every extension `X` of `Y` is EFX₀ for `H`. No bound on the number of relevant
goods is used (so the lemma holds verbatim at k = 4, with gadget agents of any size). -/
theorem m1_efx0 (v : A → G → Nat) {out ag ag' : List A} {gs gs' : List G} {inner : G → Bool} {Y X : G → A}
    {z : A} (hgs : gs.Nodup) (hgs' : gs'.Nodup) (hout : ∀ j ∈ out, j ∈ ag')
    (hinner : ∀ j ∈ out, ∀ g, inner g = true → v j g = 0)
    (hY : EFX0L v ag' gs' Y) (hX : Extension v out ag ag' gs gs' inner Y X z) :
    EFX0L v ag gs X := by
  intro i hi k hk hik g hgk
  by_cases hio : i ∈ out
  · -- an outside agent `j = i`: it values `X_i` at least as much as `Y_i`
    have hj := hinner i hio
    have hYX : value v i (bundle gs' Y i) ≤ value v i (bundle gs X i) := by
      rcases hX.keep i hio with hk' | hk'
      · rw [← value_uPart v hj (bundle gs' Y i)]
        exact value_le_of_subset v i ((LB.nodup_bundle hgs' Y i).sublist List.filter_sublist)
          fun x hx => hk' x (mem_uPart.mp hx).1 (mem_uPart.mp hx).2
      · rw [← value_uPart v hj (bundle gs' Y i)]
        have : uPart inner (bundle gs' Y i) = [] :=
          List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
            have := hk' x (mem_uPart.mp hx).1; rw [(mem_uPart.mp hx).2] at this; cases this
        rw [this]; simp
    refine Nat.le_trans ?_ hYX
    rcases hX.dom k hk with ⟨k', hk', hd⟩ | ⟨hz, hsub⟩
    · -- dominated by `Y_{k'}`, which `i` does not strongly envy (EFX₀ of `Y`, or `k' = i`)
      refine threat_le_of_dominated v hj (LB.nodup_bundle hgs X k) hd
        (fun g' hg' => ?_) g hgk
      by_cases hk'i : k' = i
      · subst hk'i; exact value_sublist v _ List.erase_sublist
      · exact hY i (hout i hio) k' hk' (Ne.symm hk'i) g' hg'
    · -- M1(b): `U(X_k) ⊆ U(Y_z)` and `i` does not envy `Y_z`
      have h1 := value_uPart v hj (bundle gs X k)
      have h2 := value_uPart v hj (bundle gs' Y z)
      have h3 : value v i (uPart inner (bundle gs X k)) ≤ value v i (uPart inner (bundle gs' Y z)) :=
        value_le_of_subset v i ((LB.nodup_bundle hgs X k).sublist List.filter_sublist) hsub
      have h4 : value v i ((bundle gs X k).erase g) ≤ value v i (bundle gs X k) :=
        value_sublist v i List.erase_sublist
      have := hz i hio
      omega
  · exact hX.safe i hi hio k hk (Ne.symm hik) g hgk

/-- **M1 and M1(b) as used on a minimal counterexample (K4.MC1).** Suppose the smaller instance `H′` (at least
one agent) has an EFX₀ allocation, and every EFX₀ allocation `Y` of `H′` with an agent `z` envied by no agent of
`H′` (which exists by F2, `EFX.exists_unenvied`) has an extension `X` allocating the goods of `H` to its agents.
Then `H` has an EFX₀ allocation. -/
theorem m1_reduce (v : A → G → Nat) {out ag ag' : List A} {gs gs' : List G} {inner : G → Bool}
    (hgs : gs.Nodup) (hgs' : gs'.Nodup) (hne' : ag' ≠ []) (hout : ∀ j ∈ out, j ∈ ag')
    (hinner : ∀ j ∈ out, ∀ g, inner g = true → v j g = 0)
    (hH' : ∃ Y : G → A, IsAllocation ag' gs' Y ∧ EFX0L v ag' gs' Y)
    (hext : ∀ Y : G → A, IsAllocation ag' gs' Y → EFX0L v ag' gs' Y →
      ∀ z ∈ ag', (∀ a ∈ ag', ¬ Envies v gs' Y a z) →
      ∃ X : G → A, IsAllocation ag gs X ∧ Extension v out ag ag' gs gs' inner Y X z) :
    ∃ X : G → A, IsAllocation ag gs X ∧ EFX0L v ag gs X := by
  obtain ⟨Y0, hY0, hE0⟩ := hH'
  obtain ⟨Y, hY, hE, z, hz, hzu⟩ := exists_unenvied v hne' hY0 hE0
  obtain ⟨X, hX, hext'⟩ := hext Y hY hE z hz hzu
  exact ⟨X, hX, m1_efx0 v hgs hgs' hout hinner hE hext'⟩

end MinCex
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.MinCex.threat_le_of_dominated
#print axioms EFX.MinCex.m1_efx0
#print axioms EFX.MinCex.m1_reduce
