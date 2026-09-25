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

/-! ## K4.MC0: the inductive statement -/

/-- An instance has an EFX₀ allocation. -/
def Solvable (agents : List A) (goods : List G) (v : A → G → Nat) : Prop :=
  ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X

/-- An instance of TARGET₄: at least one agent, no repeated agents or goods, every agent with at most four
relevant goods (nonnegative values in `Nat`). -/
def Admissible (agents : List A) (goods : List G) (v : A → G → Nat) : Prop :=
  agents ≠ [] ∧ agents.Nodup ∧ goods.Nodup ∧ ∀ i ∈ agents, (relevant v i goods).length ≤ 4

/-- `(agents', goods')` is smaller than `(agents, goods)`: fewer agents, or as many agents and fewer goods (the
order of a minimal counterexample: fewest agents, then fewest goods). -/
def LexLt (agents' : List A) (goods' : List G) (agents : List A) (goods : List G) : Prop :=
  agents'.length < agents.length ∨ (agents'.length = agents.length ∧ goods'.length < goods.length)

/-- A class of instances is *hereditary* if it is closed under deleting agents and goods (for `𝒞_β`: deleting
vertices never raises a component's cyclomatic number). -/
def Hereditary (C : List A → List G → (A → G → Nat) → Prop) : Prop :=
  ∀ agents goods v agents' goods', C agents goods v → agents'.Sublist agents → goods'.Sublist goods →
    C agents' goods' v

/-- A class *depends only on the relevant goods* (for `𝒞_β`: only the incidence graph matters). -/
def RelevanceInvariant (C : List A → List G → (A → G → Nat) → Prop) : Prop :=
  ∀ agents goods v w, C agents goods v → (∀ i g, 0 < w i g ↔ 0 < v i g) → C agents goods w

/-- Every smaller admissible instance of the class, with any valuation, has an EFX₀ allocation (K4.MC0(a)). -/
def MinimalFor (C : List A → List G → (A → G → Nat) → Prop) (agents : List A) (goods : List G) : Prop :=
  ∀ agents' goods' v', C agents' goods' v' → Admissible agents' goods' v' → LexLt agents' goods' agents goods →
    Solvable agents' goods' v'

/-- **K4.MC0(a), (b): the CORE reduction within a class.** Let `C` be hereditary. If every connected k = 4 core of
`C` all of whose smaller admissible instances in `C` have EFX₀ allocations has one itself, then every admissible
instance of `C` has one. (The proof of `EFX.core_reduction4_conn`, with the class and the order of a minimal
counterexample in place of the bound on the agents: each step, L3, R1, R2 and L6, passes to a sublist of the agents
and of the goods, with fewer agents, or with as many agents and fewer goods.) -/
theorem core_reduction4_class (C : List A → List G → (A → G → Nat) → Prop) (hher : Hereditary C)
    (hcore : ∀ agents goods v, C agents goods v → agents.Nodup → goods.Nodup → IsCore4 v agents goods →
      Connected v agents goods → MinimalFor C agents goods → Solvable agents goods v) :
    ∀ agents goods v, C agents goods v → Admissible agents goods v → Solvable agents goods v := by
  suffices H : ∀ n m (agents : List A) (goods : List G) (v : A → G → Nat), agents.length = n →
      goods.length = m → C agents goods v → Admissible agents goods v → Solvable agents goods v from
    fun agents goods v => H _ _ agents goods v rfl rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro agents goods v hn hm hC ⟨hne, hag, hgd, h4⟩
  -- every smaller admissible instance of the class is solvable
  have hmin : MinimalFor C agents goods := by
    intro agents' goods' v' hC' had' hlt
    rcases hlt with hlt | ⟨heq, hlt⟩
    · exact ihn _ (by omega) _ agents' goods' v' rfl rfl hC' had'
    · exact ihm _ (by omega) agents' goods' v' (by omega) rfl hC' had'
  have hsub : ∀ agents' goods', agents'.Sublist agents → goods'.Sublist goods → agents' ≠ [] →
      LexLt agents' goods' agents goods → Solvable agents' goods' v := fun agents' goods' ha hg hne' hlt =>
    hmin agents' goods' v (hher _ _ _ _ _ hC ha hg) ⟨hne', hag.sublist ha, hgd.sublist hg,
      fun i hi => Nat.le_trans (relevant_sublist v hg) (h4 i (ha.subset hi))⟩ hlt
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil agents hne
  -- no goods: nothing to allocate
  by_cases hg0 : goods = []
  · subst hg0
    exact ⟨fun _ => i0, fun g hg => by simp at hg, fun _ _ _ _ _ g hg => by simp [bundle] at hg⟩
  -- one agent: it takes everything
  by_cases h1 : agents.length ≤ 1
  · refine ⟨fun _ => i0, fun _ _ => hi0, fun x hx y hy hxy => ?_⟩
    exfalso
    have : x = y := by
      cases agents with
      | nil => simp at hx
      | cons a l =>
        cases l with
        | nil => simp at hx hy; rw [hx, hy]
        | cons b l => simp at h1
    exact hxy this
  -- 1. junk goods (L3)
  by_cases hjunk : ∃ g ∈ goods, isJunk v agents g = true
  · obtain ⟨g, hg, hgj⟩ := hjunk
    have hlt : (goods.filter (fun g => !isJunk v agents g)).length < goods.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [hgj]⟩
    obtain ⟨X', hX', hE'⟩ := hsub agents _ (List.Sublist.refl _) List.filter_sublist hne (Or.inr ⟨rfl, hlt⟩)
    exact junk v hne hX' hE'
  -- 2. peeling by R1
  by_cases hR1 : ∃ i ∈ agents, ∃ p ∈ goods, value v i (goods.erase p) ≤ v i p
  · obtain ⟨i, hi, p, hp, htop⟩ := hR1
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    obtain ⟨X', hX', hE'⟩ := hsub (agents.erase i) (goods.erase p) List.erase_sublist List.erase_sublist hrest
      (Or.inl (by rw [List.length_erase_of_mem hi]; have := List.length_pos_of_mem hi; omega))
    obtain ⟨hX, hE⟩ := peel v (List.Nodup.not_mem_erase hag) hp hgd hX' hE' htop
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- every agent has at least three relevant goods and is strictly balanced
  have hbal : ∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods :=
    fun i hi => not_R1 v hg0 (fun ⟨p, hp, h⟩ => hR1 ⟨i, hi, p, hp, h⟩)
  -- 3. peeling by R2
  by_cases hR2 : ∃ i ∈ agents,
      value v i (relevant v i (goods.filter (fun g => !isPrivate v i (agents.erase i) g))) ≤
        value v i (goods.filter (isPrivate v i (agents.erase i)))
  · obtain ⟨i, hi, hb⟩ := hR2
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    obtain ⟨X', hX', hE'⟩ := hsub (agents.erase i) (goods.filter (fun g => !isPrivate v i (agents.erase i) g))
      List.erase_sublist List.filter_sublist hrest
      (Or.inl (by rw [List.length_erase_of_mem hi]; have := List.length_pos_of_mem hi; omega))
    obtain ⟨hX, hE⟩ := peelR2 v (List.Nodup.not_mem_erase hag) hX' hE' hb
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- 4. components (L6)
  by_cases hconn : ¬ Connected v agents goods
  · obtain ⟨S, hS, a, ha, b, hb, hab⟩ : ∃ S : A → Bool,
        (∀ g ∈ goods, ∀ i ∈ agents, ∀ j ∈ agents, 0 < v i g → 0 < v j g → S i = S j) ∧
        ∃ a ∈ agents, ∃ b ∈ agents, S a = true ∧ S b = false := by
      refine Classical.byContradiction fun hno => hconn fun S hS i hi j hj => ?_
      cases hSi : S i <;> cases hSj : S j
      · rfl
      · exact absurd ⟨S, hS, j, hj, i, hi, hSj, hSi⟩ hno
      · exact absurd ⟨S, hS, i, hi, j, hj, hSi, hSj⟩ hno
      · rfl
    let T : G → Bool := fun g => decide (∃ a ∈ agents, S a = true ∧ 0 < v a g)
    have hST : ∀ i ∈ agents, ∀ g ∈ goods, 0 < v i g → S i = T g := by
      intro i hi g hg hpos
      cases hSi : S i
      · refine (decide_eq_false fun ⟨a', ha', hSa', hpa'⟩ => ?_).symm
        have := hS g hg i hi a' ha' hpos hpa'
        rw [hSi, hSa'] at this
        exact Bool.noConfusion this
      · exact (decide_eq_true ⟨i, hi, hSi, hpos⟩).symm
    have hlenS : (agents.filter S).length < agents.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨b, hb, by simp [hab.2]⟩
    have hlenN : (agents.filter (fun i => !S i)).length < agents.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨a, ha, by simp [hab.1]⟩
    obtain ⟨X1, hX1, hE1⟩ := hsub (agents.filter S) (goods.filter T) List.filter_sublist List.filter_sublist
      (List.ne_nil_of_mem (List.mem_filter.mpr ⟨ha, hab.1⟩)) (Or.inl hlenS)
    obtain ⟨X2, hX2, hE2⟩ := hsub (agents.filter (fun i => !S i)) (goods.filter (fun g => !T g))
      List.filter_sublist List.filter_sublist
      (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hb, by simp [hab.2]⟩)) (Or.inl hlenN)
    exact ⟨_, efx0_split v S T hST hX1 hE1 hX2 hE2⟩
  have hconn : Connected v agents goods := Classical.byContradiction hconn
  -- 5. a connected k = 4 core, all of whose smaller instances in the class are solvable
  have hq : ∀ i, ∀ g, isPrivate v i (agents.erase i) g = true → 0 < v i g :=
    fun i g hg => ((isPrivate_iff v hag).mp hg).1
  refine hcore agents goods v hC hag hgd ⟨by omega, fun i hi => ⟨(hbal i hi).1, h4 i hi⟩,
    fun i hi => (hbal i hi).2, fun i hi => ?_, fun i hi _ => ?_, fun g hg => ?_⟩ hconn hmin
  · rw [privateGoods_eq v hag, length_relevant_split v i _ goods (hq i)]
    refine Nat.add_le_add_left (Nat.le_of_not_lt fun hlt => hR2 ⟨i, hi, ?_⟩) _
    exact R2_balance_of_le_one v _ (hbal i hi).2 (by omega)
  · rw [privateGoods_eq v hag, sharedGoods_eq v hag]
    exact Nat.lt_of_not_le fun hle => hR2 ⟨i, hi, hle⟩
  · refine Classical.byContradiction fun hno => hjunk ⟨g, hg, ?_⟩
    simp only [isJunk, List.all_eq_true, beq_iff_eq]
    intro j hj
    exact Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hpos⟩

/-- **K4.MC0 (a)–(c), in inductive form.** Let `C` be a hereditary class of instances that depends only on the
relevant goods (such as `𝒞_β`). Suppose every connected k = 4 core of `C` that is *strict* (`EFX.Strict`: only the
types matter, K4.TIE) and has an agent with four relevant goods has an EFX₀ allocation whenever every smaller
admissible instance of `C` has one. Then every admissible instance of `C` has an EFX₀ allocation. Equivalently, a
minimal counterexample within `C` is a connected strict k = 4 core with a 4-good agent (cores whose agents all have
three goods are covered by TARGET, `EFX.target_lists`). -/
theorem mc0 (C : List A → List G → (A → G → Nat) → Prop) (hher : Hereditary C) (hrel : RelevanceInvariant C)
    (hcore : ∀ agents goods v, C agents goods v → agents.Nodup → goods.Nodup → IsCore4 v agents goods →
      Connected v agents goods → Strict v agents goods → (∃ i ∈ agents, (relevant v i goods).length = 4) →
      MinimalFor C agents goods → Solvable agents goods v) :
    ∀ agents goods v, C agents goods v → Admissible agents goods v → Solvable agents goods v := by
  refine core_reduction4_class C hher fun agents goods v hC hag hgd hc hconn hmin => ?_
  by_cases h4 : ∃ i ∈ agents, (relevant v i goods).length = 4
  · refine tie_reduction v hgd (fun w hw hcw hconnw hsw => hcore agents goods w (hrel _ _ _ _ hC hw) hag hgd hcw
      hconnw hsw ?_ hmin) hc hconn
    obtain ⟨i, hi, h4i⟩ := h4
    refine ⟨i, hi, ?_⟩
    have : relevant w i goods = relevant v i goods := List.filter_congr fun g _ => by simp [hw]
    rw [this]; exact h4i
  · have hne : agents ≠ [] := fun h => by have := hc.1; rw [h] at this; simp at this
    exact target_lists v hne hag hgd fun i hi => by
      have := (hc.2.1 i hi).2
      exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (by omega) fun e => h4 ⟨i, hi, e⟩)

end MinCex
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.MinCex.threat_le_of_dominated
#print axioms EFX.MinCex.m1_efx0
#print axioms EFX.MinCex.m1_reduce
#print axioms EFX.MinCex.core_reduction4_class
#print axioms EFX.MinCex.mc0
