import EFX.K4Ties
import EFX.Target
import EFX.PreAllocK

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

/-! ## K4.MC4: the counting bound -/

section count

/-- The degree of a good: the number of agents that value it. -/
def deg (v : A → G → Nat) (agents : List A) (g : G) : Nat := agents.countP (fun i => decide (0 < v i g))

/-- An agent's degree in `Γ′` (the incidence graph without the private goods): the number of goods it values
that another agent values too (degree ≥ 2). -/
def degS (v : A → G → Nat) (agents : List A) (goods : List G) (i : A) : Nat :=
  goods.countP (fun g => decide (0 < v i g) && decide (2 ≤ deg v agents g))

theorem sum_map_add' {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add' f g l]; omega

theorem sum_map_mul_left' {α : Type} (k : Nat) (f : α → Nat) :
    ∀ l : List α, (l.map (fun a => k * f a)).sum = k * (l.map f).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul_left' k f l, Nat.mul_add]

omit [DecidableEq A] in
/-- A count of at least 2 in a list without repeats, one of them `f`: another element passes. -/
theorem exists_other_of_countP {p : A → Bool} {l : List A} (hl : l.Nodup) (h2 : 2 ≤ l.countP p) {f : A}
    (_hf : f ∈ l) : ∃ e ∈ l, e ≠ f ∧ p e = true := by
  refine Classical.byContradiction fun hno => ?_
  have : l.countP p ≤ 1 := by
    rw [List.countP_eq_length_filter]
    refine LB.length_le_one (hl.sublist List.filter_sublist) (y := f) fun e he => ?_
    obtain ⟨hel, hpe⟩ := List.mem_filter.mp he
    exact Classical.byContradiction fun hef => hno ⟨e, hel, hef, hpe⟩
  omega

omit [DecidableEq G] in
/-- **K4.MC4 (counting).** Let every good be valued by some agent, every agent have `Γ′`-degree 2, 3 or 4, no good
of degree 2 be valued by two agents of `Γ′`-degree 2 (K4.MC3; with K4.MC2 these are the P3 agents), and every agent
of `Γ′`-degree 3 (the E3 agents) share at most one good of degree 2 with an agent of `Γ′`-degree 2 (K4.MC5(iii):
it ranks every such good first). Then `n ≤ 3(β − 1)`, where `β = Σ_i |R_i| − n − m + 1`: that is,
`4n + 3m ≤ 3 Σ_i |R_i|`. -/
theorem mc4_count (v : A → G → Nat) {agents : List A} {goods : List G} (hag : agents.Nodup)
    (hcov : ∀ g ∈ goods, 1 ≤ deg v agents g)
    (hd : ∀ i ∈ agents, 2 ≤ degS v agents goods i ∧ degS v agents goods i ≤ 4)
    (hMC3 : ∀ g ∈ goods, deg v agents g = 2 → ∀ f ∈ agents, ∀ f' ∈ agents, f ≠ f' → 0 < v f g → 0 < v f' g →
      degS v agents goods f = 2 → degS v agents goods f' ≠ 2)
    (hMC5 : ∀ e ∈ agents, degS v agents goods e = 3 →
      goods.countP (fun g => decide (0 < v e g) && decide (deg v agents g = 2) &&
        decide (∃ f ∈ agents, f ≠ e ∧ 0 < v f g ∧ degS v agents goods f = 2)) ≤ 1) :
    4 * agents.length + 3 * goods.length ≤ 3 * (agents.map (fun i => (relevant v i goods).length)).sum := by
  -- (F1) Σ_i |R_i| = Σ_g deg g, and (F2) Σ_i d′_i = Σ_{g shared} deg g
  have F1 : (agents.map (fun i => (relevant v i goods).length)).sum = (goods.map (deg v agents)).sum := by
    have := LB4.sum_countP_comm (fun i g => decide (0 < v i g)) agents goods
    change _ = (goods.map (fun g => agents.countP (fun i => decide (0 < v i g)))).sum
    rw [← this]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [relevant, List.countP_eq_length_filter]
  have F2 : (agents.map (degS v agents goods)).sum = (goods.map (fun g => if 2 ≤ deg v agents g then deg v agents g else 0)).sum := by
    have := LB4.sum_countP_comm (fun i g => decide (0 < v i g) && decide (2 ≤ deg v agents g)) agents goods
    change (agents.map (fun i => goods.countP (fun g => decide (0 < v i g) && decide (2 ≤ deg v agents g)))).sum = _
    rw [this]
    congr 1
    apply List.map_congr_left
    intro g _
    by_cases h2 : 2 ≤ deg v agents g
    · simp only [h2, decide_true, Bool.and_true, ↓reduceIte]
      rfl
    · simp only [h2, ↓reduceIte]
      apply List.countP_eq_zero.mpr
      intro i _ h
      simp at h
  -- the goods: `deg g = [deg ≥ 2] deg g + [deg = 1]`, and `1 = [deg ≥ 2] + [deg = 1]`
  have G1 : (goods.map (deg v agents)).sum = (goods.map (fun g => if 2 ≤ deg v agents g then deg v agents g else 0)).sum +
      (goods.map (fun g => if 2 ≤ deg v agents g then 0 else 1)).sum := by
    rw [← sum_map_add']
    congr 1
    apply List.map_congr_left
    intro g hg
    have := hcov g hg
    by_cases h2 : 2 ≤ deg v agents g
    · simp [h2]
    · simp only [h2, ↓reduceIte]; omega
  have G2 : goods.length = (goods.map (fun g => if 2 ≤ deg v agents g then 1 else 0)).sum +
      (goods.map (fun g => if 2 ≤ deg v agents g then 0 else 1)).sum := by
    rw [← sum_map_add']
    have : ∀ l : List G, l.length = (l.map (fun g => (if 2 ≤ deg v agents g then 1 else 0) + (if 2 ≤ deg v agents g then 0 else 1))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons, ← ih]
        by_cases h : 2 ≤ deg v agents a <;> simp [h] <;> omega
    exact this goods
  -- (F3) the charging: `2n ≤ 3 Σ_i (d′_i − 2) + 3 Σ_g [deg ≥ 2] (deg g − 2)`
  -- c(g): the agents of `Γ′`-degree 2 valuing a shared good `g`
  let c : G → Nat := fun g => agents.countP (fun f => decide (0 < v f g) && decide (degS v agents goods f = 2) && decide (2 ≤ deg v agents g))
  let q : A → G → Bool := fun e g => decide (0 < v e g) && decide (deg v agents g = 2) &&
    decide (∃ f ∈ agents, f ≠ e ∧ 0 < v f g ∧ degS v agents goods f = 2)
  -- (a) each agent of `Γ′`-degree 2 has exactly two shared incidences
  have Fa : (agents.map (fun f => if degS v agents goods f = 2 then 2 else 0)).sum = (goods.map c).sum := by
    have := LB4.sum_countP_comm (fun f g => decide (0 < v f g) && decide (degS v agents goods f = 2) && decide (2 ≤ deg v agents g))
      agents goods
    rw [← this]
    congr 1
    apply List.map_congr_left
    intro f _
    by_cases hf : degS v agents goods f = 2
    · simp only [hf, ↓reduceIte]
      rw [← hf]
      show _ = goods.countP _
      apply List.countP_congr
      intro g _
      simp [hf]
    · simp only [hf, ↓reduceIte]
      symm; apply List.countP_eq_zero.mpr
      intro g _ h
      simp at h
  -- (b) per good: `c(g) ≤ 3 [deg ≥ 2] (deg g − 2) + Σ_e q(e, g)`
  have Fb : ∀ g ∈ goods, c g ≤ 3 * (if 2 ≤ deg v agents g then deg v agents g - 2 else 0) + agents.countP (fun e => q e g) := by
    intro g hg
    have hcle : c g ≤ deg v agents g := by
      apply List.countP_mono_left
      intro f _ h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact h.1.1
    by_cases h3 : 3 ≤ deg v agents g
    · simp only [show 2 ≤ deg v agents g by omega, ↓reduceIte]; omega
    by_cases h2 : deg v agents g = 2
    · simp only [h2, Nat.le_refl, ↓reduceIte, Nat.sub_self, Nat.mul_zero, Nat.zero_add]
      -- at most one agent of degree 2 values `g` (K4.MC3), and then the other valuer is not one
      by_cases hc0 : c g = 0
      · omega
      obtain ⟨f, hf, hfp⟩ : ∃ f ∈ agents, (decide (0 < v f g) && decide (degS v agents goods f = 2) && decide (2 ≤ deg v agents g)) = true := by
        refine Classical.byContradiction fun hno => hc0 (List.countP_eq_zero.mpr fun f hf h => hno ⟨f, hf, ?_⟩)
        simpa using h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
      obtain ⟨e, he, hef, hep⟩ := exists_other_of_countP (p := fun i => decide (0 < v i g)) hag
        (show 2 ≤ deg v agents g by omega) hf
      simp only [decide_eq_true_eq] at hep
      have hde : degS v agents goods e ≠ 2 := hMC3 g hg h2 f hf e he (Ne.symm hef) hfp.1.1 hep hfp.1.2
      have hc1 : c g ≤ 1 := by
        refine Classical.byContradiction fun h => ?_
        obtain ⟨f₂, hf₂, hf₂f, hp₂⟩ := exists_other_of_countP (p := fun f => decide (0 < v f g) &&
          decide (degS v agents goods f = 2) && decide (2 ≤ deg v agents g)) hag (by simp only [c] at h; omega) hf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp₂
        exact hMC3 g hg h2 f hf f₂ hf₂ (Ne.symm hf₂f) hfp.1.1 hp₂.1.1 hfp.1.2 hp₂.1.2
      have hq1 : 1 ≤ agents.countP (fun e => q e g) := by
        rw [List.countP_eq_length_filter]
        apply List.length_pos_of_mem (a := e)
        refine List.mem_filter.mpr ⟨he, ?_⟩
        simp only [q, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hep, h2⟩, f, hf, hef.symm, hfp.1.1, hfp.1.2⟩
      omega
    · have : c g = 0 := by
        apply List.countP_eq_zero.mpr
        intro f _ h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        omega
      omega
  -- (c) per agent: `Σ_g q(e, g) ≤ b(e)`, with `2 [d′ ≠ 2] + b(e) ≤ 3 (d′_e − 2)`
  have Fc : ∀ e ∈ agents, (if degS v agents goods e = 2 then 0 else 2) + goods.countP (q e) ≤ 3 * (degS v agents goods e - 2) := by
    intro e he
    obtain ⟨hlo, hhi⟩ := hd e he
    by_cases h2 : degS v agents goods e = 2
    · have : goods.countP (q e) = 0 := by
        apply List.countP_eq_zero.mpr
        intro g _ h
        simp only [q, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hv, hdg⟩, f, hf, hfe, hvf, hdf⟩ := h
        exact hMC3 g (by assumption) hdg f hf e he hfe hvf hv hdf h2
      simp only [h2, ↓reduceIte, this]; omega
    by_cases h3 : degS v agents goods e = 3
    · have := hMC5 e he h3
      simp only [h2, ↓reduceIte]
      have : goods.countP (q e) ≤ 1 := by
        refine Nat.le_trans (Nat.le_of_eq ?_) this
        apply List.countP_congr; intro g _; simp [q]
      omega
    · have h4 : degS v agents goods e = 4 := by omega
      have : goods.countP (q e) ≤ degS v agents goods e := by
        apply List.countP_mono_left
        intro g _ h
        simp only [q, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        exact ⟨h.1.1, by omega⟩
      simp only [h2, ↓reduceIte]; omega
  -- summing up
  have S1 : (goods.map c).sum ≤ 3 * (goods.map (fun g => if 2 ≤ deg v agents g then deg v agents g - 2 else 0)).sum +
      (agents.map (fun e => goods.countP (q e))).sum := by
    have hq := LB4.sum_countP_comm q agents goods
    rw [hq, ← sum_map_mul_left', ← sum_map_add']
    exact LB4.sum_le_sum_of_le _ _ goods Fb
  have S2 : (agents.map (fun e => (if degS v agents goods e = 2 then 0 else 2) + goods.countP (q e))).sum ≤
      (agents.map (fun e => 3 * (degS v agents goods e - 2))).sum := LB4.sum_le_sum_of_le _ _ agents Fc
  rw [sum_map_add'] at S2
  have S3 : 2 * agents.length = (agents.map (fun f => if degS v agents goods f = 2 then 2 else 0)).sum +
      (agents.map (fun e => if degS v agents goods e = 2 then 0 else 2)).sum := by
    rw [← sum_map_add']
    have : ∀ l : List A, 2 * l.length = (l.map (fun f => (if degS v agents goods f = 2 then 2 else 0) + (if degS v agents goods f = 2 then 0 else 2))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        by_cases h : degS v agents goods a = 2 <;> simp [h] <;> omega
    exact this agents
  -- `Σ_i 3(d′_i − 2) = 3 Σ d′ − 6n` and `Σ_g [deg ≥ 2](deg − 2) = Σ_g [deg ≥ 2] deg − 2 m_s`
  have S4 : (agents.map (fun e => 3 * (degS v agents goods e - 2))).sum + 6 * agents.length = 3 * (agents.map (degS v agents goods)).sum := by
    have : ∀ l : List A, (∀ e ∈ l, 2 ≤ degS v agents goods e) →
        (l.map (fun e => 3 * (degS v agents goods e - 2))).sum + 6 * l.length = 3 * (l.map (degS v agents goods)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := hl a (by simp)
        have := ih (fun e he => hl e (by simp [he]))
        omega
    exact this agents fun e he => (hd e he).1
  have S5 : (goods.map (fun g => if 2 ≤ deg v agents g then deg v agents g - 2 else 0)).sum +
      2 * (goods.map (fun g => if 2 ≤ deg v agents g then 1 else 0)).sum =
      (goods.map (fun g => if 2 ≤ deg v agents g then deg v agents g else 0)).sum := by
    have : ∀ l : List G, (l.map (fun g => if 2 ≤ deg v agents g then deg v agents g - 2 else 0)).sum +
        2 * (l.map (fun g => if 2 ≤ deg v agents g then 1 else 0)).sum = (l.map (fun g => if 2 ≤ deg v agents g then deg v agents g else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        by_cases h : 2 ≤ deg v agents a <;> simp [h] <;> omega
    exact this goods
  rw [F1, G1]
  rw [G2]
  omega

end count

/-! ## The assembly (K4.MC6 for `b = 3`, K4.MC7 for `b = 4`) -/

/-- The structure of `Γ′` that K4.MC4 counts with: every agent has `Γ′`-degree 2, 3 or 4; no good of degree 2 is
valued by two agents of `Γ′`-degree 2 (K4.MC3); every agent of `Γ′`-degree 3 shares at most one good of degree 2 with
an agent of `Γ′`-degree 2 (K4.MC5(iii)). -/
def GammaStruct (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  (∀ i ∈ agents, 2 ≤ degS v agents goods i ∧ degS v agents goods i ≤ 4) ∧
  (∀ g ∈ goods, deg v agents g = 2 → ∀ f ∈ agents, ∀ f' ∈ agents, f ≠ f' → 0 < v f g → 0 < v f' g →
    degS v agents goods f = 2 → degS v agents goods f' ≠ 2) ∧
  (∀ e ∈ agents, degS v agents goods e = 3 →
    goods.countP (fun g => decide (0 < v e g) && decide (deg v agents g = 2) &&
      decide (∃ f ∈ agents, f ≠ e ∧ 0 < v f g ∧ degS v agents goods f = 2)) ≤ 1)

/-- The number of agents with four relevant goods. -/
def num4 (v : A → G → Nat) (agents : List A) (goods : List G) : Nat :=
  agents.countP (fun i => decide ((relevant v i goods).length = 4))

/-- **The hypotheses of the chain** for a class `C` (the instances whose incidence-graph components have
cyclomatic number at most `b`, `𝒞_b`), each a fact that Lean does not re-check here:
- `her`, `rel`: `𝒞_b` is closed under deleting agents and goods, and depends only on the relevant goods (graph
  facts, `proofs/min_counterexample.md` §1; not formalized);
- `cyc`: a connected k = 4 core of `𝒞_b` has cyclomatic number `β = Σ_i |R_i| − n − m + 1 ≤ b`;
- `red` (K4.MC2, K4.MC3, K4.MC5: Lemma M1 (`m1_reduce`) with the reduction certificate
  `results/k4_min_cex_reductions.json.gz`, checked by `k4/check_reductions4.py`): a connected strict core of `C`
  with a 4-good agent whose smaller instances in `C` are all solvable, and which violates `GammaStruct` or the
  per-agent domain cuts `Cut` (K4.MC2, and K4.MC5's restrictions of the P3/E3/Q4 profiles), is solvable;
- `small` (K4.R3–K4.R5, certified): such a core with `n ≤ 4`, or `n = 5` and at most two 4-good agents, is solvable;
- `enum` (the enumeration, `k4/mincex_shapes.py`, re-checked with orbit counting by `k4/check_mincex_cores.py`
  (`b = 3`) and `k4/check_mincex_cores4.py` (`b = 4`)): such a core satisfying `GammaStruct` and `Cut`, with `n ≥ 5`,
  `n ≤ 3(β − 1)` and `β ≤ b`, matches some entry `d` of the list `L` (isomorphic to it, with its profile in `d`'s
  restricted domain; `Matches` is not defined in Lean);
- `cert` (`results/k4_min_cex_cores_3.json.gz`, `results/k4_min_cex_cores_4.json.gz`, checked by the same
  checkers): every instance matching a certified entry is solvable;
- `lit` (the multigraph theorem of Afshinmehr et al., arXiv 2606.18665, `proofs/citations.md` item 4): every
  instance matching a graphical entry is solvable;
- `cover`: every entry is certified or graphical (for `b = 3`, all 9 are certified; for `b = 4`, 5,552 are certified
  and 6 graphical). -/
structure ChainHyp (C : List A → List G → (A → G → Nat) → Prop) (b : Nat)
    (Cut : List A → List G → (A → G → Nat) → Prop) {D : Type} (L : List D)
    (Matches : D → List A → List G → (A → G → Nat) → Prop) (certified graphical : D → Prop) : Prop where
  her : Hereditary C
  rel : RelevanceInvariant C
  cyc : ∀ agents goods v, C agents goods v → IsCore4 v agents goods → Connected v agents goods →
    (agents.map (fun i => (relevant v i goods).length)).sum + 1 ≤ b + agents.length + goods.length
  red : ∀ agents goods v, C agents goods v → agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → 0 < num4 v agents goods → MinimalFor C agents goods →
    ¬ (GammaStruct v agents goods ∧ Cut agents goods v) → Solvable agents goods v
  small : ∀ agents goods v, C agents goods v → agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → 0 < num4 v agents goods →
    (agents.length ≤ 4 ∨ (agents.length = 5 ∧ num4 v agents goods ≤ 2)) → Solvable agents goods v
  enum : ∀ agents goods v, C agents goods v → agents.Nodup → goods.Nodup → IsCore4 v agents goods →
    Connected v agents goods → Strict v agents goods → 0 < num4 v agents goods →
    GammaStruct v agents goods → Cut agents goods v → 5 ≤ agents.length →
    ¬ (agents.length = 5 ∧ num4 v agents goods ≤ 2) →
    4 * agents.length + 3 * goods.length ≤ 3 * (agents.map (fun i => (relevant v i goods).length)).sum →
    (agents.map (fun i => (relevant v i goods).length)).sum + 1 ≤ b + agents.length + goods.length →
    ∃ d ∈ L, Matches d agents goods v
  cert : ∀ d ∈ L, certified d → ∀ agents goods v, Matches d agents goods v → Solvable agents goods v
  lit : ∀ d ∈ L, graphical d → ∀ agents goods v, Matches d agents goods v → Solvable agents goods v
  cover : ∀ d ∈ L, certified d ∨ graphical d

/-- **The chain of K4.MC6 (`b = 3`) and K4.MC7 (`b = 4`), machine-checked.** Under `ChainHyp`, every admissible
instance of `C` (at least one agent, at most four relevant goods per agent) has an EFX₀ allocation. The proof is
the minimal-counterexample argument of `k4/MINCEX.md` §6 and §8: a minimal counterexample is a connected strict
k = 4 core with a 4-good agent (K4.MC0, `mc0`); it has the structure of K4.MC2, K4.MC3 and K4.MC5 (`red`), at least
five agents (`small`), and `n ≤ 3(β − 1)` (K4.MC4, `mc4_count`), so it matches an entry of the list (`enum`), which
is certified (`cert`) or graphical (`lit`). -/
theorem target4_chain {C : List A → List G → (A → G → Nat) → Prop} {b : Nat}
    {Cut : List A → List G → (A → G → Nat) → Prop} {D : Type} {L : List D}
    {Matches : D → List A → List G → (A → G → Nat) → Prop} {certified graphical : D → Prop}
    (h : ChainHyp C b Cut L Matches certified graphical) :
    ∀ agents goods v, C agents goods v → Admissible agents goods v → Solvable agents goods v := by
  refine mc0 C h.her h.rel fun agents goods v hC hag hgd hc hconn hs h4 hmin => ?_
  have hn4 : 0 < num4 v agents goods := by
    obtain ⟨i, hi, hi4⟩ := h4
    rw [num4, List.countP_eq_length_filter]
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hi, by simpa using hi4⟩)
  by_cases hst : GammaStruct v agents goods ∧ Cut agents goods v
  · by_cases hsm : agents.length ≤ 4 ∨ (agents.length = 5 ∧ num4 v agents goods ≤ 2)
    · exact h.small agents goods v hC hag hgd hc hconn hs hn4 hsm
    · have hcov : ∀ g ∈ goods, 1 ≤ deg v agents g := fun g hg => by
        obtain ⟨i, hi, hpos⟩ := hc.2.2.2.2.2 g hg
        rw [deg, List.countP_eq_length_filter]
        exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hi, by simpa using hpos⟩)
      obtain ⟨hd, h3, h5⟩ := hst.1
      have hcount := mc4_count v hag hcov hd h3 h5
      obtain ⟨d, hd, hm⟩ := h.enum agents goods v hC hag hgd hc hconn hs hn4 hst.1 hst.2 (by omega)
        (fun hh => hsm (Or.inr hh)) hcount (h.cyc agents goods v hC hc hconn)
      rcases h.cover d hd with hce | hgr
      · exact h.cert d hd hce agents goods v hm
      · exact h.lit d hd hgr agents goods v hm
  · exact h.red agents goods v hC hag hgd hc hconn hs hn4 hmin hst

end MinCex
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.MinCex.threat_le_of_dominated
#print axioms EFX.MinCex.m1_efx0
#print axioms EFX.MinCex.m1_reduce
#print axioms EFX.MinCex.core_reduction4_class
#print axioms EFX.MinCex.mc0
#print axioms EFX.MinCex.mc4_count
#print axioms EFX.MinCex.target4_chain
