import EFX.OCVariants

/-!
# What one move does (any instance)

General facts about the moves of `EFX.OC1Max.OneMove` (`k4/sdc.md` §29), used by the refutation of OC₁^max
(`EFX/OC1MaxCex.lean`), Lemma T6 (`EFX/T6.lean`) and the completion lemmas (`EFX/LemmaM.lean`).

- `value_le_of_nodup_sub`: a list without repetitions is worth at most any list containing its goods.
- `move_local`: after one move, every listed agent keeps its base, or strictly gains with a new base, without
  repetitions, inside one listed agent's old base and the junk.
- `move_released`: at bases of one good each, one move leaves at most one base good outside every new base (only a
  chain releases one, the end's).
-/

set_option autoImplicit false

namespace EFX
namespace OC1Max

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## After one move (any instance) -/

section afterMove
variable {v : A → G → Nat} {agents : List A} {goods : List G}

omit [DecidableEq A] [DecidableEq G] in
theorem value_append_eq (i : A) (S T : List G) : value v i (S ++ T) = value v i S + value v i T := by
  simp [value]

omit [DecidableEq A] in
/-- The value of a list without repetitions is at most that of any list containing its goods. -/
theorem value_le_of_nodup_sub (i : A) : ∀ {L M : List G}, L.Nodup → (∀ g ∈ L, g ∈ M) →
    value v i L ≤ value v i M
  | [], _, _, _ => by simp
  | a :: t, M, hnd, hsub => by
    obtain ⟨hat, htn⟩ := List.nodup_cons.mp hnd
    have haM : a ∈ M := hsub a List.mem_cons_self
    have hM : value v i M = v i a + value v i (M.erase a) := by
      have := ((List.perm_cons_erase haM).map (v i)).sum_nat
      simpa [value] using this
    have ih := value_le_of_nodup_sub i htn fun g hg => by
      have hne : g ≠ a := fun e => hat (e ▸ hg)
      exact (List.mem_erase_of_ne hne).mpr (hsub g (List.mem_cons_of_mem _ hg))
    rw [value_cons, hM]; omega

omit [DecidableEq A] in
theorem nodup_append_junk {B : A → List G} {j : A} (hj : j ∈ agents) {H : List G} (hBj : (B j).Nodup)
    (hH : H.Nodup) (hHJ : ∀ g ∈ H, g ∈ junkOf agents goods B) : (B j ++ H).Nodup :=
  List.nodup_append.mpr ⟨hBj, hH, fun _ ha b hb e => (mem_junkOf.mp (hHJ b hb)).2 j hj (e ▸ ha)⟩

omit [DecidableEq A] [DecidableEq G] in
theorem exists_pair_of_mem {l₁ l₂ : List A} (hlen : l₂.length ≤ l₁.length) {i : A} (hi : i ∈ l₂) :
    ∃ p ∈ l₁.zip l₂, p.2 = i := by
  rw [← List.map_snd_zip hlen] at hi
  exact List.mem_map.mp hi

/-- **After one move** (`OneMove`), with bases without repetitions: every listed agent keeps its base, or it
strictly gains and its new base, without repetitions, lies inside the base of one listed agent `j` (its own for an
addition, the predecessor's in a chain or a ring, the end's for a chain's head) and the junk. -/
theorem move_local {B B' : A → List G} (hB : ∀ k ∈ agents, (B k).Nodup) (h : OneMove v agents goods B B') :
    ∀ i ∈ agents, B' i = B i ∨ ∃ j ∈ agents, (B' i).Nodup ∧
      (∀ g ∈ B' i, g ∈ B j ∨ g ∈ junkOf agents goods B) ∧ value v i (B i) < value v i (B' i) := by
  intro i hi
  rcases h with ⟨x, H, hx, hHne, hHnd, hHJ, hB'x, hB'y⟩ | ⟨x₀, xs, H, hxs, hnd, hag, hH, -, hH0, hHJ, hgain0,
    hpairs, hB'0, hB'p, hB'o⟩ | ⟨w₀, ws, H, -, -, hag, hH, -, hp, hB'o⟩
  · -- an addition
    by_cases hix : i = x
    · subst hix
      refine Or.inr ⟨i, hx, ?_, fun g hg => ?_, ?_⟩
      · rw [hB'x]; exact nodup_append_junk hx (hB i hx) hHnd fun g hg => (hHJ g hg).1
      · rw [hB'x] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inl hg
        · exact Or.inr (hHJ g hg).1
      · rw [hB'x, value_append_eq]
        obtain ⟨h0, t, rfl⟩ := List.exists_cons_of_ne_nil hHne
        have := (hHJ h0 List.mem_cons_self).2
        rw [value_cons]; omega
    · exact Or.inl (hB'y i hix)
  · -- a chain
    by_cases hm : i ∈ x₀ :: xs
    · rcases List.mem_cons.mp hm with rfl | hixs
      · refine Or.inr ⟨(i :: xs).getLast (List.cons_ne_nil _ _),
          hag _ (List.getLast_mem (List.cons_ne_nil _ _)), ?_, fun g hg => ?_, ?_⟩
        · rw [hB'0]; exact (hH i hm).1
        · rw [hB'0] at hg
          rcases hH0 g hg with h1 | h1
          · exact Or.inr h1
          · exact Or.inl h1
        · rw [hB'0]; exact hgain0
      · obtain ⟨p, hp, rfl⟩ := exists_pair_of_mem (l₁ := x₀ :: xs) (by simp) hixs
        have hp1 : p.1 ∈ x₀ :: xs := (List.of_mem_zip hp).1
        refine Or.inr ⟨p.1, hag _ hp1, ?_, fun g hg => ?_, ?_⟩
        · rw [hB'p p hp]
          exact nodup_append_junk (hag _ hp1) (hB _ (hag _ hp1)) (hH _ hm).1 (hHJ _ hixs)
        · rw [hB'p p hp] at hg
          rcases List.mem_append.mp hg with hg | hg
          · exact Or.inl hg
          · exact Or.inr (hHJ _ hixs g hg)
        · rw [hB'p p hp]; exact (hpairs p hp).2
    · exact Or.inl (hB'o i hm)
  · -- a ring
    by_cases hm : i ∈ w₀ :: ws
    · have hm' : i ∈ ws ++ [w₀] := by
        rcases List.mem_cons.mp hm with rfl | h
        · simp
        · exact List.mem_append_left _ h
      obtain ⟨p, hpm, rfl⟩ := exists_pair_of_mem (l₁ := w₀ :: ws) (by simp) hm'
      have hp1 : p.1 ∈ w₀ :: ws := (List.of_mem_zip hpm).1
      obtain ⟨-, hgain, hB'⟩ := hp p hpm
      refine Or.inr ⟨p.1, hag _ hp1, ?_, fun g hg => ?_, ?_⟩
      · rw [hB']
        exact nodup_append_junk (hag _ hp1) (hB _ (hag _ hp1)) (hH _ hm).1 fun g hg => ((hH _ hm).2 g hg).1
      · rw [hB'] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inl hg
        · exact Or.inr ((hH _ hm).2 g hg).1
      · rw [hB']; exact hgain
    · exact Or.inl (hB'o i hm)

omit [DecidableEq A] [DecidableEq G] in
/-- Every element of a list except its last has a successor. -/
theorem exists_succ_of_ne_getLast : ∀ {l : List A} (hne : l ≠ []) {k : A}, k ∈ l → k ≠ l.getLast hne →
    ∃ s, (k, s) ∈ l.zip l.tail
  | [], hne, _, _, _ => absurd rfl hne
  | [a], _, k, hk, hl => by simp at hk; simp [hk] at hl
  | a :: b :: rest, _, k, hk, hl => by
    by_cases hka : k = a
    · exact ⟨b, by simp [hka]⟩
    · have hk' : k ∈ b :: rest := (List.mem_cons.mp hk).resolve_left hka
      have hl' : k ≠ (b :: rest).getLast (List.cons_ne_nil _ _) := by
        rwa [List.getLast_cons (List.cons_ne_nil _ _)] at hl
      obtain ⟨s, hs⟩ := exists_succ_of_ne_getLast (List.cons_ne_nil b rest) hk' hl'
      exact ⟨s, by simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr hs⟩

omit [DecidableEq A] in
/-- **At bases of one good each, one move releases at most one base good**: some agent `r` (the end of a chain)
is the only listed agent whose base good lies in no new base of a listed agent. -/
theorem move_released {v : A → G → Nat} {agents : List A} {goods : List G} {B B' : A → List G} (y : A → G)
    (hy : ∀ k ∈ agents, B k = [y k]) (h : OneMove v agents goods B B') :
    ∃ r, ∀ k ∈ agents, (∀ j ∈ agents, y k ∉ B' j) → k = r := by
  rcases h with ⟨x, H, hx, -, -, -, hB'x, hB'y⟩ | ⟨x₀, xs, H, -, -, hag, -, -, -, -, -, -, -, hB'p, hB'o⟩ |
    ⟨w₀, ws, H, -, -, hag, -, -, hp, hB'o⟩
  · refine ⟨x, fun k hk hno => ?_⟩
    by_cases hkx : k = x
    · exact hkx
    · exact absurd (by rw [hB'y k hkx, hy k hk]; simp) (hno k hk)
  · refine ⟨(x₀ :: xs).getLast (List.cons_ne_nil _ _), fun k hk hno => ?_⟩
    refine Classical.byContradiction fun hkl => ?_
    by_cases hm : k ∈ x₀ :: xs
    · obtain ⟨s, hs⟩ := exists_succ_of_ne_getLast (List.cons_ne_nil x₀ xs) hm hkl
      have hs' : (k, s) ∈ (x₀ :: xs).zip xs := hs
      have hsm : s ∈ x₀ :: xs := List.mem_cons_of_mem _ (List.of_mem_zip hs').2
      exact hno s (hag s hsm) (by rw [hB'p (k, s) hs', hy k hk]; simp)
    · exact hno k hk (by rw [hB'o k hm, hy k hk]; simp)
  · refine ⟨w₀, fun k hk hno => ?_⟩
    refine Classical.byContradiction fun _ => ?_
    by_cases hm : k ∈ w₀ :: ws
    · rw [← List.map_fst_zip (l₁ := w₀ :: ws) (l₂ := ws ++ [w₀]) (by simp)] at hm
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hm
      have hsm : p.2 ∈ w₀ :: ws := by
        have := (List.of_mem_zip hpm).2
        rcases List.mem_append.mp this with h1 | h1
        · exact List.mem_cons_of_mem _ h1
        · simp at h1; simp [h1]
      exact hno p.2 (hag _ hsm) (by rw [(hp p hpm).2.2, hy p.1 hk]; simp)
    · exact hno k hk (by rw [hB'o k hm, hy k hk]; simp)

end afterMove

end OC1Max
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OC1Max.value_le_of_nodup_sub
#print axioms EFX.OC1Max.move_local
#print axioms EFX.OC1Max.exists_succ_of_ne_getLast
#print axioms EFX.OC1Max.move_released
