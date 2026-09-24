import EFX.Rotation

/-!
# Construction LB⁺ and Theorem C (`proofs/lb_last_step.md` §6)

`EFX.LB.lbPlus` is construction LB⁺, with Phase 1's processing order as an argument:
1. Phase 1 in `order` (`phase1`); LB's upgrades (`lbUp`).
2. If the junk fits the slots (`ω ≤ 0`), the completion without owner.
3. Otherwise let `r` be the last agent not upgraded (`lastOut`). Unless the bad case holds (`k*` exists,
   its need chain ends at `r`, and the junk parts of the pairs exposed for `r` are pairwise disjoint), the
   completion with owner `r` and `H = hitSet` (Theorem A).
4. In the bad case, rotate along the need chain from `k*` to `r` (`rotPicks`, `k*` upgraded), and return
   the completion of the rotated pre-allocation without owner if its junk fits its slots, and with owner
   `k*` and `H = hitSet` otherwise (Theorem B).

LB⁺ has no failure case: it always returns an allocation (`G → A`).

- `lbPlus_sound`: **Theorem C**. For every processing order with R1 priority (any choice at every R1 step and
  every insertion step), LB⁺'s allocation is complete, EFX₀ for every additive valuation consistent with the
  rankings (ties allowed), and has at most one bundle of more than two goods.
- `lbPlus_sound_model`: the same in the model's terms (`EFX.Inst.EFX0`).

The agent `d` is a default that only unreachable branches use (LB⁺ with no agent not upgraded).
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-- **Construction LB⁺** (`proofs/lb_last_step.md` §6), with Phase 1 run in `order`. -/
def lbPlus (P : Profile A G) (agents : List A) (goods : List G) (order : List A) (d : A) : G → A :=
  let Y := phase1 P order goods
  let up := lbUp P agents goods Y
  let J := junkList P agents up Y goods
  if J.length ≤ slotSum P agents up Y then complete P agents up Y goods none [] d
  else
    match lastOut up order with
    | none => complete P agents up Y goods none [] d
    | some r =>
      let E := exposedL P agents up Y goods r
      match kstar P agents up Y goods (blkAux P order goods 0) r with
      | some k =>
        if chainEnd P agents up Y order k = r ∧ meet P J E = none then
          -- the bad case: rotate along the need chain from `k` to `r`
          let Y' := rotPicks P Y k (chainFrom P agents up Y k (after order k))
          let J' := junkList P agents (k :: up) Y' goods
          if J'.length ≤ slotSum P agents (k :: up) Y' then complete P agents (k :: up) Y' goods none [] d
          else complete P agents (k :: up) Y' goods (some k)
            (hitSet P J' (exposedL P agents (k :: up) Y' goods k)) d
        else complete P agents up Y goods (some r) (hitSet P J E) d
      | none => complete P agents up Y goods (some r) (hitSet P J E) d

section
variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

/-- Lemma 1 from `OwnerOK`. -/
theorem OwnerOK.completion (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup)
    {w : A} {H : List G} (h : OwnerOK P agents up Y goods w H) (d : A) :
    Completion P agents goods Y up (some w) (complete P agents up Y goods (some w) H d) :=
  complete_some hV hag hgd h.mem h.term h.sub h.fit
    (fun x hx hxw hxu hxa hb hc => h.hit x hx ⟨hxw, hxu, hxa, hb, hc⟩)

/-- Theorem 1′, in the form Theorem C returns it. -/
theorem conclude {o : Option A} {X : G → A} (hV : Valid P agents goods Y up)
    (hC : Completion P agents goods Y up o X) (hgd : goods.Nodup) (d : A) :
    IsAllocation agents goods X ∧ (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods X) ∧
      ∃ w, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hV.sound hC hgd
  refine ⟨hC.alloc, h1, o.getD d, fun j hj hjw => h2 j hj (fun e => hjw ?_)⟩
  rw [e]; rfl

end

/-- **Theorem C (LB⁺ never fails).** For every processing order of Phase 1 with R1 priority (any choice at
every R1 step and every insertion step), LB⁺ returns a complete allocation that is EFX₀ for every additive
valuation consistent with the rankings (each agent values exactly its three goods, `a ≥ b ≥ c > 0`,
`a ≤ b + c`), and in which at most one bundle has more than two goods. -/
theorem lbPlus_sound {P : Profile A G} {agents : List A} {goods : List G} {order : List A} (d : A)
    (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ []) (hWF : WF P agents goods)
    (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents) (hR : R1Prio P order goods) :
    IsAllocation agents goods (lbPlus P agents goods order d) ∧
    (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods (lbPlus P agents goods order d)) ∧
    ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods (lbPlus P agents goods order d) j).length ≤ 2 := by
  have hrun := phase1_run hWF hgd hord hperm hR
  obtain ⟨hV, hUT⟩ := lbState_valid hrun hWF hgd
  have hS : State P agents goods order (phase1 P order goods) (blkAux P order goods 0)
      (fun x => leadB P order goods x = true) (lbUp P agents goods (phase1 P order goods)) :=
    ⟨hrun, hV, hUT, hWF, hag, hgd⟩
  unfold lbPlus
  simp only
  split
  · rename_i hfit
    exact conclude hV (complete_none hV hag hgd hfit) hgd d
  rename_i hfit
  split
  · exact conclude hV (complete_none hV hag hgd (by
      obtain ⟨r, hr⟩ := lastOut_exists hS hne
      rename_i hnone; rw [hnone] at hr; cases hr)) hgd d
  rename_i r hr
  split
  · rename_i k hk
    split
    · rename_i hbad
      obtain ⟨hkr, hm⟩ := hbad
      have hB : BadCase P agents goods order (phase1 P order goods) (blkAux P order goods 0)
          (fun x => leadB P order goods x = true) (lbUp P agents goods (phase1 P order goods)) r k :=
        ⟨hS, hr, hk, hkr, hm⟩
      obtain ⟨hV', hO'⟩ := theoremB hB
      split
      · rename_i hfit'
        exact conclude hV' (complete_none hV' hag hgd hfit') hgd d
      · exact conclude hV' (hO'.completion hV' hag hgd d) hgd d
    · rename_i hnb
      have hO := theoremA hS hr (fun ⟨k', hk', hkr', hm'⟩ => by
        rw [hk] at hk'; cases hk'; exact hnb ⟨hkr', hm'⟩)
      exact conclude hV (hO.completion hV hag hgd d) hgd d
  · rename_i hk
    have hO := theoremA hS hr (fun ⟨k', hk', _⟩ => by rw [hk] at hk'; cases hk')
    exact conclude hV (hO.completion hV hag hgd d) hgd d

/-- **Theorem C, in the model's terms.** Agents `Fin n` (`n ≥ 1`), goods `Fin m`, a ranking profile `P` in
which each agent ranks three distinct goods, and a processing order of all agents with R1 priority. LB⁺'s
allocation is EFX₀ for every additive valuation consistent with `P`, and all its bundles but one have at
most two goods. -/
theorem lbPlus_sound_model {n m : Nat} (P : Profile (Fin n) (Fin m)) (hn : 0 < n)
    (hdist : ∀ i, P.a i ≠ P.b i ∧ P.a i ≠ P.c i ∧ P.b i ≠ P.c i)
    (order : List (Fin n)) (hord : order.Nodup) (hperm : ∀ i, i ∈ order)
    (hR : R1Prio P order (List.finRange m)) :
    (∀ v : Fin n → Fin m → Nat, P.Consistent (List.finRange n) v →
      (Inst.mk n m v).EFX0 (lbPlus P (List.finRange n) (List.finRange m) order ⟨0, hn⟩)) ∧
    ∃ o, ∀ j, j ≠ o →
      finSum m (fun g => if lbPlus P (List.finRange n) (List.finRange m) order ⟨0, hn⟩ g = j then 1 else 0)
        ≤ 2 := by
  obtain ⟨-, h1, o, h2⟩ := lbPlus_sound (P := P) ⟨0, hn⟩ (List.nodup_finRange n)
    (List.nodup_finRange m) (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩))
    (fun i _ => ⟨List.mem_finRange _, List.mem_finRange _, List.mem_finRange _, hdist i⟩) hord
    (fun i => ⟨fun _ => List.mem_finRange i, fun _ => hperm i⟩) hR
  refine ⟨fun v hv => (Inst.efx0_iff (Inst.mk n m v) _).mpr (h1 v hv), o, fun j hj => ?_⟩
  rw [finSum_bundle_eq]
  exact h2 j (List.mem_finRange j) hj

/-! ## Examples (checked by `decide`) -/

/-- A connected core with `n = 3`, `m = 5`: rankings `(0, 2, 3)`, `(2, 1, 4)`, `(0, 2, 1)`. -/
def exampleP3 : Profile Nat Nat :=
  ⟨fun i => [0, 2, 0].getD i 0, fun i => [2, 1, 2].getD i 0, fun i => [3, 4, 1].getD i 0⟩

/-- Phase 1 in the order `1, 0, 2` has R1 priority: agent 1 is inserted (takes good 2), then agents 0 and 2
are R1 steps (goods 0 and 1). -/
example : R1Prio exampleP3 [1, 0, 2] [0, 1, 2, 3, 4] := by decide

/-- On this run LB fails: no agent is a valid owner of the overflow bundle. -/
example : lb exampleP3 [0, 1, 2] [0, 1, 2, 3, 4] [1, 0, 2] 0 = none := by decide

/-- LB⁺ reaches the bad case (`r = 2`, `k* = 1`, need chain `1 → 2`) and rotates: agent 2 takes good 2,
agent 1 is upgraded to `{1, 4}`, and the junk good 3 fits agent 2's slot. The result is
`{0}, {1, 4}, {2, 3}`. -/
example : [0, 1, 2, 3, 4].map (lbPlus exampleP3 [0, 1, 2] [0, 1, 2, 3, 4] [1, 0, 2] 0) = [0, 1, 2, 2, 1] := by
  decide

/-- A connected core with `n = 5`, `m = 8`: rankings `(0, 2, 5)`, `(4, 1, 6)`, `(4, 3, 7)`, `(0, 1, 4)`,
`(4, 2, 3)`. -/
def exampleP5 : Profile Nat Nat :=
  ⟨fun i => [0, 4, 4, 0, 4].getD i 0, fun i => [2, 1, 3, 1, 2].getD i 0, fun i => [5, 6, 7, 4, 3].getD i 0⟩

example : R1Prio exampleP5 [1, 3, 0, 2, 4] [0, 1, 2, 3, 4, 5, 6, 7] := by decide

/-- With Phase 1 in the order `1, 3, 0, 2, 4`, LB⁺ rotates along the need chain `1 → 2 → 4`, and
`k* = 1`, now upgraded, owns the large bundle `{1, 6, 7}` (the same allocation as `src/lbplus.py` on
`proof/lb-last-step`). -/
example : [0, 1, 2, 3, 4, 5, 6, 7].map
    (lbPlus exampleP5 [0, 1, 2, 3, 4] [0, 1, 2, 3, 4, 5, 6, 7] [1, 3, 0, 2, 4] 0) = [3, 1, 0, 4, 2, 4, 1, 1] := by
  decide

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.lbPlus_sound
#print axioms EFX.LB.lbPlus_sound_model
