import EFX.K3Examples

/-!
`#eval` runs algorithm K3ALG (`EFX.K3.algo`, compiled from core Lean) and reports the operation count of its cost-
annotated version (`EFX.K3.algoC`). Not part of the library. Run from `lean/` after `lake build`:

    lake env lean scripts/k3_eval.lean

Expected output: the allocations of `lean/EFX/K3Examples.lean` (owner of each good), each with its count, which is at
most `400 · (n + m + 1)⁴` by `EFX.K3.algoC_cost`.
-/

open EFX K3 Examples

#eval ((List.finRange 5).map (fun g => (algo rot (by decide) g).val), (algoC rot (by decide)).cost)
#eval ((List.finRange 6).map (fun g => (algo rotOwner (by decide) g).val), (algoC rotOwner (by decide)).cost)
#eval ((List.finRange 6).map (fun g => (algo peelOwner (by decide) g).val), (algoC peelOwner (by decide)).cost)
