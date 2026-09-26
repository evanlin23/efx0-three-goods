import EFX.K3Examples

/-!
The instances of Examples 2 and 3 of `paper/k3/long.tex`, and of its remark on a repeated good in `HitSet`,
evaluated by Lean itself. Not part of the library (it lives outside `lean/`). Run from `lean/` after `lake build`:

    lake env lean ../paper/k3/examples/lean_examples.lean

`#eval` prints the owner of each good under `EFX.K3.algo` (the program whose correctness and running time are
machine-checked) and the operation count of `EFX.K3.algoC`. The two theorems check the outputs of Examples 2 and 3
by `decide`, as `lean/EFX/K3Examples.lean` does for its instances (the kernel evaluates the specification
`EFX.K3.algoSpec`, which `EFX.K3.algo_eq_spec` equates with `EFX.K3.algo`). The output is recorded in
`lean_examples_output.txt`.
-/

open EFX K3 Examples

/-- Example 2 (owner `r`): agent 4 values only good 5 and is peeled. -/
def ex1 : Inst := mkInst 5 9 [[0, 0, 6, 0, 5, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 5, 4, 0], [0, 7, 9, 5, 0, 0, 0, 0, 0],
  [0, 7, 9, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 6, 0, 0, 0]]

/-- Example 3 (a rotation, owner `k*`). -/
def ex2 : Inst := mkInst 4 8 [[3, 0, 8, 0, 0, 7, 0, 0], [0, 4, 0, 0, 8, 0, 6, 0], [0, 0, 0, 3, 9, 0, 0, 8],
  [4, 0, 0, 0, 9, 0, 0, 6]]

/-- The remark on a repeated good in `HitSet`. -/
def exdup : Inst := mkInst 4 9 [[3, 4, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 4, 2, 0, 0, 0, 0], [3, 0, 0, 0, 0, 4, 2, 0, 0],
  [3, 0, 0, 0, 0, 0, 0, 4, 2]]

#eval ((List.finRange 9).map (fun g => (algo ex1 (by decide) g).val), (algoC ex1 (by decide)).cost)
#eval ((List.finRange 8).map (fun g => (algo ex2 (by decide) g).val), (algoC ex2 (by decide)).cost)
#eval ((List.finRange 9).map (fun g => (algo exdup (by decide) g).val), (algoC exdup (by decide)).cost)

theorem ex1_spec :
    (List.finRange 9).map (fun g => (algoSpec ex1 (by decide) g).val) = [1, 2, 0, 2, 3, 4, 1, 1, 3] := by
  decide

theorem ex2_spec :
    (List.finRange 8).map (fun g => (algoSpec ex2 (by decide) g).val) = [3, 1, 0, 1, 2, 0, 1, 3] := by
  decide
