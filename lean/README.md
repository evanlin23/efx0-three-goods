# Lean formalization

Machine-checked proofs of ledger items, in core Lean 4. The conventions follow
[evanlin23/mrd-efx](https://github.com/evanlin23/mrd-efx) (the formal companion to the paper on at most two
relevant goods), whose model this library reuses verbatim.

- **Core Lean only**: no Mathlib and no other packages (`lakefile.toml` has no `require`).
- **No `sorry`**: the word may not appear in any source file, and the build must be free of errors and warnings.
- **Standard axioms only**: every declaration of the library depends only on `propext`, `Classical.choice`
  and `Quot.sound`. This rules out unfinished proofs, `native_decide` and new axioms.

Toolchain: `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain` (the same as mrd-efx).

## Build and audit

    cd lean && ./check.sh

The script fails if any source file contains the word `sorry`, if the project has a dependency, if the
build reports an error or a warning, if any `#print axioms` certificate lists an axiom other than the three
standard ones, if the number of certificates differs from the number of `#print axioms` commands, or if any
declaration of the library (certified or not; `CheckAxioms.lean`) depends on another axiom. On success the last
line is

    CHECK PASSED: 8 audited statements, 21 theorems, standard axioms only

CI runs it on every pull request (job `lean` in `.github/workflows/verify.yml`). In Claude Code on the web the
session-start hook installs the toolchain (from GitHub when `release.lean-lang.org` is unreachable).

To check one theorem interactively: `lake build`, then put `import EFX` and `#print axioms EFX.peel` in a scratch
file and run `lake env lean scratch.lean`.

## Trusted base

The definitions a reader must accept, from `EFX/Model.lean` (copied from `MRD.lean` in mrd-efx `v1.2.0`, namespace
`MRD` renamed to `EFX`):

    def finSum : (k : Nat) → (Fin k → Nat) → Nat
      | 0, _ => 0
      | k+1, f => finSum k (fun i => f i.castSucc) + f (Fin.last k)

    structure Inst where
      n : Nat
      m : Nat
      v : Fin n → Fin m → Nat

    abbrev Alloc := Fin I.m → Fin I.n

    def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
      finSum I.m (fun g => if X g = j ∧ ex ≠ some g then I.v i g else 0)

    def EFX0 (X : I.Alloc) : Prop :=
      ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
        I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

    def numRelevant (I : Inst) (i : Fin I.n) : Nat := finSum I.m (fun g => if 0 < I.v i g then 1 else 0)

Values are natural numbers. EFX₀ only compares sums of values, so rational instances reduce to these by scaling
each agent's values by a common denominator.

## Contents

- `EFX/Model.lean`: the trusted base above.
- `EFX/Lists.lean`: the same notions over explicit lists of agents and goods (`value`, `bundle`, `EFX0L`), which
  suit arguments that remove agents or goods; list lemmas; `favorite`, an agent's most valued remaining good.
- `EFX/Peeling.lean`: `EFX.peel`, peeling rule R1.
- `EFX/SerialDictatorship.lean`: `EFX.serialDictatorship`, L2c over lists.
- `EFX/Bridge.lean`: over `List.finRange` the list notions equal the model's (`finSum_eq_sum`, `bundleVal_none`,
  `bundleVal_some`, `efx0_iff`, `numRelevant_eq`); `EFX.exists_efx0_of_count`, L2c in the model's terms.
- `CheckAxioms.lean`: the all-declarations axiom check.

## Correspondence with the ledger

Every Lean name below has a `#print axioms` certificate in the build. `tools/check_ledger.py` checks that every
name in the ledger's Lean column has one.

| Ledger | Statement | Lean (file : name) |
|---|---|---|
| L2 | Peeling rule R1: `i` takes its favorite remaining good `p` with `v_i(p) ≥ v_i(remaining goods)`; the rest has an EFX₀ allocation ⟹ so does everything | Peeling : `EFX.peel` (over lists) |
| L2c | `\|R_i\| ≤ 2` for all `i` ⟹ an EFX₀ allocation exists (serial dictatorship) | Bridge : `EFX.exists_efx0_of_count`; SerialDictatorship : `EFX.serialDictatorship` |
| — | The list layer agrees with the model | Bridge : `EFX.Inst.efx0_iff` |

mrd-efx proves a stronger form of L2c (`MRD.main_theorem_L`: in addition, all bundles but one have at most one
good), and extends it to monotone valuations.

## Not formalized

- Peeling rule R2 (a bundle of private goods), L3 (junk goods and envy cycles), and everything from L4 on.
- `EFX.peel` is stated over lists: removing an agent and a good changes the index types `Fin n`, `Fin m`, so a
  model-level statement needs sub-instances. `EFX.Inst.efx0_iff` connects the two for the full instance.
- Real-valued utilities (natural numbers in Lean, as in mrd-efx).
