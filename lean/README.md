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

    CHECK PASSED: 21 audited statements, 54 theorems, standard axioms only

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
- `EFX/PeelingR2.lean`: `EFX.peelBundle`, the general peeling step (agent `i` leaves with a bundle `P` it values at
  least as much as all remaining goods, and `P` minus any one good is worthless to everyone else); its instances
  `EFX.peelR2`, peeling rule R2, and `EFX.peelEmpty`, rule R1 when nothing relevant to `i` remains (`P = ∅`).
- `EFX/SerialDictatorship.lean`: `EFX.serialDictatorship`, L2c over lists.
- `EFX/Bridge.lean`: over `List.finRange` the list notions equal the model's (`finSum_eq_sum`, `bundleVal_none`,
  `bundleVal_some`, `efx0_iff`, `numRelevant_eq`); `EFX.exists_efx0_of_count`, L2c in the model's terms.
- `EFX/Junk.lean`: L3. `EFX.rotate_efx0` (moving bundles along a permutation of the agents, each agent weakly
  gaining, preserves EFX₀); `EFX.exists_unenvied` (envy-cycle elimination: some EFX₀ allocation has an agent
  nobody envies; each rotation raises the bounded welfare, and a cycle exists by pigeonhole); `EFX.junkToSource`
  and `EFX.junk` (goods worthless to all go to that agent); `EFX.Inst.exists_efx0_of_junk`, L3 in the model's
  terms.
- `EFX/TwoOwnGoods.lean`: L8. `EFX.envyFree_of_two_own` and `EFX.safe_of_two_own` over lists,
  `EFX.Inst.safe_of_two_own` in the model's terms, `EFX.Inst.efx0_of_two_own` (every agent holds two own goods ⟹
  EFX₀), and `EFX.balance_needed` (a top-heavy agent holding two own goods can be unsafe).
- `CheckAxioms.lean`: the all-declarations axiom check.

## Correspondence with the ledger

Every Lean name below has a `#print axioms` certificate in the build. `tools/check_ledger.py` checks that every
name in the ledger's Lean column has one.

| Ledger | Statement | Lean (file : name) |
|---|---|---|
| L2 | Peeling rule R1: `i` takes its favorite remaining good `p` with `v_i(p) ≥ v_i(remaining goods)`; the rest has an EFX₀ allocation ⟹ so does everything | Peeling : `EFX.peel` (over lists) |
| L2 | Peeling rule R1 with `P = ∅`: no remaining good is relevant to `i`; `i` leaves with nothing | PeelingR2 : `EFX.peelEmpty` (over lists) |
| L2 | Peeling rule R2: `i` takes `P`, the goods relevant to `i` and to no other remaining agent, with `v_i(P) ≥ v_i(R_i \ P)`; the rest has an EFX₀ allocation ⟹ so does everything. The written hypothesis `\|P\| ≥ 2` is not needed and not assumed | PeelingR2 : `EFX.peelR2` (over lists) |
| L2 | The proof of L2: `v_i(P) ≥ v_i(remaining goods)` and `P` minus any one good worthless to every other agent ⟹ peeling `(i, P)` preserves EFX₀ | PeelingR2 : `EFX.peelBundle` (over lists) |
| L2c | `\|R_i\| ≤ 2` for all `i` ⟹ an EFX₀ allocation exists (serial dictatorship) | Bridge : `EFX.exists_efx0_of_count`; SerialDictatorship : `EFX.serialDictatorship` |
| L3 | Goods relevant to no agent: if the other goods have an EFX₀ allocation, so do all goods | Junk : `EFX.junk` (over lists), `EFX.Inst.exists_efx0_of_junk` (model: an allocation that is EFX₀ except possibly when the removed good is valued by nobody ⟹ an EFX₀ allocation exists) |
| L3 | Rotation along a permutation of the agents, each agent weakly gaining, preserves EFX₀ | Junk : `EFX.rotate_efx0` (over lists) |
| L3 | Envy-cycle elimination: from an EFX₀ allocation, rotating envy cycles reaches an EFX₀ allocation with an agent envied by nobody | Junk : `EFX.exists_unenvied` (over lists) |
| L8 | An agent with at most three relevant goods, `2 v_i(g) ≤ v_i(M)` for all `g` (i.e. `a ≤ b + c`; core agents have `a < b + c`), holding at least two of them, envies nobody and so is safe | TwoOwnGoods : `EFX.Inst.safe_of_two_own` (model), `EFX.envyFree_of_two_own` (over lists) |
| L8 | If every agent is as above, the allocation is EFX₀ (how L8 solves β = 1 cores) | TwoOwnGoods : `EFX.Inst.efx0_of_two_own` |
| L8 | The balance hypothesis is necessary: a top-heavy agent holding two of its goods can be unsafe | TwoOwnGoods : `EFX.balance_needed` |
| — | The list layer agrees with the model | Bridge : `EFX.Inst.efx0_iff` |

mrd-efx proves a stronger form of L2c (`MRD.main_theorem_L`: in addition, all bundles but one have at most one
good), and extends it to monotone valuations.

## Not formalized

- The second half of L8: that a β = 1 core has an allocation giving every agent two of its own goods (its private
  good and the next shared good around the cycle). The graph structure of cores (L4, L6, L7, L11) is not
  formalized.
- L1, L4–L7 and L9–L11, and the reduction to cores (CORE: iterate L2 and L3 until nothing applies).
- The peeling theorems are stated over lists: removing an agent and its goods changes the index types `Fin n`, `Fin m`,
  so a model-level statement needs sub-instances. `EFX.Inst.efx0_iff` connects the two for the full instance.
- Real-valued utilities (natural numbers in Lean, as in mrd-efx).
