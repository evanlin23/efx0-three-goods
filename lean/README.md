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

The script fails if any source file contains the word `sorry`, if any source file or `lakefile.toml` uses a
debug option, metaprogramming or unsafe code (`debug.`, `import Lean`, `run_cmd`, `run_meta`, `run_elab`,
`addDecl`, `implemented_by`, `extern`, `unsafe`), if the project has a dependency, if the build reports an error
or a warning, if any `#print axioms` certificate lists an axiom other than the three standard ones (a certificate
may also list none), if the number of certificates differs from the number of `#print axioms` commands, if any
declaration of the library (certified or not; `CheckAxioms.lean`) depends on another axiom, or if Lean's replay
checker `lake env leanchecker --fresh EFX` rejects the library (it re-checks every declaration, Init included,
in a fresh kernel; about a minute). The last two checks were added after the `formal/audit` review (PR #19)
showed that a declaration added under `set_option debug.skipKernelTC true` is never kernel-checked, yet builds
without warnings and has no axioms for `#print axioms` or `CheckAxioms.lean` to report; the tripwire refuses the
option and the replay checker rejects such a declaration. On success the last line is

    CHECK PASSED: 292 audited statements, 788 theorems, standard axioms only

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

In `EFX/Model.lean` the docstring of `numRelevant` reads "The counting form of 2-relevance used in the paper:
`|R_i| ≤ 2`": it is inherited verbatim from mrd-efx, whose theorem is about two goods. The definition counts the
goods `g` with `0 < v i g` and has nothing to do with the bound 2 (`Model.lean` is left untouched, as copied).

Values are natural numbers. EFX₀ only compares sums of values, so rational instances reduce to these by scaling
each agent's values by a common denominator; nonnegative real values reduce to them by L12 (`proofs/real_values.md`),
which is machine-checked: see the next section.

### Values in an ordered type (`EFX/RealValues.lean`)

TARGET and conjecture D are also stated for values in any type `V` satisfying the class `EFX.OrderedValue`, and the
model is mirrored for such values (`Model.lean` is unchanged):

    class OrderedValue (V : Type) extends Zero V, Add V, LE V where
      add_assoc : ∀ a b c : V, a + b + c = a + (b + c)
      add_comm : ∀ a b : V, a + b = b + a
      zero_add : ∀ a : V, 0 + a = a
      le_refl : ∀ a : V, a ≤ a
      le_trans : ∀ a b c : V, a ≤ b → b ≤ c → a ≤ c
      le_antisymm : ∀ a b : V, a ≤ b → b ≤ a → a = b
      le_total : ∀ a b : V, a ≤ b ∨ b ≤ a
      add_le_add_iff_right : ∀ a b c : V, a ≤ b ↔ a + c ≤ b + c

    def finSumO : (k : Nat) → (Fin k → V) → V            -- as finSum
    structure OInst (V : Type) where (n m : Nat) (v : Fin n → Fin m → V)
    def OInst.bundleVal, OInst.EFX0                         -- as Inst.bundleVal, Inst.EFX0, word for word
    def OInst.numRelevant (i : Fin I.n) : Nat := finSum I.m (fun g => if ¬ I.v i g ≤ 0 then 1 else 0)

These are the axioms of a linearly ordered cancellative additive commutative monoid. `ℝ≥0`, `ℚ≥0` and `ℕ` satisfy
them (so do `ℝ`, `ℚ`, `ℤ`); core Lean has no `ℝ`, so the `ℝ≥0` instance is the textbook fact, while the instances
for `Nat` and `Int` are in the file. Nonnegativity is not an axiom but a hypothesis of the theorems
(`∀ i g, 0 ≤ I.v i g`), which keeps the class to the order-and-sum axioms and lets `Int` (or `ℝ`) values with that
hypothesis in. A good is relevant iff `¬ v i g ≤ 0` (that is, `v i g > 0`), and balance is
`I.v i g + I.v i g ≤ finSumO I.m (I.v i)`. At `V = Nat` the mirrored model is the trusted base
(`EFX.efx0_nat_iff`, `EFX.numRelevant_nat`), and `EFX.target_of_ordered`, `EFX.corollaryD_of_ordered` (the
specializations) have exactly the types of `EFX.target`, `EFX.LB.corollaryD` (checked by `rfl` in the file).

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
- `EFX/LBSound.lean`: S2.S, abstract form. `EFX.LB.Profile` (rankings `a i`, `b i`, `c i`; consistent values `a ≥ b ≥ c > 0`, ties allowed), `Profile.Consistent`
  (additive valuations consistent with them, balanced), `Profile.NA`, and `EFX.LB.Hyp`, the properties of LB's
  output that the proof of Theorem 1 uses (picks, invariant (I1), upgraded, frozen and slot-filled bundles, the
  owner constraint). `EFX.LB.Hyp.efx0` (EFX₀ for every consistent valuation), `EFX.LB.Hyp.length_le_two` (every
  bundle but the owner's has at most two goods), `EFX.LB.sound` (both, in the model's terms).
- `EFX/LBRun.lean`: S2.S for construction LB itself. `EFX.LB.lb` defines LB as `src/construct.py` does, with
  Phase 1's processing order as an argument (LB's adaptive order is one choice); `EFX.LB.phase1_spec` (Phase 1
  satisfies (I1)); `EFX.LB.lb_hyp` (every output satisfies `Hyp`); `EFX.LB.lb_sound`, `EFX.LB.lb_sound_model`
  (Theorem 1: every output is EFX₀ for every consistent valuation and has at most one bundle of more than two
  goods).
- `scripts/lb_crosscheck.py`: evidence, not proof, that `EFX.LB.lb` computes what `src/construct.py` computes
  (runs both on every ranking profile of the given connected cores, with Python's Phase 1 order, and compares).
- `EFX/PreAlloc.lean`, `EFX/Blocks.lean`, `EFX/OwnerR.lean`, `EFX/Rotation.lean`, `EFX/LBPlus.lean`,
  `EFX/CorollaryD.lean`, `EFX/Target.lean`: construction LB⁺, conjecture D and TARGET
  (`proofs/lb_last_step.md`); see the section below.
- `EFX/K4Reduction.lean`: the k = 4 core reduction (K4.CORE, `k4/SCOUT.md` §2): `EFX.IsCore4` and
  `EFX.core_reduction4`, reusing the k = 3 induction's peeling and junk steps unchanged; L6 (`EFX.efx0_split`)
  restricts it to connected cores (`EFX.Connected`, `EFX.core_reduction4_conn`).
- `EFX/K4Ties.lean`: ties reduce to strict profiles at k = 4 (K4.TIE): `EFX.Strict`, `EFX.tieBreak` (the
  perturbation `2^|M| · v + w`), `EFX.tie_reduction`, `EFX.core_reduction4_strict`.
- `EFX/PreAllocK.lean`: LB₄'s pre-allocations (`k4/lb4.md` §1–§2, ledger K4.LB4.S), for any number of
  relevant goods (values in ℕ, as the model): bases and needs of any size (`EFX.LB4.Needs`, `Valid`, `Completion`, `OC`, `ownerNeeds`,
  `SoundCompletion`); Theorem 1′₄ (`EFX.LB4.Valid.sound`, `EFX.LB4.Valid.sound_ownerNeeds`); the counting
  (`EFX.LB4.numFrozen_eq`, `EFX.LB4.omega_eq`, `EFX.LB4.complete_none_exists`,
  `EFX.LB4.Completion.owner_length`); Lemma 2₄ (`EFX.LB4.selfProtect`, `EFX.LB4.selfProtect_seq`, and
  `EFX.LB4.selfProtect_five`: the value argument fails with five relevant goods, and `EFX.LB4.Ex5.counterexample`:
  an instance of every other hypothesis of `EFX.LB4.selfProtect` in which the agent is threatened); Lemma 3₄ (`EFX.LB4.ownerSearch_exact_base`,
  `EFX.LB4.ownerSearch_exact`); the D2 shape and the chain to K4.D and TARGET₄ (`EFX.LB4.Completion.length_le_two`,
  `EFX.LB4.SoundCompletion.efx0_d2`, `EFX.LB4.sound_model`, `EFX.LB4.k4D_of_completion`,
  `EFX.LB4.target4_of_completions`); non-vacuity examples by `decide` (`EFX.LB4.Ex.sound`, owner's needs from its
  bundle; `EFX.LB4.ExB.sound`, `Valid.sound`'s hypotheses with a frozen agent, a two-good base, a filled slot
  and a three-good owner's bundle).
- `EFX/LB4R.lean`: construction LB₄ʳ (`k4/lb4.md` §5 with §2) and Theorem C₄ (ledger K4.C4.FRAME): states `EFX.LB4R.LState`
  (bases, picks, marked agents; needs derived by `EFX.LB4R.needsOf`), `EFX.LB4R.phase1`, `EFX.LB4R.UpRun`,
  `EFX.LB4R.RotStep`, `EFX.LB4R.Output`, `EFX.LB4R.Succeeds`; the statements `EFX.LB4R.TheoremC4` and
  `EFX.LB4R.TheoremC4index` (C₄ as stated is false: ledger K4.C4.C, by Proposition H, `k4/c4.md` §7, K4.C4.R); the invariant
  `EFX.LB4R.Inv` of reachable states and `EFX.LB4R.sound_of_succeeds` (every output is a sound completion). C₄∃
  (`EFX.LB4R.TheoremC4exists`: every strict profile of every k = 4 core has a sound completion) ⟺ K4.D on strict
  cores (`EFX.LB4R.C4exists_iff`, with `EFX.LB4R.sound_of_d2`); the frame's content is the equivalence and the
  LB₄ʳ ⇒ C₄∃ direction (`EFX.LB4R.C4exists_of_C4`), with `EFX.LB4R.target4_of_C4exists`,
  `EFX.LB4R.k4D_of_C4exists`, the connected form `EFX.LB4R.C4existsConn` (`EFX.LB4R.conn_of_C4exists`,
  `EFX.LB4R.target4_of_C4existsConn`), and `EFX.LB4R.k4D_of_C4index`, `EFX.LB4R.target4_of_C4index`,
  `EFX.LB4R.target4_of_C4` (C₄ as a hypothesis). The choices where the prose leaves room are listed in the module doc,
  the single source for them.
- `EFX/LB4RExamples.lean`: LB₄ʳ is not vacuous (from the audit of PR #35; not a ledger item): two certified k = 4
  cores on which `EFX.LB4R.Succeeds` holds, checked by `decide`: `EFX.LB4R.Examples.W1.succeeds` (index order, no
  upgrades, no rotation, an owner with four goods; also `W1.sound_direct`, `W1.sound_pr`) and
  `EFX.LB4R.Examples.W2.succeeds` (one `RotStep` along the chain [0, 1] with O = {0}, `W2.rotStep`; the rotated
  one-good agent owns three goods).
- `EFX/K4One.lean`: TARGET₄ with at most one 4-good agent (ledger K4.ONE.FRAME). `EFX.AtMostOne4`;
  `EFX.atMostOne4_sublist` (a sub-instance adds no 4-good agent); `EFX.core_reduction4_conn_of` and
  `EFX.core_reduction4_mixed_of` (K4.CORE for any class of instances closed under sub-instances: the proof of
  `EFX.core_reduction4_conn` with the class carried through each recursive call); `EFX.core_reduction4_one_strict`,
  `EFX.target4one_of_strict_cores` (with K4.TIE); `EFX.LB4R.C4existsOne` (C₄∃ for connected strict cores with at
  most one 4-good agent), `EFX.LB4R.C4existsOne_iff`, `EFX.LB4R.C4existsOne_of_C4exists`,
  `EFX.LB4R.C4existsOne_of_C4existsConn` (with `EFX.LB4R.sound_of_three_cores`: Corollary D covers the cores whose
  agents all have three goods) and `EFX.LB4R.target4one_of_C4existsOne` (`C4existsOne` as a hypothesis).
- `EFX/LB4RRun.lean`: runs of Phase 1 for LB₄ʳ (`k4/c4.md` §1, `proofs/lb_last_step.md` §1). `EFX.LB4R.PhaseRun` (any
  run, by the position of each step: favourite remaining good, P-step or insertion step) and `EFX.LB4R.phase1_phaseRun`
  (LB₄ʳ's Phase 1 with LB's key and any τ is one); (I1) `EFX.LB4R.PhaseRun.pickedBefore_of_prefers`, (I3)
  `EFX.LB4R.PhaseRun.insAt_of_not_lost`, (B2) `EFX.LB4R.PhaseRun.b2`, blocks (`EFX.LB4R.SameBlock`,
  `EFX.LB4R.exists_leader`, `EFX.LB4R.leader_unique`); after envy-free upgrades (`EFX.LB4R.AfterUp`): envy-free bases
  (`EFX.LB4R.upRun_efBase`), `r` (`EFX.LB4R.IsLast`) with (A1) `EFX.LB4R.AfterUp.last_pick_free`, (A2)
  `EFX.LB4R.AfterUp.last_block`, need chains (A4) `EFX.LB4R.AfterUp.exists_chain`, and upgrades terminate
  (`EFX.LB4R.upRun_exists`).
- `EFX/K4C4AB.lean`: `k4/c4.md` §2–§4 for LB₄ʳ's states (ledger K4.C4.AB.L). Exposure (`EFX.LB4R.Wl`, `EFX.LB4R.Exposed`,
  `EFX.LB4R.Threatened.mono`); Lemma E (`EFX.LB4R.lemmaE`, `EFX.LB4R.lemmaE_three`, `EFX.LB4R.lemmaE_four`); Lemma R
  for LB₄ʳ's rotations (`EFX.LB4R.rotate_Wl`, `EFX.LB4R.needsOf_rotate`, `EFX.LB4R.rotate_valid`,
  `EFX.LB4R.rotate_exposed`, `EFX.LB4R.rotate_exposed_chain`, `EFX.LB4R.rotate_last_not_exposed`); Theorem B₄
  (`EFX.LB4R.theoremB4`, `EFX.LB4R.theoremB4c`); Theorem A₄ (`EFX.LB4R.theoremA4`, `EFX.LB4R.theoremA4_output`, with
  `EFX.LB4R.BadCase`, the completion `EFX.LB4R.placeH` and LB⁺'s terminals `EFX.LB4R.AfterUp.terminals`); Corollary
  C₄⁰ (`EFX.LB4R.corollaryC40'`, as `k4/c4.md` states it at 96ff1d0: `ω ≤ 0` or the hypotheses of A₄ and B₄;
  `EFX.LB4R.corollaryC40`) and `EFX.LB4R.succeeds_of_three` (LB₄ʳ never fails on a strict profile of a core whose
  agents all have three goods). Theorems B₄ʷ, A₄ᵀ, A₄⁺ are not formalized.
- `EFX/C4min.lean`: the space 𝒫 of `k4/c4x.md` §1 and conjecture C₄ᵐⁱⁿ (§5; ledger K4.C4MIN.FRAME): `EFX.C4min.InP`
  (bases of at most two goods inside `R_i`, value-based needs `EFX.C4min.vbNeeds`, (V1), (V2)), `EFX.C4min.nFrozen`,
  `EFX.C4min.MinFrozen`, `EFX.C4min.Completable` (a `SoundCompletion` exists), `EFX.C4min.DeficitLE` and
  `EFX.C4min.RemovalOnly`; the statements `EFX.C4min.TheoremC4min`, `EFX.C4min.TheoremC4minRO` and their connected forms;
  `EFX.C4min.completable_of_removalOnly`, `EFX.C4min.inP_phase1`, `EFX.C4min.exists_minFrozen`, and the reductions to
  C₄∃, K4.D and TARGET₄ (`EFX.C4min.C4exists_of_C4min`, `EFX.C4min.target4_of_C4min`, `EFX.C4min.target4_of_C4minConn`,
  and the removal-only forms). The choices where the prose leaves room are listed in the module doc.
- `EFX/K3Pareto.lean`, `EFX/K3Theorem.lean`: Theorem K3 (`k4/c4x.md` §3; ledger K4.C4X.K3.LEAN): Pareto-maximality
  (`EFX.C4min.ParetoMax`), the transfer move and its instances (`EFX.C4min.transfer_inP_dominates`: from any `P ∈ 𝒫` the
  move stays in 𝒫 and Pareto-dominates; `transfer_move`, `cycle_move`, `path_move` at a Pareto-maximum), Lemmas U, C, R,
  E (with `EFX.C4min.exposed_top`), O, the walk (`EFX.C4min.exists_labelCycle`), the shortening
  (`EFX.C4min.LabelCycle.disjoint`), the cycle move (`EFX.C4min.cycle_contra`), `EFX.C4min.theoremK3_owner` (`ω ≤ 0`, or
  a terminal owner with Lemma O's removal-only completion), `EFX.C4min.theoremK3`, and a
  second proof of D for k = 3 cores and of TARGET (`EFX.C4min.corollaryD_K3`, `EFX.C4min.target_K3`), independent of
  LB⁺; `EFX.C4min.sigma_nonneg` is L4's bound `m ≤ 2n` for k = 3 cores.
- `EFX/C4minExamples.lean`: non-vacuity by `decide` (part of K4.C4MIN.FRAME): a strict k = 3 core with a min-frozen,
  Pareto-maximal, completable pre-allocation with two frozen agents and `ω = −1` (every base map checked,
  `EFX.C4min.Ex3.c4min`, `EFX.C4min.Ex3.k3_hyps`); a k = 3 core with a Pareto-maximal pre-allocation with `ω = 1`, where
  Theorem K3's terminal owner is reached (4,096 base maps checked, `EFX.C4min.ExOmega.k3_owner`); and the k = 4 core W1
  with a min-frozen pre-allocation that is removal-only completable with an owner (`EFX.C4min.ExW.c4min`).
- `EFX/K3Algo.lean`, `EFX/Timed.lean`, `EFX/K3CostLB.lean`, `EFX/K3Cost.lean`, `EFX/K3CostBound.lean`,
  `EFX/K3Examples.lean`: algorithm K3ALG, a polynomial-time algorithm for k = 3 with its running time
  (`proofs/k3_algorithm.md`; ledger K3.ALG, K3.ALG.TIME).
  - `K3Algo`: the specification. `EFX.K3.reduce` peels by R1, or by R1 with `P = ∅`, taking the first agent to
    which the rule applies. The rankings are computed (`EFX.K3.sort3`, `EFX.K3.profileOf`), and LB⁺ runs with
    `r1Order` (`EFX.K3.lbStage`). Theorems: `EFX.K3.reduce_sound`, `EFX.K3.algoSpec_efx0`.
  - `Timed`: the cost model. `EFX.Timed` pairs a value with an operation count. It provides list operations with
    value and cost lemmas, and tables (`EFX.Timed.mkTable`: arrays filled once).
  - `K3CostLB`: every step of LB⁺ as a counted program, whose value lemma says it computes the existing definition.
  - `K3Cost`: `EFX.K3.algoC`, the algorithm as a counted program; `EFX.K3.algo`, its value, the algorithm;
    `EFX.K3.algo_eq_spec` and `EFX.K3.algo_efx0`.
  - `K3CostBound`: the running-time theorem `EFX.K3.algoC_cost`, at most `400 (n + m + 1)⁴` counted operations
    on every instance.
  - `K3Examples`: three instances checked by `decide`.
  `scripts/k3_eval.lean` runs `algo` and prints the count by `#eval`.
- `EFX/RealValues.lean`: L12 (`proofs/real_values.md`) and TARGET and D over any `EFX.OrderedValue`. The value
  class and mirrored model above; `EFX.Agree` (same answer to every comparison between two subset sums);
  `EFX.OrderedValue.tri_le_iff` (for three positive values, every such comparison is decided by twelve basic
  comparisons, after cancelling common goods); `EFX.Pat.table` (every consistent pattern of those twelve answers is
  realized by one of the 31 permutations of the representatives of L12, checked by `decide +kernel`);
  `EFX.OrderedValue.tri_rep`, `EFX.OrderedValue.exists_agree`, `EFX.l12`; the transfers `EFX.efx0_iff_of_agree`,
  `EFX.numRelevant_eq_of_agree`, `EFX.OrderedValue.balanced_iff_of_agree`; `EFX.target_ordered`,
  `EFX.corollaryD_ordered`.
- `EFX/Audit.lean`: red-team audit (`formal/audit`): TARGET and D restated independently (bundles as lists that
  partition the goods, a hand-written sum; written before the model was read), derived from `EFX.target` and
  `EFX.LB.corollaryD`, with non-vacuity examples checked by `decide`.
- `scripts/audit_kernel.sh`: fresh-clone build, `leanchecker --fresh`, a second kernel (lean4export + nanoda) and
  negative controls; log in `results/audit_kernel.log`.
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
| S2.S | Theorem 1, abstract form: an allocation built from picks satisfying (I1), with upgraded, frozen and slot-filled bundles and an owner bundle satisfying the owner constraint (`EFX.LB.Hyp`), is EFX₀ for every additive valuation consistent with the rankings, and every bundle but the owner's has at most two goods | LBSound : `EFX.LB.Hyp.efx0`, `EFX.LB.Hyp.length_le_two` (over lists), `EFX.LB.sound` (model) |
| S2.S | Theorem 1: every allocation construction LB returns (Phase 1 in any processing order) is EFX₀ for every additive valuation consistent with the rankings, and at most one of its bundles has more than two goods | LBRun : `EFX.LB.lb_sound` (over lists), `EFX.LB.lb_sound_model` (model); `EFX.LB.lb_hyp` (LB's output satisfies `Hyp`), `EFX.LB.phase1_spec` (Phase 1 satisfies (I1)) |
| S2.R | Theorem A: after Phase 1 (any order with R1 priority) and LB's upgrades (any order), if the last agent not upgraded, `r`, is not a valid owner (no `H` satisfies Lemma 1's condition), then the bad case holds: `k*` exists and is frozen, the junk parts of the exposed pairs are disjoint, and every need chain from `k*` ends at `r` | OwnerR : `EFX.LB.theoremA_invalid`, `EFX.LB.validOwner_iff`, `EFX.LB.theoremA`; `EFX.LB.lastOut_terminal` (A1), `EFX.LB.exposed_lead` (A3), `EFX.LB.chainEnd_spec` (A4); Blocks : `EFX.LB.phase1_run`, `EFX.LB.upFinal_valid` and LBPlus : `EFX.LB.state_of_final` (any run of Phase 1 and the upgrades gives the state these theorems assume) |
| S2.LB+ | Theorem 1′: every completion of a valid pre-allocation satisfying the owner constraint is EFX₀ for every consistent valuation, and only the owner's bundle can exceed two goods | PreAlloc : `EFX.LB.Valid.sound` (via `EFX.LB.HypNA.efx0`); Lemma 1: `EFX.LB.complete_some`, `EFX.LB.complete_none` |
| S2.LB+ | Theorem B: in the bad case, the rotation along any need chain from `k*` to `r` gives a valid pre-allocation of which `k*` is a valid owner | Rotation : `EFX.LB.theoremB` |
| S2.LB+ | Theorem C: for every processing order of Phase 1 with R1 priority, every upgrade order, every need chain and every completion satisfying (OC), LB⁺'s output is a complete allocation, EFX₀ for every consistent valuation, with at most one bundle of more than two goods; an output always exists, and in the rotation branch every need chain from `k*` to `r` gives one | LBPlus : `EFX.LB.lbPlusRun_sound`, `EFX.LB.lbPlusOut_exists`, `EFX.LB.lbPlusOut_exists_chain`, `EFX.LB.lbPlus_sound` (the computable LB⁺, over lists), `EFX.LB.lbPlus_sound_model` (model); Blocks : `EFX.LB.phase1_run`, `EFX.LB.upFinal_valid` |
| D | Corollary D: every instance in which every agent values exactly three goods and is balanced has an EFX₀ allocation with at most one bundle of more than two goods | CorollaryD : `EFX.LB.corollaryD` (model), `EFX.LB.corollaryD_lists` (over lists), values in ℕ; RealValues : `EFX.corollaryD_ordered` (values in any `EFX.OrderedValue`, e.g. ℝ≥0, via L12), `EFX.corollaryD_of_ordered` (its specialization to ℕ) |
| T | CORE: if every core with at most `N` agents has an EFX₀ allocation, so does every instance with at most `N` agents and `\|R_i\| ≤ 3` (L3, R1, R2 by induction) | Target : `EFX.core_reduction` (over lists) |
| K4.CORE | k = 4 CORE: if every (connected) k = 4 core (`EFX.IsCore4`: ≥ 2 agents; 3 ≤ `\|R_i\|` ≤ 4; strictly balanced; `\|P_i\| + 2 ≤ \|R_i\|` private goods; `v_i(P_i) < v_i(S_i)` when `\|P_i\| = 2`; no junk) with at most `N` agents has an EFX₀ allocation, so does every instance with at most `N` agents and `\|R_i\| ≤ 4`; connected cores with a 4-good agent suffice (all-3-good ones are covered by Corollary D; L6: EFX₀ allocations of the sides of a split with no good relevant across it combine) | K4Reduction : `EFX.core_reduction4_conn`, `EFX.core_reduction4`, `EFX.efx0_split`, `EFX.isCore_of_isCore4`, `EFX.isCore4_of_isCore`, `EFX.core_reduction4_mixed` (over lists), `EFX.target4_of_cores` (model) |
| K4.TIE | Ties reduce to strict profiles: if every strict profile (`EFX.Strict`: disjoint nonempty `S, T ⊆ R_i` have `v_i(S) ≠ v_i(T)`) with the same relevant goods as a connected k = 4 core has an EFX₀ allocation, so does the core; with K4.CORE, TARGET₄ up to `N` agents follows from EFX₀ for connected strict k = 4 cores with a 4-good agent. The existing certificates discharge this hypothesis for `N ≤ 4` (K4.R3, K4.R4; K4.R5 covers `n = 5` only with at most two 4-good agents, which this form cannot use), through two steps outside Lean: relabeling list cores to the certificates' indices, and K4.OT's grid completeness | K4Ties : `EFX.tie_reduction`, `EFX.core_reduction4_strict` (over lists), `EFX.target4_of_strict_cores` (model) |
| K4.LB4.S | Theorem 1′₄ (any k; values in ℕ): every completion (owner `o` a listed free agent or none; base goods with their base's agent; no junk for frozen agents; `\|C_j\| + \|B_j\| ≤ 2` for free `j ≠ o`) of a valid pre-allocation (bases of any size, needs `N_i` with `{g ∉ B_i : v_i(g) > v_i(B_i)} ⊆ N_i ⊆ R_i ∖ B_i`; (V1), (V2)) that satisfies (OC₄) is EFX₀, with the owner's needs from its base or `N_o^X` from its bundle; every bundle but the owner's has at most two goods, and a frozen agent other than the owner holds only its base | PreAllocK : `EFX.LB4.Valid.sound`, `EFX.LB4.Valid.sound_ownerNeeds`, `EFX.LB4.efx0_of_needs`, `EFX.LB4.Completion.length_le_two`, `EFX.LB4.Completion.frozen_base` (over lists), `EFX.LB4.sound_model` (model); `EFX.LB4.Needs.pick` (pick needs are needs) |
| K4.LB4.S | Counting: `\|F\| = \|NA\|` and `ω = \|J\| − S = \|NA\| − σ` (cap `2 − \|B_i\|` with its sign, 0 if frozen); if `ω ≤ 0` (all bases ≤ 2 goods) a completion without owner exists; with the other slots filled the owner holds `ω + 2` goods | PreAllocK : `EFX.LB4.numFrozen_eq`, `EFX.LB4.omega_eq`, `EFX.LB4.complete_none_exists`, `EFX.LB4.Completion.owner_length` |
| K4.LB4.S | Lemma 2₄: with an owner whose base has at most one good, an agent with at most four relevant goods, a pick base and pick needs, whose slot takes its best junk good not yet placed, does not envy (so is not threatened by) the owner's bundle; also for agents filling their slots one at a time; with five relevant goods the value argument fails, and an instance of every other hypothesis has the agent threatened | PreAllocK : `EFX.LB4.selfProtect`, `EFX.LB4.selfProtect_seq`, `EFX.LB4.selfProtect_core`, `EFX.LB4.selfProtect_five`, `EFX.LB4.Ex5.counterexample` |
| K4.LB4.S | Lemma 3₄: for a strictly balanced owner with at most four relevant goods, its base among them, and `\|B_o\| ≥ 3` or (free, other bases ≤ 2, `ω ≥ 1`): if a sound completion exists, one exists with at least `min(\|J\|, s₀)` slot goods and the same `N_o^X` | PreAllocK : `EFX.LB4.ownerSearch_exact_base`, `EFX.LB4.ownerSearch_exact`, `EFX.LB4.move_step` |
| K4.LB4.S | Shape: a sound completion is EFX₀ with at most one bundle of more than two goods; hence a sound completion of every connected strict k = 4 core with a 4-good agent gives TARGET₄ (with K4.CORE, K4.TIE) | PreAllocK : `EFX.LB4.SoundCompletion.efx0_d2` (over lists), `EFX.LB4.d2_shape`, `EFX.LB4.k4D_of_completion`, `EFX.LB4.target4_of_completions` (model) |
| K4.C4.FRAME | Theorem C₄ (LB₄ʳ, defined in Lean, succeeds on every strict profile of every k = 4 core, for every insertion sequence or for the index order; false by Proposition H, `k4/c4.md` §7, ledger K4.C4.R and K4.C4.C) implies C₄∃ (every strict profile of every k = 4 core has a completion satisfying (OC₄) of a valid pre-allocation); C₄∃ ⟺ K4.D on strict cores (every strict k = 4 core has an EFX₀ allocation with at most one bundle of more than two goods), and C₄∃ implies K4.D (all k = 4 cores) and TARGET₄; the frame's content is the equivalence and the LB₄ʳ ⇒ C₄∃ direction | LB4R : `EFX.LB4R.target4_of_C4exists`, `EFX.LB4R.target4_of_C4existsConn`, `EFX.LB4R.target4_of_C4`, `EFX.LB4R.target4_of_C4index` (model), `EFX.LB4R.C4exists_iff`, `EFX.LB4R.sound_of_d2`, `EFX.LB4R.k4D_of_C4exists`, `EFX.LB4R.conn_of_C4exists`, `EFX.LB4R.C4exists_of_C4`, `EFX.LB4R.C4exists_of_C4index`, `EFX.LB4R.theoremC4index_of_C4`, `EFX.LB4R.k4D_of_C4index`, `EFX.LB4R.sound_of_succeeds`, `EFX.LB4R.Inv.sound`, `EFX.LB4R.phase1State_inv`, `EFX.LB4R.upgrade_inv`, `EFX.LB4R.rotStep_inv`, `EFX.LB4R.rotStep_valid`, `EFX.LB4R.output_big_base` (over lists) |
| K4.ONE.FRAME | C₄∃ for connected strict k = 4 cores with at most one 4-good agent implies that every instance with at most four relevant goods per agent, at most one agent with exactly four, has an EFX₀ allocation; the K4.CORE reduction and K4.TIE's perturbation add no 4-good agent | K4One : `EFX.LB4R.target4one_of_C4existsOne`, `EFX.target4one_of_strict_cores` (model), `EFX.LB4R.C4existsOne_iff`, `EFX.LB4R.C4existsOne_of_C4exists`, `EFX.LB4R.C4existsOne_of_C4existsConn`, `EFX.LB4R.sound_of_three_cores`, `EFX.core_reduction4_one_strict`, `EFX.core_reduction4_mixed_of`, `EFX.core_reduction4_conn_of`, `EFX.atMostOne4_sublist` (over lists) |
| K4.C4.AB.L | `k4/c4.md` §2–§4 for LB₄ʳ's states after any run of Phase 1 and envy-free upgrades: Lemma E (who can be exposed), Theorem A₄ (with no exposed 4-good agent, `r` is a valid owner unless LB⁺'s bad case), Lemma R and Theorem B₄ (a)–(c) (a rotation to `r` keeps W and exposes w.r.t. the head only agents exposed w.r.t. `r`, or `r` itself (only if 4-good); LB⁺'s rotation gives an output, with no owner or owner k*, unless `r` is exposed), Corollary C₄⁰ (LB₄ʳ(τ) succeeds if ω ≤ 0 or under these hypotheses; it never fails when every agent has three goods) | K4C4AB : `EFX.LB4R.lemmaE`, `EFX.LB4R.lemmaE_three`, `EFX.LB4R.lemmaE_four`, `EFX.LB4R.theoremA4`, `EFX.LB4R.theoremA4_output`, `EFX.LB4R.theoremB4`, `EFX.LB4R.theoremB4c`, `EFX.LB4R.rotate_Wl`, `EFX.LB4R.needsOf_rotate`, `EFX.LB4R.rotate_valid`, `EFX.LB4R.rotate_exposed`, `EFX.LB4R.rotate_exposed_chain`, `EFX.LB4R.rotate_last_not_exposed`, `EFX.LB4R.corollaryC40'`, `EFX.LB4R.corollaryC40`, `EFX.LB4R.succeeds_of_three`; LB4RRun : `EFX.LB4R.phase1_phaseRun`, `EFX.LB4R.PhaseRun.b2`, `EFX.LB4R.AfterUp.exists_chain`, `EFX.LB4R.AfterUp.last_pick_free`, `EFX.LB4R.AfterUp.last_block`, `EFX.LB4R.upRun_efBase`, `EFX.LB4R.upRun_exists` (over lists) |
| K4.C4MIN.FRAME | 𝒫 (`k4/c4x.md` §1), min-frozen, completable, removal-only (deficit ≤ 0); C₄ᵐⁱⁿ (some min-frozen P ∈ 𝒫 is completable, or removal-only completable) ⟹ C₄∃ ⟹ K4.D, TARGET₄ (also on connected cores with a 4-good agent); removal-only ⟹ completable; Phase 1's picks are in 𝒫, so a min-frozen P exists | C4min : `EFX.C4min.C4exists_of_C4min`, `EFX.C4min.target4_of_C4min`, `EFX.C4min.k4D_of_C4min`, `EFX.C4min.C4min_of_C4minRO`, `EFX.C4min.target4_of_C4minRO`, `EFX.C4min.C4existsConn_of_C4minConn`, `EFX.C4min.target4_of_C4minConn`, `EFX.C4min.target4_of_C4minROConn`, `EFX.C4min.completable_of_removalOnly`, `EFX.C4min.inP_phase1`, `EFX.C4min.exists_minFrozen`; C4minExamples : `EFX.C4min.Ex3.c4min`, `EFX.C4min.Ex3.k3_hyps`, `EFX.C4min.ExW.c4min` |
| K4.C4X.K3.LEAN | Theorem K3: every Pareto-maximal P ∈ 𝒫 of a k = 3 core has ω ≤ 0 or a terminal owner with a removal-only completion; Lemmas U, C (any k), R, E, O; the moves stay in 𝒫 and dominate (from any P ∈ 𝒫); hence D for k = 3 cores and TARGET without LB⁺ | K3Pareto : `EFX.C4min.lemmaU`, `EFX.C4min.no_edge_cycle`, `EFX.C4min.exists_needChain`, `EFX.C4min.threat_shape`, `EFX.C4min.lemmaR`, `EFX.C4min.lemmaE`, `EFX.C4min.transfer_inP_dominates`, `EFX.C4min.transfer_move`, `EFX.C4min.cycle_move`, `EFX.C4min.path_move`; K3Theorem : `EFX.C4min.exposed_top`, `EFX.C4min.lemmaO`, `EFX.C4min.exists_labelCycle`, `EFX.C4min.LabelCycle.disjoint`, `EFX.C4min.cycle_contra`, `EFX.C4min.theoremK3_owner`, `EFX.C4min.theoremK3`, `EFX.C4min.exists_paretoMax`, `EFX.C4min.corollaryD_K3`, `EFX.C4min.target_K3`; C4minExamples : `EFX.C4min.ExOmega.k3_owner` |
| T | TARGET (Corollary T): every instance with `\|R_i\| ≤ 3` for every agent has a complete EFX₀ allocation | Target : `EFX.target` (model), `EFX.target_lists` (over lists), values in ℕ; RealValues : `EFX.target_ordered` (values in any `EFX.OrderedValue`, e.g. ℝ≥0, via L12), `EFX.target_of_ordered` (its specialization to ℕ) |
| L12 | Real values reduce to natural numbers: with ≤ 3 relevant goods per agent and nonnegative values, there are natural-number values with the same relevant goods and the same answer to every comparison between two subset sums; EFX₀, the relevant-goods count and balance transfer | RealValues : `EFX.l12`, `EFX.OrderedValue.exists_agree` (one agent), `EFX.OrderedValue.tri_rep` (three positive values), `EFX.numRelevant_eq_of_agree`, `EFX.OrderedValue.balanced_iff_of_agree`, `EFX.efx0_iff_of_agree` (EFX₀ for `v` iff for `w`) |
| — | The list layer agrees with the model | Bridge : `EFX.Inst.efx0_iff` |
| K3.ALG | Algorithm K3ALG (`proofs/k3_algorithm.md`): peel by R1 (or R1 with `P = ∅`), then LB⁺ with computed rankings and `r1Order`; for every instance with `n ≥ 1` in which every agent has at most three relevant goods, `algo I hn` is EFX₀; `algo` (computable) is the value of the counted program `algoC` and equals the specification | K3Cost : `EFX.K3.algo_efx0`, `EFX.K3.algo_eq_spec`; K3Algo : `EFX.K3.algoSpec_efx0`, `EFX.K3.reduce_sound`, `EFX.K3.lbStage_sound` |
| K3.ALG.TIME | Running time: `(algoC I hn).cost ≤ 400 (n + m + 1)⁴` for every instance with `n ≥ 1` (cost model of `proofs/k3_algorithm.md` §6 and `EFX.K3CostLB`) | K3CostBound : `EFX.K3.algoC_cost`, `EFX.K3.lbPlusC_cost`, `EFX.K3.reduceC_cost`; Timed : `EFX.Timed.mkTable_cost` |
| K3.OWNER | Proposition O: `r` is a valid owner (some `H` fits) exactly when `hitSet` fits, so LB⁺'s owner test needs no minimum hitting set | OwnerR : `EFX.LB.validOwner_iff` |
| AUD | Independently written TARGET and D (list bundles partitioning the goods) follow from `EFX.target` and `EFX.LB.corollaryD` | Audit : `Audit.target_audit`, `Audit.corollaryD_audit` |

mrd-efx proves a stronger form of L2c (`MRD.main_theorem_L`: in addition, all bundles but one have at most one
good), and extends it to monotone valuations.

## Not formalized

- The second half of L8: that a β = 1 core has an allocation giving every agent two of its own goods (its private
  good and the next shared good around the cycle). The graph structure of cores (L4, L6, L7, L11) is not
  formalized.
- L1, L4–L7 and L9–L11. (The reduction to cores, CORE, is formalized: `EFX.core_reduction`; for k = 4,
  `EFX.core_reduction4_conn`, with L6's restriction to connected cores.) L4's identity is not formalized; its bound
  `m ≤ 2n` for k = 3 cores is (`EFX.C4min.sigma_nonneg`).
- C₄ᵐⁱⁿ itself (`k4/c4x.md` §5) is not proved: it is the hypothesis of `EFX.C4min.target4_of_C4min`. The K3 building
  blocks are formalized for k = 3; their k = 4 analogues of `k4/c4x.md` §4 (one 4-good agent) are not.
- The peeling theorems are stated over lists: removing an agent and its goods changes the index types `Fin n`, `Fin m`,
  so a model-level statement needs sub-instances. `EFX.Inst.efx0_iff` connects the two for the full instance.
- Real-valued utilities: core Lean has no `ℝ`, so that `ℝ≥0` satisfies the axioms of `EFX.OrderedValue` is the
  textbook fact, not a Lean instance. L12's remark that cores are preserved (K1–K4) is written only, not formalized.
- S2.S: LB's rule for choosing Phase 1's processing order (R1 keys, insertion lookahead); the theorems hold for
  every order. That `EFX.LB.lb` is the algorithm of `src/construct.py` is checked by running both
  (`scripts/lb_crosscheck.py`), not proved. That LB never fails (S2.LB) is a conjecture. Lemma 2 (the size of the
  large bundle) is not formalized. `EFX.LB.lb_sound` reads its conclusion through the definitions of
  `EFX/LBRun.lean` (what `lb` computes) and `EFX.LB.Profile.Consistent`, which a reader must accept along with the
  trusted base; `EFX.LB.sound` needs only `Profile.Consistent`, `Profile.NA` and `Hyp`.
- LB₄ʳ (`EFX/LB4R.lean`) is defined relationally where the text searches; where the prose leaves room, the choices
  are listed in that file's module doc. Theorem C₄ itself is not proved: it is the hypothesis of
  `EFX.LB4R.target4_of_C4`, and it is false (ledger K4.C4.C, by Proposition H, `k4/c4.md` §7, K4.C4.R). C₄∃, equivalent to K4.D on
  strict cores, is not proved either.
- LB₄ (`k4/lb4.md` §2) is not defined in Lean: `EFX/PreAllocK.lean` proves what holds for every completion of
  every valid pre-allocation (`SoundCompletion`), and that every allocation LB₄ returns is one (its bases,
  caps, upgrades and rotation, the premise of the Shape paragraph) is read from the text, not formalized.
  Nor is the owner step's search (that its test for one set `C` is exact). Lemma 3₄: `ownerSearch_exact_base`
  uses the text's caps (`cap = 2 − |B|` for every free agent, a rotated one included); `ownerSearch_exact`
  takes any slot count `s` up to the other agents' slots and the hypothesis `|B_o| + |J| ≥ s + 3`, which also
  covers `k4/lb4.c`'s `s₀` (a rotated agent gets no slot there).
- LB⁺ (`proofs/lb_last_step.md` §7 and Remark 1): the size of the large bundle (`ω + 2` goods), that the rotation
  does not enlarge it, and S2.LB (LB's own lookahead never reaches the bad case, a conjecture). That `EFX.LB.lbPlus`
  computes what `src/lbplus.py` computes is checked only on the two `decide` examples in `EFX/LBPlus.lean`.

## LB⁺, conjecture D and TARGET (`proofs/lb_last_step.md`)

Where each part of `proofs/lb_last_step.md` (PR #13) is formalized. LB⁺ is formalized in two ways: as a relation
over all its choices (`EFX.LB.LBPlusRun`: Phase 1 in any order with R1 priority, the upgrades in any order, any
need chain from `k*` to `r`, any completions satisfying (OC)), and as a function (`EFX.LB.lbPlus`: the order is an argument; LB's
upgrade order, the chain `chainFrom`, the completions `complete`), which is one of the relation's outputs
(`EFX.LB.lbPlus_run`). Theorem C holds for both.

| `lb_last_step.md` | Lean (file : name) |
|---|---|
| §1 Phase 1: R1 steps, insertion steps, any choices | Blocks : `EFX.LB.R1Prio` (an order with R1 priority), `EFX.LB.phase1` (from `EFX/LBRun.lean`) |
| §1 (I1), (B2); (I3); blocks and leaders | Blocks : `EFX.LB.Run` (`b2`, `i3`, `lead_unique`, `first`), `EFX.LB.phase1_run`; `blkAux`, `leadB`. (I2) and (B1) are used only through (B2) |
| §2 pre-allocations, (V1), (V2), completions, (OC) | PreAlloc : `EFX.LB.Valid`, `EFX.LB.Completion` (any completion satisfying (OC); the text's remark that every `C ⊇ H` with every split into the slots gives one is not formalized) |
| §2 Theorem 1′ | PreAlloc : `EFX.LB.Valid.sound`; `EFX.LB.HypNA` generalizes `EFX.LB.Hyp` ((I1) weakened to "every NA good is picked"), `EFX.LB.Hyp.toHypNA` |
| §2 Lemma 1 (owner criterion); completion without owner | PreAlloc : `EFX.LB.complete_some`, `EFX.LB.complete_none` (the completion `EFX.LB.complete`); OwnerR : `EFX.LB.OwnerOK` bundles Lemma 1's hypotheses |
| §3 LB's state is a valid pre-allocation; (UT); any upgrade order | Blocks : `EFX.LB.upFinal_valid` (every end state `EFX.LB.UpFinal` of the upgrades, in any order `EFX.LB.UpReach`), `EFX.LB.lbState_valid`, `EFX.LB.lbUp_final`, `EFX.LB.upgrades_fix` |
| §4 (A1), (A3), (A4) | OwnerR : `EFX.LB.lastOut_terminal`, `EFX.LB.exposed_lead` and `EFX.LB.exposed_blk_inj`, `EFX.LB.chainEnd_spec` |
| §4 "r is a valid owner" (Lemma 1's condition for some `H`) | OwnerR : `EFX.LB.ValidOwner`; `EFX.LB.validOwner_iff` (exactly when `hitSet` fits) |
| §4 Theorem A: r not valid ⟹ the bad case | OwnerR : `EFX.LB.theoremA_invalid`; also `EFX.LB.theoremA` (unless `EFX.LB.Bad`, a weaker form of the bad case, `r` is valid with `H = hitSet`: a weaker corollary), `EFX.LB.kstar_spec` |
| §5 Theorem B, (a)–(g), any need chain from `k*` to `r` | Rotation : `EFX.LB.theoremB` (for `EFX.LB.BadCase`, which takes the chain as an argument); `BadCase.rot_valid` (a, c), `BadCase.rot_NA` (b), `BadCase.rot_term` (d), `BadCase.rot_exposed` (e), `BadCase.rot_pair` (f), `BadCase.rot_count` (g) |
| §6 LB⁺, Theorem C | LBPlus : `EFX.LB.LBPlusRun`, `EFX.LB.lbPlusRun_sound`, `EFX.LB.lbPlusOut_exists`, `EFX.LB.lbPlusOut_exists_chain` (every need chain gives an output), `EFX.LB.state_of_final`; `EFX.LB.lbPlus`, `EFX.LB.lbPlus_run`, `EFX.LB.lbPlus_sound`, `EFX.LB.lbPlus_sound_model` |
| §6 Corollary D | CorollaryD : `EFX.LB.corollaryD`, `EFX.LB.corollaryD_lists` |
| §6 Corollary T, with the CORE theorem of `proofs/lemmas.md` | Target : `EFX.target`, `EFX.target_lists`, `EFX.core_reduction` |

The final statements use only the trusted base: `EFX.target` assumes `0 < I.n` and `numRelevant I i ≤ 3` for every
agent and concludes `∃ X, I.EFX0 X`; `EFX.LB.corollaryD` assumes `0 < I.n`, `numRelevant I i = 3` and balance
`2 * I.v i g ≤ finSum I.m (I.v i)` for every agent and good, and concludes an EFX₀ `X` and an agent `o` such that
every other bundle has at most two goods (counted with `finSum`). `EFX.LB.lbPlus_sound_model` also needs the
definitions of `EFX/LBPlus.lean` (what LB⁺ computes), `EFX.LB.R1Prio` and `EFX.LB.Profile.Consistent`.

Readings and deliberate differences:
- Phase 1's choices: a processing order with `R1Prio`. Every run of §1 is one, and conversely.
- "r is a valid owner" means Lemma 1's condition for some `H` (`ValidOwner`), not "one good per exposed pair",
  which can reject a valid `r` (example `exampleQ5` in `EFX/LBPlus.lean`: `r` is valid only through a shared
  good). `validOwner_iff` makes the test computable: `hitSet` fits.
- `B*` is defined as `r`'s block, and `k*` as the agent exposed for `r` in it; (A2) (it is the last block) is not
  needed, and in the bad case `k*` is its leader (`exposed_lead`).
- Examples by `decide` (`EFX/LBPlus.lean`): a run on which LB fails and LB⁺ rotates (n = 3), a rotation with owner
  `k*` (n = 5), and the example above; the first two outputs equal `src/lbplus.py`'s.
- Balance with ties: valuations consistent with the rankings have `a ≥ b ≥ c > 0` and `a ≤ b + c`
  (`Profile.Consistent`), and Corollary D assumes `2 v_i(g) ≤ v_i(M)`, which core agents satisfy strictly.
- TARGET assumes at least one agent: with no agent, an allocation exists only when there is no good.
- The CORE theorem is stated over lists (removing agents and goods changes the index types of the model).
