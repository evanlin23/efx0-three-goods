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

    CHECK PASSED: 857 audited statements, 1919 theorems, standard axioms only

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
each agent's values by a common denominator (machine-checked for K3ALG: `EFX.ratScale`, `EFX.K3.algoRat_efx0` in
`EFX/K3Extras.lean`); nonnegative real values reduce to them by L12 (`proofs/real_values.md`), which is
machine-checked: see the next section.

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
for `Nat` and `Int` are in the file, and the one for core Lean's `Rat` in `EFX/K3Extras.lean`. Nonnegativity is not an axiom but a hypothesis of the theorems
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
- `EFX/ThmZ.lean`: Theorem Z (`k4/c4min.md` §3, PR #41; ledger K4.C4MIN.Z.LEAN): all-pairs allocations
  (`EFX.C4min.IsAPA`), threats, valid owners, robust agents, pool-optimality; Lemma Z0 (`EFX.C4min.c4min_of_zvalid`,
  removal-only form `EFX.C4min.removalOnly_of_zvalid`), Lemma Z1 (`EFX.C4min.exists_apa`, `EFX.C4min.exists_zmax`),
  Lemma Z2 (`EFX.C4min.threat_unique`, `threat_adm`, `threat_gain`), Lemmas P and R (`EFX.C4min.zvalid_or_all4`,
  `EFX.C4min.zvalid_of_zmax`), and Theorem Z: C₄ᵐⁱⁿ's conclusion in both forms on every k = 4 core whose fewest frozen
  agents is 0 (`EFX.C4min.theoremZ_RO`, `EFX.C4min.theoremZ`; `EFX.C4min.theoremZ_min` with only the hypotheses used,
  n ≥ 1, |R_i| ≤ 4, every good relevant; `EFX.C4min.efx0_of_f0`, the EFX₀ allocation with at most one bundle of more
  than two goods). The choices where the prose leaves room are listed in the module doc.
- `EFX/ThmF.lean`: Theorem F (`k4/c4min.md` §3.6, PR #41; ledger K4.C4MIN.F.LEAN): configurations with frozen agents
  (`EFX.C4min.IsCfg`), frozen-robust configurations (`EFX.C4min.FRobust`), the rigidity of the needed set at the fewest
  frozen agents (`EFX.C4min.rigid_NA`, `EFX.C4min.frozen_of_min`), Lemma 1(a) with unfreezing (`EFX.C4min.CfgOwner`,
  `EFX.C4min.removalOnly_of_cfgOwner`, `EFX.C4min.c4min_of_cfgOwner`), the free agents as an all-pairs allocation over `M ∖ 𝒩` (`EFX.C4min.isAPA_sub`,
  `EFX.C4min.isCfg_joinH`), a maximum of (robust free agents, welfare) (`EFX.C4min.fmax_poolOpt`,
  `EFX.C4min.fmax_nRobust`), rotations of frozen cycles (`EFX.C4min.frozen_cycle`), and Theorem F
  (`EFX.C4min.theoremF_min`, `EFX.C4min.theoremF`, `EFX.C4min.c4minRO_of_frobust`): C₄ᵐⁱⁿ's conclusion in both forms on
  every k = 4 core with a frozen-robust configuration at the fewest frozen agents. The choices where the prose leaves room
  are listed in the module doc.
- `EFX/ThmFExamples.lean`: Theorem F is not vacuous (`EFX.C4min.ExF.c4min`): a strict k = 4 core with three agents and
  five goods, and a frozen-robust configuration with two frozen agents, which is the fewest (all 1,024 base maps checked,
  `EFX.C4min.ExF.hmin`), and `ω = 1`.
- `EFX/C4minDescent.lean`: step 4 of `k4/strategy.md` §3 (ledger K4.STRAT.DL2.LEAN): conjecture DL₂ for any
  neighbourhood relation `R` on pre-allocations (`EFX.C4min.Nbhd`): `EFX.C4min.DefLocalAt` (if `ω = f − (2n − m) ≥ 1`,
  every min-frozen P with `def(P) > 0`, `+∞` included, has a min-frozen neighbour P′ with `def(P′) < def(P)`,
  `EFX.C4min.DeficitLT`), `EFX.C4min.DefLocal` (DL_R on every strict profile of every connected k = 4 core, DL₂'s scope),
  `EFX.C4min.DefLocalAll` (every core), `EFX.C4min.BasesDiffer` (the bases of at most k agents differ) and
  `EFX.C4min.DefLocal2` (DL₂). The deficit is an element of ℤ ∪ {+∞} (`EFX.C4min.deficitLE_mono`,
  `EFX.C4min.deficitLE_lower`, `EFX.C4min.exists_least_deficit`, `EFX.C4min.deficitLT_iff`); `ω(P) = f(P) − (2n − m)` on
  𝒫, the same for every min-frozen P, and `def(P) > 0` forces `ω(P) ≥ 1` (`EFX.C4min.omegaP_eq`,
  `EFX.C4min.omegaP_minFrozen_eq`, `EFX.C4min.omegaP_pos`). The descent (`EFX.C4min.exists_removalOnly_of_defLocalAt`)
  and DL_R ⟹ `C4minROConn` ⟹ TARGET₄ for every R (`EFX.C4min.C4minROConn_of_defLocal`, `EFX.C4min.target4_of_defLocal`),
  in particular DL₂ ⟹ TARGET₄ (`EFX.C4min.C4minROConn_of_defLocal2`, `EFX.C4min.target4_of_defLocal2`); on every core,
  DL_R ⟹ `TheoremC4minRO` (`EFX.C4min.C4minRO_of_defLocalAll`). For the full relation DL_R is exactly C₄ᵐⁱⁿ's conclusion
  (`EFX.C4min.defLocalAt_top_iff`), and widening R weakens DL_R (`EFX.C4min.DefLocal.mono`, `EFX.C4min.basesDiffer_mono`).
  The differences from the prose (descent on the deficit instead of finiteness of the min-frozen class; the scope) are
  listed in the module doc.
- `EFX/DL13.lean`: DL₁₃ with Theorem Z at f = 0 ⟹ TARGET₄ (`k4/dl2.md` §3; ledger K4.DL2.T13.LEAN). The moves of
  `k4/dl2.md` §3 as relations on base maps: `EFX.C4min.MoveT1` ((T1): one listed agent, free in P, re-bases inside
  `(B_y ∪ J) ∩ R_y`, the other bases and the needed set unchanged), `EFX.C4min.MoveT3` ((T3): a frozen `x` with base
  `{g}` and a free `z` needing `g` swap roles, `z` taking `{g}`, plus at most one free helper whose new base misses a
  good of its old one, the other bases and the needed set unchanged), `EFX.C4min.R13` (their union, R₁₃);
  `EFX.C4min.FewestFrozenZero` (some P ∈ 𝒫 has no frozen agent), `EFX.C4min.R13Z` (every pair when f = 0, R₁₃
  otherwise) and `EFX.C4min.DL13` (conjecture DL₁₃: `DefLocalAt R13` on every strict profile of every connected k = 4
  core with fewest frozen agents ≥ 1). At f = 0 Theorem Z gives DL for the full relation
  (`EFX.C4min.defLocalAt_top_of_f0`, `EFX.C4min.defLocalAt_R13Z_of_f0`); so DL₁₃ ⟹ `DefLocal R13Z`
  (`EFX.C4min.defLocal_R13Z_of_DL13`, and the converse: `EFX.C4min.dl13_iff_defLocal_R13Z`) ⟹ `C4minROConn` ⟹
  TARGET₄ (`EFX.C4min.C4minROConn_of_DL13`, `EFX.C4min.target4_of_DL13`). Sanity facts on the moves: on 𝒫 the
  subset clause of (T1) is automatic (`EFX.C4min.moveT1_of_inP`), `x` takes a new base in (T3)
  (`EFX.C4min.moveT3_new_base`), and R₁₃ changes at most three bases (`EFX.C4min.r13_basesDiffer`). How the relation
  compares with the code `R13` of `k4/dl2_relations.py` (frozen-status changes instead of the needed set; the same
  pairs of min-frozen pre-allocations by the text's Lemmas 1 and 6) is in the module doc; that agreement is machine-checked
  in `EFX/DL2Moves.lean` (`EFX.C4min.moveT1_iff_code`, `EFX.C4min.moveT3_iff_code`).
- `EFX/DL2Moves.lean`: the move lemmas of the deficit-descent route (`k4/dl2.md` §4, ledger K4.DL2.MOVES.LEAN and
  K4.DL2.DEF.LEAN) and Lemma H1 (`k4/hall.md` §1, ledger K4.HALL.H1.LEAN), over `InP`, `MinFrozen`, `NA`, `Frozen`,
  `DeficitLE` and the moves `MoveT1`, `MoveT3`; it imports `EFX/MovesC.lean` and derives the facts on 𝒫 proved there
  (`EFX.C4min.exists_frozen_of_NA`, `EFX.C4min.minFrozen_of_NA_eq`, `EFX.C4min.not_frozen_of_forall`) instead of
  reproving them. New definitions name the sets of `k4/dl2.md` §4: bundles
  (`EFX.C4min.IsBundle`, `B_o ⊆ Z ⊆ B_o ∪ J`), safety (`EFX.C4min.SafeFor`), `N_o(Z)` (`EFX.C4min.setNeeds`), `u_o(Z)`
  (`EFX.C4min.Counted`, `EFX.C4min.uCount`), optimal bundles of best owners (`EFX.C4min.OptimalBest`) and
  `def(P′) ≤ def(P) − k` (`EFX.C4min.DeficitDrop`). Moves inside the min-frozen class: `EFX.C4min.minFrozen_of_cover`
  (the common core, with the counting step `EFX.C4min.NA_iff_of_sub`), Lemma 1 (`EFX.C4min.lemma1a`, `EFX.C4min.lemma1b`, `EFX.C4min.lemma1c`), Lemma 1′
  (`EFX.C4min.lemma1'`), Lemma 6 (`EFX.C4min.lemma6`, `EFX.C4min.needs_single_sub`); (T1) and (T3) are well defined
  (`EFX.C4min.minFrozen_of_moveT1`, `EFX.C4min.moveT1_of_admissible`, `EFX.C4min.moveT1_iff_needs`,
  `EFX.C4min.minFrozen_of_moveT3`, `EFX.C4min.moveT3_of_lemma6`) and agree with the code's phrasing by frozen-status
  changes (`EFX.C4min.moveT1_iff_status`, `EFX.C4min.moveT1_iff_code`, `EFX.C4min.moveT3_iff_code`; this settles the
  point `EFX/DL13.lean` left to the text). Lemma H1: `def(P) = ω + 2 − Val*(P)` on 𝒫 with `ω ≥ 1`
  (`EFX.C4min.lemmaH1`, from the slot identity `EFX.C4min.h1_core`; per owner, `EFX.C4min.lemmaH1_owner`). Deficit
  criteria: Lemma 2* (`EFX.C4min.lemma2star`, `_drop`, `_lt`), Lemma 2 (`EFX.C4min.lemma2`, `_drop`, `_lt`), Lemma 3
  (`EFX.C4min.lemma3`, `EFX.C4min.lemma3_val`, `EFX.C4min.lemma3_lt`), Lemma 7 (`EFX.C4min.lemma7`,
  `EFX.C4min.lemma7_bigTop`, `EFX.C4min.lemma7_bigTop_base`), Corollaries 4 and 5 (`EFX.C4min.cor4`, `EFX.C4min.cor4_i_of_i'`, `EFX.C4min.cor5`). The
  module doc lists, for each, where the Lean hypotheses are weaker than the text's.
- `EFX/DL13Moves.lean`: the role-swap and frozen-rotation lemmas of `k4/dl13.md` §2 (ledger K4.DL13.SWAP.LEAN,
  K4.DL13.ROT.LEAN), on top of `EFX/DL2Moves.lean`. The swap of Lemma 6 as a structure (`EFX.C4min.RoleSwap`; constructed
  without helper by `EFX.C4min.swapBase`, `EFX.C4min.roleSwap_swapBase`, and with one helper by `EFX.C4min.swapBase1`,
  `EFX.C4min.roleSwap_swapBase1`, the move of `k4/sx.md` Lemma B with k = 1; such a swap with a needer and at most one
  helper giving up a good is a min-frozen (T3) move, `EFX.C4min.RoleSwap.moveT3`, `EFX.C4min.moveT3_swapBase1`, hence a
  (T3⁺) move of `EFX/MovesC.lean` by `EFX.C4min.moveT3_moveT3plus`, usable as the move of the key frame). Lemma 8 (`EFX.C4min.RoleSwap.lemma8_bundle`,
  `_safe`, `_u`, `EFX.C4min.RoleSwap.lemma8`, `_val`: the unfrozen agent's owner value after a swap, `u′_x = ū + ι`, on
  strict profiles) and Corollary 8.2 (`EFX.C4min.RoleSwap.cor8_2`, `EFX.C4min.bigTop_pair_admissible`); Lemma 9 (`EFX.C4min.lemma9_admissible`,
  `EFX.C4min.RoleSwap.lemma9`, `EFX.C4min.RoleSwap.eSwap_eq_zero`, `EFX.C4min.RoleSwap.eSwap_le_one`) with Corollaries
  9.1 (`EFX.C4min.cor9_1_drop`, `EFX.C4min.cor9_1`: the S1 repair, for every admissible `A`, as a min-frozen (T3)
  neighbour) and 9.2 (`EFX.C4min.cor9_2`); Lemma 10
  (`EFX.C4min.lemma10`, `EFX.C4min.lemma10_a`); Lemma 11 (`EFX.C4min.lemma11` with `κ`, `EFX.C4min.lemma11_one`,
  `EFX.C4min.not_counted_of_needer`, `EFX.C4min.not_counted_needs_single`) and Corollary 11.1
  (`EFX.C4min.cor11_1`, `EFX.C4min.cor11_1_auto`); Lemma 12 for a Pareto reassignment of the frozen goods
  (`EFX.C4min.ParetoReassign`, a (T4) move by `EFX.C4min.moveT4_of_paretoReassign`, the identity by
  `EFX.C4min.paretoReassign_refl`; `EFX.C4min.lemma12_move`, `EFX.C4min.lemma12`, `EFX.C4min.lemma12_lt_iff`,
  `EFX.C4min.lemma12_lt`, with `u_o` counted over the goods, `EFX.C4min.uCount_eq_goods`) and Corollary 12.1
  (`EFX.C4min.cor12_1`: finitely many reassignments reach a T4-optimal pre-allocation, `EFX.C4min.T4Optimal`, without
  raising the deficit). The module doc lists the encodings and the weaker hypotheses.
- `EFX/DL13MovesExamples.lean`: Lemma 12 is not vacuous. On the smallest failure of DL₁₃ (`k4/dl13.md` §2.2, n = 4,
  m = 6, a strict k = 4 core), `P = ({4}, {1}, {3}, {5})` is min-frozen (640 base maps checked) with `ω = 1`, and the
  exchange of the frozen agents 0 and 3 is a Pareto reassignment and a (T4) move with `def(P′) < def(P)`
  (`EFX.C4min.ExRot.lemma12_example`, by `EFX.C4min.lemma12_lt`; all by `decide`).
- `EFX/KeyFrame.lean`: the key frame of `k4/dl13.md` §2.3 (Remark "DL on the key graph"; ledger K4.DL2.KEY.LEAN), for
  an arbitrary move relation M: the key κ(P) (`EFX.C4min.key`: the needed set and the frozen agents with their bases),
  def\*(κ) (`EFX.C4min.KeyDeficitLE`, `EFX.C4min.KeyDeficitLT`: the least deficit of a min-frozen P of key κ), N_M(κ)
  (`EFX.C4min.KeyNbr`), R_key (`EFX.C4min.RKey`: every pair at f = 0, otherwise κ(P′) ∈ N_M(κ(P)) ∪ {κ(P)}) and DL on
  the key graph (`EFX.C4min.DLKey`, at f ≥ 1). DLKey M ⟺ DL for R_key (`EFX.C4min.dlKey_iff_defLocal_rKey`) ⟹
  TARGET₄ (`EFX.C4min.target4_of_DLKey`), for every M; monotone in M on min-frozen pairs (`EFX.C4min.DLKey.mono`);
  def\*(κ) is attained (`EFX.C4min.exists_keyMin`); a relation K that keeps the key can be added to M
  (`EFX.C4min.dlKeyAt_of_defLocalAt_keep`); the Remark's point that the move may start from any state of the key, as the
  reduction repair lemmas plug into (`EFX.C4min.dlKeyAt_of_keyMin`: at every key-minimal min-frozen P with def(P) > 0, some
  state of the same key has an M-move to a min-frozen Q with def(Q) < def(P); `EFX.C4min.dlKeyAt_of_keyMin_key`: the same
  with def\*(κ(Q)) < def\*(κ(P))). Choices where the Remark leaves room (e.g. `KeyNbr` asks the target to be
  min-frozen) are listed in the module doc.
- `EFX/MovesC.lean`: the moves (T2) rotation, (T4) frozen permutation and (T3⁺) the frozen-chain role swap
  (`EFX.C4min.MoveT2`, `EFX.C4min.MoveT4`, `EFX.C4min.MoveT3plus`), R_T4 = (T1) ∪ (T2) ∪ (T3) ∪ (T4) (`EFX.C4min.RT4`,
  with the refuted DL_RT4, `EFX.C4min.DLRT4`; ledger K4.DL2.RT4), R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4) (`EFX.C4min.RC`)
  and the conjecture DL_RC (`EFX.C4min.DLRC`; ledger K4.DL2.RC, formalized as K4.DL2.RC.LEAN). On 𝒫, (T3) is (T3⁺) with
  W = ∅ (`EFX.C4min.moveT3_iff`), R₁₃ ⊆ R_C and R_T4 ⊆ R_C (`EFX.C4min.r13_rc`, `EFX.C4min.rt4_rc`), (T1), (T2) keep
  the key (`EFX.C4min.moveT1_key`, `EFX.C4min.moveT2_key`), (T4) contains the identity (`EFX.C4min.moveT4_refl`), a
  pre-allocation with the needed set of a min-frozen one is min-frozen (`EFX.C4min.minFrozen_of_NA_eq`), and
  `EFX.C4min.moveT3plus_of_inP` builds a (T3⁺) move, as `EFX.C4min.moveT1_of_inP` does a (T1) move. DL_RC ⟺ DL for RCZ
  ⟹ TARGET₄ (`EFX.C4min.dlrc_iff_defLocal_RCZ`, `EFX.C4min.target4_of_DLRC`), DL_RC ⟹ DLKey((T3⁺) ∪ (T4))
  (`EFX.C4min.DLKey_of_DLRC`), and DL_RT4 ⟹ DL_RC (`EFX.C4min.DLRC_of_DLRT4`; vacuous, the inclusion is the content).
- `EFX/MovesCExamples.lean`: on the smallest n = 5 failure of DL_RT4 (`results/k4_rt4/n5b_FAILURES.md`, ledger
  K4.DL2.RT4; a k = 4 core), a pair P, P′ ∈ 𝒫 that is a (T3⁺) move and not a (T1), (T2), (T3) or (T4) move
  (`EFX.C4min.Ex5.wider`, `EFX.C4min.Ex5.rc_not_rt4`, by `decide`). The profile's strictness and the core's
  connectivity are not checked in Lean.
- `EFX/RuleF.lean`: rule F's target (`k4/rulef.md` §7; ledger K4.RF.LEAN). `EFX.LB4R.SucceedsR d` (LB₄ʳ(τ) succeeds
  with at most `d` rotations; `EFX.LB4R.rotReach_mono`, `EFX.LB4R.succeeds_of_succeedsR`,
  `EFX.LB4R.succeeds_iff_succeedsR3`), `EFX.LB4R.TheoremRuleF` (every strict profile of every k = 4 core has a first
  agent `a` with `SucceedsR 1 … [a]`; `[a]` is "a first, then index order"), `EFX.LB4R.RuleFConn` (connected cores
  with a 4-good agent), `EFX.LB4R.RuleFOne` (at most one 4-good agent), and their consequences C₄∃ and TARGET₄
  (`EFX.LB4R.C4exists_of_ruleF`, `EFX.LB4R.C4existsConn_of_ruleFConn`, `EFX.LB4R.C4existsOne_of_ruleFOne`,
  `EFX.LB4R.target4_of_ruleF`, `EFX.LB4R.target4_of_ruleFConn`, `EFX.LB4R.target4one_of_ruleFOne`). The three rule F
  statements are hypotheses, not axioms, and open (K4.AD.F).
- `EFX/RuleFK.lean`: the counting lemmas of rule F (`k4/rulef.md` §2, §3, §6, §7; ledger K4.RF.K.LEAN, K4.RF.S.LEAN,
  K4.RF.KR.LEAN, K4.RF.M.LEAN), over the pre-allocations of `PreAllocK.lean` and LB₄ʳ's states. Definitions of §2:
  `EFX.LB4R.needsK` (N^K), `EFX.LB4R.InE` (E), `EFX.LB4R.Serves`, `EFX.LB4R.ServiceOn`, `EFX.LB4R.Separated`,
  `EFX.LB4R.sizeOn`, `EFX.LB4R.kappaK` (κ^K), `EFX.LB4R.KDefLE`, `EFX.LB4R.KPDefLE` (the deficits of Lemmas K and K′).
  Lemma K′ (`EFX.LB4R.lemmaK'`: a completion with owner `o` satisfying (OC₄) exists iff some K′-service has size
  ≤ κ^K) and Lemma K (`EFX.LB4R.lemmaK`: deficit ≤ 0 gives a sound completion), and for LB₄ʳ's states
  `EFX.LB4R.output_iff_lemmaK'`, `EFX.LB4R.output_of_lemmaK`, `EFX.LB4R.output_none_of_omega`. Lemma S
  (`EFX.LB4R.lemmaS`: free exposed agents never raise the deficit). Lemma KR (`EFX.LB4R.lemmaKR`,
  `EFX.LB4R.lemmaKR_output`: one rotation lowers the deficit and, if the bound is ≤ 0, gives an `Output` with owner `k`
  or without owner), for states with `Inv` and hypothesis (iv) `EFX.LB4R.MarkedOK`, which every state LB₄ʳ reaches
  satisfies (`EFX.LB4R.upRun_facts`, `EFX.LB4R.markedOK_of_rotStep`); not vacuous
  (`EFX.LB4R.KRExample.lemmaKR_nonvacuous`). Lemma M as a `Prop` (`EFX.LB4R.LemmaM`, `LemmaMConn`, `LemmaMExact`;
  classes `ClassK0`, `ClassK1`, certificate `CertK`) and Lemma M ⟹ rule F ⟹ TARGET₄ (`EFX.LB4R.ruleF_of_lemmaM`,
  `EFX.LB4R.ruleFConn_of_lemmaMConn`, `EFX.LB4R.target4_of_lemmaM`, `EFX.LB4R.target4_of_lemmaMConn`;
  `EFX.LB4R.ruleF_iff_lemmaMExact`: the exact form is equivalent to `TheoremRuleF`). Lemma M is a hypothesis, not an
  axiom, and open (K4.RF.M). The differences from the text are listed in the module doc.
- `EFX/Adaptive.lean`: adaptive Lemma M's target (`k4/lemmam_x.md` §7.2, §7.4; ledger K4.LMX.AD.LEAN).
  `EFX.LB4R.TheoremAdaptive` (M_ad: every strict profile of every k = 4 core has an insertion sequence `τ` with
  `SucceedsR 1 … τ`, the inserted agent chosen at every insertion step), its consequences C₄∃ and TARGET₄
  (`EFX.LB4R.C4exists_of_adaptive`, `EFX.LB4R.target4_of_adaptive`), and rule F as its special case `τ = [a]`
  (`EFX.LB4R.adaptive_of_ruleF`). `TheoremAdaptive` is a hypothesis, not an axiom, and open (K4.LMX.AD).
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
- `EFX/K3DE.lean`, `EFX/K3DEImprove.lean`, `EFX/K3DEAlgo.lean`, `EFX/K3DEExamples.lean`: the short proof of the
  k = 3 result and algorithm Draft and Exchange (DE) (`paper/k3-simple/long.tex` §4–§6,
  `k3/simplify/po/hall/NOTES.md`; ledger K3S.PO.LEAN), over the valid pre-allocations of `PreAlloc` (rank-based
  states: each agent holds nothing, one of its goods, or its pair `{b, c}`).
  - `K3DE`: utilities (`EFX.DE.util`, pair 4 > a 3 > b 2 > c 1 > nothing 0), Pareto domination, free agents,
    exposure, valid absorbers (`EFX.DE.Absorber`), the paper's completion (`EFX.DE.completeDE`: the goods of `H` to
    different free agents, the rest of the junk to the absorber) and soundness (`EFX.DE.soundness`, through Theorem 1′),
    Lemma transfer (`EFX.DE.transfer`), and one exchange lemma for need cycles, pair chains and exchange cycles
    (`EFX.DE.exchange`).
  - `K3DEImprove`: the computable step of DE (`EFX.DE.step`: pair chain if (P) fails; all pair holders, an empty free
    agent, or `|H_o| ≤ |F| − 1` stop; otherwise the exchange cycle of σ built from greedy distinct representatives),
    Lemmas empty and forced (`EFX.DE.absorber_iff`), and the **Improvement Lemma** (`EFX.DE.improvement`) with its
    Corollary (`EFX.DE.completable_of_undominated`).
  - `K3DEAlgo`: the draft is valid (`EFX.DE.draft_valid`), the loop ends at a valid absorber after at most `4n`
    exchanges (`EFX.DE.loop_spec`), and DE with R1 peeling (`EFX.DE.run`, `EFX.DE.deSpec`) returns an EFX₀ allocation
    with at most one bundle of more than two goods on every instance with at most three relevant goods per agent
    (`EFX.DE.run_sound`, `EFX.DE.deSpec_correct`).
  - `K3DEExamples`: by `decide`, DE on the paper's worked example (one exchange with two exposure arcs; the paper's
    output) and on three small instances (protecting goods, two pair chains, peeling).
- `EFX/K3DEPrelim.lean`, `EFX/K3DELimits.lean`, `EFX/K3DEShort.lean`, `EFX/K3DEShortExamples.lean`,
  `EFX/K3DERings.lean`, `EFX/K3DEReal.lean`, `EFX/K3DERemarks.lean`, `EFX/K3DECost*.lean`: the rest of `paper/k3-simple/` (ledger K3S.PRELIM.LEAN, K3S.LIMITS,
  K3S.SHORT, K3S.EX.LEAN, K3S.RINGS, K3S.REAL.LEAN).
  - `K3DEPrelim`: threats and safety (`EFX.DE.efx0L_iff_safe`), Lemmas threats and safety, Lemma peeling in the
    paper's form (`EFX.DE.peeling`), Lemma R1fail (`EFX.DE.R1fail`).
  - `K3DELimits`: Lemma cases of safety (`EFX.DE.Limits.safe_iff_cases`) and Proposition limits of the shape for every
    strictly balanced valuation with distinct values (`limits_a`, `limits_b`), also for ordered values, by `decide`
    over all allocations.
  - `K3DEShort`, `K3DEShortExamples`: Proposition short moves (`EFX.DE.prop_short`) with both instances attaining its
    bounds, and the worked example's facts (exactly four dominating valid states, `w_exactly_four`; all ten
    candidate completions fail, `w_completions`).
  - `K3DERings`: the ring family for every k and depth: every cycle of the exchange digraph uses exactly k exposure
    arcs (`EFX.DE.Rings.nExp_eq`), and no free agent absorbs iff k ≤ 2^d (`no_free_absorber_iff`).
  - `K3DEReal`: DE on ordered values through L12's surrogate (`EFX.DE.deOrd_correct`), existence with the shape for
    ordered values (`EFX.DE.thmD_ordered`), and at most n peeling rounds (`EFX.DE.de_correct`).
  - `K3DECost`, `K3DECostStep`, `K3DECostRun`, `K3DECostBound`, `K3DECostReal` (ledger K3S.TIME): the running time.
    A counted DE (`EFX.DE.deC`, with unit-cost array writes `EFX.DE.wr`) computes exactly DE's output
    (`EFX.DE.de_eq_spec`) in at most `750 (n + 1)(n + m + 1)` counted operations (`EFX.DE.deC_cost`); on ordered
    values with a comparison oracle, `EFX.DE.deOrdC_cost`.
  - `K3DERemarks`: Example EFX-but-not-EFX₀ (`EFX.DE.Remarks.efx_not_efx0`), the remark that the protecting goods
    cannot be dropped (`pg_undominated`, `pg_only_g2`), and the worked example's remaining numbers (every cycle of
    D⁺ has two exposure arcs, `w_cycles`; DE's step, the totals 14 and 20, the completion: `w_step`, `w_totals`,
    `w_after`).
- `EFX/K3Real.lean`: K3ALG on values in any `EFX.OrderedValue` type in the comparison model (ledger K3.ALG.REAL;
  `proofs/k3_algorithm.md` §3; the paper's Corollary "real values"). The program receives a comparison oracle
  `le : V → V → Bool` and inspects the values only through it (plus unit-cost addition of two of one agent's values; for agents with one or two relevant goods some compared sums count a good twice); the theorems assume `le x y = true ↔ x ≤ y`. It computes
  L12's natural-number surrogate as an `n × m` table (`EFX.K3.surrogate`, `EFX.K3.surrogateC`: per agent, `m` oracle
  calls `v_i(g) ≤ 0` find the relevant goods, twelve more give the pattern of the first three, and the first row of
  `EFX.Pat.reps` with that pattern gives the values) and runs `EFX.K3.algoC` on it (`EFX.K3.algoOrdC`,
  `EFX.K3.algoOrd`; `EFX.K3.algoOrd_eq`: `algoOrd` is `algo` on the surrogate). Correctness:
  `EFX.K3.algoOrd_efx0`, EFX₀ for the original values (via `EFX.K3.agree_surrogate`, the constructive L12, and
  `EFX.efx0_iff_of_agree`). Cost: `EFX.K3.surrogateC_cost` charges `c` units per oracle call and bounds the surrogate
  by `c · n (m + 12) + 10 n m + 971 n`, so at most `n (m + 12)` calls; `EFX.K3.algoOrdC_cost` (`c = 1`) bounds the
  whole run by `n (m + 12) + 10 n m + 971 n + 400 (n + m + 1)⁴`. An example over `Int` checked by `decide`
  (`EFX.K3.Examples.peelOwnerZ_algoOrd`).
- `EFX/K3CostFine.lean`: the finer count of K3ALG (ledger K3.ALG.FINE; `proofs/k3_algorithm.md` §5). Every stage of
  `EFX.K3.algoC` is re-bounded with two numbers, `a` for the lists of agents and `b` for the lists of goods (the
  upgraded agents after the rotation have at most `a + 1`), instead of one `N = n + m + 1` (`EFX.K3.lbUpC_cost_fine`,
  the upgrade loop, `a⁴ + 17a³ + a²b + …`; `EFX.K3.lbPlusC_cost_fine`; `EFX.K3.reduceC_cost_fine`). The sum along
  LB⁺'s longest path is formed syntactically over polynomials given by their coefficients (`EFX.K3.Poly`,
  macro `poly_sum`, checked coefficientwise by `decide`). The theorem `EFX.K3.algoC_cost_fine`: at most
  `n⁴ + 20n³ + 25n²m + 124n² + 47nm + 119n + 22m + 3` counted operations on every instance with `n ≥ 1`; hence
  `EFX.K3.algoC_cost_fine'` (`≤ 145n⁴ + 72n²m + 119n + 22m + 3`) and `EFX.K3.algoC_cost_fine''`
  (`≤ 270 (n⁴ + n²m)`). For ordered values: `EFX.K3.algoOrdC_cost_fine`.
- `EFX/K3Extras.lean`: four results of the k = 3 paper (`paper/k3/`) that were written only (ledger K3.LASTBLOCK,
  K3.SIZE, K3.SD2, K3.RAT).
  - `r` lies in the last block: `EFX.LB.lastOut_lastBlock` (in the setting of `EFX.LB.lastOut_terminal`) and the
    general `EFX.LB.blk_le_lastOut` (Phase 1 in any order; no upgraded agent picks its top).
  - The size of the large bundle, for every valid pre-allocation: `EFX.LB.numFrozen_eq_numNA` (`|F| = |NA|`),
    `EFX.LB.omega_eq` (`ω = |J| − S = m − 2n + |NA|`), `EFX.LB.Completion.owner_length_ge` (every completion with an
    owner gives it at least `ω + 2` goods), `EFX.LB.Completion.owner_length_eq` (exactly `ω + 2` when the other
    terminals' slots are full), together `EFX.LB.largeBundle_size`; `EFX.LB.BadCase.omega_le` (the rotation does
    not increase `ω`); `EFX.LB.complete_owner_length` (K3ALG's completion `complete` fills every other slot when `H`
    repeats no good, so its owner gets exactly `ω + 2`); `EFX.K3.Examples.repeatedGood_state`,
    `EFX.K3.Examples.repeatedGood_algo` (the paper's remark "a repeated good", by `decide`: `HitSet = (g₀, g₀)`,
    `ω = 1`, and K3ALG's owner gets `ω + 3 = 4` goods).
  - At most two relevant goods: `EFX.SDRun` (every run of serial dictatorship: any order, any favourite at every
    step, the last agent takes the rest), `EFX.sdRun_efx0` (over lists) and `EFX.Inst.sdRun_efx0` (model): every
    run is EFX₀; `EFX.Inst.serialDict`, a computable run, and `EFX.Inst.serialDict_efx0`; example
    `EFX.K3.Examples.twoRel_serialDict`.
  - Rational values: `OrderedValue Rat`; `EFX.denProd`, `EFX.scaleNat`, `EFX.ratScale` (each agent's values times
    the product of their denominators, as natural numbers); `EFX.scaleNat_cast`, `EFX.agree_scaleNat`,
    `EFX.ratScale_agree` (every subset-sum comparison preserved), `EFX.ratScale_relevant`,
    `EFX.ratScale_numRelevant`, `EFX.ratScale_efx0_iff`; `EFX.K3.algoRat` (K3ALG on the scaled values) and
    `EFX.K3.algoRat_efx0`.
- `EFX/K4MinCex.lean`: the minimal-counterexample chain at k = 4 (`k4/MINCEX.md`, ledger K4.MC0–K4.MC7).
  K4.MC1: M1 and M1(b) in semantic form (`EFX.MinCex.Extension`, `EFX.MinCex.m1_efx0`, `EFX.MinCex.m1_reduce`);
  K4.MC0 (a)–(c) in inductive form over a hereditary class (`EFX.MinCex.core_reduction4_class`, `EFX.MinCex.mc0`);
  K4.MC4's counting (`EFX.MinCex.mc4_count`); the assembly of K4.MC6 and K4.MC7 (`EFX.MinCex.target4_chain`) under
  the named hypotheses of `EFX.MinCex.ChainHyp` (graph facts about 𝒞_b; reduction certificates; K4.R3–K4.R5;
  an abstract core list, its certificates and the multigraph theorem: `L`, `Matches` and the domain cuts `Cut` are
  parameters, not the files), which Lean does not re-check.
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
  negative controls; logs in `results/audit_kernel.log` (commit ebf27a2, the natural-number development of T and D) and `results/audit_kernel_2026-09-27.log` (commit bf81efb, the whole library: 2,934 named declarations, 8,762 with dependencies, including K3ALG, its cost bounds, the ordered-value transfer and the K3 corollaries).
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
| K4.C4MIN.Z.LEAN | Theorem Z: on every k = 4 core whose fewest frozen agents is 0, some min-frozen P ∈ 𝒫 has def(P) ≤ 0 and is completable (C₄ᵐⁱⁿ's conclusion, both forms); a pool-optimal all-pairs allocation with the most robust agents has a valid owner | ThmZ : `EFX.C4min.theoremZ_min`, `EFX.C4min.theoremZ_RO`, `EFX.C4min.theoremZ`, `EFX.C4min.c4minRO_of_f0`, `EFX.C4min.c4min_of_f0`, `EFX.C4min.efx0_of_f0`, `EFX.C4min.removalOnly_of_zvalid`, `EFX.C4min.zvalid_of_zmax`, `EFX.C4min.c4min_of_zvalid`, `EFX.C4min.exists_zmax`, `EFX.C4min.threat_unique`, `EFX.C4min.threat_gain`, `EFX.C4min.zvalid_or_all4`, `EFX.C4min.robust_of_rel_le2` |
| K4.C4MIN.F.LEAN | Theorem F: on every k = 4 core with a frozen-robust configuration at the fewest frozen agents, some min-frozen P ∈ 𝒫 has def(P) ≤ 0 and is completable (C₄ᵐⁱⁿ's conclusion, both forms); rigidity of the needed set at the fewest frozen agents; Lemma 1(a): a valid owner of a configuration (with unfreezing) gives def(P) ≤ 0 | ThmF : `EFX.C4min.theoremF_min`, `EFX.C4min.theoremF`, `EFX.C4min.c4minRO_of_frobust`, `EFX.C4min.rigid_NA`, `EFX.C4min.frozen_of_min`, `EFX.C4min.removalOnly_of_cfgOwner`, `EFX.C4min.c4min_of_cfgOwner`, `EFX.C4min.isAPA_sub`, `EFX.C4min.not_threat_frozen`, `EFX.C4min.fmax_poolOpt`, `EFX.C4min.fmax_nRobust`, `EFX.C4min.frozen_cycle`; ThmZ : `EFX.C4min.zvalid_or_all4`; ThmFExamples : `EFX.C4min.ExF.c4min` |
| K4.STRAT.DL2.LEAN | DL_R ⟹ TARGET₄ for every neighbourhood relation R, by finite descent on the deficit: DL_R on an instance gives a min-frozen P ∈ 𝒫 with def(P) ≤ 0; DL_R on connected cores ⟹ `C4minROConn` ⟹ TARGET₄; in particular DL₂ ⟹ TARGET₄; DL_R on every core ⟹ `TheoremC4minRO`; the deficit is an element of ℤ ∪ {+∞}; ω(P) = f − (2n − m) on 𝒫, the same for every min-frozen P | C4minDescent : `EFX.C4min.exists_removalOnly_of_defLocalAt`, `EFX.C4min.C4minROConn_of_defLocal`, `EFX.C4min.target4_of_defLocal`, `EFX.C4min.C4minROConn_of_defLocal2`, `EFX.C4min.target4_of_defLocal2`, `EFX.C4min.C4minRO_of_defLocalAll`, `EFX.C4min.defLocalAt_top_iff`, `EFX.C4min.deficitLT_iff`, `EFX.C4min.exists_least_deficit`, `EFX.C4min.omegaP_eq`, `EFX.C4min.omegaP_minFrozen_eq`, `EFX.C4min.omegaP_pos` |
| K4.DL2.T13.LEAN | DL₁₃ (DL for R₁₃ = (T1) ∪ (T3) on connected k = 4 cores with fewest frozen agents ≥ 1) and Theorem Z at f = 0 ⟹ DL for R13Z (every pair at f = 0, R₁₃ otherwise), and conversely ⟹ `C4minROConn` ⟹ TARGET₄ | DL13 : `EFX.C4min.target4_of_DL13`, `EFX.C4min.C4minROConn_of_DL13`, `EFX.C4min.defLocal_R13Z_of_DL13`, `EFX.C4min.dl13_iff_defLocal_R13Z`, `EFX.C4min.defLocalAt_R13Z_of_f0`, `EFX.C4min.defLocalAt_top_of_f0`, `EFX.C4min.moveT1_of_inP`, `EFX.C4min.moveT3_new_base`, `EFX.C4min.r13_basesDiffer` |
| K4.DL2.KEY.LEAN | DL on the key graph for any move relation M (every key of a min-frozen P with def\*(κ) > 0 has a key in N_M(κ) with a smaller least deficit, at f ≥ 1) ⟺ DL for R_key (every pair at f = 0, otherwise κ(P′) ∈ N_M(κ(P)) ∪ {κ(P)}) ⟹ `C4minROConn` ⟹ TARGET₄; monotone in M; the move may start from any state of the key (repairs at key-minimal states give DLKey) | KeyFrame : `EFX.C4min.target4_of_DLKey`, `EFX.C4min.C4minROConn_of_DLKey`, `EFX.C4min.defLocal_rKey_of_DLKey`, `EFX.C4min.dlKey_iff_defLocal_rKey`, `EFX.C4min.DLKey.mono`, `EFX.C4min.exists_keyMin`, `EFX.C4min.dlKeyAt_of_defLocalAt_keep`, `EFX.C4min.dlKeyAt_of_keyMin`, `EFX.C4min.dlKeyAt_of_keyMin_key` |
| K4.DL2.RC.LEAN | (T2), (T4), (T3⁺), R_T4 = (T1) ∪ (T2) ∪ (T3) ∪ (T4) and R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4) (ledger K4.DL2.RT4, K4.DL2.RC); on 𝒫, (T3) is (T3⁺) with W = ∅, R₁₃ ⊆ R_C, R_T4 ⊆ R_C, (T1) and (T2) keep the key, a pre-allocation with the needed set of a min-frozen one is min-frozen; DL_RC with Theorem Z at f = 0 ⟺ DL for RCZ ⟹ TARGET₄; DL_RC ⟹ DLKey((T3⁺) ∪ (T4)); on the n = 5 failure of DL_RT4, a (T3⁺) move outside R_T4 | MovesC : `EFX.C4min.target4_of_DLRC`, `EFX.C4min.dlrc_iff_defLocal_RCZ`, `EFX.C4min.DLKey_of_DLRC`, `EFX.C4min.dlKey_RC_iff`, `EFX.C4min.moveT3_iff`, `EFX.C4min.r13_rc`, `EFX.C4min.rt4_rc`, `EFX.C4min.DLRC_of_DLRT4`, `EFX.C4min.moveT1_key`, `EFX.C4min.moveT2_key`, `EFX.C4min.minFrozen_of_NA_eq`, `EFX.C4min.moveT3plus_of_inP`, `EFX.C4min.moveT4_refl`; MovesCExamples : `EFX.C4min.Ex5.wider`, `EFX.C4min.Ex5.rc_not_rt4` |
| K4.DL2.MOVES.LEAN | `k4/dl2.md` §4, Lemmas 1, 1′ and 6: the moves inside the min-frozen class (re-bases of free agents, role swaps) keep NA and ω; (T1) and (T3) stay in the min-frozen class, and the text's (T1), (T3) agree with the code's phrasing | DL2Moves : `EFX.C4min.lemma1a`, `EFX.C4min.lemma1b`, `EFX.C4min.lemma1c`, `EFX.C4min.lemma1'`, `EFX.C4min.lemma6`, `EFX.C4min.needs_single_sub`, `EFX.C4min.minFrozen_of_cover`, `EFX.C4min.minFrozen_of_moveT1`, `EFX.C4min.moveT1_of_admissible`, `EFX.C4min.moveT1_iff_needs`, `EFX.C4min.moveT1_iff_status`, `EFX.C4min.moveT1_iff_code`, `EFX.C4min.minFrozen_of_moveT3`, `EFX.C4min.moveT3_of_lemma6`, `EFX.C4min.moveT3_iff_code` |
| K4.DL2.DEF.LEAN | `k4/dl2.md` §4, the deficit criteria: Lemmas 2*, 2, 3, 7 and Corollaries 4, 5 | DL2Moves : `EFX.C4min.lemma2star`, `EFX.C4min.lemma2star_drop`, `EFX.C4min.lemma2star_lt`, `EFX.C4min.lemma2`, `EFX.C4min.lemma2_drop`, `EFX.C4min.lemma2_lt`, `EFX.C4min.W_rebase`, `EFX.C4min.lemma3`, `EFX.C4min.lemma3_val`, `EFX.C4min.lemma3_lt`, `EFX.C4min.lemma7`, `EFX.C4min.lemma7_bigTop`, `EFX.C4min.lemma7_bigTop_base`, `EFX.C4min.cor4`, `EFX.C4min.cor4_i_of_i'`, `EFX.C4min.cor5`, `EFX.C4min.isBundle_of_disjoint`, `EFX.C4min.setNeeds_mono`, `EFX.C4min.deficitLT_of_drop` |
| K4.HALL.H1.LEAN | Lemma H1 of `k4/hall.md` §1: on 𝒫 with ω ≥ 1, def(P) = ω + 2 − Val*(P), and the per-owner covering form | DL2Moves : `EFX.C4min.lemmaH1`, `EFX.C4min.lemmaH1_owner`, `EFX.C4min.h1_core`, `EFX.C4min.otherSlots_roNeeds`, `EFX.C4min.deficitLE_of_safe`, `EFX.C4min.exists_safe_of_deficitLE`, `EFX.C4min.deficit_of_optimalBest`, `EFX.C4min.not_deficitLE_of_val_lt` |
| K4.DL13.SWAP.LEAN | `k4/dl13.md` §2.1: the role swap (`RoleSwap`, constructed without and with one helper), Lemmas 8–11 and Corollaries 8.2, 9.1, 9.2, 11.1; a swap with a needer and at most one helper giving up a good is a min-frozen (T3) move | DL13Moves : `EFX.C4min.RoleSwap.junk_iff`, `EFX.C4min.RoleSwap.lemma8_bundle`, `EFX.C4min.RoleSwap.lemma8_safe`, `EFX.C4min.RoleSwap.lemma8_u`, `EFX.C4min.RoleSwap.lemma8`, `EFX.C4min.RoleSwap.lemma8_val`, `EFX.C4min.RoleSwap.cor8_2`, `EFX.C4min.roleSwap_swapBase`, `EFX.C4min.roleSwap_swapBase1`, `EFX.C4min.RoleSwap.moveT3`, `EFX.C4min.moveT3_swapBase1`, `EFX.C4min.lemma9_admissible`, `EFX.C4min.RoleSwap.lemma9`, `EFX.C4min.RoleSwap.eSwap_eq_zero`, `EFX.C4min.RoleSwap.eSwap_le_one`, `EFX.C4min.bigTop_pair_admissible`, `EFX.C4min.cor9_1_drop`, `EFX.C4min.cor9_1`, `EFX.C4min.cor9_2`, `EFX.C4min.lemma10`, `EFX.C4min.lemma10_a`, `EFX.C4min.lemma11`, `EFX.C4min.lemma11_one`, `EFX.C4min.not_counted_of_needer`, `EFX.C4min.not_counted_needs_single`, `EFX.C4min.cor11_1`, `EFX.C4min.cor11_1_auto` |
| K4.DL13.ROT.LEAN | `k4/dl13.md` §2.2: Lemma 12 (a Pareto reassignment of a min-frozen P is a min-frozen (T4) move that never raises the deficit, and the exact strict case) and Corollary 12.1; not vacuous on the smallest failure of DL₁₃ | DL13Moves : `EFX.C4min.lemma12_move`, `EFX.C4min.moveT4_of_paretoReassign`, `EFX.C4min.paretoReassign_refl`, `EFX.C4min.lemma12`, `EFX.C4min.lemma12_lt_iff`, `EFX.C4min.lemma12_lt`, `EFX.C4min.uCount_eq_goods`, `EFX.C4min.cor12_1`, `EFX.C4min.frozenWelfare_lt`; DL13MovesExamples : `EFX.C4min.ExRot.lemma12_example` |
| K4.RF.LEAN | Rule F's target: `SucceedsR d` (at most d rotations); `TheoremRuleF` ⟹ C₄∃ ⟹ TARGET₄, `RuleFConn` ⟹ `C4existsConn` ⟹ TARGET₄, `RuleFOne` ⟹ `C4existsOne` ⟹ TARGET₄ for at most one 4-good agent | RuleF : `EFX.LB4R.rotReach_mono`, `EFX.LB4R.succeeds_of_succeedsR`, `EFX.LB4R.succeeds_iff_succeedsR3`, `EFX.LB4R.C4exists_of_ruleF`, `EFX.LB4R.C4existsConn_of_ruleFConn`, `EFX.LB4R.C4existsOne_of_ruleFOne`, `EFX.LB4R.target4_of_ruleF`, `EFX.LB4R.target4_of_ruleFConn`, `EFX.LB4R.target4one_of_ruleFOne` |
| K4.RF.K.LEAN | Lemmas K and K′: for a valid pre-allocation whose bases belong to listed agents, an owner that is not frozen and every other base of at most two goods, a completion with owner o satisfying (OC₄) exists iff some K and K′-service have size ≤ κ^K; a K-service of size ≤ κ^K gives a sound completion; for LB₄ʳ's states, an `Output` with owner o iff some K has Lemma K′ deficit ≤ 0 (ω ≥ 1 or a base of three goods), and an `Output` without owner when ω ≤ 0 | RuleFK : `EFX.LB4R.lemmaK'_if`, `EFX.LB4R.lemmaK'_onlyIf`, `EFX.LB4R.lemmaK'`, `EFX.LB4R.lemmaK`, `EFX.LB4R.serves_slot_iff`, `EFX.LB4R.serves_keep_iff`, `EFX.LB4R.output_iff_lemmaK'`, `EFX.LB4R.output_of_lemmaK`, `EFX.LB4R.output_none_of_omega` |
| K4.RF.S.LEAN | Lemma S: with o not frozen and \|B_o\| ≤ 1, a ∅-service of the agents of E that are not free extends, unchanged on them, to all of E, at most one good more per free agent of E; deficit(o, ∅) ≤ \|σ\| − κ₀ | RuleFK : `EFX.LB4R.serve_free`, `EFX.LB4R.lemmaS_aux`, `EFX.LB4R.lemmaS_extend`, `EFX.LB4R.lemmaS`, `EFX.LB4R.W_not_NA` |
| K4.RF.KR.LEAN | Lemma KR for states with `Inv` (needs `needsOf`, so (iii) is a theorem) whose bases have at most two goods, with (iv) `MarkedOK`: the rotation along a need chain k → … → o with base O is a `RotStep`, and the deficit of (P′, k, ∅) is at most \|σ\| − κ − 1 − c_k + ε; if that is ≤ 0, an `Output` with owner k, or (all bases ≤ 2 goods, ω′ ≤ 0) without owner; (iv) holds in every reached state; not vacuous | RuleFK : `EFX.LB4R.lemmaKR`, `EFX.LB4R.lemmaKR_output`, `EFX.LB4R.Inv.needs_value`, `EFX.LB4R.needsK_empty`, `EFX.LB4R.needsOf_rotate_inv`, `EFX.LB4R.rotate_valid_inv`, `EFX.LB4R.upRun_facts`, `EFX.LB4R.markedOK_of_rotStep`, `EFX.LB4R.KRExample.lemmaKR_nonvacuous` |
| K4.RF.M.LEAN | Lemma M (a `Prop`: every strict profile of every k = 4 core has a first agent in class K0 or K1 of rule RK) ⟹ `TheoremRuleF` ⟹ TARGET₄; `LemmaMConn` ⟹ `RuleFConn` ⟹ TARGET₄; Lemma M with Lemma K′ and all three policies is equivalent to `TheoremRuleF` | RuleFK : `EFX.LB4R.ruleF_of_lemmaM`, `EFX.LB4R.ruleFConn_of_lemmaMConn`, `EFX.LB4R.target4_of_lemmaM`, `EFX.LB4R.target4_of_lemmaMConn`, `EFX.LB4R.ruleF_iff_lemmaMExact`, `EFX.LB4R.lemmaMExact_of_lemmaM`, `EFX.LB4R.lemmaMConn_of_lemmaM`, `EFX.LB4R.succeedsR_of_classK0`, `EFX.LB4R.succeedsR_of_classK1`, `EFX.LB4R.classes_of_succeedsR`, `EFX.LB4R.certK_iff_of_upRun` |
| K4.LMX.AD.LEAN | M_ad (`TheoremAdaptive`: some insertion sequence τ with at most one rotation on every strict profile of every k = 4 core) ⟹ C₄∃ ⟹ TARGET₄; `TheoremRuleF` ⟹ `TheoremAdaptive` | Adaptive : `EFX.LB4R.C4exists_of_adaptive`, `EFX.LB4R.adaptive_of_ruleF`, `EFX.LB4R.target4_of_adaptive` |
| K4.MC1 | M1, M1(b): an extension of an EFX₀ allocation of the smaller instance (outside agents keep their goods outside `I ∪ I′`, agents of `S` safe, every bundle dominated by a bundle of `Y` or with its `U`-part inside that of a bundle no outside agent envies) is EFX₀; any number of relevant goods | K4MinCex : `EFX.MinCex.m1_efx0`, `EFX.MinCex.m1_reduce`, `EFX.MinCex.threat_le_of_dominated` (over lists) |
| K4.MC0 | (a)–(c): within a hereditary, relevance-invariant class, a minimal counterexample is a connected strict k = 4 core with a 4-good agent | K4MinCex : `EFX.MinCex.mc0`, `EFX.MinCex.core_reduction4_class` (over lists) |
| K4.MC4 | the counting: with K4.MC3 and K4.MC5(iii) on `Γ′`, `4n + 3m ≤ 3 Σ_i \|R_i\|`, i.e. `n ≤ 3(β − 1)` | K4MinCex : `EFX.MinCex.mc4_count` (over lists) |
| K4.MC6, K4.MC7 | the chain: under `EFX.MinCex.ChainHyp` (hypotheses `her`, `rel`, `cyc`, `red`, `small`, `enum`, `cert`, `lit`, `cover`), every admissible instance of the class is solvable (`L`, `Matches`, `Cut` abstract; `enum`, `cert`, `lit`, `cover` together say that the remaining cores are solvable) | K4MinCex : `EFX.MinCex.target4_chain` (over lists) |
| T | TARGET (Corollary T): every instance with `\|R_i\| ≤ 3` for every agent has a complete EFX₀ allocation | Target : `EFX.target` (model), `EFX.target_lists` (over lists), values in ℕ; RealValues : `EFX.target_ordered` (values in any `EFX.OrderedValue`, e.g. ℝ≥0, via L12), `EFX.target_of_ordered` (its specialization to ℕ) |
| L12 | Real values reduce to natural numbers: with ≤ 3 relevant goods per agent and nonnegative values, there are natural-number values with the same relevant goods and the same answer to every comparison between two subset sums; EFX₀, the relevant-goods count and balance transfer | RealValues : `EFX.l12`, `EFX.OrderedValue.exists_agree` (one agent), `EFX.OrderedValue.tri_rep` (three positive values), `EFX.numRelevant_eq_of_agree`, `EFX.OrderedValue.balanced_iff_of_agree`, `EFX.efx0_iff_of_agree` (EFX₀ for `v` iff for `w`) |
| — | The list layer agrees with the model | Bridge : `EFX.Inst.efx0_iff` |
| K3.ALG | Algorithm K3ALG (`proofs/k3_algorithm.md`): peel by R1 (or R1 with `P = ∅`), then LB⁺ with computed rankings and `r1Order`; for every instance with `n ≥ 1` in which every agent has at most three relevant goods, `algo I hn` is EFX₀; `algo` (computable) is the value of the counted program `algoC` and equals the specification | K3Cost : `EFX.K3.algo_efx0`, `EFX.K3.algo_eq_spec`; K3Algo : `EFX.K3.algoSpec_efx0`, `EFX.K3.reduce_sound`, `EFX.K3.lbStage_sound` |
| K3.ALG.TIME | Running time: `(algoC I hn).cost ≤ 400 (n + m + 1)⁴` for every instance with `n ≥ 1` (cost model of `proofs/k3_algorithm.md` §6 and `EFX.K3CostLB`) | K3CostBound : `EFX.K3.algoC_cost`, `EFX.K3.algoC_cost'` (`≤ 6400 (n + m)⁴`), `EFX.K3.lbPlusC_cost`, `EFX.K3.reduceC_cost`; Timed : `EFX.Timed.mkTable_cost` |
| K3.ALG.REAL | K3ALG on ordered values (e.g. ℝ≥0) in the comparison model: with a correct comparison oracle, computing L12's surrogate takes `n (m + 12)` oracle calls and `O(nm)` other operations, and K3ALG on it is EFX₀ for the original values when every agent has at most three relevant goods | K3Real : `EFX.K3.algoOrd_efx0`, `EFX.K3.algoOrd_eq`, `EFX.K3.agree_surrogate`, `EFX.K3.numRelevant_eq_relOf`, `EFX.K3.repOf_spec`, `EFX.K3.surrogateC_cost`, `EFX.K3.algoOrdC_cost`, `EFX.K3.Examples.peelOwnerZ_algoOrd` |
| K3.ALG.FINE | The finer count: `(algoC I hn).cost ≤ n⁴ + 20n³ + 25n²m + 124n² + 47nm + 119n + 22m + 3` for every instance with `n ≥ 1`, hence `O(n⁴ + n²m)` | K3CostFine : `EFX.K3.algoC_cost_fine`, `EFX.K3.algoC_cost_fine'`, `EFX.K3.algoC_cost_fine''`, `EFX.K3.lbPlusC_cost_fine`, `EFX.K3.reduceC_cost_fine`, `EFX.K3.lbUpC_cost_fine`, `EFX.K3.algoOrdC_cost_fine` |
| K3S.PO.LEAN | The Improvement Lemma: a valid state in which no free agent is a valid absorber and some agent is not a pair holder is Pareto-dominated by a valid state (a need cycle, a pair chain or an exchange cycle; computed by `step`); every undominated valid state has a valid absorber, free unless every agent holds its pair | K3DEImprove : `EFX.DE.improvement`, `EFX.DE.completable_of_undominated`, `EFX.DE.step_stop`, `EFX.DE.step_next`, `EFX.DE.step_next_cycle`, `EFX.DE.cycleStep_cycle`, `EFX.DE.succ_pair`, `EFX.DE.succ_exchange`, `EFX.DE.cycleStep_spec`, `EFX.DE.reps_spec` |
| K3S.PO.LEAN | Lemmas transfer, exchange cycle, empty and forced; soundness of the completion (EFX₀ for every consistent valuation, only the absorber's bundle larger than two goods) | K3DE : `EFX.DE.transfer`, `EFX.DE.exchange`, `EFX.DE.completeDE_completion`, `EFX.DE.soundness`; K3DEImprove : `EFX.DE.absorber_empty`, `EFX.DE.forced_hOf`, `EFX.DE.absorber_forced`, `EFX.DE.absorber_iff` |
| K3S.PO.LEAN | Algorithm DE is correct: on every instance with at most three relevant goods per agent it returns an EFX₀ allocation with all bundles but at most one of at most two goods, after at most `4n` exchanges; the paper's worked example | K3DEAlgo : `EFX.DE.draft_valid`, `EFX.DE.loop_spec`, `EFX.DE.deCore_spec`, `EFX.DE.deStage_sound`, `EFX.DE.run_sound`, `EFX.DE.deSpec_correct`; K3DEExamples : `EFX.DE.Examples.worked_spec` |
| K3S.PRELIM.LEAN | Threats and safety (EFX₀ iff every agent is safe); Lemma threats (a)–(c); Lemma safety (a), (b); Lemma peeling (P of at most one good); Lemma R1fail | K3DEPrelim : `EFX.DE.efx0L_iff_safe`, `EFX.DE.threat_pair`, `EFX.DE.safe_of_pair`, `EFX.DE.safe_of_gy`, `EFX.DE.peeling`, `EFX.DE.R1fail` |
| K3S.LIMITS | Lemma cases of safety; Proposition limits of the shape (a), (b) for every valuation with distinct, strictly balanced values (natural numbers and ordered values) | K3DELimits : `EFX.DE.Limits.safe_iff_cases`, `EFX.DE.Limits.limits_a`, `EFX.DE.Limits.limits_b`, `EFX.DE.Limits.limits_a_ordered`, `EFX.DE.Limits.limits_b_ordered` |
| K3S.SHORT | Proposition short moves: without a short move, at least 2 free agents, n ≥ 6, m ≥ 8 (n ≥ 9, m ≥ 12 with 3); both bounds attained | K3DEShort : `EFX.DE.prop_short`, `EFX.DE.short_counts`; K3DEShortExamples : `EFX.DE.ShortExamples.w_attains`, `EFX.DE.ShortExamples.s8_attains`, `EFX.DE.ShortExamples.s8_remark` |
| K3S.EX.LEAN | The worked example: exactly four dominating valid states; all ten candidate completions fail EFX₀; every cycle of D⁺ has two exposure arcs; DE's step and the completion; Example EFX-but-not-EFX₀; the protecting goods cannot be dropped | K3DEShortExamples : `EFX.DE.ShortExamples.w_facts`, `EFX.DE.ShortExamples.w_exactly_four`, `EFX.DE.ShortExamples.w_completions`; K3DERemarks : `EFX.DE.Remarks.w_cycles`, `EFX.DE.Remarks.w_after`, `EFX.DE.Remarks.efx_not_efx0`, `EFX.DE.Remarks.pg_undominated`, `EFX.DE.Remarks.pg_only_g2` |
| K3S.RINGS | The ring family: every cycle of D⁺ uses exactly k exposure arcs; no free agent absorbs iff k ≤ 2^d | K3DERings : `EFX.DE.Rings.gen_tree_ring`, `EFX.DE.Rings.nExp_eq`, `EFX.DE.Rings.no_free_absorber_iff` |
| K3S.TIME | The running time of DE: a counted program that computes exactly DE's output takes at most 750 (n + 1)(n + m + 1) operations (array reads and writes one unit each); on ordered values, plus the surrogate's n(m + 12) oracle calls and O(nm) operations | K3DECostRun : `EFX.DE.de_eq_spec`; K3DECostBound : `EFX.DE.deC_cost`, `EFX.DE.deC_cost_poly`, `EFX.DE.stepC_cost`; K3DECostReal : `EFX.DE.deOrdC_cost` |
| K3S.REAL.LEAN | DE on ordered values (comparison model through L12's surrogate); existence with the shape for ordered values; at most n peeling rounds | K3DEReal : `EFX.DE.deOrd_correct`, `EFX.DE.thmD_ordered`, `EFX.DE.de_correct`, `EFX.DE.peels_le` |
| K3.OWNER | Proposition O: `r` is a valid owner (some `H` fits) exactly when `hitSet` fits, so LB⁺'s owner test needs no minimum hitting set | OwnerR : `EFX.LB.validOwner_iff` |
| K3.LASTBLOCK | `r`, the last agent of Phase 1 not upgraded, lies in the last block: every agent's block (`blkAux`) is at most `r`'s, and `r`'s block is the last processed agent's | K3Extras : `EFX.LB.lastOut_lastBlock`, `EFX.LB.blk_le_lastOut` |
| K3.SIZE | Size of the large bundle: for a valid pre-allocation, `\|F\| = \|NA\|` and `ω = \|J\| − S = m − 2n + \|NA\|`; every completion with an owner (terminal or upgraded) gives it at least `ω + 2` goods, exactly `ω + 2` with the other terminals' slots full; the rotation does not increase `ω`; K3ALG's `complete` with `H` repeating no good gives exactly `ω + 2`; with a repeated good K3ALG's owner can get `ω + 3` (the paper's example) | K3Extras : `EFX.LB.largeBundle_size`, `EFX.LB.omega_eq`, `EFX.LB.numFrozen_eq_numNA`, `EFX.LB.Completion.owner_length_ge`, `EFX.LB.Completion.owner_length_eq`, `EFX.LB.BadCase.omega_le`, `EFX.LB.complete_owner_length`, `EFX.K3.Examples.repeatedGood_state`, `EFX.K3.Examples.repeatedGood_algo` |
| K3.SD2 | `\|R_i\| ≤ 2` for all `i` (values in ℕ) ⟹ every run of serial dictatorship (any order of all agents, any favourite at every step, the last agent takes the rest) is EFX₀ | K3Extras : `EFX.Inst.sdRun_efx0`, `EFX.Inst.serialDict_efx0` (model), `EFX.sdRun_efx0`, `EFX.serialDict_run` (over lists), `EFX.K3.Examples.twoRel_serialDict` |
| K3.RAT | Rational values: scaling each agent's nonnegative rational values by the product of their denominators preserves every comparison of subset sums (so relevance and EFX₀); K3ALG on the scaled values is EFX₀ for the rational values when every agent has at most three relevant goods | K3Extras : `EFX.K3.algoRat_efx0`, `EFX.ratScale_agree`, `EFX.agree_scaleNat`, `EFX.scaleNat_cast`, `EFX.ratScale_val`, `EFX.ratScale_relevant`, `EFX.ratScale_numRelevant`, `EFX.ratScale_efx0_iff` |
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
- DL₂ itself (`k4/strategy.md` §3) is not proved: it is the hypothesis of `EFX.C4min.target4_of_defLocal2`.
- The peeling theorems are stated over lists: removing an agent and its goods changes the index types `Fin n`, `Fin m`,
  so a model-level statement needs sub-instances. `EFX.Inst.efx0_iff` connects the two for the full instance.
- Real-valued utilities: core Lean has no `ℝ`, so that `ℝ≥0` satisfies the axioms of `EFX.OrderedValue` is the
  textbook fact, not a Lean instance. L12's remark that cores are preserved (K1–K4) is written only, not formalized.
- S2.S: LB's rule for choosing Phase 1's processing order (R1 keys, insertion lookahead); the theorems hold for
  every order. That `EFX.LB.lb` is the algorithm of `src/construct.py` is checked by running both
  (`scripts/lb_crosscheck.py`), not proved. That LB never fails (S2.LB) is a conjecture. Lemma 2 (the size of the
  large bundle) is not formalized for LB's own output (its count `ω = |NA| − σ` holds for every valid pre-allocation,
  `EFX.LB.omega_eq`, and LB's state after its upgrades is one, `EFX.LB.lbState_valid`). `EFX.LB.lb_sound` reads its conclusion through the definitions of
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
- LB⁺ (`proofs/lb_last_step.md` §7): S2.LB (LB's own lookahead never reaches the bad case, a conjecture). (Remark 1,
  the size of the large bundle and that the rotation does not enlarge it, is in `EFX/K3Extras.lean`.) That `EFX.LB.lbPlus`
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
  needed (it is proved separately: `EFX.LB.lastOut_lastBlock`), and in the bad case `k*` is its leader
  (`exposed_lead`).
- Examples by `decide` (`EFX/LBPlus.lean`): a run on which LB fails and LB⁺ rotates (n = 3), a rotation with owner
  `k*` (n = 5), and the example above; the first two outputs equal `src/lbplus.py`'s.
- Balance with ties: valuations consistent with the rankings have `a ≥ b ≥ c > 0` and `a ≤ b + c`
  (`Profile.Consistent`), and Corollary D assumes `2 v_i(g) ≤ v_i(M)`, which core agents satisfy strictly.
- TARGET assumes at least one agent: with no agent, an allocation exists only when there is no good.
- The CORE theorem is stated over lists (removing agents and goods changes the index types of the model).
