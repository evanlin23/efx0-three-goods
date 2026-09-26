# The k = 4 counterexample suite

Workstream `proof/k4-strategy` (ledger rows K4.STRAT.*; the plan is `k4/strategy.md`). Every known small instance
that refuted a proposed k = 4 statement, one JSON file each in `instances/`, and a runner that evaluates any candidate
statement on all of them with two independent implementations where possible. A candidate target for TARGET₄ has to
survive this suite before anyone writes a proof of it. EVIDENCE only (PROMPT.md §5 rule 3): the suite is a regression
test, not a certificate.

## Contents

- `instances/*.json`: 152 records, 147 complete instances and 5 local configurations of `k4/MINCEX.md` (marked
  `"kind"`, skipped by the runner). Collected from main and from the branches of PRs #37, #41, #43, #44, #45, #50, #51,
  #53 (read with `git show`, never edited), plus one instance that was in no repository: the non-core counterexample
  to #51's local improvement lemma found by #51's referee (`lil-noncore-n3`, re-derived here, see below).
- `model.py`: this workstream's own implementation of the objects, written from the definitions (k4/c4x.md §1,
  k4/c4min.md §1, §3.6, §4, k4/hall.md §1): 𝒫, needs, frozen agents, keys, configurations, valid owners with the
  unfreezing clause, the removal-only deficit, completions, the potentials t, r, Λ, p, Φ, Φ′, and an own SAT encoding of
  EFX₀ / D2 / "w unenvied" (every model re-checked by the raw definition; self-test against plain enumeration: 1,800
  random instances, 0 mismatches).
- `ext.py`: adapters to the other workstreams' independent tools, imported from the working tree when merged, else
  from the pinned branch head via `git show` into `.cache/` (gitignored): #53's `k4/gap_model.py` (245040b), #51's
  `k4/red_lib.py` and `k4/red_lil.py` (827c76f), #43's `k4/induct_sat.py` (29e91b4), #44's `k4/adaptive.c` (146d31b),
  main's `k4/hall_check.py` and `k4/c4x_check.py`.
- `predicates.py`: the statements (`python3 k4/suite/run.py --list`), each with its implementations.
- `run.py`: the runner. `table.py`: prints the provenance table below from the records.
- `triples.py`, `deficit_local.py`, `deficit_sweep.py`: the Step 2 experiments of `k4/strategy.md` (§2.4, §2.1).

## Record format

```
{"id": "...", "n": 4, "m": 8,
 "sets": [[0, 2, 5, 7], ...],            agent i's relevant goods, in the source's order; goods 0..m-1 as in the source
 "vals": [[2, 3, 6, 10], ...],           agent i's values, in the order of sets[i]
 "is_core": true, "strict": true,        computed by model.py (k = 4 core: C1-C5 of EFX.IsCore4, connected; strict types)
 "core_ref": "core 104 of results/k4_certs_4_pure.json.gz",   0-based position in the file's "cores" list, when known
 "source": {"pr": 53, "branch": "...", "files": [...], "replay": "..."},
 "refutes": [{"statement": "...", "ledger": "...", "smallest": true}],   as the source states it
 "witness": {...},                       the configuration / pre-allocation / allocation the source exhibits, if any
 "expect_fail": ["phi-prime", ...],      predicates of predicates.py that must come out False here
 "aliases": [...], "also": [...],        the same (sets, vals) found in other sources
 "notes": "..."}
```
`vals[i][k]` is agent i's value of `sets[i][k]`. The format is the `{"sets", "vals"}` profile of `k4/gap_model.py`
with provenance added. Instances were transcribed from the sources and confirmed with each source's own replay script
(the collection notes are in the PR description); the runner then re-checks every refutation it can express.

## Running
```
python3 k4/suite/run.py --list                               # the statements and their implementations
python3 k4/suite/run.py --expected                           # every "expect_fail" refutation, both implementations
python3 k4/suite/run.py efx0 d2 ps c4min c4min-cfg           # candidate targets on every instance
python3 k4/suite/run.py --pred=my_candidate.py:pred          # a new candidate: pred(record) -> (True/False/None, detail)
```
A line reads `holds`, `FAILS` or `n/a` (hypothesis not met, instance too large, or timeout) per implementation, and
`DISAGREE` when two implementations give different verdicts; the exit status is nonzero on any disagreement.

## Results

(Being filled in: the baseline run of the candidate targets on every instance, `results/k4_strategy/suite_baseline.log`.)

## Instances

| id | n | m | core | PR | source files | refutes (as the source states it; full text in the record) | re-checked by `run.py --expected` |
|---|---|---|---|---|---|---|---|
| `mincex-drop-private-p3` | 1 | 3 | local | #23 | `attempts/k4-mincex-drop-private.md` | Minimal-counterexample reduction (k = 4): removing the private good of a P3 agent (replace e on {s, t, p} by … |  |
| `mincex-px-open-q3` | 2 | 5 | local | #23 | `attempts/k4-mincex-px-open.md`, `LEDGER.md` | Minimal-counterexample reduction for configuration px (open): a P3 agent f = {g, y, p_f} sharing a good g of … |  |
| `mincex-px-open-q3-swapped` | 2 | 5 | local | #23 | `attempts/k4-mincex-px-open.md` | Minimal-counterexample reduction for configuration px (open), as for mincex-px-open-q3 |  |
| `lb4-fixed-insertion-n3m6` | 3 | 6 | yes | #24 | `attempts/lb4-fixed-insertion.md`, `LEDGER.md` | LB₄ with index insertion and every upgrade policy, every owner, one rotation (chains may end at upgraded agen… |  |
| `lb4-last-block-leader-index-n4m8` | 4 | 8 | yes | #24 | `attempts/lb4-last-block-leader.md`, `LEDGER.md` | LB₄ᴸ(index order): index insertion, and if it fails every other leader of its last block, LB₄ otherwise (lb4.… |  |
| `lb4-last-block-leader-n4m8` | 4 | 8 | yes | #24 | `attempts/lb4-last-block-leader.md`, `LEDGER.md` | LB₄ with only the last block's leader searched, for every run of Phase 1 (lb4.c -i9 -u1 -r1 -w1 -c1): LB₄ on … |  |
| `lb4-lbplus-ef-n3m6` | 3 | 6 | yes | #24 | `attempts/lb4-lbplus-shape.md`, `LEDGER.md` | LB₄ in the shape of LB⁺ with envy-free upgrades only (SCOUT §5's rule; lb4.c -i0 -u2 -o2 -r1) succeeds |  |
| `lb4-n2m5-upgrade` | 2 | 5 | yes | #24 | `attempts/lb4-lbplus-shape.md`, `attempts/lb4-fixed-insertion.md` | LB₄ in the shape of LB⁺ (index insertion, need-shrinking upgrades, owner r, else one rotation with any chain …; LB₄ with a fixed insertion rule (index insertion, -i0) with LB₄'s single upgrade policy and one rotation (-i0… (+2 more) | `pre-every:(-frozen,slots)` |
| `lb4-no-rotation-n3m5` | 3 | 5 | yes | #24 | `attempts/lb4-no-rotation.md`, `LEDGER.md` | LB₄ without a rotation (every insertion sequence, every upgrade policy, every owner and completion, owner's n… |  |
| `lb4-owner-needs-from-base-n4m8` | 4 | 8 | yes | #24 | `attempts/lb4-owner-needs-from-base.md`, `LEDGER.md` | LB₄ with the owner's needs taken from its base, as at k = 3 (every insertion sequence, every upgrade policy, … |  |
| `ls-alt-rule-n4m7` | 4 | 7 | yes | #27 | `attempts/k4-ls-alt-rule.md`, `LEDGER.md` | LS4 with the alternative choice rule -DALT (most valuable improving set in M1, rotating agent scan start, lon… |  |
| `ls-clean-placement-n3m5` | 3 | 5 | yes | #27 | `attempts/k4-ls-clean-placement.md`, `LEDGER.md` | LS4's Phase 2 by 'clean' placement ignoring values (goods with a clean source go to one; dirty goods alone to… |  |
| `ls-dead-end-n4m7` | 4 | 7 | yes | #27 | `attempts/k4-ls-dead-end.md`, `attempts/k4-ls-exact-placement.md` | Conjecture TP₄ (k4/local_search4.md §4): every stable state of LS4 (no M1, R or X move) can be completed by P…; Any two-phase local search whose Phase 1 makes Pareto improvements of junk-free EFX₀ partial allocations with… (+2 more) |  |
| `ls-exchange-no-keep-n3m6` | 3 | 6 | yes | #27 | `attempts/k4-ls-exchange-no-keep.md`, `LEDGER.md` | Two-phase local search with M1, R and exchange cycles that do not keep own goods (the k = 3 augmented envy cy… |  |
| `ls-no-exchange-n2m4` | 2 | 4 | yes | #27 | `attempts/k4-ls-no-exchange.md`, `LEDGER.md` | The k = 3 Algorithm LS2 carried to k = 4 without cycle moves (Phase 1: M1 single-agent rebundles and R envy-c… |  |
| `ls-one-pool-agent-n5m8` | 5 | 8 | yes | #27 | `attempts/k4-ls-one-pool-agent.md`, `LEDGER.md` | LS4 with exchange cycles restricted so that at most one agent on the cycle takes pool goods (k4/ls4.c -x -k -… |  |
| `ls-short-cycles-n3m5` | 3 | 5 | yes | #27 | `attempts/k4-ls-short-cycles.md`, `LEDGER.md` | LS4 with exchange cycles of length at most 2 (k4/ls4.c -x -k -L 2) completes |  |
| `ls-simple-split-n4m6` | 4 | 6 | yes | #27 | `attempts/k4-ls-simple-split.md`, `LEDGER.md` | LS4's Phase 2 (c) by the simplest polynomial split (the dump keeps every individually harmless pool good; the… |  |
| `ls-single-dump-n4m7` | 4 | 7 | yes | #27 | `attempts/k4-ls-single-dump.md`, `LEDGER.md` | Two-phase local search whose Phase 2 is a single dump (the whole pool to one empty bundle or one source) comp… |  |
| `mincex-twins` | 2 | 4 | local | #28 | `attempts/k4-mincex-twins.md` | Minimal-counterexample reduction for configuration twins (two P3 agents e, f with the same two shared goods G… |  |
| `mincex-xy-p4p4-open` | 2 | 7 | local | #28 | `attempts/k4-mincex-xy-pairs.md` | Minimal-counterexample reduction for configuration xy (open): two P4 agents e, f sharing only a good g of deg… |  |
| `lsp-bounded-coalitions-n4m7` | 4 | 7 | yes | #29 | `attempts/k4-lsp-bounded-coalitions.md`, `LEDGER.md` | LS4⁺_k with coalition re-divisions of at most k = 2 or k = 3 agents (level-sum-raising, some may lose; k4/ls4… |  |
| `lsp-early-stop-n4m7` | 4 | 7 | yes | #29 | `attempts/k4-lsp-early-stop.md`, `LEDGER.md` | LS4 that stops at the first placement (before every move, check Phase 2 (b)/(c) and stop if it places the poo… |  |
| `gm4-A` | 4 | 7 | yes | #30 | `attempts/k4-gm4-level-sum.md`, `attempts/k4-gm4-potentials.md` | Conjecture GM₄: for every strict profile of every k = 4 core, every junk-free EFX₀ partial allocation that ma…; GM₄∃ with the Σℓ-maxima narrowed by the leximin tie-break: the leximin-largest Σℓ-maximum admits a placement |  |
| `gm4-B` | 4 | 7 | yes | #30 | `attempts/k4-gm4-level-sum.md`, `k4/gm4_counterexample.py` | Conjecture GM₄: for every strict profile of every k = 4 core, every junk-free EFX₀ partial allocation that ma… |  |
| `gm4-C` | 4 | 7 | yes | #30 | `attempts/k4-gm4-level-sum.md`, `k4/gm4_counterexample.py` | Conjecture GM₄: for every strict profile of every k = 4 core, every junk-free EFX₀ partial allocation that ma… |  |
| `gm4-D` | 4 | 7 | yes | #30 | `attempts/k4-gm4-level-sum.md`, `k4/gm4_counterexample.py` | Conjecture GM₄: for every strict profile of every k = 4 core, every junk-free EFX₀ partial allocation that ma… |  |
| `gm4-E` | 4 | 7 | yes | #30 | `attempts/k4-gm4-level-sum.md`, `attempts/k4-gm4-potentials.md` | Conjecture GM₄: for every strict profile of every k = 4 core, every junk-free EFX₀ partial allocation that ma…; GM₄∃ with the Σℓ-maxima narrowed by the leximin tie-break: the leximin-largest Σℓ-maximum admits a placement (+2 more) |  |
| `gm4-F` | 4 | 7 | yes | #30 | `attempts/k4-gm4-level-sum.md`, `k4/gm4_counterexample.py` | Conjecture GM₄: for every strict profile of every k = 4 core, every junk-free EFX₀ partial allocation that ma… |  |
| `gm4-G` | 4 | 7 | yes | #30 | `attempts/k4-gm4-existence.md`, `attempts/k4-gm4-potentials.md` | Conjecture GM₄∃: every strict profile of every k = 4 core has some Σℓ-maximum that admits a placement (equiva…; GM₄∃ with the Σℓ-maxima narrowed by a tie-break (largest Σℓ², leximax or leximin) (+1 more) |  |
| `gm4-H` | 4 | 6 | yes | #30 | `attempts/k4-gm4-envier-source.md`, `k4/gm4_counterexample.py` | H1: at a Σℓ-maximum, every source that envies someone admits the single dump |  |
| `gm4-P` | 4 | 7 | yes | #30 | `attempts/k4-gm4-potentials.md`, `k4/gm4_counterexample.py` | GM for Σ 2^ℓ and for leximax (Σ 16^ℓ): every maximum of the potential admits a placement ('every' form) |  |
| `gm4-S` | 4 | 6 | yes | #30 | `attempts/k4-gm4-single-dump.md`, `k4/gm4_counterexample.py` | Conjecture GM₄ˢ: every Σℓ-maximum with a nonempty pool admits the empty-bundle dump or a single dump (one age… |  |
| `c4-H1` | 5 | 13 | yes | #33 | `k4/c4.md`, `attempts/k4-c4-gadget-stacking.md` | LB₄ʳ with index insertion (each of the three upgrade policies, owner's needs from its base or its bundle, eve… |  |
| `c4-H2` | 9 | 23 | yes | #33 | `k4/c4.md`, `attempts/k4-c4-gadget-stacking.md` | LB₄ʳ with index insertion (each upgrade policy, owner's needs from base or bundle, every owner, every rotatio… |  |
| `c4-H5` | 21 | 53 | yes | #33 | `k4/c4.md`, `attempts/k4-c4-gadget-stacking.md` | Candidate Theorem C₄ (open item 18; Lean EFX.LB4R.TheoremC4index / TheoremC4): for every strict profile of ev…; Proposition H instance: LB₄ʳ with index insertion fails on H_t with q nested rotations whenever 3(t − q) > t … |  |
| `c4-exposure-deficit2-n2m5` | 2 | 5 | yes | #33 | `attempts/k4-c4-exposure-counting.md`, `k4/c4.md` | At k = 4 owner r's deficit (the least number of extra slots that would make r valid) is at most 1, as at k = … |  |
| `c4-exposure-earlier-block-n3m6` | 3 | 6 | yes | #33 | `attempts/k4-c4-exposure-counting.md`, `k4/c4.md` | LB⁺'s Theorem A counting at k = 4: each earlier block has its own terminal for its exposed agents, so the def… |  |
| `c4-exposure-nonleader-n3m5` | 3 | 5 | yes | #33 | `attempts/k4-c4-exposure-counting.md`, `k4/c4.md` | LB⁺'s Theorem A counting carried to k = 4, step 1: every exposed agent (threatened by W = J ∪ {Y_r}) is a blo… |  |
| `c4-g2-other-runs-n4m7` | 4 | 7 | yes | #33 | `attempts/k4-c4-g2-other-runs.md`, `k4/c4.md` | k4/c4.md §6.1 item 4 as first written: with at most one 4-good agent, a 4-good r that is exposed after LB⁺'s … |  |
| `c4-gadget-stacking-1copy-n3m6` | 3 | 6 | yes | #33 | `attempts/k4-c4-gadget-stacking.md` | LB₄ʳ with index insertion, every upgrade policy and one rotation (-i0 -u3 -r1 -w1 -c1) succeeds (this core ne… |  |
| `c4-gadget-stacking-2copies-n6m11` | 6 | 11 | yes | #33 | `attempts/k4-c4-gadget-stacking.md` | Stacking hard gadgets: several copies of a core that needs two nested rotations under LB₄ʳ with index inserti… |  |
| `c4-lbplus-rotation-n3m6` | 3 | 6 | yes | #33 | `attempts/k4-c4-lbplus-rotation.md`, `k4/c4.md` | Theorem B₄ extended to a 4-good r: in LB⁺'s bad case, LB⁺'s rotation (the leader k* gives its top up a need c… |  |
| `c4-one-rotation-owner-r-n3m6` | 3 | 6 | yes | #33 | `attempts/k4-c4-one-rotation.md`, `k4/c4.md` | With one 4-good agent, LB⁺'s exact shape suffices: envy-free upgrades, owner r, else one rotation (lb4.c -i1 … |  |
| `c4-one-rotation-two4-n3m6` | 3 | 6 | yes | #33 | `attempts/k4-c4-one-rotation.md`, `k4/c4.md` | One rotation suffices at k = 4 (LB₄ʳ with every upgrade policy, every owner, every chain and subset O, one ro… |  |
| `c4-owner-last-n3m8` | 3 | 8 | yes | #33 | `attempts/k4-c4-owner-last.md` | Owner processed last: choose the owner o first, run Phase 1 on the other agents, give o (all, or any part, of… |  |
| `c4-pareto-moves-n3m6` | 3 | 6 | yes | #33 | `attempts/k4-c4-pareto-moves.md`, `k4/c4.md` | Local-search proof of C₄ by Pareto-improving moves (upgrades: a free agent adds a junk good; rotations in whi… |  |
| `c4x-n2m5-base-needs` | 2 | 5 | yes | #36 | `attempts/k4-c4x-variant-spaces.md`, `LEDGER.md` | Variant space of 𝒫 with the owner's needs taken from its base (as at k = 3, LB₄'s -w0): some valid pre-alloca… |  |
| `c4x-n2m5-frozen` | 2 | 5 | yes | #36 | `attempts/k4-c4x-frozen-first.md`, `LEDGER.md` | Over 𝒫 (valid pre-allocations, bases ≤ 2 goods, value-based needs), every pre-allocation with the fewest froz… | `pre-every:-frozen` |
| `c4x-n3m5-big-bases` | 3 | 5 | yes | #36 | `attempts/k4-c4x-variant-spaces.md`, `LEDGER.md` | Variant space of 𝒫 in which one base of three or four goods is allowed (its agent must be the owner; LB₄ʳ's r… |  |
| `c4x-n3m6-3good-first` | 3 | 6 | yes | #36 | `attempts/k4-c4x-pareto-potentials.md`, `LEDGER.md` | Over 𝒫, every maximum of Ψ = (Σℓ over 3-good agents, Σℓ over 4-good agents) is completable ('every' form; the… |  |
| `c4x-n3m6-ef-bases` | 3 | 6 | yes | #36 | `attempts/k4-c4x-variant-spaces.md`, `LEDGER.md` | Variant space of 𝒫 with only envy-free two-good bases (v_i(B) ≥ v_i(R_i ∖ B), LB₄ʳ's second upgrade policy): … |  |
| `c4x-n3m6-onefour-a` | 3 | 6 | yes | #36 | `attempts/k4-c4x-frozen-first.md`, `attempts/k4-c4x-pareto-potentials.md` | Over 𝒫, every maximum of (−frozen, Σℓ) is completable ('every' form); Over 𝒫, every maximum of the level sum Σℓ is completable ('every' form) | `pre-every:(-frozen,sumlev)`, `pre-every:sumlev` |
| `c4x-n3m6-onefour-b` | 3 | 6 | yes | #36 | `attempts/k4-c4x-pareto-potentials.md`, `LEDGER.md` | Over 𝒫, some maximum of Σ 2^ℓ is completable ('some' form); Over 𝒫, some leximax-maximum is completable ('some' form) (+1 more) | `pre-every:pareto`, `pre-some:leximax`, `pre-some:sum2l` |
| `c4x-n3m8-leximin` | 3 | 8 | yes | #36 | `attempts/k4-c4x-pareto-potentials.md`, `LEDGER.md` | Over 𝒫, every leximin-maximum is completable ('every' form) | `pre-every:leximin` |
| `c4x-n3m8-pure-top7` | 3 | 8 | yes | #36 | `attempts/k4-c4x-frozen-first.md`, `attempts/k4-c4x-pareto-potentials.md` | Over 𝒫, some maximum of (−frozen, Σℓ) is completable ('some' form); Over 𝒫, some leximin-maximum is completable ('some' form) (+2 more) | `pre-some:(-frozen,sumlev)`, `pre-some:leximin`, `pre-some:pareto`, `pre-some:sumlev` |
| `c4x-n4m7-frozen-slots-some` | 4 | 7 | yes | #36 | `attempts/k4-c4x-frozen-first.md`, `LEDGER.md` | Over 𝒫, some maximum of (−frozen, slots) is completable ('some' form) | `pre-some:(-frozen,slots)` |
| `c4one-one-rotation-m8` | 5 | 8 | yes | #37 | `attempts/k4-c4one-one-rotation.md`, `k4/c4one.md` | C4^1 in its LB4r form (k4/c4.md §6.2, restated in k4/c4one.md §1): take every run of Phase 1 on a k = 4 core … |  |
| `c4one-one-rotation-m9` | 5 | 9 | yes | #37 | `k4/c4one.md`, `attempts/k4-c4one-one-rotation.md` | C4^1 in its LB4r form (k4/c4.md §6.2, restated in k4/c4one.md §1): take every run of Phase 1 on a k = 4 core …; Route 2's local step (k4/c4one.md §4): whenever, after Phase 1 and upgrades (or after earlier rotations), no … |  |
| `c4one-realization-d1` | 5 | 8 | yes | #37 | `attempts/k4-c4one-realization.md`, `k4/c4one.md` | Part (a) of the proof route for Lemma X' (realization): take a run of Phase 1 in case (Tc), with q the unique…; Inserting q at the start of its block in case (Tc) lowers omega (so the move is a step down in key(tau), Lemm… |  |
| `nsw-local-n3m5` | 3 | 5 | yes | #40 | `attempts/k4-nsw-local.md`, `LEDGER.md` | Local form of the NSW potential for LB₄ʳ's rotations: in every stuck state reached from LB₄ʳ's Phase 1 (index… |  |
| `nsw-strict-n4m8` | 4 | 8 | yes | #40 | `attempts/k4-nsw-strict.md`, `LEDGER.md` | Strict existence form of the NSW potential: for some upgrade policy, some sequence of RotSteps from LB₄ʳ's Ph… |  |
| `nsw-strict-n4m9` | 4 | 9 | yes | #40 | `attempts/k4-nsw-strict.md`, `LEDGER.md` | Strict existence form of the NSW potential (as for nsw-strict-n4m8): some strictly Φ-increasing RotStep path … |  |
| `c4min-moves-neither-n3-m9-n3c50` | 3 | 9 | yes | #41 | `results/k4_c4min_moves.log`, `k4/c4min.md` | (k4/c4min.md section 4, measured move catalogue; k4/c4min_moves.py --moves) every configuration without a val… |  |
| `c4min-nounfreeze-n2-m6` | 2 | 6 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | Lemma 1(b) with the owner test WITHOUT the unfreezing clause (-U0): on every profile on which C4min holds (so… |  |
| `c4min-pareto-n3-m7` | 3 | 7 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | Pareto-maximality, f = 1: every Pareto-maximal configuration has a valid owner | `cfg:pareto` |
| `c4min-phi-n4-m8-n4pc72` | 4 | 8 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | Conjecture Phi (first form), f = 2: every configuration at the fewest frozen agents that maximizes Phi = (-t,… | `phi` |
| `c4min-phi-n4-m9-n43c274` | 4 | 9 | yes | #41 | `results/k4_c4min_phi2.log`, `attempts/k4-c4min-potentials.md` | Conjecture Phi (first form): every configuration at the fewest frozen agents that maximizes Phi = (-t, r, Lam… | `phi` |
| `c4min-r-alone-n3-m7` | 3 | 7 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | The robust count r alone, f = 0: every configuration (all-pairs allocation) maximizing r has a valid owner | `cfg:r` |
| `c4min-rlam-n3-m8-n3c46` | 3 | 8 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | (r, Lambda), f = 1: every configuration maximizing (r, Lambda) has a valid owner; Lambda alone, f = 1: every configuration maximizing Lambda has a valid owner | `cfg:lam`, `cfg:r,lam` |
| `c4min-tlam-n3-m6` | 3 | 6 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | (-t, Lambda), f = 2: every configuration maximizing (-t, Lambda) has a valid owner | `cfg:-t,lam` |
| `c4min-tleximin-n4-m7` | 4 | 7 | yes | #41 | `attempts/k4-c4min-potentials.md`, `attempts/k4_c4min_attempts.py` | (-t, leximin), f = 2: every configuration maximizing (-t, leximin of the levels) has a valid owner | `cfg:-t,leximin` |
| `induct-b-r0-pot-minvw` | 2 | 4 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-remove-agent.md` | B-form insertion lemma with bounded repair rho = 0: for some 4-good agent w and some d in R_w, every X' in E(…; Extremal X' (G-form), potential Phi = -v_w(X'_w) (min v_w): for some (w, d), EVERY maximizer of Phi on E(I - … |  |
| `induct-b-r1` | 3 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-remove-agent.md` | B-form insertion lemma with bounded repair rho = 1: for some 4-good agent w and some d in R_w, every X' in E(… |  |
| `induct-b-r2` | 4 | 7 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-remove-agent.md` | B-form insertion lemma with bounded repair rho = 2: for some 4-good agent w and some d in R_w, every X' in E(… |  |
| `induct-g-r0` | 2 | 4 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-bounded-repair.md` | G-form insertion lemma with bounded repair rho = 0: for some 4-good agent w and some d in R_w, every EFX0 all… |  |
| `induct-g-r1` | 2 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-bounded-repair.md` | G-form insertion lemma with bounded repair rho = 1: for some 4-good agent w and some d in R_w, every EFX0 all… |  |
| `induct-g-r2` | 3 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-bounded-repair.md` | G-form insertion lemma with bounded repair rho = 2: for some 4-good agent w and some d in R_w, every EFX0 all… |  |
| `induct-g-r3` | 5 | 6 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-bounded-repair.md` | G-form insertion lemma with bounded repair rho = 3: for some 4-good agent w and some d in R_w, every EFX0 all… |  |
| `induct-gps-q4-a` | 3 | 5 | yes | #43 | `k4/induct.md`, `results/k4_induct_n3.log` | GPS for a Q4 agent (k4/induct.md §5): 'some X' in E(I - d) admits d -> w', for some d in R_w, where w is a 4-… |  |
| `induct-gps-q4-b` | 3 | 5 | yes | #43 | `k4/induct.md`, `results/k4_induct_n3.log` | GPS for a Q4 agent (k4/induct.md §5): 'some X' in E(I - d) admits d -> w', for some d in R_w, where w is a 4-… |  |
| `induct-lbo-every-run` | 4 | 5 | yes | #43 | `k4/induct.md`, `results/k4_induct_lbo_variants.log` | Conjecture LBO (K4.IND.LBO, k4/induct.md §4b; k = 3 setting: every agent other than w values three goods and … |  |
| `induct-lbo-no-partial` | 4 | 5 | yes | #43 | `k4/induct.md`, `results/k4_induct_lbo_variants.log` | Conjecture LBO (K4.IND.LBO, k4/induct.md §4b; k = 3 setting: every agent other than w values three goods and … |  |
| `induct-lbo-no-rot` | 4 | 5 | yes | #43 | `k4/induct.md`, `results/k4_induct_lbo_variants.log` | Conjecture LBO (K4.IND.LBO, k4/induct.md §4b; k = 3 setting: every agent other than w values three goods and … |  |
| `induct-lbo-not-last` | 5 | 9 | yes | #43 | `k4/induct.md`, `results/k4_induct_lbo_variants.log` | Conjecture LBO (K4.IND.LBO, k4/induct.md §4b; k = 3 setting: every agent other than w values three goods and … |  |
| `induct-lbo-owner-only` | 4 | 6 | yes | #43 | `k4/induct.md`, `results/k4_induct_lbo_variants.log` | Conjecture LBO (K4.IND.LBO, k4/induct.md §4b; k = 3 setting: every agent other than w values three goods and … |  |
| `induct-pot-env` | 3 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-potentials.md` | Extremal X' (G-form), potential Phi = -#agents envying w: for some (w, d), EVERY maximizer of Phi on E(I - d)… |  |
| `induct-pot-env-tiebreaks` | 3 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-potentials.md` | Extremal X' (G-form), potential Phi = (-#agents envying w, v_w): for some (w, d), EVERY maximizer of Phi on E…; Extremal X' (G-form), potential Phi = (-#agents envying w, utilitarian): for some (w, d), EVERY maximizer of … |  |
| `induct-pot-envy` | 3 | 4 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-potentials.md` | Extremal X' (G-form), potential Phi = -#agents that envy someone: for some (w, d), EVERY maximizer of Phi on … |  |
| `induct-pot-maxvw` | 3 | 4 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-potentials.md` | Extremal X' (G-form), potential Phi = v_w(X'_w) (max v_w): for some (w, d), EVERY maximizer of Phi on E(I - d… |  |
| `induct-pot-nash` | 3 | 6 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-potentials.md` | Extremal X' (G-form), potential Phi = Nash welfare (#positive, then sum log v_i): for some (w, d), EVERY maxi… |  |
| `induct-pot-util` | 3 | 6 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-potentials.md` | Extremal X' (G-form), potential Phi = utilitarian welfare sum_i v_i(X'_i): for some (w, d), EVERY maximizer o… |  |
| `induct-q4-rules` | 3 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-q4-rules.md` | PS-selected placement rules for a Q4 agent, every-minimizer form: for some 4-good w, d in R_w and agent h, th… |  |
| `induct-v-pot-env-util` | 2 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-value-drop.md` | V-form extremal Y: for some (w, d), every maximizer Y of (-#agents envying w, utilitarian) on E(I_{w,d}) (w's… |  |
| `induct-v-r0` | 2 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-value-drop.md` | V-form insertion lemma with bounded repair rho = 0: for some 4-good agent w and some d in R_w, every Y in E(I… |  |
| `induct-v-r1` | 3 | 5 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-value-drop.md` | V-form insertion lemma with bounded repair rho = 1: for some 4-good agent w and some d in R_w, every Y in E(I… |  |
| `induct-v-r3` | 3 | 6 | yes | #43 | `k4/induct.md`, `attempts/k4-induct-value-drop.md` | V-form insertion lemma with bounded repair rho = 3: for some 4-good agent w and some d in R_w, every Y in E(I… |  |
| `adaptive-cover-multi4` | 2 | 4 | yes | #44 | `k4/adaptive.md`, `attempts/k4-adaptive-coverage-multi4.md` | Choosing the insertion sequence so that the theorems cover the run, for every core (the multi-4-good extensio… |  |
| `adaptive-p1` | 3 | 6 | yes | #44 | `k4/adaptive.md`, `attempts/k4-adaptive-greedy-omega.md` | Insertion rule -A0 (index order): LB4r run on the insertion sequence this rule chooses succeeds with at most …; Insertion rule -A1 (least |NA| of the new block, lb4.c's -i3): LB4r run on the insertion sequence this rule c… (+13 more) |  |
| `adaptive-p3` | 3 | 6 | yes | #44 | `k4/adaptive.md`, `attempts/k4-adaptive-local-features.md` | Insertion rule -A9 (most contested top): LB4r run on the insertion sequence this rule chooses succeeds with a…; Insertion rule -A18 (matching: agents matched to their second choice first (adaptive.c's optimal matching)): … |  |
| `c4min-w0-n4-m11-n4pc217` | 4 | 11 | yes | #45 | `attempts/k4-c4min-w0-owner-base.md`, `attempts/k4_c4min_w0_replay.py` | C4min with the owner's needs taken from its base instead of its bundle (the needs of LB4's -w0): for every st… |  |
| `hall-cyc6` | 6 | 15 | yes | #46 | `k4/hall_instances/cyc6.inst`, `attempts/k4-hall-pareto-no-frozen.md` | Every Pareto-maximum of 𝒫 without frozen agents is removal-only completable (k = 4): Theorem K3's statement r… | `pareto-nofrozen` |
| `hall-local3` | 3 | 7 | yes | #46 | `k4/hall_instances/local3.inst`, `attempts/k4-hall-local-exposures.md` | Theorem K3 at k = 4 when every frozen exposure is local: if no frozen exposure is of the big-top kinds (G) or…; Pareto-maximality is the extremal principle for the big-top owner step (k = 4): the repair here is an exchang… | `pareto`, `pre-every:pareto` |
| `f1-bigtop-n3-m8-n3c46` | 3 | 8 | yes | #50 | `attempts/k4-c4min-f1-bigtop.md`, `attempts/k4_c4min_f1_bigtop.py` | Psi = (r, Lambda) at f = 1: some (every) configuration maximizing Psi = (#robust agents, sum of levels) has a…; Theorem F1 extended to big-top frozen agents ('Theorem F1*' in results/k4_c4min_f1_n3.log): every Psi-maximum… | `cfg:r,lam` |
| `lil-noncore-n3` | 3 | 9 | NO | #51 |  | The local improvement lemma LIL of k4/c4min_reduce.md §5.3 (#51) without the core's private-goods rule: every… | `lil` |
| `red-a1-hopeless-key` | 3 | 6 | yes | #51 | `k4/c4min_reduce.md`, `attempts/k4-c4min-reduce-a.md` | Reduction (a) at a fixed key: for a key (g, x) of a strict profile with fewest frozen agents f = 1 (x frozen … |  |
| `red-a2-hstar` | 3 | 8 | yes | #51 | `k4/c4min_reduce.md`, `attempts/k4-c4min-reduce-a.md` | Reduction (a) with Theorem Z's potential at the best key: some key (g, x) has every maximum of (r', Lambda') …; Reduction (c), one role swap, two-level rule: take a non-completable (r', Lambda')-maximum at a key (g, x) an… (+2 more) | `cfg:r,lam` |
| `red-b1-blocked-improvement` | 4 | 11 | yes | #51 | `k4/c4min_reduce.md`, `attempts/k4-c4min-reduce-b.md` | Reduction (b): at a fixed key, rerun Theorem Z's argument with the constraint t = 0 first; every maximum of (… |  |
| `red-key-without-t0` | 3 | 7 | yes | #51 | `k4/c4min_reduce.md`, `results/k4_red_n3.log` | Lemma T0 at a fixed key: every key (g, x) has a configuration with t = 0 (the pool alone does not threaten x)… |  |
| `red-lil-nokeep-b` | 3 | 7 | yes | #51 | `results/k4_red_lil_gapbench.log`, `k4/red_lil_gapbench.py` | LIL (Phi_r = (r', -t, Lambda)) with PR #53's move catalogue WITHOUT keeping: every f = 1 configuration withou… |  |
| `red-pm-offpath-hypothesis` | 3 | 7 | yes | #51 | `k4/c4min_reduce.md` | Lemma PM without its hypothesis that the terminal tau is threatened by some owner o not among p_1, ..., p_k: … |  |
| `hall-bestpair-core44` | 3 | 7 | yes | #52 | `k4/hall_bt.md` | #41 §4's rule for the exchange-digraph cycle move: a receiver of a threat edge takes its *best* admissible pa… |  |
| `hall-bt4` | 4 | 7 | yes | #52 | `k4/hall_instances/bt4.inst`, `attempts/k4-hall-bt-n4.md` | Conjecture BT (K4.HALL.BT): a Pareto-maximum inside the min-frozen class of 𝒫, with ω ≥ 1, that is not remova…; A frozen agent that is not big-top (exposed only locally) is repaired by the exchange cycle through the owner… | `bt`, `bt-cfg`, `pareto-minfrozen` |
| `hall-btown-core46` | 3 | 8 | yes | #52 | `k4/hall_bt.md` | BTOWN (the variant of K4.HALL.BTCYC with x as the owner): at every Pareto-maximal P ∈ 𝒫 inside the min-frozen… |  |
| `gap-bt5-n5-m10-n53c7265` | 5 | 10 | yes | #53 | `results/k4_gap_bench_n5.log`, `results/k4_gap_bt5.log` | #41 section 4, the local improvement lemma with pool moves and exchange-cycle moves (best pairs, every order …; from each Pareto-maximal configuration without a valid owner, exchange-cycle moves alone reach one with a val… (+1 more) | `bt-cfg` |
| `gap-btcyc-n4-m8-pure122` | 4 | 8 | yes | #53 | `results/k4_gap_bench_hard_hunt.log`, `results/k4_gap_btcyc.log` | #41 section 4, the local improvement lemma with pool moves and exchange-cycle moves (best pairs, every order …; every configuration without a valid owner has a Phi'-raising move, with LOCAL's catalogue (pool moves; exchan… (+4 more) | `max-simple` |
| `gap-f2-n4-m7-n42c93` | 4 | 7 | yes | #53 | `results/k4_gap/hard_base.json.gz`, `results/k4_gap_hard_base.log` | [extremal flag, not a refutation] category F2 (k4/gap.md section 3): f >= 2 (the exposed-frozen gap beyond f … |  |
| `gap-f2-n5-m8-n52c1748` | 5 | 8 | yes | #53 | `results/k4_gap/hard_base.json.gz`, `results/k4_gap_hard_base.log` | [extremal flag, not a refutation] category F2 (k4/gap.md section 3): f >= 2 (the exposed-frozen gap beyond f … |  |
| `gap-iiinor-n4-m8-n43c170` | 4 | 8 | yes | #53 | `results/k4_gap_bench_n4.log` | roadmap (iii): in that setting [f = 1, x 3-good, no valid owner, pool-optimal, t = 0], the threat path into x… |  |
| `gap-iit0-n4-m8-n43c145` | 4 | 8 | yes | #53 | `results/k4_gap_bench_n4.log`, `results/k4_gap_bench_n4_b.log` | roadmap (ii): in that setting [SIGMA_INJ's: f = 1, x 3-good, no valid owner, pool-optimal, t = 0] with x thre…; roadmap (ii) with (iii): in that setting [f = 1, x 3-good, no valid owner, pool-optimal, t = 0] with x threat… |  |
| `gap-iit0-n5-m10-n54c6724` | 5 | 10 | yes | #53 | `results/k4_gap_bench_n5.log` | roadmap (ii): in that setting [SIGMA_INJ's: f = 1, x 3-good, no valid owner, pool-optimal, t = 0] with x thre…; roadmap (ii) with (iii): in that setting [f = 1, x 3-good, no valid owner, pool-optimal, t = 0] with x threat… |  |
| `gap-ipoollocal-n3-m8-n3c45` | 3 | 8 | yes | #53 | `results/k4_gap_bench_n23.log` | (i) as a local lemma: a configuration without a valid owner that is not pool-optimal has a Phi'-raising pool … |  |
| `gap-ipoollocal-n4-m9-n42c278` | 4 | 9 | yes | #53 | `results/k4_gap_bench_n4.log` | (i) as a local lemma: a configuration without a valid owner that is not pool-optimal has a Phi'-raising pool … |  |
| `gap-ipoollocal-n4-m9-n43c304` | 4 | 9 | yes | #53 | `results/k4_gap_bench_hard_hunt.log` | (i) as a local lemma: a configuration without a valid owner that is not pool-optimal has a Phi'-raising pool … |  |
| `gap-ipoollocal-n5-m12-n5pc4202` | 5 | 12 | yes | #53 | `results/k4_gap_bench_n5.log` | (i) as a local lemma: a configuration without a valid owner that is not pool-optimal has a Phi'-raising pool …; #41 section 4, the local improvement lemma with pool moves and exchange-cycle moves (best pairs, every order … |  |
| `gap-ipoolopt-n4-m10-n4pc197` | 4 | 10 | yes | #53 | `results/k4_gap_bench_n4.log` | roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-ipoolopt-n4-m10-n4pc205` | 4 | 10 | yes | #53 | `results/k4_gap_bench_hard_hunt.log` | roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-ipoolopt-n4-m9-n43c247` | 4 | 9 | yes | #53 | `results/k4_gap/hard_hunt_smallest.json.gz`, `results/k4_gap_hard_hunt.log` | roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-ipoolopt-n4-m9-n43c252` | 4 | 9 | yes | #53 | `results/k4_gap/hard_base.json.gz`, `results/k4_gap_hard_base.log` | roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-ipoolopt-n5-m11-n5pc3385` | 5 | 11 | yes | #53 | `results/k4_gap/hard_hunt_smallest.json.gz`, `results/k4_gap_hard_hunt.log` | roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-ipoolopt-n5-m12-n54c9458` | 5 | 12 | yes | #53 | `results/k4_gap_bench_n5.log`, `results/k4_gap/hard_base.json.gz` | roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-itlocal-n3-m8-n3c46` | 3 | 8 | yes | #53 | `results/k4_gap_bench_n23.log`, `results/k4_gap/hard_base.json.gz` | (i) as a local lemma: a configuration without a valid owner with t > 0 has a Phi'-raising pool or cycle move; roadmap (i), first half: every Phi'-maximum is pool-optimal |  |
| `gap-ivmax-n4-m8-n42c203` | 4 | 8 | yes | #53 | `results/k4_gap/hard_hunt_smallest.json.gz`, `results/k4_gap_hard_hunt.log` | roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner |  |
| `gap-ivmax-n4-m8-n43c167` | 4 | 8 | yes | #53 | `results/k4_gap_bench_n4.log` | roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner |  |
| `gap-ivmax-n5-m9-n53c5848` | 5 | 9 | yes | #53 | `results/k4_gap_bench_n5.log` | roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner |  |
| `gap-ivmax-n5-m9-n54c4018` | 5 | 9 | yes | #53 | `results/k4_gap/hard_base.json.gz`, `results/k4_gap_hard_base.log` | roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner |  |
| `gap-ivmax-n5-m9-n5pc1347` | 5 | 9 | yes | #53 | `results/k4_gap/hard_hunt_smallest.json.gz`, `results/k4_gap_hard_hunt.log` | roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner; [extremal flag, not a refutation] category F2 (k4/gap.md section 3): f >= 2 (the exposed-frozen gap beyond f … |  |
| `gap-ivsetting-n3-m6-n3c23` | 3 | 6 | yes | #53 | `results/k4_gap_bench_n23.log` | roadmap (iv) in the proof's setting: without a valid owner, pool-optimal, t = 0: a 4-good frozen agent is thr… |  |
| `gap-ivsetting-n4-m7-n41c75` | 4 | 7 | yes | #53 | `results/k4_gap_bench_n4.log` | roadmap (iv) in the proof's setting: without a valid owner, pool-optimal, t = 0: a 4-good frozen agent is thr… |  |
| `gap-ivsetting-n5-m8-n51c875` | 5 | 8 | yes | #53 | `results/k4_gap_bench_n5.log` | roadmap (iv) in the proof's setting: without a valid owner, pool-optimal, t = 0: a 4-good frozen agent is thr… |  |
| `gap-local-n3-m7-n3c43` | 3 | 7 | yes | #53 | `results/k4_gap_bench_n23.log` | #41 section 4, the local improvement lemma with pool moves and exchange-cycle moves (best pairs, every order …; every configuration without a valid owner has a Phi'-raising move, with LOCAL's catalogue (pool moves; exchan… |  |
| `gap-npo-n2-m6` | 2 | 6 | yes | #53 | `results/k4_gap_bench_n23.log`, `results/k4_gap/hard_base.json.gz` | roadmap (i), first half: every Phi'-maximum is pool-optimal; #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing) | `max-simple` |
| `gap-phi-n4-m10-pure183` | 4 | 10 | yes | #53 | `results/k4_gap/hard_hunt_smallest.json.gz`, `results/k4_gap_hard_hunt.log` | #41 Conjecture Phi' (K4.C4MIN.PHI): every Phi'-maximum has a valid owner; #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing) (+2 more) | `max-simple`, `phi-prime` |
| `gap-phi-n4-m8-pure104` | 4 | 8 | yes | #53 | `results/k4_gap_bench_hard_hunt.log`, `results/k4_gap/hard_hunt_smallest.json.gz` | #41 Conjecture Phi' (K4.C4MIN.PHI): every Phi'-maximum has a valid owner; #41 section 4, the first form Phi = (-t, r, Lambda) (known false at n = 4): every maximum has a valid owner (+6 more) | `max-simple`, `phi`, `phi-prime` |
| `gap-phi-w-n4-m10-pure178` | 4 | 10 | yes | #53 | `results/k4_gap/hard_hunt.json.gz`, `results/k4_gap_bench_hard_hunt.log` | #41 Conjecture Phi' (K4.C4MIN.PHI): every Phi'-maximum has a valid owner; #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing) (+3 more) | `max-simple`, `phi`, `phi-prime` |
| `gap-phifirst-n4-m9-n4pc133` | 4 | 9 | yes | #53 | `results/k4_gap_bench_n4.log` | #41 section 4, the first form Phi = (-t, r, Lambda) (known false at n = 4): every maximum has a valid owner | `phi` |
| `gap-samen-n4-m8-n43c147` | 4 | 8 | yes | #53 | `results/k4_gap_bench_n4.log`, `results/k4_gap_bench_n4_b.log` | #41 section 4, the local improvement lemma with pool moves and exchange-cycle moves (best pairs, every order …; every configuration without a valid owner has a Phi'-raising move, with LOCAL's catalogue (pool moves; exchan… (+3 more) |  |
| `gap-t2-n4-m8-n42c204` | 4 | 8 | yes | #53 | `results/k4_gap/hard_base.json.gz`, `results/k4_gap_hard_base.log` | roadmap (iv): at every Phi'-maximum each frozen agent is threatened by at most one owner |  |
| `gap-w-n2-m5` | 2 | 5 | yes | #53 | `results/k4_gap_bench_n23.log`, `results/k4_gap/hard_base.json.gz` | #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing) | `max-simple` |
| `gap-w-n4-m10-pure179` | 4 | 10 | yes | #53 | `results/k4_gap/hard_base.json.gz`, `results/k4_gap_hard_base.log` | #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing) | `max-simple` |
| `gap-w-n4-m8-pure117` | 4 | 8 | yes | #53 | `results/k4_gap_bench_hard_hunt.log`, `results/k4_gap/hard_hunt_smallest.json.gz` | #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing); [extremal flag, not a refutation] category F2 (k4/gap.md section 3): f >= 2 (the exposed-frozen gap beyond f … | `max-simple` |
| `gap-w-n4-m8-pure120` | 4 | 8 | yes | #53 | `results/k4_gap/hard_hunt_smallest.json.gz`, `results/k4_gap_hard_hunt.log` | #41 section 4 (-U0): some Phi'-maximum has a valid owner with C empty (no withheld goods, no unfreezing) | `max-simple` |
