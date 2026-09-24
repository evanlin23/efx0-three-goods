# Ledger: EFX₀ with at most three relevant goods per agent

The single source of truth. A status changes only in a pull request that adds the artifact in the Artifact column; CI checks that every PROVED, CERTIFIED or REFUTED row points to files that exist. The Lean column names machine-checked statements in `lean/` (core Lean, no `sorry`, standard axioms only; see `lean/README.md`); CI checks that each has a `#print axioms` certificate and that `lean/check.sh` passes.

| ID | Claim | Status | Artifact | Lean | Notes |
|---|---|---|---|---|---|
| L1 | For fixed (n, m): EFX₀ for all additive instances ⟺ EFX for all positive additive instances | PROVED | `proofs/lemmas.md` | | sketch; expand in Step 0 |
| L2 | Peeling rules R1 and R2 | PROVED | `proofs/lemmas.md` | `EFX.peel` | Lean: R1 only (over lists). `src/lemmas.py`: 1,500 random instances through the pipeline, 0 failures |
| L2c | ≤ 2 relevant goods per agent ⟹ EFX₀ (serial dictatorship; the HW1 theorem) | PROVED | `proofs/lemmas.md` | `EFX.exists_efx0_of_count` | stronger form (all bundles but one have ≤ 1 good) machine-checked in evanlin23/mrd-efx: `MRD.main_theorem_L` |
| L3 | Worthless goods go to an envy-graph source | PROVED | `proofs/lemmas.md` | | same pipeline test |
| L4 | Core counting: 3n = 2m − π + Σ(deg − 2), so m ≤ 2n | PROVED | `proofs/lemmas.md` | | |
| L5 | In a core, EFX₀ is ordinal and equals cases T/P/B/C/E | PROVED | `proofs/lemmas.md` | | `src/coreG.py`: 896,400 allocations vs. the definition, 0 mismatches |
| L6 | Disconnected cores are solved component by component | PROVED | `proofs/lemmas.md` | | |
| L7 | β = 2n − m + 1; alone-goods identity | PROVED | `proofs/lemmas.md` | | |
| L8 | Two own goods ⟹ safe; β = 1 cores solved by orientation | PROVED | `proofs/lemmas.md` | | |
| L9 | Bundles ≤ 2: EFX₀ ⟺ every good in another's 2-good bundle is worth ≤ own bundle | PROVED | `proofs/lemmas.md` | | basis of `src/verify_fail.py` |
| L10 | Insertion lemma | PROVED | `proofs/lemmas.md` | | |
| L11 | Cores are subdivisions of finitely many shapes per β; β = 2: theta, dumbbell, figure-eight | PROVED | `proofs/lemmas.md` | | |
| R1 | EFX₀ exists for every instance with ≤ 3 relevant goods per agent and n ≤ 6 | CERTIFIED | `results/certs_5_6.json.gz`, `results/frontier_results_5_6.json`, `results/enum_crosscheck.log` | | conditional on Mahara (m ≤ n + 3); 251 connected cores, enumeration reproduced independently (nauty genbg, bijection up to isomorphism); CI re-checks without SAT |
| R2 | Conjecture D holds for n = 7, m = 13 | CERTIFIED | `results/frontier_results_7.json`, `results/certs_7_13.json.gz`, `results/enum_crosscheck.log` | | 37 cores (enumeration reproduced independently); CI re-checks the certificates without SAT |
| X1 | Bundles ≤ 2 always suffice in a core | REFUTED | `results/exhaust5.log` | | n = 5: 1,226 of 93,312 profiles |
| X2 | Conjecture A: m ≤ 2n − 2 ⟹ bundles ≤ 2 suffice | REFUTED | `results/frontier_results_5_6.json`, `src/verify_fail.py`, `proofs/counterexamples.md` | | n = 6, m = 10: 57 of 211 cores; two independent encodings |
| X3 | Conjecture A for non-core instances | REFUTED | `proofs/counterexamples.md` | | four identical agents + three worthless goods |
| X4 | One bundle of 3 goods always suffices | REFUTED | `results/frontier_results_5_6.json` | | single implementation; confirm independently |
| D2.C | Collector theorem: agents with a private good are edges of a multigraph on shared goods; if #E + #pins = #V + 1 and a cover state exists, then with one collector (the only bundle that may exceed two goods) every agent of E is safe | PROVED | `proofs/beta2.md`, `src/test_collector.py`, `results/test_collector.log` | | potential argument: each switch lowers the number of bad agents by one. Random test beyond β = 2: 164,861 multigraphs with pins, 0 failures |
| D2.O | Lemma O: a Q-agent z can hold only its top good while every other agent holds two own goods, whenever the component of a_z in G − z is a tree | PROVED | `proofs/beta2.md` | | Hall's theorem; all bundles ≤ 2 |
| D2 | Conjecture D holds for every connected core with β = 2 (m = 2n − 1), for all n ≥ 2 | PROVED | `proofs/beta2.md`, `src/beta2.py`, `src/verify_beta2.py`, `results/verify_beta2.log` | | constructive, self-contained (re-derives the parts of L4, L5, L8 it uses). Cross-check: the proof run as an algorithm on every β = 2 core and profile, n = 2–8 (98,991,756 core–profile pairs), every output EFX₀ by the raw definition, 0 failures; certificates `results/certs_beta2_{2..8}.json.gz` accepted by `tools/check_certs.py` (`results/check_certs_beta2.log`). Includes n = 2, 3, 4, not covered by R1 |
| D | Every core has an EFX₀ allocation with at most one bundle of more than two goods | CONJECTURE | | | certified n ≤ 6; n = 7 at m = 13; proved for β = 2, all n (D2) |
| T | TARGET: EFX₀ exists whenever every agent has ≤ 3 relevant goods | OPEN | | | implied by D |
| T2 | TARGET holds for every instance whose core has only connected components with β ≤ 2 | PROVED | `proofs/beta2.md` | | D2 with L2, L3, L6, L8 (those proofs are sketches in `proofs/lemmas.md`) |

## Lessons
- About 3,000 random cores "supported" conjecture A; exhaustive search refuted it in minutes (failures: 1 to 747 of 46,656 profiles per hypergraph, median 22; `results/fail_density_6_10.log`. An earlier sample of three hypergraphs showed 2 to 36).
- Every UNSAT claim that refutes a conjecture gets a second, independently written encoding before it enters this ledger.

## Open items
1. ~~Independent re-implementation of the core enumeration (the trust point of R1): reproduce 15 / 211 / 25 / 37.~~ Done: `src/cores_nauty.py` (nauty genbg) matches `gen_cores` up to isomorphism, `results/enum_crosscheck.log`.
2. Verify the Mahara citation (m ≤ n + 3).
3. ~~Regenerate the n = 7, m = 13 certificates~~ (done: `results/certs_7_13.json.gz`); run m = 12 and 11 (`src/run7.py 12 11`: 541 and 3,103 cores, about 1 and 10 min on 4 CPUs); then n = 8 at m = 15 (`src/run7.py 15 --n=8`: 52 cores, 15 s). Beyond the plan, estimated from samples on 4 CPUs: n = 8, m = 14: 1,232 cores, ~20 min; m = 13: 11,478 cores, ~13 h; m = 12: 52,889 cores, ~4 days.
4. Characterize the large bundle (Step 2). ~~Attempt D for β = 2 via L11~~ done: D2, `proofs/beta2.md` (collector theorem and Lemma O; no path shortening was needed).
5. Conjecture D for β = 3 (m = 2n − 2, plan Step 3.2): the collector theorem (D2.C) absorbs exactly one deficit unit, and a β = 3 core without Q-agents has two; see `proofs/beta2.md` §6.
