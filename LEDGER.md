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
| R2 | Conjecture D holds for every connected core with n = 7 and 11 ≤ m ≤ 13 | CERTIFIED | `results/certs_7_13.json.gz`, `results/certs_7_12.json.gz`, `results/certs_7_11.json.gz`, `results/frontier_results_7.json`, `results/frontier_results_7_12.json`, `results/frontier_results_7_11.json`, `results/check_certs_frontier.log`, `results/check_enum.log`, `results/enum_crosscheck.log` | | m = 13, 12, 11: 37, 541, 3,103 cores, each with an allocation in model C3 for every one of the 6^7 profiles (with L8 for m = 14: every connected core with n = 7 and m ≥ 11). Lists complete by orbit counting (`tools/check_enum.py`, independent of nauty; m = 13 also reproduced by gen_cores). Certificates re-checked without SAT, D shape included (`check_certs.py --require-d`): CI re-checks m = 13, 12 and all orbit counts; m = 11 (2.5 min on 4 CPUs) is re-checked locally, see the log |
| R3 | Conjecture D holds for every connected core with n = 8 and m ∈ {14, 15} | CERTIFIED | `results/certs_8_15.json.gz`, `results/certs_8_14.json.gz`, `results/frontier_results_8_15.json`, `results/frontier_results_8_14.json`, `results/check_certs_frontier.log`, `results/check_enum.log` | | m = 15 (β = 2), 14 (β = 3): 52, 1,232 cores, each with an allocation in model C3 for every one of the 6^8 profiles (m = 16 by L8). Lists complete by orbit counting. Certificates re-checked without SAT, D shape included: CI re-checks m = 15 and the orbit counts; m = 14 (7.5 min on 4 CPUs) is re-checked locally, see the log. n = 8, m ≤ 13 not run |
| R4 | EFX₀ exists for every instance with ≤ 3 relevant goods per agent and n ≤ 7 | CERTIFIED | `results/certs_5_6.json.gz`, `results/certs_7_13.json.gz`, `results/certs_7_12.json.gz`, `results/certs_7_11.json.gz`, `results/check_enum.log` | | conditional on Mahara (m ≤ n + 3), like R1, and by R1's argument (L1–L8): every connected component of a core with ≤ 7 agents has n′ ≥ 2 agents and m′ goods with m′ = 2n′ (L8), m′ ≤ n′ + 3 (Mahara via L1), or (n′, m′) ∈ {(5, 9), (6, 10), (6, 11), (7, 11), (7, 12), (7, 13)} (R1, R2) |
| X1 | Bundles ≤ 2 always suffice in a core | REFUTED | `results/exhaust5.log` | | n = 5: 1,226 of 93,312 profiles |
| X2 | Conjecture A: m ≤ 2n − 2 ⟹ bundles ≤ 2 suffice | REFUTED | `results/frontier_results_5_6.json`, `src/verify_fail.py`, `proofs/counterexamples.md` | | n = 6, m = 10: 57 of 211 cores; two independent encodings |
| X3 | Conjecture A for non-core instances | REFUTED | `proofs/counterexamples.md` | | four identical agents + three worthless goods |
| X4 | One bundle of 3 goods always suffices | REFUTED | `results/frontier_results_5_6.json` | | single implementation; confirm independently |
| D | Every core has an EFX₀ allocation with at most one bundle of more than two goods | CONJECTURE | | | certified for connected cores with n ≤ 7 and m ≥ n + 4 (R1, R2; m = 2n by L8) and with n = 8, m ≥ 14 (R3). Not checked for m ≤ n + 3 (there EFX₀ comes from Mahara, with no bound on bundle sizes) nor for n = 8, m ≤ 13 |
| T | TARGET: EFX₀ exists whenever every agent has ≤ 3 relevant goods | OPEN | | | implied by D; holds for n ≤ 7 (R1, R4; conditional on Mahara) |

## Lessons
- About 3,000 random cores "supported" conjecture A; exhaustive search refuted it in minutes (failures: 1 to 747 of 46,656 profiles per hypergraph, median 22; `results/fail_density_6_10.log`. An earlier sample of three hypergraphs showed 2 to 36).
- Every UNSAT claim that refutes a conjecture gets a second, independently written encoding before it enters this ledger.

## Open items
1. ~~Independent re-implementation of the core enumeration (the trust point of R1): reproduce 15 / 211 / 25 / 37.~~ Done: `src/cores_nauty.py` (nauty genbg) matches `gen_cores` up to isomorphism, `results/enum_crosscheck.log`.
2. Verify the Mahara citation (m ≤ n + 3).
3. ~~Regenerate the n = 7, m = 13 certificates; run m = 12 and 11; then n = 8 at m = 15 and 14~~ Done (R2, R3; logs `results/frontier7_12.log`, `results/frontier7_11.log`, `results/frontier8_15.log`, `results/frontier8_14.log`): measured on 4 CPUs, n = 7: m = 12 in 46 s, m = 11 in 11 min; n = 8: m = 15 in 20 s, m = 14 in 33 min (roughly the first half on shared CPUs; the estimate was ~20 min). Not run, estimated from samples on 4 CPUs and probably low given m = 14: n = 8, m = 13: 11,478 cores, ~13 h; m = 12: 52,889 cores, ~4 days. D for m ≤ n + 3 is also unchecked (TARGET holds there by Mahara).
4. Characterize the large bundle; attempt D for β = 2 via L11.
