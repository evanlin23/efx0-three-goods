# Ledger: EFX₀ with at most three relevant goods per agent

The single source of truth. A status changes only in a pull request that adds the artifact in the Artifact column; CI checks that every PROVED, CERTIFIED or REFUTED row points to files that exist.

| ID | Claim | Status | Artifact | Notes |
|---|---|---|---|---|
| L1 | For fixed (n, m): EFX₀ for all additive instances ⟺ EFX for all positive additive instances | PROVED | `proofs/lemmas.md` | sketch; expand in Step 0 |
| L2 | Peeling rules R1 and R2 | PROVED | `proofs/lemmas.md` | `src/lemmas.py`: 1,500 random instances through the pipeline, 0 failures |
| L2c | ≤ 2 relevant goods per agent ⟹ EFX₀ (serial dictatorship; the HW1 theorem) | PROVED | `proofs/lemmas.md` | |
| L3 | Worthless goods go to an envy-graph source | PROVED | `proofs/lemmas.md` | same pipeline test |
| L4 | Core counting: 3n = 2m − π + Σ(deg − 2), so m ≤ 2n | PROVED | `proofs/lemmas.md` | |
| L5 | In a core, EFX₀ is ordinal and equals cases T/P/B/C/E | PROVED | `proofs/lemmas.md` | `src/coreG.py`: 896,400 allocations vs. the definition, 0 mismatches |
| L6 | Disconnected cores are solved component by component | PROVED | `proofs/lemmas.md` | |
| L7 | β = 2n − m + 1; alone-goods identity | PROVED | `proofs/lemmas.md` | |
| L8 | Two own goods ⟹ safe; β = 1 cores solved by orientation | PROVED | `proofs/lemmas.md` | |
| L9 | Bundles ≤ 2: EFX₀ ⟺ every good in another's 2-good bundle is worth ≤ own bundle | PROVED | `proofs/lemmas.md` | basis of `src/verify_fail.py` |
| L10 | Insertion lemma | PROVED | `proofs/lemmas.md` | |
| L11 | Cores are subdivisions of finitely many shapes per β; β = 2: theta, dumbbell, figure-eight | PROVED | `proofs/lemmas.md` | |
| R1 | EFX₀ exists for every instance with ≤ 3 relevant goods per agent and n ≤ 6 | CERTIFIED | `results/certs_5_6.json.gz`, `results/frontier_results_5_6.json`, `results/enum_crosscheck.log` | conditional on Mahara (m ≤ n + 3); 251 connected cores, enumeration reproduced independently (nauty genbg, bijection up to isomorphism); CI re-checks without SAT |
| R2 | Conjecture D holds for n = 7, m = 13 | CERTIFIED | `results/frontier_results_7.json`, `results/certs_7_13.json.gz`, `results/enum_crosscheck.log` | 37 cores (enumeration reproduced independently); CI re-checks the certificates without SAT |
| X1 | Bundles ≤ 2 always suffice in a core | REFUTED | `results/exhaust5.log` | n = 5: 1,226 of 93,312 profiles |
| X2 | Conjecture A: m ≤ 2n − 2 ⟹ bundles ≤ 2 suffice | REFUTED | `results/frontier_results_5_6.json`, `src/verify_fail.py`, `proofs/counterexamples.md` | n = 6, m = 10: 57 of 211 cores; two independent encodings |
| X3 | Conjecture A for non-core instances | REFUTED | `proofs/counterexamples.md` | four identical agents + three worthless goods |
| X4 | One bundle of 3 goods always suffices | REFUTED | `results/frontier_results_5_6.json` | single implementation; confirm independently |
| D | Every core has an EFX₀ allocation with at most one bundle of more than two goods | CONJECTURE | | certified n ≤ 6; n = 7 at m = 13 |
| T | TARGET: EFX₀ exists whenever every agent has ≤ 3 relevant goods | OPEN | | implied by D |

## Lessons
- About 3,000 random cores "supported" conjecture A; exhaustive search refuted it in minutes (failures: 1 to 747 of 46,656 profiles per hypergraph, median 22; `results/fail_density_6_10.log`. An earlier sample of three hypergraphs showed 2 to 36).
- Every UNSAT claim that refutes a conjecture gets a second, independently written encoding before it enters this ledger.

## Open items
1. ~~Independent re-implementation of the core enumeration (the trust point of R1): reproduce 15 / 211 / 25 / 37.~~ Done: `src/cores_nauty.py` (nauty genbg) matches `gen_cores` up to isomorphism, `results/enum_crosscheck.log`.
2. Verify the Mahara citation (m ≤ n + 3).
3. ~~Regenerate the n = 7, m = 13 certificates~~ (done: `results/certs_7_13.json.gz`); run m = 12 and 11 (`src/run7.py 12 11`: 541 and 3,103 cores); then n = 8 at m = 15 (`src/run7.py 15 --n=8`: 52 cores).
4. Characterize the large bundle; attempt D for β = 2 via L11.
