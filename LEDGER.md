# Ledger: EFX₀ with at most three relevant goods per agent

The single source of truth. A status changes only in a pull request that adds the artifact in the Artifact column; CI checks that every PROVED, CERTIFIED or REFUTED row points to files that exist. The Lean column names machine-checked statements in `lean/` (core Lean, no `sorry`, standard axioms only; see `lean/README.md`); CI checks that each has a `#print axioms` certificate and that `lean/check.sh` passes.

| ID | Claim | Status | Artifact | Lean | Notes |
|---|---|---|---|---|---|
| L1 | For fixed (n, m): EFX₀ for all additive instances ⟺ EFX for all positive additive instances | PROVED | `proofs/lemmas.md` | | sketch; expand in Step 0 |
| L2 | Peeling rules R1 and R2 | PROVED | `proofs/lemmas.md` | `EFX.peel`, `EFX.peelEmpty`, `EFX.peelR2`, `EFX.peelBundle` | Lean (over lists): R1, R1 with P = ∅, R2 (without its unused hypothesis that P has ≥ 2 goods), and the general peeling step that R2 and R1 with P = ∅ instantiate. `src/lemmas.py`: 1,500 random instances through the pipeline, 0 failures |
| L2c | ≤ 2 relevant goods per agent ⟹ EFX₀ (serial dictatorship; the HW1 theorem) | PROVED | `proofs/lemmas.md` | `EFX.exists_efx0_of_count` | stronger form (all bundles but one have ≤ 1 good) machine-checked in evanlin23/mrd-efx: `MRD.main_theorem_L` |
| L3 | Worthless goods go to an envy-graph source | PROVED | `proofs/lemmas.md` | `EFX.junk`, `EFX.Inst.exists_efx0_of_junk`, `EFX.rotate_efx0`, `EFX.exists_unenvied` | same pipeline test. Lean: over lists and in the model; rotation preserves EFX₀, and rotating envy cycles reaches an allocation with an unenvied agent |
| L4 | Core counting: 3n = 2m − π + Σ(deg − 2), so m ≤ 2n | PROVED | `proofs/lemmas.md` | | |
| L5 | In a core, EFX₀ is ordinal and equals cases T/P/B/C/E | PROVED | `proofs/lemmas.md` | | `src/coreG.py`: 896,400 allocations vs. the definition, 0 mismatches |
| L6 | Disconnected cores are solved component by component | PROVED | `proofs/lemmas.md` | | |
| L7 | β = 2n − m + 1; alone-goods identity | PROVED | `proofs/lemmas.md` | | |
| L8 | Two own goods ⟹ safe; β = 1 cores solved by orientation | PROVED | `proofs/lemmas.md` | `EFX.Inst.safe_of_two_own`, `EFX.envyFree_of_two_own`, `EFX.Inst.efx0_of_two_own`, `EFX.balance_needed` | Lean: the first half, for agents with a ≤ b + c (all core agents), and "every agent holds two own goods ⟹ EFX₀". Balance is necessary (`EFX.balance_needed`: a top-heavy counterexample). Not formalized: that a β = 1 core admits such an allocation |
| L9 | Bundles ≤ 2: EFX₀ ⟺ every good in another's 2-good bundle is worth ≤ own bundle | PROVED | `proofs/lemmas.md` | | basis of `src/verify_fail.py` |
| L10 | Insertion lemma | PROVED | `proofs/lemmas.md` | | |
| L11 | Cores are subdivisions of finitely many shapes per β; β = 2: theta, dumbbell, figure-eight | PROVED | `proofs/lemmas.md` | | |
| L12 | Collisions vs. P-capacity: an EFX₀ allocation with all bundles ≤ 2 and e empty bundles leaves ≥ δ contested tops alone, so δ ≤ σ − 2e (δ = #contested tops − P-capacity, σ = 2n − m) | PROVED | `proofs/construction.md` | | §2. Necessary only, and never the binding reason for n ≤ 5: every C2-failing profile there has δ ≤ σ (`results/large_bundle_relate.log`) |
| L13 | Construction LB is sound: any allocation it returns is EFX₀ with ≤ 1 bundle of > 2 goods; that bundle has #NA − σ + 2 goods (NA = the goods some agent needs alone) | PROVED | `proofs/construction.md`, `src/construct.py` | | §3, Theorems 1–2 (direct from the EFX₀ definition, no L5). LB can fail only in its last step (no owner for the overflow) |
| R1 | EFX₀ exists for every instance with ≤ 3 relevant goods per agent and n ≤ 6 | CERTIFIED | `results/certs_5_6.json.gz`, `results/frontier_results_5_6.json`, `results/enum_crosscheck.log` | | conditional on Mahara (m ≤ n + 3; R3 removes this condition); 251 connected cores, enumeration reproduced independently (nauty genbg, bijection up to isomorphism); CI re-checks without SAT |
| R2 | Conjecture D holds for n = 7, m = 13 | CERTIFIED | `results/frontier_results_7.json`, `results/certs_7_13.json.gz`, `results/enum_crosscheck.log` | | 37 cores (enumeration reproduced independently); CI re-checks the certificates without SAT |
| R3 | Conjecture D for every core with n ≤ 6 (connected or not, every m), by construction LB; hence T for n ≤ 6 without Mahara | CERTIFIED | `results/certs_lb_2_6.json.gz`, `results/certs_lb_disconnected_4_6.json.gz`, `results/check_certs_lb.log`, `results/construct_2_5.log`, `results/construct_6.log`, `results/construct_6_cert.log`, `results/construct_disconnected_4_6.log`, `results/enum_crosscheck_all_m.log` | | 3,436 connected and 131 disconnected cores, all 6^n profiles each: LB never fails. Every output checked against the raw definition in `src/construct.c`; C and Python implementations give identical outputs (all cores n ≤ 5, every 10th at n = 6, all disconnected); certificates (LB's own outputs) re-checked by `tools/check_certs.py` (CI); enumeration cross-checked at every (n, m) with n ≤ 6. `proofs/construction.md` §4 |
| X1 | Bundles ≤ 2 always suffice in a core | REFUTED | `results/exhaust5.log`, `proofs/construction.md`, `results/large_bundle_c2.log` | | n = 5: 1,226 of 93,312 profiles. Smallest: n = 3, m = 5, agents (0,1,p₀), (0,1,p₁), (0,1,p₂) with private p_i (hand proof, §1); no failure at n = 2; SAT and brute force agree on every core with n ≤ 4 |
| X2 | Conjecture A: m ≤ 2n − 2 ⟹ bundles ≤ 2 suffice | REFUTED | `results/frontier_results_5_6.json`, `src/verify_fail.py`, `proofs/counterexamples.md` | | n = 6, m = 10: 57 of 211 cores; two independent encodings |
| X3 | Conjecture A for non-core instances | REFUTED | `proofs/counterexamples.md` | | four identical agents + three worthless goods |
| X4 | One bundle of 3 goods always suffices | REFUTED | `results/frontier_results_5_6.json` | | single implementation; confirm independently |
| D | Every core has an EFX₀ allocation with at most one bundle of more than two goods | CONJECTURE | | | certified for every core with n ≤ 6, connected or not, every m (R3); n = 7 at m = 13 (R2) |
| LB | Construction LB never fails (implies D, by L13) | CONJECTURE | | | certified n ≤ 6 (R3). `src/construct.py`; the gap is its last step, `proofs/construction.md` §3 |
| T | TARGET: EFX₀ exists whenever every agent has ≤ 3 relevant goods | OPEN | | | implied by D; holds for n ≤ 6 (R3) |

## Lessons
- About 3,000 random cores "supported" conjecture A; exhaustive search refuted it in minutes (failures: 1 to 747 of 46,656 profiles per hypergraph, median 22; `results/fail_density_6_10.log`. An earlier sample of three hypergraphs showed 2 to 36).
- Every UNSAT claim that refutes a conjecture gets a second, independently written encoding before it enters this ledger.

## Open items
1. ~~Independent re-implementation of the core enumeration (the trust point of R1): reproduce 15 / 211 / 25 / 37.~~ Done: `src/cores_nauty.py` (nauty genbg) matches `gen_cores` up to isomorphism, `results/enum_crosscheck.log`.
2. Verify the Mahara citation (m ≤ n + 3).
3. ~~Regenerate the n = 7, m = 13 certificates~~ (done: `results/certs_7_13.json.gz`); run m = 12 and 11 (`src/run7.py 12 11`: 541 and 3,103 cores, about 1 and 10 min on 4 CPUs); then n = 8 at m = 15 (`src/run7.py 15 --n=8`: 52 cores, 15 s). Beyond the plan, estimated from samples on 4 CPUs: n = 8, m = 14: 1,232 cores, ~20 min; m = 13: 11,478 cores, ~13 h; m = 12: 52,889 cores, ~4 days.
4. Characterize the large bundle (done for n ≤ 6: `proofs/construction.md`, construction LB); attempt D for β = 2 via L11.
5. Prove that construction LB never fails (its last step: an owner for the overflow bundle whose bundle holds no b_k, c_k pair of an agent holding only its top), or find the smallest core where it fails.
