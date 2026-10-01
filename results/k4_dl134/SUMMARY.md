# compute/k4-dl134: summary

Conjecture DL₁₃₄: DL₁₃ (`k4/dl2.md` §3, ledger K4.DL2.T13) with a third move **(T4)** added. T4 permutes the frozen
agents' singleton bases among the frozen agents. Every frozen agent stays frozen, NA′ = NA, and all other bases are
unchanged; any cycle structure is allowed. R_134 = T1 ∪ T3 ∪ T4. Branch `compute/k4-dl134`, from 0617abf
(compute/k4-dl13-n4), 4 CPUs. **EVIDENCE only.** The ledger is not edited and no pull request is opened.

**Result: DL₁₃₄ fails at no f ≥ 1 state of any run.** That includes all 3,062 DL₁₃ failures of `results/k4_dl13`.
T4 is needed exactly at the DL₁₃ failures, and at each of them **a single 2-swap of two frozen agents' goods
suffices**. No state needs a longer cycle. So `FAILURES.md` is not written.

## Tools and validation

- `k4/dl134.c` (sha256 `2a24ba5045b25414530928ea81b7a6bbd9aef6d33c7fa52e39fffe9293267cee`) is a copy of `k4/dl13.c` with
  the T4 test added. Per state it gives the R_134 branch (T1, T3p, T3h, T4) and the cycle types of the improving T4
  moves ("2" = a single 2-swap, "3", "2+2", …). dl13.c's own output is kept: the "K" line (dl2.c's) and the "L" line
  (DL₁₃'s counters). The new "M" line holds DL₁₃₄'s counters. Above 3,000 min-frozen P, the T4 candidates are every
  bijection of the frozen agents onto their goods, looked up in the class's hash.
- `k4/dl134_run.py`: a copy of `k4/dl13_run.py` that builds dl134.c. Its added `tsv` mode runs the failing profiles
  of `results/k4_dl13/n4_failures_*.tsv` and reports each listed state.
- `k4/dl134_ref.py`: the independent Python reference.
  - 𝒫 and def come from `k4/suite/model.py`.
  - T1 and T3 come from `k4/dl2_relations.py` (its R13).
  - T4 has its own test, written from the definition.
  - It compares per state: f, def, k, the nearest R_13 and R_134 distances, t1/t3p/t3h/t4, the T1, T3 and T4 type
    sets, and dT1/dT3/dT4.
  - It also checks that the `-DBIGPP=0` (hash) build's whole output is identical, that the "K" line equals dl2.c's
    and that the "L" line equals dl13.c's.

| validation input (log) | profiles | states compared (f ≥ 1) | with an improving T4 move | mismatches |
|---|---:|---:|---:|---:|
| suite, n ≤ 6 (`validate_suite.log`) | 148 | 360 (162) | 0 | 0 |
| the 1,131 DL₁₃-failing profiles, the 3,062 failing states among them (`validate_failures.log`) | 1,131 | 7,586 (7,586) | 7,586 | 0 |
| n = 3 cores, random, screened for f ≥ 1 (`validate_rand_n3.log`) | 760 | 2,004 (2,004) | 209 | 0 |
| n = 4 cores (all four files), random, screened for f ≥ 1 (`validate_rand_n4.log`) | 647 | 2,031 (2,031) | 91 | 0 |
| unscreened random profiles, n = 3 and n = 4 (same logs) | 600 | 29 (1) | 0 | 0 |

- `validate_mutations.log`: six mutations of dl134.c are each caught. They are: T4 limited to 2-swaps, no T4, T4
  without the NA and frozen-status conditions, wrong cycle names, and two faults in the hash-mode candidate generation.
- `t4only_xcheck.log`: the reference agrees at all 3,066 T4-only states dumped by runs (b)–(d).

## Runs

Each log starts with its command line. Every run used `--jobs=4` (`nproc`), and (b)–(d) used a checkpoint. No run
was interrupted, so each wall time is a single invocation.

| run | profiles | f >= 1 states, def > 0 | DL134 fails at | DL13 fails at | repaired by T4 only (a 2-swap / longer cycles only) | with an improving T1 / T3 / T4 move | wall time (CPU time of the units) |
|---|---:|---:|---:|---:|---:|---:|---|
| (a) the DL13 failures of results/k4_dl13 (1,131 profiles) | 1,131 | 7,586 | **0** | 3,062 | 3,062 (3,062 / 0) | 0 / 4,524 / 7,586 | 1 s |
| (b) `k4_certs_4_n4_1`, exhaustive | 7,247,232 | 286 | **0** | 20 | 20 (20 / 0) | 0 / 266 / 140 | 6 s (17 s) |
| (c) `k4_certs_4_n4_2`, exhaustive | 724,847,616 | 324,658 | **0** | 3,040 | 3,040 (3,040 / 0) | 229,032 / 321,618 / 63,560 | 1313 s (5,134 s) |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 1 | 169,500 | 1,110 | **0** | 0 | 0 (0 / 0) | 1,055 / 1,102 / 57 | 3 s (11 s) |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 2 | 169,500 | 1,047 | **0** | 2 | 2 (2 / 0) | 983 / 1,042 / 108 | 3 s (10 s) |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 3 | 169,500 | 1,037 | **0** | 2 | 2 (2 / 0) | 987 / 1,029 / 72 | 3 s (10 s) |
| (d) `k4_certs_4_pure`, 500 per core, seed 1 | 109,500 | 3,141 | **0** | 0 | 0 (0 / 0) | 2,976 / 3,125 / 97 | 4 s (15 s) |
| (d) `k4_certs_4_pure`, 500 per core, seed 2 | 109,500 | 3,111 | **0** | 2 | 2 (2 / 0) | 2,965 / 3,094 / 95 | 4 s (15 s) |
| (d) `k4_certs_4_pure`, 500 per core, seed 3 | 109,500 | 3,529 | **0** | 0 | 0 (0 / 0) | 3,310 / 3,521 / 129 | 4 s (15 s) |

For (b) and (c), the DL₁₃ counters (dl13.c's "L" line) equal those in `results/k4_dl13/n4_1.log` and `n4_2.log`.
(c) took 1.35 times dl13.c's wall time on the same file.

**R_134 branches** of the f ≥ 1 states with def > 0. The classes are exclusive; T3 means T3p or T3h; "none" would be a
DL₁₃₄ failure.

| run | T1 | T3 | T4 | T1+T3 | T1+T4 | T3+T4 | T1+T3+T4 | none |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| (a) the DL13 failures of results/k4_dl13 (1,131 profiles) | 0 | 0 | 3,062 | 0 | 0 | 4,524 | 0 | 0 |
| (b) `k4_certs_4_n4_1`, exhaustive | 0 | 146 | 20 | 0 | 0 | 120 | 0 | 0 |
| (c) `k4_certs_4_n4_2`, exhaustive | 0 | 47,106 | 3,040 | 213,992 | 0 | 45,480 | 15,040 | 0 |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 1 | 8 | 45 | 0 | 1,000 | 0 | 10 | 47 | 0 |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 2 | 3 | 23 | 2 | 913 | 0 | 39 | 67 | 0 |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 3 | 6 | 32 | 2 | 927 | 0 | 16 | 54 | 0 |
| (d) `k4_certs_4_pure`, 500 per core, seed 1 | 16 | 133 | 0 | 2,895 | 0 | 32 | 65 | 0 |
| (d) `k4_certs_4_pure`, 500 per core, seed 2 | 15 | 118 | 2 | 2,883 | 0 | 26 | 67 | 0 |
| (d) `k4_certs_4_pure`, 500 per core, seed 3 | 8 | 169 | 0 | 3,223 | 0 | 50 | 79 | 0 |

**T4 cycle types**: the number of f ≥ 1 states with an improving T4 move of each type. Only "2" and "3" occur: every state with
a T4 move has f = 2 or 3.

| run | T4 "2" | T4 "3" |
|---|---:|---:|
| (a) the DL13 failures of results/k4_dl13 (1,131 profiles) | 5,324 | 5,324 |
| (b) `k4_certs_4_n4_1`, exhaustive | 120 | 80 |
| (c) `k4_certs_4_n4_2`, exhaustive | 61,320 | 32,000 |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 1 | 57 | 0 |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 2 | 106 | 12 |
| (d) `k4_certs_4_n4_3`, 500 per core, seed 3 | 70 | 4 |
| (d) `k4_certs_4_pure`, 500 per core, seed 1 | 97 | 0 |
| (d) `k4_certs_4_pure`, 500 per core, seed 2 | 93 | 14 |
| (d) `k4_certs_4_pure`, 500 per core, seed 3 | 129 | 20 |


## What the runs show

- **DL₁₃₄ holds at every f ≥ 1 state tested.** That is 337,919 states over runs (b)–(d), plus the 7,586 states of the
  failing profiles in (a). The nearest improving R_134 move always involves at most 3 agents.
- **T4 is needed exactly at the DL₁₃ failures**, and only there. That is 3,062 states in (a) and 3,066 in runs (b)–(d):
  the 3,062 again, plus 4 from the new seeds. Every one has the shape of `results/k4_dl13/n4_FAILURES.md`: f = 3
  (one free agent), def = 1, k = 2, signature G or O.
- **At each such state a single 2-swap of two frozen agents' goods lowers the deficit to 0.** A 3-cycle of the
  three frozen goods also does (table Q: `3|2|2,3` at every one).
- **New DL₁₃ failures**, not in `results/k4_dl13` (seed 3 is new; for `pure` seed 2 they are among draws 201–500). Each profile has 2 failing
  states, the twin agents swapped, and both are repaired by a 2-swap:
  - `k4_certs_4_n4_3` pos 153 (idx 16, m = 8): sets [[0,2,5,7],[1,5,6,7],[3,5,6,7],[4,6,7]], profile
    (65, 35, 40, 1), seed 3.
  - `k4_certs_4_pure` pos 26 (idx 5, m = 7): sets [[0,2,5,6],[1,4,5,6],[3,4,5,6],[3,4,5,6]], profile
    (6, 183, 103, 3), seed 2. All four agents have 4 goods.

  So the DL₁₃ failures also occur at m = 8, and on a core where every agent has 4 goods.
- **f = 0**: R_134 fails at 8 (`pure` seed 2) and 5 (`pure` seed 3) states with f = 0. These lie outside DL₁₃₄,
  which is stated for f ≥ 1. With no frozen agent there is no T3 or T4 move, so R_134 = R_13 there, and Theorem Z
  covers f = 0 (`k4/dl2.md` §3). dl13.c's counters fail at the same 8 and 5 states (R_13 fails there too).
- **T4 moves at f = 2**: they appear only alongside T1 or T3 moves. No f = 2 state needs T4.

## Files (`results/k4_dl134/`)

- Validation: `validate_*.log`, `validate_mutations.py`, `t4only_xcheck.{py,log}`.
- (a): `dl13fail.log`, `dl13fail_states.tsv` (one line per failing state: branch, T4 cycle types, distances, dT4),
  `dump_dl13fail.jsonl.gz`, `tables_dl13fail.json`.
- (b)–(d): `n4_1.log`, `n4_2.log`, `{n4_3,pure}_s500_seed{1,2,3}.log`, each with `tables_*.json`,
  `dump_*.jsonl.gz` and `ckpt_*.jsonl`. The dumps hold every T4-only state with its improving T4 moves
  (`t4moves`), the first state of each (signature, branch) cell, and every 50th state without a T1 move.
- `summary_table.py` writes the three tables above.

Reproduce: rerun the command on the first line of each log. `python3 k4/dl134_ref.py suite --jobs=4` (19 s) re-runs
the comparison on the suite.

## For the coordinator (the ledger is unchanged)

- DL₁₃₄ survives everything run here, so it is a candidate successor to K4.DL2.T13. The data suggest something
  narrower may suffice: T4 restricted to **2-swaps of frozen goods**, i.e. a "frozen exchange" keeping NA. On these
  runs DL holds for that narrower relation at every state where it holds for R_134.
- Coverage: n = 4, exhaustive on `k4_certs_4_n4_1` and `k4_certs_4_n4_2`, sampled on `n4_3` and `pure`. n = 3 was
  not re-run here, but R_13 ⊆ R_134, so every state where `k4/dl2.md` §3 found DL₁₃ to hold also satisfies DL₁₃₄.
  n ≥ 5 is not covered.
