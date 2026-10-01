# compute/k4-rt4, slice n4_3_x4: summary

Conjecture DL_RT4 (RT4 = T1 ∪ T2 ∪ T3 ∪ T4, `k4/dlrt4.c`'s header; `k4/dl2.md`, `results/k4_dl13/n4_FAILURES.md`) on **every profile**
of the n = 4 cores with three 4-good agents at core positions **171 to 227** (0-based; 57 cores, all m = 8) of
`results/k4_certs_4_n4_3.json.gz`. EVIDENCE only.

Tool: `k4/dlrt4_run.py` with `k4/dlrt4.c` sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`, checked before the run
and printed by the driver. Branch `compute/k4-rt4-n4-3-x4` from `compute/k4-rt4` at 2e9adeb (after 862c0cd), 4 CPUs.
`--cores=A:B` is `range(A, B)` in the driver (B exclusive), so the run uses `--cores=171:228`.

```
python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=171:228 --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_3_x4.jsonl --dump=results/k4_rt4/dump_n4_3_x4.jsonl.gz --tables=results/k4_rt4/tables_n4_3_x4.json
```

## Result

| run | cores | profiles | ω ≥ 1 | f ≥ 1 states with def > 0 | DL_RT4 failures (f ≥ 1) | f = 0 states (RT4 fails) | wall time (CPU time of the units) |
|---|---|---:|---:|---:|---:|---:|---|
| n4_3_x4 (exhaustive) | 171..227 | 6,449,725,440 | 375,679,744 | 6,446,728 | **0** | 0 (0) | 4,668 s (17,888 s) |

**DL_RT4 holds at every f ≥ 1 state of the slice.** There were no failures, so there is no `n4_3_x4_FAILURES.md`. Anomalies 0 + 0. The run
completed in one go, with no restart (the checkpoint has 57 units, positions 171..227, each once). Core 172 has no state with def > 0. The
other 56 cores all have states.

States by f: f = 1: 1,599,840; f = 2: 4,846,888; no state has f ≥ 3. Nearest better state (k(P)) at distance 1: 5,724,812, at distance 2:
721,916, none farther. The smallest RT4 move has the same counts (size 1: 5,724,812, size 2: 721,916, none of size ≥ 3).
Pareto-maximal states: 678,140.

## Repair branches (f ≥ 1 states, each counted once per branch it has an improving move of)

| | all | f = 1 | f = 2 |
|---|---:|---:|---:|
| states | 6,446,728 | 1,599,840 | 4,846,888 |
| T1 | 5,724,812 | 1,588,288 | 4,136,524 |
| T2 | 5,006,036 | 1,594,736 | 3,411,300 |
| T3p | 5,255,280 | 720,544 | 4,534,736 |
| T3h | 6,027,304 | 1,330,384 | 4,696,920 |
| T4 | 1,559,160 | 0 | 1,559,160 |
| only T1 / only T2 / only T4 | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 |
| only T3 (T3p and/or T3h) | 410,020 | 2,496 | 407,524 |
| R_T = T1+T2+T3 fails | 0 | 0 | 0 |
| R_13 = T1+T3 fails | 0 | 0 | 0 |
| R_13 + T4 fails | 0 | 0 | 0 |

The f = 2 "only T3" states split into 307,276 with T3p and T3h and 100,248 with T3p alone. The f = 1 ones all have both.
Every state with an improving T4 move has one of size 2, a transposition (table C: `2|2|2`, 1,559,160). In this slice T4 is never needed:
R_13 alone already repairs every state. Per f, the least size of an improving move of each branch available (table Z): T1 1; T2 2 (f = 1:
4,224 states at 3); T3p 2; T3h 3; T4 2.

## Timing

The estimate printed after the first unit (core 174: 71,663,616 profiles in 203.1 s) was about 353k profiles/s per process, 18,300 CPU-s,
about 1.3 h on 4 CPUs. Measured: 17,888 CPU-s of units, 4,668 s (1.30 h) wall; the longest unit took 463 s.

## Files (all under `results/k4_rt4/`)

- `n4_3_x4.log`: it starts with the command line and the dlrt4.c sha256, then the counters and tables B, G, M, Z, C, Y;
- `tables_n4_3_x4.json`: merged counters and tables;
- `ckpt_n4_3_x4.jsonl`: one line per core (57), with its counters, tables and time;
- `dump_n4_3_x4.jsonl.gz`: 1,090 "D" records from 56 cores (the first f ≥ 1 state of each (signature, branch) cell per core, with the core
  and the values; no failure records, and no "outside R_13" records since R_13 never fails).

LEDGER.md is not edited and no pull request is opened.
