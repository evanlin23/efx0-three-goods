# compute/k4-rt4, slice n4_3_x3: summary

Conjecture DL_RT4 (RT4 = T1 ∪ T2 ∪ T3 ∪ T4, `k4/dlrt4.c`'s header; `k4/dl2.md`, `results/k4_dl13/n4_FAILURES.md`) on
**every profile** of the n = 4 cores with three 4-good agents at core positions **114 to 170** (0-based, 57 cores) of
`results/k4_certs_4_n4_3.json.gz`. Run with `k4/dlrt4_run.py` (dlrt4.c sha256
`fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`, checked before the run) on 4 CPUs, branch
`compute/k4-rt4-n4-3-x3` from 2e9adeb (on `compute/k4-rt4`, after 862c0cd). EVIDENCE only.

`dlrt4_run.py`'s `--cores=A:B` is `range(A, B)`, so it excludes B. The run used `--cores=114:171`, and the log's
header reads "cores 114..170, 57 units". The checkpoint holds exactly positions 114..170, one unit each, all from this
one run (no restart).

Command (the first line of `n4_3_x3.log`):

    python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=114:171 --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_3_x3.jsonl --dump=results/k4_rt4/dump_n4_3_x3.jsonl.gz --tables=results/k4_rt4/tables_n4_3_x3.json

## Result

| run | slice | profiles | ω ≥ 1 | f ≥ 1 states with def > 0 (f = 1 / 2 / 3) | DL_RT4 failures (f ≥ 1) | f = 0 states | anomalies | wall time (CPU time of the units) |
|---|---|---:|---:|---:|---:|---:|---:|---|
| n4_3_x3 | cores 114..170, every profile | 5,518,098,432 | 305,539,848 | 6,716,042 (96,280 / 6,520,498 / 99,264) | **0** | 0 | 0 + 0 | 2,941 s (11,397 s) |

**DL_RT4 holds at every f ≥ 1 state of the slice.** No unit has `fail1` > 0, so there is no `n4_3_x3_FAILURES.md`.

By m:

| m | cores | profiles | ω ≥ 1 | f ≥ 1 states | failures | T4-only states | CPU time |
|---|---:|---:|---:|---:|---:|---:|---:|
| 7 (positions 114..136) | 23 | 3,296,526,336 | 7,265,544 | 837,168 | 0 | 0 | 4,258 s |
| 8 (positions 137..170) | 34 | 2,221,572,096 | 298,274,304 | 5,878,874 | 0 | 12,480 | 7,139 s |

dl2.c's counters (the "K" line, shared with dl13.c): k* = 0: 301,435,730, 1: 3,661,968, 2: 441,894, 3: 256,
≥ 4: 0, inf: 0. P with def > 0: 6,716,042, at distance 1: 5,355,106, 2: 1,360,680, 3: 256. Pareto-maximal: 279,720.
Largest least deficit: 0.

## Repair branches (f ≥ 1 states)

States with an improving move of each kind: T1 5,355,106; T2 4,612,774; T3p 6,330,938; T3h 6,182,906; T4 2,542,840.
Only one branch available: only T1 0, only T2 0, only T3 899,696, **only T4 12,480**. R_T = T1 + T2 + T3 fails at
12,480 states, R_13 = T1 + T3 at 12,480, R_13 + T4 at 0. Smallest RT4 move size 1 / 2 / 3 / ≥ 4 / none:
5,355,106 / 1,360,680 / 256 / 0 / 0.

States by the set of branches that hold (table B summed over signatures):

| branches | f = 1 | f = 2 | f = 3 | total |
|---|---:|---:|---:|---:|
| T1+T2+T3p+T3h | 73,720 | 2,678,998 | | 2,752,718 |
| T1+T2+T3p+T3h+T4 | | 1,505,280 | | 1,505,280 |
| T3p+T3h | 18,080 | 558,402 | | 576,482 |
| T1+T3p+T3h | 2,840 | 347,568 | | 350,408 |
| T1+T3p+T3h+T4 | | 346,000 | | 346,000 |
| T3p | | 291,854 | 31,104 | 322,958 |
| T3p+T3h+T4 | | 258,010 | | 258,010 |
| T3p+T4 | | 75,270 | 55,680 | 130,950 |
| T1+T2+T3h+T4 | | 127,000 | | 127,000 |
| T1+T2+T3h | | 118,624 | | 118,624 |
| T1+T3h+T4 | | 86,840 | | 86,840 |
| T2+T3h+T4 | | 30,400 | | 30,400 |
| T1+T2+T3p | | 29,376 | | 29,376 |
| T1+T2+T3p+T4 | | 25,000 | | 25,000 |
| T2+T3p+T3h | 1,640 | 15,040 | | 16,680 |
| **T4** | | | **12,480** | **12,480** |
| T1+T3p+T4 | | 9,360 | | 9,360 |
| T3h+T4 | | 5,920 | | 5,920 |
| T2+T3p+T3h+T4 | | 5,600 | | 5,600 |
| T1+T3h | | 1,888 | | 1,888 |
| T1+T3p | | 1,716 | | 1,716 |
| T1+T2 | | 896 | | 896 |
| T2+T3h | | 800 | | 800 |
| T2+T3p | | 400 | | 400 |
| T3h | | 256 | | 256 |
| **total** | 96,280 | 6,520,498 | 99,264 | 6,716,042 |

Two groups stand out:

- **T4 only (12,480 states, f = 3, signature G):** 9,600 at core 151 (idx 14, m = 8,
  sets [[0,2,5,7],[1,4,6,7],[3,5,6,7],[5,6,7]]) and 2,880 at core 153 (idx 16, m = 8,
  sets [[0,2,5,7],[1,5,6,7],[3,5,6,7],[4,6,7]]). At these states R_T and R_13 have no improving move, so DL_T and DL₁₃
  fail there. Every one has an improving T4 move of size 2 (a transposition of two frozen agents' singleton bases,
  table M `3|T4|2`), and also one with cycle type 3 (table Y `3|T4|T4:2` and `3|T4|T4:3`, 12,480 each). This is the
  same shape as the DL₁₃ failures of `results/k4_dl13/n4_FAILURES.md`: f = 3, nearest better state at distance 2,
  repaired by an exchange between frozen agents.
- **T3h only, smallest move size 3 (256 states, f = 2, signature fO,L, core 139: idx 2, m = 8,
  sets [[0,1,2,7],[2,4,5,6],[3,4,5,7],[3,6,7]]):** the only improving moves are T3 moves with a helper, of size 3, and
  the nearest better state is at distance 3 (table G `2|3|T3h`; the K line has 256 profiles with k* = 3 and 256
  states at distance 3). DL_RT4 holds at them. One is in the dump (the first state of its (signature, branch) cell):
  profile [6, 1, 192, 4], vals [[2,3,4,8],[1,4,8,6],[7,3,5,6],[4,2,3]], B = [[7],[2,5],[3],[6]], def 1, witness
  W = [[2],[5],[3],[7]] (dumped `defW` −1, `wkind` T3h, `wsize` 3).

T4 smallest sizes and cycle types (table C): f = 2: size 2, type "2", 2,474,680 states; f = 3: size 2, type "2",
60,480 states; f = 3: size 3, type "3", 7,680 states.

## Time

Estimate before the run (`n4_3_x3_estimate.txt`): the first four units (cores 114..117, 143,327,232 profiles each)
took about 184 s each, which suggested about 30 min. The run took 2,941 s (49 min). Per profile, the m = 8 cores cost
about 2.5 times as much as the m = 7 cores: a 71,663,616-profile m = 8 unit took 240 to 306 s against about 185 s for
a 143,327,232-profile m = 7 unit, because a far larger share of the m = 8 profiles has ω ≥ 1 (13% against 0.2%).
The whole slice was run; nothing was sampled or cut.

## Files (all under `results/k4_rt4/`)

- `n4_3_x3.log`: the command line, the dlrt4.c SHA-256, the counters and tables B, G, M, Z, C, Y;
- `ckpt_n4_3_x3.jsonl`: one line per core (57 lines, positions 114..170) with its counters, tables and seconds;
- `dump_n4_3_x3.jsonl.gz`: dlrt4.c's "D" records (994; no failing state, so none of the failure kind);
- `tables_n4_3_x3.json`: the merged counters and tables;
- `n4_3_x3_estimate.txt`: the estimate printed before the run finished.

The ledger is not edited and no pull request is opened: the coordinator merges this branch.
