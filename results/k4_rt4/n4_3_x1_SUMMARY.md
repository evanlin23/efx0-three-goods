# n4_3_x1: DL_RT4 on every profile of the n = 4 cores with three 4-good agents, positions 0..56

EVIDENCE only (exhaustive over the slice's strict profiles; not a proof). Branch `compute/k4-rt4-n4-3-x1`, from
`compute/k4-rt4` at 2e9adeb.

## Slice and command

- Cores: positions 0..56 (0-based) of `results/k4_certs_4_n4_3.json.gz` (339 cores in all). `k4/dlrt4_run.py` reads
  `--cores=A:B` as `range(A, B)`, so B is exclusive and the slice is `--cores=0:57`.
- Tool: `k4/dlrt4.c`, sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae` (checked before the
  run, and printed by the driver on line 2 of the log). No file of the repository was modified.
- One run, tag `n4_3_x1`:
  ```
  python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=0:57 --jobs=4 \
    --ckpt=results/k4_rt4/ckpt_n4_3_x1.jsonl --dump=results/k4_rt4/dump_n4_3_x1.jsonl.gz \
    --tables=results/k4_rt4/tables_n4_3_x1.json > results/k4_rt4/n4_3_x1.log 2>&1
  ```
  Every profile (no `--sample`). The default copts are `-r50 -o0`.
- Files: `n4_3_x1.log` (command, sha, report, tables), `ckpt_n4_3_x1.jsonl` (57 units),
  `dump_n4_3_x1.jsonl.gz` (1,746 "D" records), `tables_n4_3_x1.json` (merged counters and tables).
- Coverage, checked from the checkpoint:
  - It holds exactly one unit for each position 0..56, all under one ckey (`certs`, P = 0, bt = None,
    copts `-r50 -o0`).
  - Each unit's `prof` equals the product of the `check4.core_domains` sizes: 143,327,232 for the 47 cores with domains
    288·288·288·6, and 71,663,616 for the 10 cores with domains 144·288·288·6 (positions 9, 10, 47..56).
  - The run went straight through: no kill, no resume, and the log has a single segment.

## Results

| quantity | value |
|---|---|
| profiles | 7,309,688,832 |
| profiles with ω ≥ 1 | 21,765,488 |
| k* = 0 / 1 / 2 / ≥ 3 / ∞ | 21,427,384 / 89,090 / 249,014 / 0 / 0 |
| min-frozen P with def > 0 | 1,238,086 |
| ... at nearest distance 1 / 2 / ≥ 3 / ∞ | 104,570 / 1,133,516 / 0 / 0 |
| Pareto-maximal; largest least deficit | 26,496; 0 |
| **f ≥ 1 states with def > 0** | **1,238,086** (f = 2: 264,070; f = 3: 974,016) |
| f = 0 states with def > 0 | 0 (RT4 fails at 0) |
| **DL_RT4 failures (fail1)** | **0** |
| anomalies | 0 + 0 |

DL_RT4 therefore holds at every f ≥ 1 state of the slice, and no `n4_3_x1_FAILURES.md` was written.

f ≥ 1 states lie on 24 of the 57 cores: positions 9, 10, 12..16, 18..21, 26..29, 31, 48, 49, 51..56. The other
33 cores have no min-frozen P with def > 0:
- 10 of them have ω ≥ 1 profiles: positions 11, 17, 22, 30, 35, 38, 41, 44, 47, 50.
- 23 have none: positions 0..8, 23..25, 32..34, 36, 37, 39, 40, 42, 43, 45, 46.

## Repair branches (f ≥ 1 states)

Each count below is the number of states with at least one improving move of that kind:

| T1 | T2 | T3p | T3h | T4 |
|---|---|---|---|---|
| 104,570 | 43,530 | 1,157,446 | 213,920 | 1,054,560 |

- Only one kind: T1 0, T2 0, T3 121,956, T4 **80,640**.
- R_T = T1 + T2 + T3 fails at 80,640, R_13 at 80,640, and R_13 + T4 at 0.
- Smallest RT4 move size 1 / 2 / 3 / ≥ 4 / none: 104,570 / 1,133,516 / 0 / 0 / 0.

**States by f and branch set** (table B summed over the 14 signatures):

| f | branch set | states |
|---|---|---|
| 3 | T3p+T4 | 864,000 |
| 3 | T4 | 80,640 |
| 3 | T3p | 29,376 |
| 2 | T3p+T3h+T4 | 66,420 |
| 2 | T3p+T3h | 47,230 |
| 2 | T3p | 45,350 |
| 2 | T1+T3p+T3h | 30,920 |
| 2 | T1+T2+T3p+T3h | 26,650 |
| 2 | T1+T3p+T3h+T4 | 26,620 |
| 2 | T1+T2+T3p+T3h+T4 | 16,080 |
| 2 | T1+T3p | 3,200 |
| 2 | T1+T2+T3p | 800 |
| 2 | T3p+T4 | 500 |
| 2 | T1+T3p+T4 | 300 |

**T4-only states** (R_T fails and T4 repairs):
- There are 80,640 of them, all with f = 3, nearest distance 2 and smallest RT4 move size 2.
- Per table Y, each of them has both an improving 2-cycle T4 move and an improving 3-cycle T4 move.
- They fall on 11 cores (positions: states): 9: 11,520; 10: 5,760; 12: 11,520; 15: 15,360; 16: 5,760; 20: 2,880;
  21: 2,880; 26: 9,600; 27: 9,600; 29: 2,880; 31: 2,880.

**Smallest T4 move** (table C), among the states with a T4 move:
- f = 3: size 2 with cycle type "2" at 878,400 states; size 3 with cycle type "3" at 66,240 states.
- f = 2: size 2 with cycle type "2" at 109,920 states.

The full tables B, G, M, Z, C and Y are in `n4_3_x1.log` and `tables_n4_3_x1.json`.

**Dump.** 1,746 records, none with branch "none" (no failing state).
- 1,620 records are T4-only f = 3 states. They come from the `-r50` sampling (every 50th state that needs a branch
  outside R_13), plus the first such state of each cell.
- The other 126 are first-of-cell records: the first f ≥ 1 state of each (signature, branch) cell per process.
- By core, the T4-only records fall on 15: 308, 12: 232, 9: 231, 26: 193, 27: 192, 10: 116, 16: 116, and 58 each on
  20, 21, 29 and 31.

## Time

- Wall time 2,698 s (45 min) on 4 jobs (`nproc` = 4), 21:19:57 to 22:04 UTC on 2026-10-01.
- The units' recorded times sum to 10,603 s, from 102.5 s per unit (core 9) to 320.6 s (core 0).
- Before the run, two scratch timing runs, not committed, took 319 s (core 0) and 133 s (core 53) with two processes
  running side by side. They gave a 70–90 min estimate.

## Remaining

Nothing is left in this slice: all 57 units ran over every profile. The other positions of `k4_certs_4_n4_3.json.gz`
(57..338) are not covered here.
