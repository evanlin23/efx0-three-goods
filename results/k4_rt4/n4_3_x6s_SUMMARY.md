# DL_RT4 on n4_3 cores 289–338, random sample (compute/k4-rt4-n4-3-x6s)

EVIDENCE only: random sampling, no proof. The ledger is not edited here.

**Conjecture DL_RT4** (`results/k4_rt4/SUMMARY.md`). At f ≥ 1, every min-frozen P with def(P) > 0 has an
RT4-neighbour P′ that is min-frozen with def(P′) < def(P), where RT4 = T1 ∪ T2 ∪ T3 ∪ T4.

## Result

**DL_RT4 fails at none of the 2,175,707 f ≥ 1 states with def > 0 in 100,000,000 sampled profiles.** Every unit has
`fail1` = 0, so `n4_3_x6s_FAILURES.md` is not written.

- R_13 (T1 ∪ T3) fails at no state, so no state in this sample needs T2 or T4.
- RT4 fails at none of the 23,476,749 f = 0 states with def > 0.
- The tool reports no anomalies (0 + 0).

## What was run

- **Input:** cores 289 to 338 (0-based; `--cores=289:339`) of `results/k4_certs_4_n4_3.json.gz`. That is 50 cores:
  29 with m = 9, 20 with m = 10, 1 with m = 11.
- **Sample:** 2,000,000 random strict profiles per core, seed 11. These come from dlrt4.c's generator, which is
  seeded by the seed and the core's position. This is the full 2,000,000 the task asked for; it was not lowered.
- **Tool:** `k4/dlrt4.c` (sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`, checked before the
  run), driven by `k4/dlrt4_run.py`. No existing file was modified.
- **Command** (the first line of the log):
  ```
  python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=289:339 --sample=2000000 --seed=11 --jobs=4 \
    --ckpt=results/k4_rt4/ckpt_n4_3_x6s.jsonl --dump=results/k4_rt4/dump_n4_3_x6s.jsonl.gz \
    --tables=results/k4_rt4/tables_n4_3_x6s.json > results/k4_rt4/n4_3_x6s.log 2>&1
  ```
- **Files:**

  | file | contents |
  |---|---|
  | `n4_3_x6s.log` | both invocations (the run was resumed once); the final report and tables are at the end |
  | `ckpt_n4_3_x6s.jsonl` | one line per core: counters, tables and time |
  | `dump_n4_3_x6s.jsonl.gz` | dlrt4.c's "D" records, 850 records from 49 cores (core 307 has no f ≥ 1 state) |
  | `tables_n4_3_x6s.json` | the merged counters and tables, all 50 cores |
  | `ref_n4_3_x6s.log` | the reference cross-check of the dumped profiles (below) |

## Counts (all 50 cores)

| quantity | count |
|---|---:|
| profiles | 100,000,000 |
| with ω ≥ 1 | 100,000,000 |
| k* = 0 / 1 / 2 / ≥ 3 | 91,670,699 / 8,320,734 / 8,567 / 0 |
| P with def > 0 | 25,652,456 |
| … at distance 1 / 2 / ≥ 3 | 25,606,678 / 45,778 / 0 |
| largest least deficit | 0 |
| states with def > 0 and f = 0 (RT4 fails) | 23,476,749 (0) |
| states with def > 0 and f ≥ 1 | **2,175,707** (f = 1: 2,078,333; f = 2: 97,374; f ≥ 3: 0) |
| **DL_RT4 failures (f ≥ 1)** | **0** |
| R_13 fails / R_T fails / R_13 + T4 fails | 0 / 0 / 0 |
| anomalies | 0 + 0 |

## Repair branches (f ≥ 1 states)

"With": some improving move of that branch exists at the state. "Only": it is the only such branch (T3 = T3p or
T3h). "Smallest move size": the least number of agents an improving RT4 move changes.

| T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / ≥ 4 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 2,129,929 | 2,123,830 | 1,855,889 | 2,147,299 | 2,828 | 3 | 0 | 30,294 | 0 | 2,129,929 / 45,778 / 0 / 0 |

- **T4 occurs only at f = 2, on cores 326 (1,885 states) and 327 (943 states).** Every such state has an improving T4
  move that is a 2-cycle, and none has a larger least T4 move. T3 is also available at each of them, so T4 is never
  the only branch.
- **Only T1:** 3 states, all on core 306, at f = 1.
- **Only T3:** 30,294 states, all with smallest move size 2.
- **No improving move larger than 2 agents is ever the smallest.** Every f ≥ 1 state is at nearest distance 1 or 2.

Branch combinations by f, with the smallest RT4 move size (table M; `k4/dlrt4_summary.py`):

| f | branches with an improving move | smallest size | states |
|---|---|---:|---:|
| 1 | T1+T2+T3p+T3h | 1 | 1,712,033 |
| 1 | T1+T2+T3h | 1 | 304,133 |
| 2 | T1+T2+T3p+T3h | 1 | 66,527 |
| 1 | T3p+T3h | 2 | 15,631 |
| 1 | T1+T2 | 1 | 15,366 |
| 1 | T2+T3p+T3h | 2 | 13,228 |
| 2 | T3p+T3h | 2 | 11,949 |
| 2 | T1+T3p+T3h | 1 | 11,465 |
| 1 | T1+T2+T3p | 1 | 8,858 |
| 1 | T1+T3p+T3h | 1 | 8,534 |
| 2 | T3p | 2 | 2,714 |
| 2 | T1+T2+T3p+T3h+T4 | 1 | 1,450 |
| 2 | T3p+T3h+T4 | 2 | 1,246 |
| 2 | T1+T2+T3p | 1 | 1,118 |
| 2 | T2+T3p+T3h | 2 | 655 |
| 1 | T2+T3p | 2 | 349 |
| 1 | T1+T3h | 1 | 192 |
| 2 | T1+T3p+T3h+T4 | 1 | 132 |
| 2 | T1+T2+T3h | 1 | 107 |
| 2 | T1+T3h | 1 | 11 |
| 1 | T2+T3h | 2 | 6 |
| 1 | T1 | 1 | 3 |

The per-signature table (B), the nearest-distance table (G) and the move-type table (Y) are in the log and in
`tables_n4_3_x6s.json`.

## Cross-check with the reference

No dump record is a failure or a state without a T1 or T3 move, so `dlrt4_ref.py records` without `--allrec` would
compare nothing. Every dumped profile was re-derived instead:

```
python3 k4/dlrt4_ref.py records results/k4_rt4/dump_n4_3_x6s.jsonl.gz --allrec --jobs=4 --x
```

The check took 55 s. Its log is `ref_n4_3_x6s.log`.

- **Coverage:** 653 profiles and every one of their states: 2,203 states, all at f ≥ 1. This includes 34 states with
  an improving T4 move.
- **Agreement:** the reference (`model.py`, `dl2_relations.py` and its own T4 test) agrees exactly with dlrt4.c at
  every state. So do dl13.c's K line and per-state T1/T3 flags, the `-DBIGPP=0` build, and `dl134_xcheck.py` (`--x`,
  2,203 states). There are 0 mismatches in each comparison and 0 failed reference assertions.
- **Failures:** the reference also finds 0 DL_RT4 failures (f ≥ 1) and 0 RT4 failures (f = 0).

## Time

- **Timing run (scratch, outside the checkpoint):** 20,000 profiles on each of the 50 cores took 134.7 unit-seconds.
  That scales to about 3.7 CPU-hours for 2,000,000 per core, about 1 hour on 4 CPUs, so the full sample size was kept.
- **Main run:** 13,136 unit-seconds summed over the 50 cores (3.65 CPU-hours). The slowest core was 338 (m = 11), at
  742 s.
- **Wall time:** about 64 minutes on 4 CPUs, in two invocations.
  - The first ran from 21:57 to about 22:43 UTC and finished 44 cores. The container then restarted and killed it,
    losing the cores that were in progress.
  - The second resumed from the checkpoint and ran the last 6 cores (333–338) in 1,063 s.
  - The time `k4/dlrt4_summary.py` prints (17.7 min) covers only that second invocation, because the first was killed
    before its report line.
- **The restart lost no data:** after it, the checkpoint had 44 complete lines and the dump decoded cleanly. Every dump
  record belongs to a core in the checkpoint, so no records are duplicated.

## Scope

This is a sample: 2,000,000 of each core's strict profiles. It is not exhaustive. Another worker is checking cores
285–338 of the same file exhaustively.
