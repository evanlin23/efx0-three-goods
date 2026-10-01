# DL_RT4 on every profile of the n4_3 cores at positions 57..113 (compute/k4-rt4, run n4_3_x2)

EVIDENCE only (exhaustive enumeration; no proof). The ledger is not edited here.

**Result: DL_RT4 fails at none of the 4,326,264 f ≥ 1 states with def > 0.** The states come from 7,453,016,064
profiles: every strict profile of the 57 cores at positions 57 to 113 (0-based) of `results/k4_certs_4_n4_3.json.gz`,
the n = 4 cores with three 4-good agents. `n4_3_x2_FAILURES.md` is not written, because there is no failure.

## Run

- Tool: `k4/dlrt4.c`, sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae` (checked before the run;
  the log's second line repeats it). Driver: `k4/dlrt4_run.py`, unchanged. Branch base: `compute/k4-rt4` at 68c0444.
- Command (first line of `n4_3_x2.log`):
  ```
  python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=57:114 --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_3_x2.jsonl --dump=results/k4_rt4/dump_n4_3_x2.jsonl.gz --tables=results/k4_rt4/tables_n4_3_x2.json
  ```
  `--cores=A:B` covers positions `range(A, B)`, so B is exclusive (`dlrt4_run.py`: `for k in range(lo, hi)`).
  `57:114` therefore covers 57..113, and the report line confirms this ("cores 57..113, 57 units").
- One unit per core and no sampling. Cores 57–66 have domain sizes 144·6·288·288 (71,663,616 profiles each). Cores
  67–113 have 288·288·288·6 in some order (143,327,232 profiles each). Every core has m = 7.
- The run had one invocation, with no restart, and every unit finished: 57 of 57 checkpoint lines.
- Time: **51.1 min wall on 4 CPUs** (3,066 s, from the report line) and 12,018 CPU-seconds summed over the units. The
  slowest unit is core 67, at 299 s.
  - Before the run, 200,000 random profiles of each core gave an estimate of about 1.1 h wall.

## Counts

| profiles | ω ≥ 1 | f ≥ 1 states (def > 0) | by f | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails (T4 needed) | R_13 + T4 fails (T2 needed) | anomalies |
|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 7,453,016,064 | 117,615,768 | 4,326,264 | f = 1: 0, f = 2: 3,600,696, f = 3: 725,568 | **0** | 0 (0) | 42,240 | 42,240 | 0 | 0 + 0 |

dl2.c's counters, from the `K` line, which dlrt4.c shares with dl13.c:
- k\* = 0: 115,282,430; 1: 1,852,250; 2: 481,088; none larger.
- P with def > 0: 4,326,264, at distance 1: 2,845,594, at distance 2: 1,480,670.
- Pareto-maximal: 191,408. Largest least deficit: 0.

## Repair branches (f ≥ 1 states)

A branch is "with" a state when some improving move of that branch exists there. "Only" means it is the only such
branch (T3 = T3p or T3h). The smallest size is the least number of agents an improving RT4 move changes.

| T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / ≥ 4 / none |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 2,845,594 | 1,963,210 | 3,921,016 | 3,268,024 | 1,921,980 | 0 | 0 | 818,510 | 42,240 | 2,845,594 / 1,480,670 / 0 / 0 / 0 |

### T4 cycle types

1,921,980 states have an improving T4 move.
- Least T4 size 2 (cycle type "2"): 1,889,340 states. Least size 3 (cycle type "3"): 32,640.
- "2" is available at 1,889,340 states and "3" at 401,280.

### Where T4 is needed (R_T fails)

There are **42,240 states**, all at f = 3, where T4 is the only repairing branch.
- At each of them the least improving T4 move has size 2 (a 2-cycle: two frozen agents swap their goods), and an
  improving 3-cycle also exists (`n4_3_x2_tables.md` §3).
- They lie on 7 cores: 58 (11,520), 61 (9,600), 63 (2,880), 64 (2,880), 68 (9,600), 71 (2,880) and 72 (2,880).
- R_13 fails exactly at these states, so they are DL₁₃ failures. dl13 only sampled n4_3 (`results/k4_dl13/n4_SUMMARY.md`
  rows (c), (e)). It found one failing profile there, with 2 states, on core 64 (`n4_FAILURES.md`), and this
  exhaustive run covers every profile of core 64. The other 6 cores are new places where DL₁₃ fails and T4 repairs.

The dump holds 848 of these states. They all have the shape of `n4_FAILURES.md`:
- f = 3, def 1, nearest distance k = 2;
- signature G (644) or O (204); both occur among n4_2's failures;
- the witness is a 2-cycle to a P′ with def 0, and both "2" and "3" improving cycles are available.

### Where T2 is needed

Nowhere: R_13 + T4 fails at no state. This slice has no f = 1 state with def > 0.

### Branch combinations

The full list by f, branch combination and smallest size is in `n4_3_x2_tables.md` §4, made by `k4/dlrt4_summary.py`;
its command is in the reproduction section below. The largest combinations are:
- f = 2, T1+T2+T3p+T3h: 998,878;
- f = 2, T1+T2+T3p+T3h+T4: 575,020;
- f = 3, T3p+T4: 456,960;
- f = 2, T1+T3p+T3h+T4: 436,170.

## Cross-check of the dumped states (after the run)

I ran `python3 k4/dlrt4_ref.py records results/k4_rt4/dump_n4_3_x2.jsonl.gz --jobs=4 --x`, logged in
`ref_n4_3_x2_dumps.log`. It takes the 848 distinct dumped profiles that have a state with no T1 or T3 move and
recomputes all 5,858 states of those profiles, all with f ≥ 1. It checks them against three things:
- the reference (`model.py` + `dl2_relations.py` + its own T4 test);
- dl13.c (the `K` line and the per-state T1/T3 results);
- the `-DBIGPP=0` build and `k4/dl134_xcheck.py` (`--x`).

**0 mismatches** in every comparison. DL_RT4 fails at none of these states. 2,466 of them are T4-only.

## Files (all under `results/k4_rt4/`)

| file | content |
|---|---|
| `n4_3_x2.log` | the run's log: command, sha256, report line, tables B G M Z C Y |
| `ckpt_n4_3_x2.jsonl` | one line per finished core (57 lines), with its counters and time |
| `dump_n4_3_x2.jsonl.gz` | dlrt4.c's `D` records with the core and values (1,641 records) |
| `tables_n4_3_x2.json` | the merged counters and tables |
| `n4_3_x2_tables.md` | the tables in Markdown (`k4/dlrt4_summary.py`) |
| `ref_n4_3_x2_dumps.log` | the reference cross-check of the dumped T4-needed states |

The dump holds the default selection (`--rt=50`, `--ro=0`). That is every f ≥ 1 failure (none here), the 1st, 51st, …
state per unit that has no T1 or T3 move, and the first f ≥ 1 state of each (signature, branch) cell per unit.

## Reproduction

```
python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=57:114 --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_3_x2.jsonl --dump=results/k4_rt4/dump_n4_3_x2.jsonl.gz --tables=results/k4_rt4/tables_n4_3_x2.json
python3 k4/dlrt4_summary.py "n4_3 cores 57..113, every profile=results/k4_rt4/tables_n4_3_x2.json=results/k4_rt4/n4_3_x2.log"
python3 k4/dlrt4_ref.py records results/k4_rt4/dump_n4_3_x2.jsonl.gz --jobs=4 --x
```

A rerun with the same checkpoint skips the finished cores. Delete or rename the checkpoint to recompute.
