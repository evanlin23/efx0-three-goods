# n4_3_x5: DL_RT4 on every profile of the n = 4 cores with three 4-good agents, positions 228..284

EVIDENCE only (exhaustive enumeration by `k4/dlrt4.c`; no proof). The ledger is not edited here.

**Slice.** Every strict profile (`check4.core_domains`, as `k4/dlrt4_run.py` certs mode) of the cores at positions
228..284 (0-based, 57 cores) of `results/k4_certs_4_n4_3.json.gz`. `dlrt4_run.py`'s `--cores=A:B` is `range(A, B)`,
exclusive of B, so the slice is `--cores=228:285`. Tool: `k4/dlrt4.c`, sha256
`fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae` (checked before the runs and printed on the second
line of every log), unchanged.

## Result

**DL_RT4 fails at no state of the slice.** The slice has 4,425,228,288 profiles, and 28,153,056 f ≥ 1 states with
def > 0. All 57 cores are complete; no core was sampled. `n4_3_x5_FAILURES.md` is not written, because there is no
failure.

- **Only f = 1 and f = 2 occur:** 21,747,832 states have f = 1, and 6,405,224 have f = 2. No f = 0 state with
  def > 0 occurs (`st0` = 0), and no f = 3 state occurs.
- **R_13 never fails.** Every state already has an improving T1 or T3 move. So R_T and R_13 + T4 never fail either:
  no state needs T2 or T4.
- **T3 is the only repair branch at 766,156 states.** T1, T2 and T4 are never the only branch.
- **T4 moves are always 2-cycles.** 2,090,640 states (all f = 2) have an improving T4 move. Each of them has one
  of least size 2, and no other cycle type is improving. Every such state also has another branch.
- **Move sizes.** The smallest improving RT4 move changes 1 agent at 26,703,476 states and 2 agents at 1,449,580.
  It never changes 3 or more.
- **No anomalies:** the `anom` and `anom4` counters are 0.

## Runs

The slice ran as two runs with their own tags and files. The main command (`dlrt4_run.py`, tag `n4_3_x5`) covered
cores 228..259. The split driver (`k4/dlrt4_split.py`, tag `n4_3_x5_split`) covered 260..284; see "Why two runs".
The cores do not overlap. "Process time" sums the per-unit times in the checkpoints. Each unit was one single-threaded
dlrt4.c process, four at a time on 4 CPUs.

| run | cores | profiles | f ≥ 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 / R_T / R_13 + T4 fail | wall time | process time | log |
|---|---|---:|---:|---:|---:|---|---|---:|---|
| `n4_3_x5` | 228..259 (32 units) | 3,045,703,680 | 11,589,592 | **0** | 0 (0) | 0 / 0 / 0 | 2 h 15 min (21:19–23:34 UTC; includes the work lost to two container restarts) | 7.2 h | `n4_3_x5.log` (+ `_run1`, `_run2`, `_run3`) |
| `n4_3_x5_split` | 260..284 (200 sub-units: 8 per core) | 1,379,524,608 | 16,563,464 | **0** | 0 (0) | 0 / 0 / 0 | 5 h 48 min (20,874 s; 23:35–05:23 UTC) | 22.7 h | `n4_3_x5_split.log` |
| **slice** | 228..284 | **4,425,228,288** | **28,153,056** | **0** | 0 (0) | 0 / 0 / 0 | 8 h 04 min elapsed | 29.8 h | `tables_n4_3_x5_all.json` |

### Repair branches (f ≥ 1 states)

A branch is "with" a state when some improving move of that branch exists there. "Only" means it is the only such
branch (T3 = T3p or T3h).

| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / ≥ 4 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `n4_3_x5` (228..259) | 11,090,112 | 10,953,480 | 8,275,064 | 11,115,836 | 763,840 | 0 | 0 | 330,840 | 0 | 11,090,112 / 499,480 / 0 / 0 |
| `n4_3_x5_split` (260..284) | 15,613,364 | 15,219,472 | 15,422,184 | 16,169,916 | 1,326,800 | 0 | 0 | 435,316 | 0 | 15,613,364 / 950,100 / 0 / 0 |
| slice | 26,703,476 | 26,172,952 | 23,697,248 | 27,285,752 | 2,090,640 | 0 | 0 | 766,156 | 0 | 26,703,476 / 1,449,580 / 0 / 0 |

T4 cycle types: every state with an improving T4 move has one of least size 2, of cycle type "2". The "available"
column lists "2" only, and T4 is needed nowhere. `n4_3_x5_summary_tables.md` has the full tables, made by
`k4/dlrt4_summary.py`; its command is in its first line. They include the branch combinations by f and the smallest
move size.

Other counters of the slice, from `tables_n4_3_x5_all.json`:
- ω ≥ 1 profiles: 1,904,519,424;
- k* = 1 / 2: 18,001,584 / 382,316;
- Pareto-maximal P with def > 0: 792,576;
- largest least deficit: 0.

## Why two runs (deviations from the slice's single command)

1. **Timing first.** Scratch runs, written to no results file, timed 1,000,000 random profiles of each of cores 228,
   246, 252 and 271, and then 100,000 of every core in the slice; see `n4_3_x5_estimate.txt`.
   - Cost per profile: m = 8 cores about 2.5 µs; m = 9 cores 36 to 74 µs.
   - Estimate: about 36 CPU-hours, or 9 h wall on 4 CPUs. One unit of cores 271..284 takes 75 to 100 min in one
     process.
   - The estimate exceeded 4 hours, so, as the slice text allows, the run went as far as it could, pushing at least
     every 30 minutes. In the end it covered the whole slice.
2. **Detached driver.** It ran under `setsid nohup`, so the ~30-minute background-job kill could not cut units.
3. **Two container restarts killed the run.** The first came at about 22:42 UTC, with cores 228..255 in the
   checkpoint. The second came at about 23:03. Both times units 256..259 were lost while running. The same command
   resumed from the checkpoint, intact both times.
   - Each re-run's redirect overwrote `n4_3_x5.log`, so the earlier attempts' logs are kept as `n4_3_x5_run1.log`,
     `_run2.log` and `_run3.log`. Their report lines are absent: each attempt was killed or stopped.
4. **The split driver.** A unit of 75–100 min could not finish between restarts 20–80 min apart, and `dlrt4_run.py`
   checkpoints whole cores only. So I added `k4/dlrt4_split.py`, a new file; no existing file was changed.
   - It runs the same certs mode, with dlrt4_run.py's functions imported. The largest agent domain of each core is
     cut into S contiguous chunks, and each (core, chunk) is one dlrt4.c process.
   - The chunks partition that agent's domain, and dlrt4.c evaluates every profile on its own. So each core's K and L
     counters and B/G/M/Z/C/Y tables are the sums over its chunks.
   - **Validation** (`n4_3_x5_split_validation.log`): with `--split=4` on cores 244 (m = 8) and 252 (m = 9; 1,701,912
     states, 177 table keys), every counter and table entry equals the main checkpoint's unit for that core.
     Every dumped profile's `vals` equal the core's full-domain values at `prof`.
5. **The handover.** Once 256..259 had finished in the main run, I stopped it at 23:34. It had just started
   260..263, about 2 minutes in, and that partial work was discarded.
   - The main tag's final report and tables (`n4_3_x5.log`, `tables_n4_3_x5.json`) come from the same command with
     `--cores=228:260`. All 32 units were read from the checkpoint; nothing was recomputed.
   - Cores 260..284 then ran with `--split=8`: sub-units of 1 to 16 min.
6. **The two dumps differ in sampling, not in content.** dlrt4.c dumps the first state per (signature, branch)
   cell, and every 50th state outside R_13, per process. A split core has 8 processes, so the split run's dump holds
   more such records: 2,209, against 501 in the main dump. Both dumps hold every failing state, and there are none.

`tables_n4_3_x5_all.json` is the merge of the two runs' tables, made with `dlrt4_run.merge_tot`. It is the slice's
total.

## Files (all in `results/k4_rt4/`)

| file | content |
|---|---|
| `n4_3_x5.log`, `tables_n4_3_x5.json`, `ckpt_n4_3_x5.jsonl`, `dump_n4_3_x5.jsonl.gz` | run `n4_3_x5`: cores 228..259 (32 whole-core units) |
| `n4_3_x5_run1.log`, `n4_3_x5_run2.log`, `n4_3_x5_run3.log` | the logs of that run's killed/stopped attempts (each began with the full `--cores=228:285` command) |
| `n4_3_x5_split.log`, `tables_n4_3_x5_split.json`, `ckpt_n4_3_x5_split.jsonl`, `dump_n4_3_x5_split.jsonl.gz` | run `n4_3_x5_split`: cores 260..284 (200 sub-units) |
| `tables_n4_3_x5_all.json` | merged counters and tables of the slice |
| `n4_3_x5_summary_tables.md` | `k4/dlrt4_summary.py` tables for the two runs and the slice |
| `n4_3_x5_estimate.txt` | the timing and estimate made before the run |
| `n4_3_x5_split_validation.log` | `k4/dlrt4_split.py` against `dlrt4_run.py` on cores 244 and 252 |

## Reproduction

```
python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=228:260 --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_3_x5.jsonl \
    --dump=results/k4_rt4/dump_n4_3_x5.jsonl.gz --tables=results/k4_rt4/tables_n4_3_x5.json > results/k4_rt4/n4_3_x5.log 2>&1
python3 k4/dlrt4_split.py results/k4_certs_4_n4_3.json.gz --cores=260:285 --split=8 --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_3_x5_split.jsonl \
    --dump=results/k4_rt4/dump_n4_3_x5_split.jsonl.gz --tables=results/k4_rt4/tables_n4_3_x5_split.json > results/k4_rt4/n4_3_x5_split.log 2>&1
```

Both commands resume from their checkpoints, so with the committed checkpoints they only re-print the reports. To
recompute, use fresh checkpoint paths. `python3 k4/dlrt4_run.py certs ... --cores=228:285` (the slice's command, one
process per core) gives the same counters and tables, given enough time without a restart.

## Per core

"T4": states with an improving T4 move. "Process time": the unit's time, or the sum of its 8 sub-units' times.

| core | m | domains | profiles | f >= 1 states (def > 0) | DL_RT4 fails | T4 | only T3 | only T4 | R_T fails | R_13 + T4 fails | run | process time |
|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|
| 228 | 8 | 288x288x288x6 | 143,327,232 | 69,816 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.7 min |
| 229 | 8 | 288x288x288x6 | 143,327,232 | 60,400 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.3 min |
| 230 | 8 | 288x6x288x288 | 143,327,232 | 6,272 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.2 min |
| 231 | 8 | 288x288x288x6 | 143,327,232 | 232,448 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.9 min |
| 232 | 8 | 288x288x288x6 | 143,327,232 | 57,216 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.4 min |
| 233 | 8 | 288x6x288x288 | 143,327,232 | 25,264 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.9 min |
| 234 | 8 | 288x288x288x6 | 143,327,232 | 84,192 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.3 min |
| 235 | 8 | 288x6x288x288 | 143,327,232 | 11,328 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.2 min |
| 236 | 8 | 288x6x288x288 | 143,327,232 | 109,824 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.1 min |
| 237 | 8 | 288x288x288x6 | 143,327,232 | 228,096 | **0** | 0 | 17,280 | 0 | 0 | 0 | main | 3.8 min |
| 238 | 8 | 288x6x288x288 | 143,327,232 | 20,160 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.1 min |
| 239 | 8 | 288x288x288x6 | 143,327,232 | 186,624 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.5 min |
| 240 | 8 | 288x288x288x6 | 143,327,232 | 116,352 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.9 min |
| 241 | 8 | 288x288x288x6 | 143,327,232 | 107,264 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.8 min |
| 242 | 8 | 288x288x288x6 | 143,327,232 | 56,448 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.9 min |
| 243 | 8 | 288x288x288x6 | 143,327,232 | 333,888 | **0** | 0 | 0 | 0 | 0 | 0 | main | 4.0 min |
| 244 | 8 | 6x288x288x288 | 143,327,232 | 3,456 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.7 min |
| 245 | 8 | 6x288x288x288 | 143,327,232 | 46,848 | **0** | 0 | 0 | 0 | 0 | 0 | main | 3.7 min |
| 246 | 9 | 144x144x288x6 | 35,831,808 | 428,768 | **0** | 0 | 0 | 0 | 0 | 0 | main | 30.0 min |
| 247 | 9 | 144x144x288x6 | 35,831,808 | 303,072 | **0** | 0 | 0 | 0 | 0 | 0 | main | 29.2 min |
| 248 | 9 | 144x144x288x6 | 35,831,808 | 74,400 | **0** | 0 | 0 | 0 | 0 | 0 | main | 27.2 min |
| 249 | 9 | 144x144x288x6 | 35,831,808 | 572,640 | **0** | 0 | 3,200 | 0 | 0 | 0 | main | 28.4 min |
| 250 | 9 | 144x144x288x6 | 35,831,808 | 373,200 | **0** | 0 | 3,200 | 0 | 0 | 0 | main | 28.5 min |
| 251 | 9 | 144x144x288x6 | 35,831,808 | 232,800 | **0** | 0 | 86,400 | 0 | 0 | 0 | main | 26.2 min |
| 252 | 9 | 144x144x144x6 | 17,915,904 | 1,701,912 | **0** | 264,280 | 90,800 | 0 | 0 | 0 | main | 8.5 min |
| 253 | 9 | 144x144x144x6 | 17,915,904 | 1,268,496 | **0** | 53,520 | 37,200 | 0 | 0 | 0 | main | 8.4 min |
| 254 | 9 | 144x144x288x6 | 35,831,808 | 733,936 | **0** | 164,880 | 0 | 0 | 0 | 0 | main | 25.4 min |
| 255 | 9 | 144x144x288x6 | 35,831,808 | 945,972 | **0** | 7,200 | 16,120 | 0 | 0 | 0 | main | 25.6 min |
| 256 | 9 | 144x144x288x6 | 35,831,808 | 934,396 | **0** | 17,480 | 34,240 | 0 | 0 | 0 | main | 28.9 min |
| 257 | 9 | 144x144x288x6 | 35,831,808 | 899,664 | **0** | 17,840 | 21,760 | 0 | 0 | 0 | main | 29.4 min |
| 258 | 9 | 144x144x6x288 | 35,831,808 | 1,051,616 | **0** | 236,640 | 0 | 0 | 0 | 0 | main | 30.6 min |
| 259 | 9 | 144x144x6x288 | 35,831,808 | 312,824 | **0** | 2,000 | 20,640 | 0 | 0 | 0 | main | 30.2 min |
| 260 | 9 | 144x144x288x6 | 35,831,808 | 161,984 | **0** | 17,840 | 22,720 | 0 | 0 | 0 | split (8 chunks) | 25.4 min |
| 261 | 9 | 144x144x6x288 | 35,831,808 | 624,440 | **0** | 4,200 | 12,000 | 0 | 0 | 0 | split (8 chunks) | 25.5 min |
| 262 | 9 | 144x144x288x6 | 35,831,808 | 457,512 | **0** | 0 | 0 | 0 | 0 | 0 | split (8 chunks) | 26.1 min |
| 263 | 9 | 144x144x6x288 | 35,831,808 | 466,240 | **0** | 4,480 | 1,920 | 0 | 0 | 0 | split (8 chunks) | 26.6 min |
| 264 | 9 | 144x144x288x6 | 35,831,808 | 311,520 | **0** | 16,240 | 46,800 | 0 | 0 | 0 | split (8 chunks) | 23.9 min |
| 265 | 9 | 144x144x288x6 | 35,831,808 | 1,126,592 | **0** | 0 | 17,600 | 0 | 0 | 0 | split (8 chunks) | 25.3 min |
| 266 | 9 | 144x144x6x288 | 35,831,808 | 1,040,256 | **0** | 283,200 | 0 | 0 | 0 | 0 | split (8 chunks) | 26.5 min |
| 267 | 9 | 144x144x144x6 | 17,915,904 | 2,267,792 | **0** | 628,080 | 52,800 | 0 | 0 | 0 | split (8 chunks) | 7.7 min |
| 268 | 9 | 144x144x288x6 | 35,831,808 | 1,156,708 | **0** | 130,400 | 119,140 | 0 | 0 | 0 | split (8 chunks) | 22.8 min |
| 269 | 9 | 144x144x288x6 | 35,831,808 | 1,090,008 | **0** | 70,760 | 28,600 | 0 | 0 | 0 | split (8 chunks) | 21.3 min |
| 270 | 9 | 144x144x288x6 | 35,831,808 | 459,648 | **0** | 2,800 | 18,840 | 0 | 0 | 0 | split (8 chunks) | 23.6 min |
| 271 | 9 | 144x288x288x6 | 71,663,616 | 323,808 | **0** | 81,440 | 0 | 0 | 0 | 0 | split (8 chunks) | 71.8 min |
| 272 | 9 | 144x288x288x6 | 71,663,616 | 585,720 | **0** | 3,640 | 16,140 | 0 | 0 | 0 | split (8 chunks) | 67.5 min |
| 273 | 9 | 144x6x288x288 | 71,663,616 | 1,375,704 | **0** | 4,280 | 17,320 | 0 | 0 | 0 | split (8 chunks) | 67.0 min |
| 274 | 9 | 144x288x288x6 | 71,663,616 | 405,876 | **0** | 0 | 17,120 | 0 | 0 | 0 | split (8 chunks) | 77.2 min |
| 275 | 9 | 144x6x288x288 | 71,663,616 | 362,608 | **0** | 0 | 1,920 | 0 | 0 | 0 | split (8 chunks) | 75.8 min |
| 276 | 9 | 144x288x288x6 | 71,663,616 | 270,848 | **0** | 3,200 | 27,228 | 0 | 0 | 0 | split (8 chunks) | 78.3 min |
| 277 | 9 | 144x288x288x6 | 71,663,616 | 844,912 | **0** | 12,240 | 33,440 | 0 | 0 | 0 | split (8 chunks) | 77.8 min |
| 278 | 9 | 144x288x288x6 | 71,663,616 | 491,840 | **0** | 0 | 0 | 0 | 0 | 0 | split (8 chunks) | 79.2 min |
| 279 | 9 | 144x6x288x288 | 71,663,616 | 682,784 | **0** | 64,000 | 0 | 0 | 0 | 0 | split (8 chunks) | 78.4 min |
| 280 | 9 | 144x288x288x6 | 71,663,616 | 288,864 | **0** | 0 | 0 | 0 | 0 | 0 | split (8 chunks) | 87.4 min |
| 281 | 9 | 144x288x288x6 | 71,663,616 | 470,864 | **0** | 0 | 0 | 0 | 0 | 0 | split (8 chunks) | 87.8 min |
| 282 | 9 | 144x288x288x6 | 71,663,616 | 197,664 | **0** | 0 | 0 | 0 | 0 | 0 | split (8 chunks) | 83.3 min |
| 283 | 9 | 144x288x288x6 | 71,663,616 | 275,272 | **0** | 0 | 1,728 | 0 | 0 | 0 | split (8 chunks) | 88.0 min |
| 284 | 9 | 144x288x288x6 | 71,663,616 | 824,000 | **0** | 0 | 0 | 0 | 0 | 0 | split (8 chunks) | 86.9 min |
