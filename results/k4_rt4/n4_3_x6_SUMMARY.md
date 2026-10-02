# n4_3_x6: DL_RT4 on every profile of n4_3 cores 285..338 (compute/k4-rt4). EVIDENCE only.

**Status: IN PROGRESS (provisional; updated at each push).**

Slice: every strict profile (exhaustive, no sampling) of the n = 4 cores with three 4-good agents at core positions
285..338 (0-based) of `results/k4_certs_4_n4_3.json.gz` (54 cores, 3,816,087,552 profiles). `--cores=A:B` is
`range(A, B)` in `k4/dlrt4_run.py` (B exclusive), so the bounds are `--cores=285:339`.

Tool: `k4/dlrt4.c`, sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae` (checked before the run;
the log prints it again).

Run (one run, tag `n4_3_x6`):

```
python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_3.json.gz --cores=285:339 --jobs=4 \
  --ckpt=results/k4_rt4/ckpt_n4_3_x6.jsonl --dump=results/k4_rt4/dump_n4_3_x6.jsonl.gz \
  --tables=results/k4_rt4/tables_n4_3_x6.json > results/k4_rt4/n4_3_x6.log 2>&1
```

Resumes after a restart re-run the same command and append (`>>`) to the log, so each segment of the log starts with
the command line the driver prints.

## Time estimate (far above the 4 h budget)

Every sampled profile of these cores has omega >= 1 (run (e)'s checkpoints: om1 = 500 of 500 for each of them), so
every profile goes through the full evaluation. Measured on this 4-CPU container:

- One unit, core 318 (17,915,904 profiles), timed alone on one CPU: not finished after 32.8 min (stopped then, so as
  not to slow the real run).
- 3,000 random profiles of each of the 54 cores through the same binary (seed 7), one CPU, scaled by each core's
  profile count: 2,600 to 10,700 profiles/s depending on the core, about **144 CPU-h in total, about 36 h on 4 CPUs**
  (core 318: 7,985 profiles/s, so about 37 CPU-min, which matches the timing above).

| cores | domains | profiles each | est. CPU-h each |
|---|---|---|---|
| 285..307 (23) | 144 x 288 x 288 x 6 | 71,663,616 | 1.9 to 3.0 |
| 308..317 (10) | 288 x 288 x 288 x 6 | 143,327,232 | 4.8 to 6.1 |
| 318..320, 326..328, 338 (7) | 144 x 144 x 144 x 6 | 17,915,904 | 0.5 to 0.7 (338: 1.9) |
| 321..325, 329..334 (11) | 144 x 144 x 288 x 6 | 35,831,808 | 1.7 to 2.3 |
| 335..337 (3) | 144 x 288 x 288 x 6 | 71,663,616 | 4.9 to 5.1 |

The pool takes the cores in order (285, 286, ...), one dlrt4.c process per core, so a core counts only once its whole
process finishes; a kill loses the cores in progress. As the slice text allows for an estimate above 4 h, the run goes
as far as this session lasts, with the checkpoint pushed at least every 30 minutes; the cores covered are the `pos` keys
in `ckpt_n4_3_x6.jsonl`, and anyone can resume the rest with the same command and checkpoint.

**Restart and segment order.** The first segment (the command above, started 21:36 UTC) ran cores 285..288 for about
85 min and was killed by a container restart (before 23:03 UTC) with no core finished, so none of it is in the
checkpoint. With units of 0.5 to 6 CPU-h and a container that may restart, the run then resumed in segments, cheap cores
first: the same command with `--cores=` 318:321, 326:329, 321:335, 285:308, 335:339, 308:318 and finally 285:339. The
driver's checkpoint key (mode, file, P, seed, bt, copts) does not contain the core range, so every segment is the same
run resumed (same options, same checkpoint, dump and tables files; the log is appended, each segment starting with its
command line), and the final 285:339 segment reports the whole slice from the checkpoint. Until that final segment, the
tables file holds only the last segment's cores; the Progress section below is computed from the checkpoint.

## Progress

Last update 2026-10-02 03:43 UTC: 14 of 54 cores finished; 3 dlrt4.c processes running.

| core | profiles | omega >= 1 | f >= 1 states (def > 0) | DL_RT4 fails | T4 | only T3 | only T4 | CPU s |
|---|---|---|---|---|---|---|---|---|
| 318 | 17,915,904 | 17,915,904 | 1,074,688 | 0 | 0 | 1,728 | 0 | 1747 |
| 319 | 17,915,904 | 17,915,904 | 1,864,224 | 0 | 0 | 9,120 | 0 | 1856 |
| 320 | 17,915,904 | 17,915,904 | 1,315,104 | 0 | 0 | 5,760 | 0 | 1796 |
| 321 | 35,831,808 | 35,831,808 | 1,283,776 | 0 | 0 | 32,256 | 0 | 5911 |
| 322 | 35,831,808 | 35,831,808 | 321,312 | 0 | 0 | 15,552 | 0 | 6218 |
| 323 | 35,831,808 | 35,831,808 | 297,024 | 0 | 0 | 5,184 | 0 | 5811 |
| 324 | 35,831,808 | 35,831,808 | 1,129,152 | 0 | 0 | 0 | 0 | 5590 |
| 325 | 35,831,808 | 35,831,808 | 992,256 | 0 | 0 | 0 | 0 | 5903 |
| 326 | 17,915,904 | 17,915,904 | 1,315,408 | 0 | 17,840 | 49,360 | 0 | 1568 |
| 327 | 17,915,904 | 17,915,904 | 2,028,744 | 0 | 8,120 | 46,200 | 0 | 1563 |
| 328 | 17,915,904 | 17,915,904 | 1,414,720 | 0 | 0 | 3,200 | 0 | 1604 |
| 329 | 35,831,808 | 35,831,808 | 1,015,312 | 0 | 0 | 0 | 0 | 5308 |
| 330 | 35,831,808 | 35,831,808 | 492,696 | 0 | 0 | 1,488 | 0 | 5245 |
| 331 | 35,831,808 | 35,831,808 | 1,176,928 | 0 | 0 | 0 | 0 | 4990 |

**Totals over the 14 finished cores** (summed from the checkpoint; the driver's report for the final 285:339 segment gives the same counters):

- profiles 394,149,888 (omega >= 1: 394,149,888); states (def > 0) with f = 0: 118,692,864 (RT4 fails at 0), **with f >= 1: 15,721,344**;
- **DL_RT4 fails at 0 of the f >= 1 states**; anomalies 0 + 0;
- repair branches (f >= 1 states with an improving move of the kind): T1 15,456,960, T2 15,415,824, T3p 13,411,528, T3h 15,488,308, T4 25,960; only T1 0, only T2 0, only T3 169,848, only T4 0; R_T fails at 0, R_13 at 0, R_13 + T4 at 0;
- smallest RT4 move size 1 / 2 / 3 / >= 4 / none: 15,456,960 / 264,384 / 0 / 0 / 0;
- all P with def > 0 (f = 0 and f >= 1: 134,414,208), nearest better min-frozen P at distance 1 / 2 / 3 / >= 4 / inf: 134,149,824 / 264,384 / 0 / 0 / 0; Pareto-maximal 1,246,536;
- CPU time 55,111 s (15.3 CPU-h; 4 workers).

Covered: cores [318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331].

Not yet covered (40): [285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 332, 333, 334, 335, 336, 337, 338].
