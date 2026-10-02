# n5a: DL_RT4 on random profiles of the n = 5 cores with one or two 4-good agents (EVIDENCE only)

Branch `compute/k4-rt4-n5a` (from `compute/k4-rt4` at 2e9adeb). Tool: `k4/dlrt4.c`, sha256
`fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae` (checked before the runs; every log prints it),
driven by `k4/dlrt4_run.py`, both unchanged. Machine: 4 CPUs, `--jobs=4`.

Question: does Conjecture DL_RT4 hold here? At f >= 1, does every min-frozen P with def(P) > 0 have a min-frozen P' with
def(P') < def(P) and RT4(P, P'), where RT4 = T1 + T2 + T3 + T4 (k4/dlrt4.c's header)?

**Result: DL_RT4 holds at every one of the 782,086 f >= 1 states with def > 0 met in the four runs. No failures, so
there is no `n5a_FAILURES.md`. No f = 0 state with def > 0 occurred.** This is random sampling, so EVIDENCE, not a
certificate.

## Choice of P1 and P2 (timing first)

Before the runs, a stratified sample (8 cores per m) at P = 20,000 per core gave these estimates at 4 jobs: n5a_1
about 0.5 min, n5a_1bt about 0.5 min, n5a_2 about 4.9 min, n5a_2bt about 5 to 6 min. Cost is linear in P and comes
almost entirely from the cores with m >= 10: most profiles at smaller m have omega = 0 and are discarded in about
10 µs. P1 was fixed at 300,000. Runs 1 and 2 then took 7.5 and 7.9 min, against the estimate of about 7.5 min each.
Next, a precise timing of the n4_2 file timed all 665 cores with m >= 10 and 10 cores per smaller m, at P = 1 and
P = 8,000. It gave cpu-s = 29 + 0.0498 P without the restriction and 27 + 0.0658 P with --bt=all. P2 = 350,000 was
then predicted to take 73 + 96 min. Actual: 72 min, and about 93 min of running time. Both exceed the aims (P1 >= 20,
P2 >= 5) by far. The whole slice took about 3 h 05 min of wall time for the runs (21:19 to 00:24 UTC), plus about
10 min of timing.

Profiles are drawn independently and uniformly, with replacement, from each core's strict profiles. Expected number of
distinct profiles (from the per-core profile-space sizes after the big-top filter):

| run | per-core profile space | draws per core | expected distinct, share of draws | share of the profile space covered |
|---|---|---|---|---|
| n5a_1   | 186,624 .. 373,248       | 300,000 | 0.644 | 0.584 |
| n5a_1bt | 31,104 .. 62,208         | 300,000 | 0.183 | 0.993 |
| n5a_2   | 4,478,976 .. 17,915,904  | 350,000 | 0.986 | 0.024 |
| n5a_2bt | 124,416 .. 497,664       | 350,000 | 0.646 | 0.556 |

Repeated draws are counted again in every counter below (each draw is one "profile"). n5a_1bt draws so many profiles
per core that it almost exhausts the big-top profile space of the n4_1 cores (99.3% expected).

## Runs

| | n5a_1 | n5a_1bt | n5a_2 | n5a_2bt |
|---|---|---|---|---|
| certificate file | `k4_certs_5_n4_1` (1,735 cores) | same | `k4_certs_5_n4_2` (5,468 cores) | same |
| options | `--sample=300000 --seed=1` | `--sample=300000 --seed=2 --bt=all` | `--sample=350000 --seed=1` | `--sample=350000 --seed=2 --bt=all` |
| profiles | 520,500,000 | 520,500,000 | 1,913,800,000 | 1,913,800,000 |
| profiles with omega >= 1 | 2,707,180 | 6,026,025 | 66,368,016 | 163,267,440 |
| f >= 1 states with def > 0 | **881** | **0** | **153,029** | **628,176** |
| by f (1 / 2 / 3 / 4) | 0 / 148 / 733 / 0 | - | 82,218 / 53,032 / 17,591 / 188 | 521,585 / 85,812 / 20,591 / 188 |
| f = 0 states with def > 0 | 0 | 0 | 0 | 0 |
| **DL_RT4 failures (fail1)** | **0** | **0** | **0** | **0** |
| RT4 failures at f = 0 (fail0) | 0 | 0 | 0 | 0 |
| anomalies (anom + anom4) | 0 + 0 | 0 + 0 | 0 + 0 | 0 + 0 |
| wall time | 7.5 min (driver 446 s) | 7.9 min (driver 471 s) | 72.0 min (driver 4,317 s) | 93.8 min, in 3 invocations (see below) |
| sum of unit times (cpu-s) | 1,499 | 1,695 | 16,814 | 21,772 |
| dump records | 22 | 0 (no file written) | 1,286 | 403 |

### Repair branches (f >= 1 states)

Counts of states with an improving move of each kind, of states where that kind is the only branch, and of states
where a smaller relation fails (the L counters):

| | n5a_1 | n5a_1bt | n5a_2 | n5a_2bt |
|---|---|---|---|---|
| T1 | 148 | 0 | 142,633 | 624,262 |
| T2 | 0 | 0 | 135,717 | 618,544 |
| T3p | 881 | 0 | 130,376 | 628,100 |
| T3h | 148 | 0 | 143,847 | 621,103 |
| T4 | 0 | 0 | 9,628 | 14,109 |
| only T1 / only T2 / only T3 / only T4 | 0 / 0 / 733 / 0 | 0 / 0 / 0 / 0 | 0 / 0 / 8,861 / **44** | 0 / 0 / 1,766 / **36** |
| R_T = T1 + T2 + T3 fails | 0 | 0 | 44 | 36 |
| R_13 = T1 + T3 fails | 0 | 0 | 44 | 36 |
| R_13 + T4 fails | 0 | 0 | 0 | 0 |
| smallest RT4 move size 1 / 2 / >= 3 / none | 148 / 733 / 0 / 0 | - | 142,633 / 10,396 / 0 / 0 | 624,262 / 3,914 / 0 / 0 |

Branch sets (table B summed over f and signature):
- n5a_1: T3p 733, T1+T3p+T3h 148.
- n5a_2: T1+T2+T3p+T3h 105,550; T1+T2+T3h 22,580; T3p 6,287; T1+T2+T3p+T3h+T4 6,117; T1+T3p+T3h 5,438;
  T3p+T3h 2,574; T1+T3p+T3h+T4 1,501; T3p+T4 1,433; T1+T2+T3p 908; T1+T2+T3p+T4 504; T2+T3p+T3h 58; **T4 44**;
  T1+T3h+T4 29; T1+T3p 6.
- n5a_2bt: T1+T2+T3p+T3h 606,707; T1+T2+T3p+T3h+T4 8,688; T1+T3p+T3h 3,169; T1+T3p+T3h+T4 2,499; T1+T2+T3p 2,415;
  T3p+T4 2,112; T3p 1,766; T1+T2+T3p+T4 734; T1+T3h+T4 40; **T4 36**; T1+T3p 10.

T4 moves by f | smallest T4 size | cycle type at that size (table C): n5a_2: 2|2|2 6,206; 3|2|2 2,943; 3|3|3 291;
4|2|2 144; 4|3|3 44. n5a_2bt: 2|2|2 8,942; 3|2|2 4,637; 3|3|3 342; 4|2|2 152; 4|3|3 36.

Nearest distance k (to a min-frozen P' with smaller deficit, any move; table G): 1 or 2 at every state (n5a_1: 148 /
733; n5a_2: 142,633 / 10,396; n5a_2bt: 624,262 / 3,914). The largest least deficit (over the profiles with omega >= 1)
is 0 in every run.

### Where the states are (by m; cores are sorted by m)

- n5a_1: states only at m = 8 (18 cores, 593 states, all T3-only) and m = 9 (4 cores, 288 states). No core with
  m = 10 or 11 has a state, although at m = 11 every profile has omega >= 1.
- n5a_1bt: no state at any m.
- n5a_2: m = 7: 3 cores, 188 states (all f = 4, all with T4); m = 8: 223 cores, 7,234; m = 9: 246, 13,752; m = 10: 169,
  44,515; m = 11: 35, 83,333; m = 12: 1, 4,007.
- n5a_2bt: m = 7: 3 cores, 188 states (all f = 4, all with T4); m = 8: 44, 2,413; m = 9: 126, 15,241; m = 10: 91, 74,235;
  m = 11: 20, 389,898; m = 12: 1, 146,201.

### The states that need T4 (R_13 and R_T fail, DL_RT4 holds only through T4)

80 states: 44 in n5a_2 and 36 in n5a_2bt. All come from two m = 7 cores of `k4_certs_5_n4_2`:
- pos 491 (idx 82), sets [[0,2,4,6],[1,3,5,6],[3,5,6],[4,5,6],[4,5,6]]: 16 (n5a_2) + 24 (n5a_2bt);
- pos 498 (idx 89), sets [[0,2,4,6],[1,4,5,6],[3,5,6],[3,5,6],[4,5,6]]: 28 (n5a_2) + 12 (n5a_2bt).

All have f = 4, omega = 1, def = 1, signature G, and nearest distance 2. The smallest improving RT4 move is a T4
transposition (|ch| = 2), with a 3-cycle also available, and the witness P' has def 0. For example (n5a_2bt dump, core
pos 491, vals [[2,3,4,8],[2,10,6,3],[4,3,2],[4,3,2],[4,3,2]]): bases B = [{4},{1},{3},{5},{6}] with agents 0, 2, 3, 4
frozen, NA = {3,4,5,6}. The witness swaps the singleton goods 4 and 6 of the frozen agents 0 and 4, giving
[{6},{1},{3},{5},{4}] with def 0. In all four dumped T4-only profiles the three 3-good agents have the same strict
type (4, 3, 2). The same two cores give the T4-only states in both runs (seeds 1 and 2, with and without the big-top
restriction). The third m = 7 core with states (pos 490: 56 states in n5a_2, 80 in n5a_2bt) has only f = 4 states
with T3p + T4. On pos 491 and 498 the other states also have T3p + T4.

The dumps hold 2 T4-only states per run (the first per (signature, branch) cell). `k4/dlrt4_ref.py inst` agrees exactly
with dlrt4.c on all four of their profiles (24 states each run, 8 T4-only), with 0 mismatches against the reference
(model.py + dl2_relations.py + its own T4), 0 against dl13.c, and 0 against the -DBIGPP=0 build:
`ref_n5a_t4only.log` (from `n5a_t4only_inst.json`, n5a_2) and `ref_n5a_2bt_t4only.log` (from
`n5a_2bt_t4only_inst.json`).

### Reference check at n = 5

The earlier validation logs of dlrt4.c (`ref_random_n3.log`, `ref_random_n4.log`, `ref_suite.log`, ...) use random
profiles of n <= 4 cores, so I added one at n = 5 on this slice's two files: `python3 k4/dlrt4_ref.py random
results/k4_certs_5_n4_2.json.gz results/k4_certs_5_n4_1.json.gz --states=300 --neg=100 --seed=1 --jobs=4`, log
`ref_random_n5a.log`, 8 min. It screened 7,162,000 random (core, profile) draws (the two files in turn). It kept 205
profiles with an f >= 1 state (300 states) and 100 without one. With an improving move: T1 276, T2 259, T3p 257,
T3h 273, T4 23; none T4-only. It found 0 mismatches against the reference (model.py + dl2_relations.py + its own T4),
0 reference assertion failures, 0 against dl13.c (the K line, and T1/T3 per state) and 0 against the -DBIGPP=0
build. dl134_xcheck.py (`--x`) is for n <= 4 only and was not run. The reference supports DL_RT4 at all 300 states.

## Interruptions

Run n5a_2bt was stopped twice by container restarts: after 3,402 units, and after 4,907 units. Each time the same
command was re-run and resumed from `ckpt_n5a_2bt.jsonl` (the log holds three command headers: 5,468, then 2,066, then
561 units to run). Before each resume I checked that every checkpoint line parses, that the dump reads to the end, and
that every unit with dump records has a checkpoint line, so that no unit is counted twice. No dump has an exact
duplicate record. The totals and tables printed at the end of the log, and `tables_n5a_2bt.json`, cover all 5,468
units (profiles = 5,468 x 350,000). Its "[3293 s]" is the last invocation only. The three invocations ran 22:50:39 to
about 23:04:50, 23:05:23 to about 23:28:46, and 23:29:25 to 00:24:24 UTC.

## Files (all under `results/k4_rt4/`)

- `n5a_1.log`, `ckpt_n5a_1.jsonl`, `dump_n5a_1.jsonl.gz`, `tables_n5a_1.json`
- `n5a_1bt.log`, `ckpt_n5a_1bt.jsonl`, `tables_n5a_1bt.json` (no dump: the run produced no dump record)
- `n5a_2.log`, `ckpt_n5a_2.jsonl`, `dump_n5a_2.jsonl.gz`, `tables_n5a_2.json`
- `n5a_2bt.log`, `ckpt_n5a_2bt.jsonl`, `dump_n5a_2bt.jsonl.gz`, `tables_n5a_2bt.json`
- `n5a_t4only_inst.json`, `ref_n5a_t4only.log`, `n5a_2bt_t4only_inst.json`, `ref_n5a_2bt_t4only.log`
- `ref_random_n5a.log`
- this file

To reproduce a run, use the command on the first line of its log (re-running it resumes from the checkpoint; delete
the checkpoint, dump and tables first to start over).

## What this does and does not show

- EVIDENCE only: random profiles, 3.6 billion draws over 7,203 cores. No DL_RT4 failure was found. The n4_2 profile
  space is sampled thinly (2.4% of it without the restriction), and the n4_1 space at about 58% (99% under --bt=all).
- T4 is needed: R_13 (and R_T) fails at 80 states, all on two m = 7 cores with f = 4. R_13 + T4 never fails, and T2 is
  never the only branch.
- With every 4-good agent big-top, no def > 0 state appears among the n4_1 cores at all (n5a_1bt). Among the n4_2 cores
  they do appear (628,176 states), and DL_RT4 holds at all of them.
- Not done here: n = 5 cores with three or more 4-good agents, the pure n = 5 cores, exhaustive enumeration.
