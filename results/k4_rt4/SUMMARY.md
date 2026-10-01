# DL_RT4 on the n = 4 cores (compute/k4-rt4)

EVIDENCE only (random and exhaustive enumeration; no proof). The ledger is not edited here.

**Conjecture DL_RT4.** For every strict profile of every connected k = 4 core whose fewest frozen agents is f ≥ 1, with
ω ≥ 1, every min-frozen P with def(P) > 0 has an RT4-neighbour P′ that is min-frozen with def(P′) < def(P). Here
RT4 = T1 ∪ T2 ∪ T3 ∪ T4 = R_T (`k4/dl2.md` §3) plus

- **(T4)** a permutation of the frozen agents' singleton bases among those agents, each staying frozen, with NA
  unchanged and every other base unchanged. Any cycle structure is allowed.

The tool is `k4/dlrt4.c` (sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`; its header
defines every counter), run by `k4/dlrt4_run.py` and `k4/dlrt4_nbhd.py`. These are copies of `k4/dl13.c`,
`k4/dl13_run.py` and `k4/dl13_nbhd.py` with the R_13 test replaced by the RT4 test. Each log below has its command on
the first line.

## Result

**DL_RT4 fails at no state of any run.** The runs cover 733,349,317 profiles and 429,969 f ≥ 1 states with def > 0,
summed over the runs; the runs overlap, see below. `FAILURES.md` is not written, because there is no failure.

- **T4 is needed only at f = 3.** R_T fails at exactly these states. That is 3,062 states in the exhaustive runs
  ((b), (c)) and in the failure list, plus 6 sampled states.
  - At every such state an improving **2-cycle** exists: two frozen agents swap their goods.
  - Each of these states also has an improving 3-cycle.
  - No T4 move with a cycle type other than "2" or "3" lowers a deficit anywhere in these runs.
- **T2 is needed only at f = 1.** R_13 + T4 fails at exactly these states: the 3,971 states near `dl13-n4m9-rot`
  and that profile's own state in #53's catalogue.
  - The least improving rotation involves 3 free agents at 2,991 + 1 of them and 2 free agents (a trade) at 980.
- **No state needs both T2 and T4.** No state needs more than three agents to change. The smallest improving RT4
  move changes 1, 2 or 3 agents; 3 occurs only at T2-needed states.
- **f = 0 states:** RT4 fails at none of them (expected: at f = 0 every min-frozen P′ is a T1/T2 neighbour, and
  Theorem Z applies).
- **New DL₁₃ failures.** The sampled runs found two DL₁₃ (and DL_T) failures that are not in
  `results/k4_dl13/n4_FAILURES.md`. Both have the known shape: f = 3, def 1, repaired only by a T4 2-cycle.
  - pure core 26 (m = 7), profile 6,183,103,3: run (d), seed 2, draws 201–500;
  - n4_3 core 153 (m = 8), profile 65,35,40,1: run (e), seed 3.

  Their dump records are in `dump_d_pure_s500_2.jsonl.gz` and `dump_e_n4_3_s500_3.jsonl.gz`. All three
  implementations re-derived them (`ref_run_dumps.log`, below).

## Validation of the tool (before the runs)

`k4/dlrt4_ref.py` is the reference. It runs on `k4/suite/model.py` and `k4/dl2_relations.py`; R_T is that file's
`RTr`, and T1, T2 and T3 are its predicates. Its T4 test is written separately from the C code.

For every state it compares the following with dlrt4.c's `-s` line, and requires exact agreement:
- def, the nearest distance, the branch flags, the least size per branch, the smallest RT4 move size;
- the T1, T2 and T3 type masks;
- the T4 cycle types (all of them, and those at the least T4 size);
- the witness deficit and the Pareto flag.

It also checks four more things:
- **dl13.c:** dlrt4.c's `K` line equals dl13.c's, and so do the per-state T1/T3 flags and type masks.
- **The hashed build:** dlrt4.c built with `-DBIGPP=0` (every class hashed, candidates generated) prints exactly the
  default build's output.
- **Internal consistency of the reference:** RTr ⇔ T1 ∨ T2 ∨ T3, R13 ⇔ T1 ∨ T3, and the four kinds are disjoint, at
  every improving move.
- **A third implementation (`--x`, n ≤ 4):** the flags and the least T4 size against `k4/dl134_xcheck.py`, which is
  main's `c4x_check.py` plus that file's own move kinds.

| input | profiles | states (f ≥ 1) | mismatches (reference / dl13.c / hash build / xcheck) | log |
|---|---:|---:|---|---|
| suite (cores, n ≤ 6) | 150 | 367 (169) | 0 / 0 / 0 / 0 | `ref_suite.log` |
| `dl13-n4m9-rot`, `dl13-n4m6-fswap` | 2 | 7 (7) | 0 / 0 / 0 / 0 | `ref_n4m9rot.log` |
| the 3,062 DL₁₃ failures (all states of their 1,131 profiles; each listed failing state found) | 1,131 | 7,586 (7,586) | 0 / 0 / 0 / 0 | `ref_dl13_failures.log` |
| random n = 3 (`k4_certs_3`), screened for f ≥ 1, plus 300 profiles without such a state | 1,090 | 2,034 (2,001) | 0 / 0 / 0 / 0 | `ref_random_n3.log` |
| random n = 4 (n4_1, n4_2, n4_3, pure in turn), screened, plus 300 without | 920 | 2,057 (2,011) | 0 / 0 / 0 / 0 | `ref_random_n4.log` (`_nox`: the same without xcheck) |
| after the runs: every dumped profile with a state that needs T2 or T4 (runs (a) neighbourhood to (e)) | 277 | 724 (724) | 0 / 0 / 0 / 0 | `ref_run_dumps.log` |

## Per run

Full tables, including the branch combinations by f and the smallest move size: `summary_tables.md`, made by
`k4/dlrt4_summary.py` from the `tables_*.json` files and logs; its command is on its first line. Times are wall
times on 4 CPUs, from the report line of each log.

| run | profiles | f ≥ 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails (T4 needed) | R_13 + T4 fails (T2 needed) | time | log |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| (a) the 1,131 profiles of the 3,062 DL₁₃ failures | 1,131 | 7,586 | **0** | 0 (0) | 3,062 | 3,062 | 0 | 1 s | `a_dl13_failures.log` |
| (a) `dl13-n4m9-rot`, `dl13-n4m6-fswap` | 2 | 7 | **0** | 0 (0) | 3 | 2 | 1 | 0 s | `a_suite2.log` |
| (a) every profile within two type changes of `dl13-n4m9-rot` | 371,235 | 59,439 | **0** | 0 (0) | 3,971 | 0 | 3,971 | 15 s | `a_nbhd123.log` |
| (b) `k4_certs_4_n4_1`, every profile | 7,247,232 | 286 | **0** | 0 (0) | 20 | 20 | 0 | 4 s | `b_n4_1.log` |
| (c) `k4_certs_4_n4_2`, every profile | 724,847,616 | 324,658 | **0** | 0 (0) | 3,040 | 3,040 | 0 | 15.5 min | `c_n4_2.log` |
| (d) `k4_certs_4_pure`, 500 per core, seed 1 | 109,500 | 3,141 | **0** | 42,953 (0) | 0 | 0 | 0 | 3 s | `d_pure_s500_1.log` |
| (d) `k4_certs_4_pure`, 500 per core, seed 2 | 109,500 | 3,111 | **0** | 44,058 (0) | 2 | 2 | 0 | 3 s | `d_pure_s500_2.log` |
| (d) `k4_certs_4_pure`, 500 per core, seed 3 | 109,500 | 3,529 | **0** | 42,384 (0) | 0 | 0 | 0 | 3 s | `d_pure_s500_3.log` |
| (d) #53's `gap_n4_pure_s4000`, every record | 45,101 | 25,018 | **0** | 0 (0) | 1 | 0 | 1 | 4 s | `d_cat_gap_n4_pure_s4000.log` |
| (e) `k4_certs_4_n4_3`, 500 per core, seed 1 | 169,500 | 1,110 | **0** | 5,694 (0) | 0 | 0 | 0 | 2 s | `e_n4_3_s500_1.log` |
| (e) `k4_certs_4_n4_3`, 500 per core, seed 2 | 169,500 | 1,047 | **0** | 5,494 (0) | 2 | 2 | 0 | 2 s | `e_n4_3_s500_2.log` |
| (e) `k4_certs_4_n4_3`, 500 per core, seed 3 | 169,500 | 1,037 | **0** | 5,824 (0) | 2 | 2 | 0 | 2 s | `e_n4_3_s500_3.log` |

**Overlaps between the runs:**
- The profiles of (a)'s first row lie in (b), (c) and dl13's n4_3 seed-2 sample.
- dl13.c's generator is the same as dlrt4.c's, so the first 200 draws per core of seeds 1 and 2 in (d) and (e) are
  the profiles of the dl13 runs `n4_*_s200` / `s200b`. That is where (e) seed 2's two T4-only states come from (core
  64, as in `n4_FAILURES.md`).
- The catalogue in (d) contains `dl13-n4m9-rot`.
- The (a) neighbourhood is the same set of profiles as dl13's `nbhd123.log`.

dlrt4.c's `K` counters on each input equal dl13.c's logs: for example 324,658 states with def > 0 in (c), and 59,439
in the neighbourhood.

### Repair branches (f ≥ 1 states)

A branch is "with" a state when some improving move of that branch exists there; "only" means it is the only such
branch (T3 = T3p or T3h). The smallest size is the least number of agents changed by an improving RT4 move.

| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / ≥ 4 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| (a) DL₁₃ failures' profiles | 0 | 0 | 4,524 | 0 | 7,586 | 0 | 0 | 0 | 3,062 | 0 / 7,586 / 0 / 0 |
| (a) the two suite instances | 0 | 1 | 4 | 0 | 6 | 0 | 1 | 0 | 2 | 0 / 6 / 1 / 0 |
| (a) neighbourhood of `dl13-n4m9-rot` | 48,928 | 58,207 | 28,144 | 47,692 | 0 | 32 | 3,971 | 1,104 | 0 | 48,928 / 6,160 / 4,351 / 0 |
| (b) n4_1 | 0 | 0 | 266 | 0 | 140 | 0 | 0 | 146 | 20 | 0 / 286 / 0 / 0 |
| (c) n4_2 | 229,032 | 187,344 | 282,138 | 256,772 | 63,560 | 0 | 0 | 45,906 | 3,040 | 229,032 / 95,626 / 0 / 0 |
| (d) pure s1 | 2,976 | 3,017 | 2,890 | 3,095 | 97 | 0 | 0 | 70 | 0 | 2,976 / 165 / 0 / 0 |
| (d) pure s2 | 2,965 | 2,992 | 2,818 | 3,054 | 95 | 0 | 0 | 69 | 2 | 2,965 / 146 / 0 / 0 |
| (d) pure s3 | 3,310 | 3,309 | 3,249 | 3,468 | 129 | 0 | 0 | 133 | 0 | 3,310 / 219 / 0 / 0 |
| (d) `gap_n4_pure_s4000` | 23,876 | 24,163 | 22,720 | 24,835 | 22 | 0 | 1 | 611 | 0 | 23,876 / 1,140 / 2 / 0 |
| (e) n4_3 s1 | 1,055 | 1,033 | 926 | 1,079 | 57 | 0 | 0 | 41 | 0 | 1,055 / 55 / 0 / 0 |
| (e) n4_3 s2 | 983 | 959 | 916 | 1,011 | 108 | 0 | 0 | 22 | 2 | 983 / 64 / 0 / 0 |
| (e) n4_3 s3 | 987 | 974 | 860 | 1,006 | 72 | 0 | 0 | 27 | 2 | 987 / 50 / 0 / 0 |

No T1 or T4 anomaly occurs in any run: no one-agent move by a frozen agent, and no T4 candidate that fails to be a
permutation (the `anom` and `anom4` counters are 0).

### T4 cycle lengths

The table covers the f ≥ 1 states with an improving T4 move. "Least size: cycle type" counts states by the least number
of agents in an improving T4 move, and the cycle types at that size. "Available" counts the states that have an
improving T4 move of each cycle type.

| run | states with T4 | least size: cycle type (states) | available | T4 needed (only branch) |
|---|---:|---|---|---|
| (a) DL₁₃ failures' profiles | 7,586 | 2: "2" (5,324); 3: "3" (2,262) | "2": 5,324, "3": 5,324 | 3,062, all of least size 2 ("2"), each also with a "3" |
| (a) the two suite instances | 6 | 2: "2" (4); 3: "3" (2) | "2": 4, "3": 4 | 2, least size 2 |
| (b) n4_1 | 140 | 2: "2" (120); 3: "3" (20) | "2": 120, "3": 80 | 20, least size 2, each also with a "3" |
| (c) n4_2 | 63,560 | 2: "2" (61,320); 3: "3" (2,240) | "2": 61,320, "3": 32,000 | 3,040, least size 2, each also with a "3" |
| (d) pure s1 / s2 / s3 | 97 / 95 / 129 | 2: "2" (97 / 93 / 129); 3: "3" (0 / 2 / 0) | "3": 0 / 14 / 20 | 0 / 2 / 0, least size 2 |
| (d) `gap_n4_pure_s4000` | 22 | 2: "2" (22) | "2": 22 | 0 |
| (e) n4_3 s1 / s2 / s3 | 57 / 108 / 72 | 2: "2" (57 / 106 / 70); 3: "3" (0 / 2 / 2) | "3": 0 / 12 / 4 | 0 / 2 / 2, least size 2 |

At n = 4 a T4 move involves at most three frozen agents (f ≤ 3), so the only possible cycle types are "2" and "3".
Both occur. T4 moves appear at f = 2 states too (in (c): 24,360 states with least size 2), but there another branch
always repairs as well. Every state that needs T4 has f = 3 (`summary_tables.md` §4).

### Where T2 is needed

All states that need T2 have f = 1:

| run | states | least T2 size 2 (a trade) / 3 (a 3-rotation) |
|---|---:|---|
| (a) neighbourhood of `dl13-n4m9-rot` | 3,971 | 980 / 2,991 |
| (a) `dl13-n4m9-rot` (suite); (d) the same profile in `gap_n4_pure_s4000` | 1; 1 | 0 / 1; 0 / 1 |

These are the states where R_13 fails. dl13.c's `results/k4_dl13/nbhd123.log` counts the same number of DL₁₃
failures on the same profiles (3,971), and dlrt4.c's R_13 test is dl13.c's code (validated above).

## Reproduction

```
python3 k4/dlrt4_ref.py suite --jobs=4 --x                              # validation (see the logs ref_*.log for each command)
python3 k4/dlrt4_ref.py write-tsv-inst results/k4_rt4/dl13_failure_profiles.json results/k4_dl13/n4_failures_*.tsv
python3 k4/dlrt4_run.py inst results/k4_rt4/dl13_failure_profiles.json --chunk=100 --jobs=3 --rt=1 --ro=1 ...   # (a)
python3 k4/dlrt4_nbhd.py results/k4_certs_4_pure.json.gz 123 7,196,164,44 --radius=2 --jobs=3 ...               # (a)
python3 k4/dlrt4_run.py certs results/k4_certs_4_n4_2.json.gz --jobs=4 --ckpt=results/k4_rt4/ckpt_n4_2.jsonl ... # (c), resumable
python3 k4/dlrt4_run.py certs results/k4_certs_4_pure.json.gz --sample=500 --seed=S --jobs=4 ...                 # (d), (e)
python3 k4/dlrt4_ref.py records results/k4_rt4/dump_*.jsonl.gz --x                                             # the dumped T2/T4 states
```

Each log's first line has the exact command. Dumps (`dump_*.jsonl.gz`) hold dlrt4.c's `D` records with the core
and the values:
- (a) failure profiles and suite instances: every state (`--rt=1 --ro=1`);
- (a) neighbourhood: every 20th state that needs T2 or T4 (`--rt=20`);
- other runs: the 1st, 51st, … such state per unit (`--rt=50`, the default);
- every run: the first state of each (signature, branch) cell per process.

Checkpoints (`ckpt_*.jsonl`) let each run resume.
