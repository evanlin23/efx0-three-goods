# compute/k4-dl13, n = 4 slice: summary

Conjecture DL₁₃ (K4.DL2.T13, `k4/dl2.md` §3) on the n = 4 cores, with `k4/dl13_run.py` (dl13.c sha256
`f891de3a228a63fcd05008c0e4d9202068fc0d2b41be5876775affd4b2131d65`) on 4 CPUs, branch `compute/k4-dl13-n4` from 893c778. EVIDENCE only.

Validation first: `python3 k4/dl13_check.py suite` on this machine gave 360 states and 0 mismatches in every comparison (model, xcheck,
K line, hash build). See `n4_check_suite.log`.

| run | certificate file | profiles | def > 0 states with f ≥ 1 | DL₁₃ failures (f ≥ 1) | f = 0 states (R₁₃ fails) | wall time (CPU time of the units) |
|---|---|---:|---:|---:|---:|---|
| (a) exhaustive | `k4_certs_4_n4_1` | 7,247,232 | 286 | **20** | 0 (0) | 5 s (16 s) |
| (b) exhaustive | `k4_certs_4_n4_2` | 724,847,616 | 324,658 | **3,040** | 0 (0) | 972 s (3,817 s) |
| (c) 200 per core, seed 1 | `k4_certs_4_n4_3` | 67,800 | 462 | 0 | 2,114 (0) | 2 s (3 s) |
| (d) 200 per core, seed 1 | `k4_certs_4_pure` | 43,800 | 1,303 | 0 | 16,144 (0) | 2 s (5 s) |
| (e) 200 per core, seed 2 | `k4_certs_4_n4_3` | 67,800 | 437 | **2** | 2,205 (0) | 2 s (3 s) |
| (e) 200 per core, seed 2 | `k4_certs_4_pure` | 43,800 | 1,324 | 0 | 17,431 (2) | 2 s (5 s) |

dl13.c reports anomalies 0 in every run. The 2 f = 0 states of the last run where R₁₃ fails are outside DL₁₃, which is stated for f ≥ 1;
at f = 0 DL_T holds by Theorem Z. The estimate printed before (b), about 9 min (`n4_2_estimate.txt`), assumed (a)'s cost per profile. (b)
cost about 1.8 times more per profile.

**DL₁₃ fails at 3,062 states (1,131 profiles, 9 cores)**, at m = 6 and m = 7, with one, two and three 4-good agents. See `n4_FAILURES.md`
for the list and its TSVs.

- All failing states have f = 3, def = 1 and a nearest better state at distance 2.
- Every nearest repair is an exchange of goods between two frozen agents that both stay frozen, with the needed set unchanged. That move is
  outside R₁₃ and R_T.
- dl13.c, the model (`k4/dl2_relations.py`) and `k4/c4x_check.py` + `rel_B` agree at every failing state. R_T (DL_T) fails there too.

Files (all under `results/k4_dl13/`):

- per run: `n4_*.log` (it starts with its command line), `tables_n4_*.json`, `dump_n4_*.jsonl.gz`, `ckpt_n4_*.jsonl`;
- the failures: `n4_FAILURES.md`, `n4_failures_*.tsv`, `n4_failures_list.{py,log}`, `n4_failures_xcheck.py` and `n4_*_failures_xcheck.log`.

The ledger is not edited and no pull request is opened: the coordinator merges this branch.
