# DL₁₃ failures on the n = 4 cores (compute/k4-dl13, n = 4 slice)

EVIDENCE: the output of `k4/dl13_run.py` (dl13.c sha256 `f891de3a228a63fcd05008c0e4d9202068fc0d2b41be5876775affd4b2131d65`), every failure
re-checked with the two other implementations of `k4/dl13_check.py`. Conjecture DL₁₃ is K4.DL2.T13 (`k4/dl2.md` §3). The ledger is not edited
here; what follows is for the coordinator of compute/k4-dl13 and the proof workstream to weigh.

## Counts

| run | profiles | def > 0 states with f ≥ 1 | DL₁₃ fails at | failing profiles | failing cores (pos) |
|---|---:|---:|---:|---:|---|
| (a) `k4_certs_4_n4_1`, exhaustive | 7,247,232 | 286 | **20** | 10 | 25 |
| (b) `k4_certs_4_n4_2`, exhaustive | 724,847,616 | 324,658 | **3,040** | 1,120 | 20, 22, 24, 27, 28, 92, 94 |
| (c) `k4_certs_4_n4_3`, 200 per core, seed 1 | 67,800 | 462 | 0 | 0 | |
| (d) `k4_certs_4_pure`, 200 per core, seed 1 | 43,800 | 1,303 | 0 | 0 | |
| (e) `k4_certs_4_n4_3`, 200 per core, seed 2 | 67,800 | 437 | **2** | 1 | 64 |
| (e) `k4_certs_4_pure`, 200 per core, seed 2 | 43,800 | 1,324 | 0 | 0 | |

Each run's DL13 counters are in its log (`n4_*.log`, the line starting `DL13:`) and its tables JSON (`tables_n4_*.json`, `counters.fail1`). The
dumps (`dump_n4_*.jsonl.gz`) hold every failing state (dl13.c's "D" records with `"br": "none"` and `f ≥ 1`, with the core and the values).

**Every failing (core, profile)** is one line of `n4_failures_n4_1.tsv` (10 profiles), `n4_failures_n4_2.tsv` (1,120) and
`n4_failures_n4_3_s200b.tsv` (1). Each line gives the file, core position and idx, m, the sets, the profile (indices into
`check4.core_domains`), the values, and the failing bases. Written by `n4_failures_list.py` (log: `n4_failures_list.log`).

| run | core pos (idx, m) | sets | failing profiles | failing states | (f, def, k, signature) |
|---|---|---|---:|---:|---|
| (a) | 25 (5, 6) | [[0,2,4,5],[1,3,5],[3,4,5],[3,4,5]] | 10 | 20 | (3, 1, 2, G): 20 |
| (b) | 20 (2, 6) | [[0,1,3,5],[2,3,4,5],[2,4,5],[3,4,5]] | 120 | 240 | (3, 1, 2, G): 240 |
| (b) | 22 (4, 6) | [[0,2,4,5],[1,3,4,5],[3,4,5],[3,4,5]] | 240 | 480 | (3, 1, 2, G): 480 |
| (b) | 24 (6, 6) | [[0,2,3,5],[1,2,4,5],[3,4,5],[3,4,5]] | 200 | 800 | (3, 1, 2, O): 600, (3, 1, 2, G): 200 |
| (b) | 27 (9, 6) | [[0,2,3,5],[1,3,4,5],[2,4,5],[3,4,5]] | 120 | 240 | (3, 1, 2, O): 240 |
| (b) | 28 (10, 6) | [[0,2,3,5],[1,4,5],[2,3,4,5],[3,4,5]] | 120 | 240 | (3, 1, 2, G): 240 |
| (b) | 92 (12, 7) | [[0,2,4,6],[1,3,5,6],[4,5,6],[4,5,6]] | 200 | 800 | (3, 1, 2, G): 800 |
| (b) | 94 (14, 7) | [[0,2,5,6],[1,4,5,6],[3,4,6],[4,5,6]] | 120 | 240 | (3, 1, 2, G): 240 |
| (e) | 64 (17, 7) of `n4_3` | [[0,2,5,6],[1,4,6],[3,4,5,6],[3,4,5,6]] | 1 | 2 | (3, 1, 2, G): 2 |

## The common shape

All 3,062 failing states have f = 3 (n = 4, so exactly one free agent), def = 1, and a nearest better min-frozen state at distance k = 2.
Every nearest better state (c4x_check.py's 𝒫 and deficit, `n4_failures_list.py --nearest`) is reached by **an exchange of goods between two
frozen agents that both stay frozen, with the needed set NA unchanged** (shape `FF=NA` in the TSVs: a frozen agent here means a singleton
base inside NA, as in `k4/dl2_relations_xcheck.py`). That move is neither a (T1) re-base of a free agent nor a (T3) role swap, where the frozen
agent x becomes free and the needer z becomes frozen. dl13.c tests every better min-frozen P′, not only the nearest ones, and finds no R₁₃
move to any of them.

The smallest example, run (a), core pos 25 (idx 5) of `k4_certs_4_n4_1`, m = 6, profile (6, 1, 3, 3):

- agent 0 on goods {0, 2, 4, 5} with values (2, 3, 4, 8); agent 1 on {1, 3, 5}: (2, 4, 3); agents 2 and 3 (twins) on {3, 4, 5}: (3, 4, 2);
- state P = ({4}, {1}, {3}, {5}): min-frozen with f = 3 (agents 0, 2, 3 frozen), NA = {3, 4, 5}, def(P) = 1;
- its only better min-frozen state at distance 2 is P′ = ({5}, {1}, {3}, {4}), def(P′) = 0: agents 0 and 3 exchange goods 4 and 5, both
  stay frozen, NA stays {3, 4, 5};
- the second failing state of this profile is the same with the twins 2 and 3 swapped: ({4}, {1}, {5}, {3}).

The other 9 profiles of this core differ only in agent 0's values (`n4_failures_n4_1.tsv`), and the failures in (b) and (e) have the same
structure (`n4_*_failures_xcheck.log` prints the nearest repair of each state).

## Cross-checks

`n4_failures_xcheck.py` re-runs every failing profile through the three implementations that `k4/dl13_check.py` compares, imported unchanged:
dl13.c `-s`, the model (`k4/dl2_relations.py` on `k4/suite/model.py`) and main's `k4/c4x_check.py` with
`k4/dl2_relations_xcheck.rel_B`. It also tests R_T (DL_T's relation, `RTr` in both Python implementations).

| dump | profiles | failing states | all three agree that DL₁₃ fails | R_T fails too (model and xcheck) | log |
|---|---:|---:|---:|---:|---|
| (a) `dump_n4_1` | 10 | 20 | 20 | 20 | `n4_1_failures_xcheck.log` |
| (b) `dump_n4_2` | 1,120 | 3,040 | 3,040 | 3,040 | `n4_2_failures_xcheck.log` |
| (e) `dump_n4_3_s200b` | 1 | 2 | 2 | 2 | `n4_3_s200b_failures_xcheck.log` |

Before the runs, `python3 k4/dl13_check.py suite` gave on this machine 360 states and 0 mismatches (`n4_check_suite.log`), as in the
commit that added dl13.c.

## What this bears on (for the coordinator; the ledger is unchanged here)

- **K4.DL2.T13 (DL₁₃).** The data contradict it at n = 4 (m = 6 and m = 7) in 9 cores. Each failing state has a better min-frozen state, reached
  by an exchange between two frozen agents.
- **K4.DL2.T (DL_T).** Its relation R_T also fails at every failing state checked, in both Python implementations. At f = 3 there is one free
  agent, so a rotation is just a re-base of that agent.
- **K4.DL2.T13E / K4.DL2.TE.** Those rows sampled 20 random profiles per n = 4 core, and the failures are rare:
  - (a): 10 of core 25's 31,104 profiles;
  - (b): 120 to 240 of each failing core's 746,496 to 2,985,984 profiles, at most 0.03 %;
  - (c), (e): 1 of the 135,600 draws over both seeds for three 4-good agents.
- A relation that adds the frozen–frozen exchange keeping NA (both agents stay frozen) would cover every failing state here. That is
  conjecture, not tested.
