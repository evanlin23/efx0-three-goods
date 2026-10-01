# DL_RT4 on n = 5: pure cores and the hard-instance catalogues (compute/k4-rt4, n5c slice)

EVIDENCE only. Branch `compute/k4-rt4-n5c`, started from `compute/k4-rt4` at 2e9adeb. The tool is `k4/dlrt4.c`, unchanged
(sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`, checked before the runs and printed in every log),
driven by `k4/dlrt4_run.py`. The machine had 4 CPUs, and every run used `--jobs=4` with the default `--rt=50 --ro=0`. No
existing file was modified, and LEDGER.md is not edited.

**Result: DL_RT4 fails.** It fails at 64 f ≥ 1 states of 8 big-top profiles in 3 pure n = 5 cores (`n5c_purebt`).
`k4/dlrt4_ref.py` confirms every one, and the details are in **`n5c_FAILURES.md`**. Every other run found no failure.

## Runs

Every run has its log `<tag>.log` (it starts with the command line), checkpoint `ckpt_<tag>.jsonl`, dump
`dump_<tag>.jsonl.gz` (absent when a run dumped nothing) and tables `tables_<tag>.json`, all in `results/k4_rt4/`.

| tag | input | profiles | ω ≥ 1 | def > 0 states with f ≥ 1 | (with f = 0) | **DL_RT4 fails** | RT4 fails at f = 0 | anomalies | wall time |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| n5c_cat_gap_n5_1_s100 | catalogue, every record | 547 | 547 | 0 | 0 | **0** | 0 | 0 | < 1 s |
| n5c_cat_gap_n5_2_s100 | catalogue, every record | 7,713 | 7,713 | 25 | 0 | **0** | 0 | 0 | 1 s |
| n5c_cat_gap_n5_3_s100 | catalogue, every record | 31,190 | 31,190 | 897 | 0 | **0** | 0 | 0 | 4 s |
| n5c_cat_gap_n5_4_s100 | catalogue, every record | 47,274 | 47,274 | 5,794 | 0 | **0** | 0 | 0 | 9 s |
| n5c_cat_gap_n5_pure_s100 | catalogue, every record | 29,086 | 29,086 | 14,262 | 0 | **0** | 0 | 0 | 6 s |
| n5c_cat_hard_hunt | `hard_hunt.json.gz`, every record (all n = 4) | 117 | 117 | 192 | 0 | **0** | 0 | 0 | < 1 s |
| n5c_cat_hard_hunt_smallest | `hard_hunt_smallest.json.gz` via `inst` (see below) | 12 | 12 | 5 | 0 | **0** | 0 | 0 | < 1 s |
| n5c_pure | `certs results/k4_certs_5_pure.json.gz --sample=5000 --seed=1` | 23,370,000 | 7,888,182 | 725,850 | 6,605,105 | **0** | 0 | 0 | 1,372 s |
| n5c_purebt | the same with `--bt=all`, `--seed=2` | 23,370,000 | 12,625,575 | 1,856,467 | 0 | **64** | 0 | 0 | 1,098 s |
| n5c_suite | `suite --minn=5` | 20 | 13 | 21 | 5,119 | **0** | 0 | 0 | 20 s |

Totals: 46,855,959 profiles, 2,603,513 f ≥ 1 states with def > 0, 64 failures. The catalogue runs cover 115,939
profiles and 21,175 such states. The wall time is the driver's own (`[N s]` in the log). The checkpoints also give each
unit's seconds: 5,294 s summed over the units of `n5c_pure`, 4,313 s for `n5c_purebt`.

## Repair branches (states with f ≥ 1 and def > 0, improving moves)

Columns: states with an improving T1 / T2 / T3p / T3h / T4 move; states whose only branch is T1 / T2 / T3 / T4; states at
which R_T = T1+T2+T3, R_13 = T1+T3 and R_13+T4 fail; the least RT4 move size (1 / 2 / 3 / none). This is dlrt4.c's "L"
line (`counters` in the tables JSON).

| tag | T1 | T2 | T3p | T3h | T4 | only T1 / T2 / T3 / T4 | R_T / R_13 / R_13+T4 fail | least move size 1 / 2 / 3 / none |
|---|---:|---:|---:|---:|---:|---|---|---|
| n5c_cat_gap_n5_1_s100 | 0 | 0 | 0 | 0 | 0 | 0 / 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 / 0 |
| n5c_cat_gap_n5_2_s100 | 25 | 25 | 19 | 25 | 0 | 0 / 0 / 0 / 0 | 0 / 0 / 0 | 25 / 0 / 0 / 0 |
| n5c_cat_gap_n5_3_s100 | 896 | 891 | 731 | 865 | 2 | 0 / 0 / 0 / 0 | 0 / 0 / 0 | 896 / 1 / 0 / 0 |
| n5c_cat_gap_n5_4_s100 | 5,768 | 5,782 | 4,725 | 5,512 | 21 | 0 / 0 / 1 / 0 | 0 / 0 / 0 | 5,768 / 26 / 0 / 0 |
| n5c_cat_gap_n5_pure_s100 | 14,189 | 14,244 | 12,210 | 14,025 | 20 | 0 / 0 / 0 / 0 | 0 / 0 / 0 | 14,189 / 73 / 0 / 0 |
| n5c_cat_hard_hunt | 121 | 117 | 192 | 191 | 0 | 0 / 0 / 71 / 0 | 0 / 0 / 0 | 121 / 71 / 0 / 0 |
| n5c_cat_hard_hunt_smallest | 5 | 5 | 5 | 5 | 0 | 0 / 0 / 0 / 0 | 0 / 0 / 0 | 5 / 0 / 0 / 0 |
| n5c_pure | 718,292 | 722,707 | 626,032 | 711,638 | 15,784 | 2 / 0 / 1,439 / 8 | 8 / 8 / 0 | 718,292 / 7,551 / 7 / 0 |
| n5c_purebt | 1,836,835 | 1,833,936 | 1,829,403 | 1,839,425 | 84,176 | 32 / 28 / 11,807 / 37 | 101 / 130 / 92 | 1,836,835 / 19,427 / 141 / **64** |
| n5c_suite | 21 | 21 | 21 | 21 | 0 | 0 / 0 / 0 / 0 | 0 / 0 / 0 | 21 / 0 / 0 / 0 |

States by f (table B summed): n5c_pure f = 1: 652,534, 2: 70,997, 3: 2,283, 4: 36. n5c_purebt f = 1: 585,694, 2: 1,241,973,
3: 28,734, 4: 66. The catalogues and the suite have only f = 1 to 3.

The most frequent branch sets (table B summed over f and signature):
- n5c_pure: T1+T2+T3p+T3h 602,461; T1+T2+T3h 85,878; T1+T2+T3p+T3h+T4 14,494; T1+T2 13,454; T2+T3p+T3h 5,378; T3p+T3h 1,234;
  T1+T3p+T3h 1,032; T4 alone 8; T1 alone 2; T3p alone 202; T3h alone 3.
- n5c_purebt: T1+T2+T3p+T3h 1,723,650; T1+T2+T3p+T3h+T4 79,019; T1+T2 15,702; T3p+T3h 11,041; T1+T2+T3h 10,854;
  T1+T3p+T3h 6,247; T3p alone 625; T3h alone 141; **none 64**; T4 alone 37; T1 alone 32; T2 alone 28.

Where T4 is needed:
- In n5c_pure, T4 is the only branch at 8 states, all with f = 4, signature G and nearest distance 2. Each is repaired by
  a T4 2-cycle: two frozen agents exchange their one-good bases. R_T fails there and R_13 + T4 holds. Cores 65 and 392
  are dumped as examples.
- In n5c_purebt, T4 alone holds at 37 states: 27 with f = 3 and 10 with f = 4.

## Choices and deviations

- **P = 5,000** for both pure runs. It was chosen from timing at P = 1,000, which projected about 8 min for all 4,674
  cores on 4 CPUs: a core took about 0.035 s at m = 9 and about 5 s at m = 14. At P = 5,000 the m = 14 cores took about
  22 s each. The two runs took 23 and 18 min. The whole slice took about 42 min of wall time, well under the 4-hour
  budget, so nothing was reduced.
- **hard_hunt_smallest.json.gz** maps a category (W, N, X, T2, NPO, F2) to records and has no "records" list, so
  `dlrt4_run.py catalog` cannot read it. Its 12 distinct (core, profile) records include 8 that are not in
  `hard_hunt.json.gz`. 4 of the 12 have n = 5. They were converted, with ids as `catalog` builds them plus the category, to
  `n5c_hard_hunt_smallest_inst.json` and run with `dlrt4_run.py inst`.
- `hard_hunt.json.gz` at 245040b holds 117 records, all n = 4 (categories W 115, N 2). It was run as the slice asks.
- **c4-H5** (n = 21, m = 53) is the one suite instance with n ≥ 5 that `suite --minn=5` skips: the default build allows
  m ≤ 32. It was not run. It is H_5 of `k4/c4.md` §7, which the driver's `ht` mode (with `--wide`) covers. That mode is
  outside this slice.
- The catalogues were extracted at 245040b exactly as in `k4/strategy.md` §4, into `k4/suite/.cache/gapbench/`, which is
  gitignored.

## Reproduce

```
git cat-file -e 245040b^{commit} || git fetch --unshallow origin || git fetch origin 245040b
mkdir -p k4/suite/.cache/gapbench && git archive 245040b k4 results/k4_gap | tar -x -C k4/suite/.cache/gapbench
G=k4/suite/.cache/gapbench/results/k4_gap; R=results/k4_rt4; O="--jobs=$(nproc)"
for x in gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100 hard_hunt; do t=n5c_cat_$x
  python3 k4/dlrt4_run.py catalog $G/$x.json.gz --every=1 $O --ckpt=$R/ckpt_$t.jsonl --dump=$R/dump_$t.jsonl.gz --tables=$R/tables_$t.json; done
t=n5c_cat_hard_hunt_smallest; python3 k4/dlrt4_run.py inst $R/n5c_hard_hunt_smallest_inst.json $O --ckpt=$R/ckpt_$t.jsonl --dump=$R/dump_$t.jsonl.gz --tables=$R/tables_$t.json
t=n5c_pure; python3 k4/dlrt4_run.py certs results/k4_certs_5_pure.json.gz --sample=5000 --seed=1 --progress $O --ckpt=$R/ckpt_$t.jsonl --dump=$R/dump_$t.jsonl.gz --tables=$R/tables_$t.json
t=n5c_purebt; python3 k4/dlrt4_run.py certs results/k4_certs_5_pure.json.gz --sample=5000 --seed=2 --bt=all --progress $O --ckpt=$R/ckpt_$t.jsonl --dump=$R/dump_$t.jsonl.gz --tables=$R/tables_$t.json
t=n5c_suite; python3 k4/dlrt4_run.py suite --minn=5 --progress $O --ckpt=$R/ckpt_$t.jsonl --dump=$R/dump_$t.jsonl.gz --tables=$R/tables_$t.json
python3 results/k4_rt4/n5c_failures_list.py $R/n5c_failures_purebt.tsv $R/dump_n5c_purebt.jsonl.gz --inst=$R/n5c_fail_inst.json
python3 k4/dlrt4_ref.py inst $R/n5c_fail_inst.json
```

(With an existing checkpoint, a run resumes. Delete the checkpoint and dump to start over.)

## Status

- **Proved:** nothing.
- **Certified:** nothing (no certificate files). The 64 failures are confirmed by two implementations: dlrt4.c and the
  Python reference `k4/dlrt4_ref.py`.
- **Evidence against DL_RT4:** 64 failing states on the pure n = 5 cores with big-top profiles (`n5c_FAILURES.md`). The
  repair the data show is a 3-agent chain role swap that RT4 does not contain.
- **Evidence for DL_RT4:** no other failure in 46.8 M profiles, including every record of #53's n = 5 catalogues.
- **Open:** whether RT4 plus the chain move (or chains through more frozen agents) suffices, and how often the chain is
  needed at n = 5 with other profile restrictions, or at n = 6.
