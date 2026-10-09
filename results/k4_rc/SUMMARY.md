# DL_RC on data: summary (compute/k4-rc)

EVIDENCE only. Random and adversarial search proves nothing, and a hunt that finds nothing is no proof either. Every negative claim below about a given input is single-implementation unless a log of `k4/dlrc_ref.py` is named. LEDGER.md is not edited.

## Results

1. **DL_RC is false (EVIDENCE).** It fails in two pure n = 5 cores of `results/k4_certs_5_pure.json.gz`. Every failing profile is confirmed by dlrc_ref.py. The DL_RT4 part is also confirmed by dlrt4_ref.py (model.py) for all 369 profiles of core 4604 and for the first 81 of core 4515. Details are in `FAILURES.md`.

   | core | m | f | failing profiles | failing states | the repairs it would need |
   |---|---:|---:|---:|---:|---|
   | 4604 | 13 | 1 | 369 | 369, one state P = ({11}, {12}, {3,7}, {4,8}, {5,9}) | a role swap whose helper grows by a junk good (distance 3), or two helpers (distance 4) |
   | 4515 | 12 | 2 | 1,076 | 4,304, four states per profile | a role swap with two helpers (distance 4), or a double role swap, two frozen agents out and two in (distance 5) |

   - Both are also **new DL_RT4 failures**, at f = 1 and f = 2. They are not chain states.
   - **DL on the key graph holds at all of them:** def*(κ(P)) = def(P) = 1 and kmin = −1 at every failing state. In the profiles examined (`rc_failures_n5_keyform.log`, `rc_failures_4515_keyform.log`), every state of the key has def 1, and from other states of the key a plain T3p / T3h move improves.
2. **DL_RC holds on the inputs that produced the n = 5 DL_RT4 failures** (task (c), full runs):
   - all 1,856,467 + 1,122,391 states with f ≥ 1;
   - the 64 + 3 DL_RT4 failures there are chain states: their only repairs are T3⁺ moves with |W| = 1;
   - the key form holds at all 1,920 + 1,823 keys with def* > 0.
3. **Chain states are common, and every one has least |W| = 1.**
   - **Where found:** the hunt finds DL_RT4 failures repaired only by T3c in many places:
     - at **n = 4** (pure cores 153, m = 9; 199, m = 10; 213, m = 11; f = 2);
     - at n = 5 with f = 2 and f = 3;
     - at n = 6 (extensions of the failing n = 5 cores);
     - at n = 10 (gluings, f = 6).
   - **What was not found:** no state needs a chain with |W| ≥ 2, none needs two chain role swaps at once, and no T3c-repaired state fails the key form.
4. **The key form never failed:** no failing key in (b) or (c), and no key-form failure (kf = 0) at any profile the hunt evaluated.

## Tools (new files; existing files unchanged)

| file | what | sha256 (first 16) |
|---|---|---|
| `k4/dlrc.c` | copy of `k4/dlrt4.c` with the T3⁺ test, the least \|W\|, the key graph (def*, kmin, the key form), per-profile H lines, dumps with shapes | `f1cf4cc169a34762` (all runs) |
| `k4/dlrc_run.py` | driver, copy of `k4/dlrt4_run.py`, same modes; `--cores=A:B:S` | `b0c6d71786f23364` |
| `k4/dlrc_ref.py` | independent check on `dl134_xcheck.py` / `c4x_check.py` (T3⁺ = the coordinator's `t3plus`); compares every field of every state and the H lines; also checks that dlrc.c's K / L lines, tables and S-line prefixes equal dlrt4.c's, and that the -DBIGPP=0 build agrees | `8b90a88456df0b23` |
| `k4/dlrc_hunt.py` | the hill-climbing hunt | runs used `7fc97147` (= commit 27df591), `80bd796e` (ac6d83d), `fe0fa508` (d7e6949); the later ones only add modes / options |
| `k4/dlrc_chains.py`, `k4/dlrc_failures.py`, `k4/dlrc_shrink.py`, `k4/dlrc_hunt_summary.py`, `k4/dlrc_n6_probe.py` | analysis: chain-state shapes; failure listing; deleting goods from a failure; hunt table; the n = 6 probe | |
| `k4/dlrc_runs.sh`, `k4/dlrc_ref_runs.sh`, `k4/dlrc_hunt_runs*.sh` | the commands of every run (`_runs2.sh` and `_runs3.sh` were not run, see their headers) | |

`k4/dlrt4.c` keeps sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`.

## (b) Validation of dlrc.c against dlrc_ref.py

Every row has 0 mismatches. That covers every field of every state against the reference, the H lines, dlrc.c's K / L lines, tables and S lines against dlrt4.c, and the -DBIGPP=0 build. dlrc.c's internal checks were also 0: anomc (a T3⁺ move with W = ∅ that is not a T3 move) and rcnokey (DL_RC holding where the key form fails).

| input | log | profiles | states f ≥ 1 | DL_RT4 fails | DL_RC fails | key form fails |
|---|---|---:|---:|---:|---:|---:|
| the 10 failing n = 5 profiles (`rt4_fail10_inst.json`) | `ref_fail10.log` | 10 | 168 | **67** | **0** | 0 |
| n = 4 DL13 failures (`results/k4_dl13/n4_failures_*.tsv`) | `ref_n4_failures.log` | 1,131 | 7,586 | 0 | 0 | 0 |
| the suite (151 instances; c4-H2 and c4-H5 are too large for the reference) | `ref_suite.log` | 151 | 189 | 0 | 0 | 0 |
| 1,000 random n = 3 profiles (800 with an f ≥ 1 state) | `ref_random_n3.log` | 1,000 | 2,027 | 0 | 0 | 0 |
| 1,000 random n = 4 profiles (800 with an f ≥ 1 state) | `ref_random_n4.log` | 1,000 | 2,479 | 0 | 0 | 0 |
| later: 54 hunt profiles from the failing ones (4 at f = 2) | `ref_hunt_fail10_sample.log` | 54 | 1,264 | 415 | 0 | 0 |
| later: 60 n = 4 chain profiles (core 153) | `ref_hunt_n4_pure_chain_sample.log` | 60 | 1,138 | 178 | 0 | 0 |
| later: 60 n = 4 chain profiles (20 each of cores 153, 199, 213) | `ref_hunt_n4_chain_cores.log` | 60 | 1,368 | 408 | 0 | 0 |
| later: the 369 DL_RC-failing profiles of core 4604 | `ref_rc_fail_all.log` (+ `ref_rt4_rc_fail_all.log`, dlrt4_ref.py) | 369 | 16,605 | 369 | **369** | 0 |
| later: the first 81 DL_RC-failing profiles of core 4515 | `ref_rc_fail_4515.log` (+ `ref_rt4_rc_fail_4515.log`, dlrt4_ref.py) | 81 | 8,018 | 324 | **324** | 0 |
| later: all 1,076 DL_RC-failing profiles of core 4515 | `ref_rc_fail_4515_all.log` | 1,076 | 99,583 | 4,304 | **4,304** | 0 |

## (c) The inputs of the n = 5 DL_RT4 failures

Both runs are complete, over every core, with dlrc.c `f1cf4cc1…`.

| run | log / tables / dump | profiles | ω ≥ 1 | states f ≥ 1 | DL_RT4 fails | DL_RC fails | chain states (least \|W\| = 1 / ≥ 2) | keys def* > 0 | key form fails |
|---|---|---:|---:|---:|---:|---:|---|---:|---:|
| `k4_certs_5_pure`, `--bt=all`, 5,000 per core, seed 2 (n5c's `n5c_purebt`) | `c_purebt.log`, `tables_c_purebt.json`, `dump_c_purebt.jsonl.gz` | 23,370,000 | 12,625,575 | 1,856,467 | 64 | **0** | 64 / 0 | 1,920 | 0 |
| `k4_certs_5_n4_4`, 16,000 per core, seed 1 (n5b's `n5b_4`; that run's log stopped at 9,131 cores, this one has all 9,846) | `c_n4_4.log`, `tables_c_n4_4.json`, `dump_c_n4_4.jsonl.gz` | 157,536,000 | 33,567,616 | 1,122,391 | 3 | **0** | 3 / 0 | 1,823 | 0 |

- **Agreement with dlrt4.c:** the DL_RT4 counters equal dlrt4.c's on the n5c run (the same 64 failures in cores 2614, 4170 and 4214). The n4_4 run has n5b's 3 failures, in cores 3206 and 3521.
- **The chain states** (`chains_c_purebt.log`, `chains_c_n4_4.log`): all have f = 3, def 1, k = 3 and least |W| = 1. Improving T3c moves with |W| = 2 exist besides.
- **Better states that are not R_C moves:** some better states of the n4_4 chain states are double role swaps, of shape (|U|, |Z|, |W|, |Y|) = (2, 2, 1, 0).
- **Interruption:** the n4_4 driver was stopped once at the background time limit and resumed from its checkpoint, so its log has two headers.

## (d) The hunt

**Method.** `k4/dlrc_hunt.py` hill-climbs strict profiles of a fixed core. The types come from `check4.core_domains`.
- **Moves:** each step changes the type of one agent (two with probability 0.2). A 4-good agent's new type is big-top with probability `--bt`. Each step evaluates 24 neighbours in one dlrc.c call and takes the best one if it is at least as good (or, with probability 0.05, anyway). After 40 steps without a new best the climb restarts from the best profile.
- **Objective (std).** Over the def > 0 states with f ≥ 1, compared in order:
  1. DL_RC failures;
  2. key-form failures;
  3. **chain states** (only T3c moves improve);
  4. **chain states with f ≥ 3**;
  5. **−(least deficit gap)**, where the gap of a state is def(P) minus the least deficit of an improving R_C move;
  6. then, as tie-breakers: states whose least R_C repair changes ≥ 3 agents, dl2's k*, −(the least number of improving R_C moves), and the number of states.

  Terms 3 to 5 are the brief's three terms; the last terms give a gradient on the plateaus. Variants: **w2** puts the chain states with least |W| ≥ 2 first, after the failures; **k3** puts the distance terms before the gap.
- **Seeds:**
  - the 10 failing profiles (`fail10`, also with w2);
  - the n = 5 cores with ≥ 3 four-good agents, both the top 200 of each file as ranked by the earlier dlrt4.c / dlrc.c checkpoints (`ranked_*`) and random samples (`certs_*`);
  - n = 6: `k4_certs_6_n4_1` (`n6`, w2);
  - gluings of two failing n = 5 profiles sharing a good, each checked with `check4.is_core` (`glue`, n = 10, w2);
  - additions to the brief's list:
    - n = 6 extensions of the failing cores by one agent (`extend6`, w2);
    - after the failures, towards smaller n and m:
      - every n = 4 core with three or four four-good agents (`n4_*`);
      - the cores obtained from cores 4604 and 4515 by deleting one or two goods (`shrink_cores`, `shrink_cores_4515`);
      - climbs from the failing profiles (`core4604`, `core4515`).

The table is from `hunt_summary.log` (`k4/dlrc_hunt_summary.py`):
- one row per run; a unit is one climb;
- "profiles evaluated" counts repeats;
- "f ≥ 1 states met" sums the def > 0 states with f ≥ 1 of every evaluated profile;
- "DL_RC fails" sums, over the climbs, the distinct failing profiles each climb met, so a profile met by two climbs counts twice;
- CPU s is the sum of the climbs' times; it includes time spent waiting while the CPUs were shared;
- the best score is in the order of the run's objective (std: rcf, kf, chain, chain3, −gap, c3, k*, −minmv, st1; w2 inserts chainw2 after kf; k3 moves c3 and k* before −gap).

| run | units | n | profiles evaluated | f >= 1 states met | units reaching a chain state | distinct chain profiles | largest least \|W\| | DL_RC fails | key form fails | CPU s | best score (where) |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| certs_n4_3 | 200 | 5 | 1960000 | 230352 | 0 | 0 | 0 | 0 | 0 | 295 | [0, 0, 0, 0, -2, 0, 2, -14, 14] ({"file": "k4_certs_5_n4_3.json.gz", "pos": 9840}, k4_certs_5_n4_3.json.gz#9840[m=12,idx=74], profile [34, 79, 42, 2, 3]) |
| certs_n4_3_x | 1000 | 5 | 9800000 | 944768 | 0 | 0 | 0 | 0 | 0 | 2111 | [0, 0, 0, 0, -1, 0, 2, -12, 3] ({"file": "k4_certs_5_n4_3.json.gz", "pos": 7738}, k4_certs_5_n4_3.json.gz#7738[m=10,idx=517], profile [106, 43, 64, 0, 5]) |
| certs_n4_4 | 200 | 5 | 1960000 | 783664 | 0 | 0 | 0 | 0 | 0 | 445 | [0, 0, 0, 0, -1, 0, 2, -15, 8] ({"file": "k4_certs_5_n4_4.json.gz", "pos": 9574}, k4_certs_5_n4_4.json.gz#9574[m=12,idx=161], profile [92, 34, 17, 10, 5]) |
| certs_n4_4_x | 1500 | 5 | 14700000 | 4641628 | 1 | 76 | 1 | 0 | 0 | 5307 | [0, 0, 4, 4, -2, 4, 3, -20, 12] ({"file": "k4_certs_5_n4_4.json.gz", "pos": 1123}, k4_certs_5_n4_4.json.gz#1123[m=8,idx=213], profile [79, 146, 148, 190, 4]) |
| certs_pure | 200 | 5 | 1960000 | 2188904 | 1 | 169 | 1 | 0 | 0 | 662 | [0, 0, 14, 0, -1, 14, 3, -13, 74] ({"file": "k4_certs_5_pure.json.gz", "pos": 4214}, k4_certs_5_pure.json.gz#4214[m=12,idx=69], profile [44, 6, 6, 44, 45]) |
| certs_pure_x | 1500 | 5 | 14700000 | 16424078 | 5 | 962 | 1 | 81 | 0 | 4835 | [4, 0, 0, 0, 0, 38, 4, 0, 114] ({"file": "k4_certs_5_pure.json.gz", "pos": 4515}, k4_certs_5_pure.json.gz#4515[m=12,idx=370], profile [74, 153, 112, 227, 80]) |
| core4515 | 12 | 5 | 288012 | 5770935 | 0 | 0 | 0 | 2562 | 0 | 498 | [4, 0, 0, 0, 0, 38, 4, 0, 114] ({"inst": 0, "rep": 0}, k4_certs_5_pure.json.gz#4515[m=12,idx=370]|prof=37,223,112,218,42, profile [14, 129, 112, 218, 42]) |
| core4604 | 12 | 5 | 432012 | 8996569 | 0 | 0 | 0 | 1510 | 0 | 531 | [1, 0, 0, 0, 0, 4, 3, 0, 45] ({"inst": 2, "rep": 0}, k4_certs_5_pure.json.gz#4604[m=13,idx=58]|prof=44,118,8,36,200, profile [44, 118, 8, 36, 200]) |
| extend6 | 80 | 6 | 784000 | 1409133 | 5 | 2190 | 1 | 0 | 0 | 574 | [0, 0, 0, 41, 41, -2, 41, 3, -18, 129] ({"a": 5, "S": [0, 8, 12, 13]}, ext(5:[0, 8, 12, 13]), profile [6, 38, 72, 45, 77, 27]) |
| fail10 | 80 | 5 | 5760080 | 12819372 | 80 | 256719 | 1 | 0 | 0 | 5319 | [0, 0, 21, 0, -2, 21, 3, -17, 72] ({"inst": 7, "rep": 6}, k4_certs_5_pure.json.gz#4170[m=12,idx=25]:22,18,4,10,37, profile [79, 34, 34, 46, 61]) |
| fail10_w2 | 20 | 5 | 960020 | 2072027 | 20 | 45619 | 1 | 0 | 0 | 844 | [0, 0, 0, 12, 12, -2, 12, 3, -14, 32] ({"inst": 8, "rep": 0}, k4_certs_5_pure.json.gz#4214[m=12,idx=69]:0,12,4,11,39, profile [102, 38, 72, 38, 262]) |
| fail10_w2bt | 20 | 5 | 960020 | 3158111 | 20 | 27700 | 1 | 0 | 0 | 623 | [0, 0, 0, 12, 12, -2, 12, 3, -14, 32] ({"inst": 8, "rep": 0}, k4_certs_5_pure.json.gz#4214[m=12,idx=69]:0,12,4,11,39, profile [106, 38, 10, 38, 213]) |
| glue | 20 | 10 | 6420 | 243878 | 4 | 45 | 1 | 0 | 0 | 3384 | [0, 0, 0, 20, 20, -2, 20, 3, -63, 152] ({"a": 6, "b": 2, "gA": 8, "gB": 1}, glue(6:8,2:1), profile [106, 34, 64, 72, 260, 46, 31, 211, 80, 80]) |
| n4_n4_3 | 339 | 4 | 4949400 | 1486472 | 0 | 0 | 0 | 0 | 0 | 1560 | [0, 0, 0, 0, -1, 0, 2, -5, 3] ({"file": "k4_certs_4_n4_3.json.gz", "pos": 180}, k4_certs_4_n4_3.json.gz#180[m=8,idx=43], profile [75, 182, 128, 0]) |
| n4_n4_3_k3 | 339 | 4 | 4949400 | 1917054 | 0 | 0 | 0 | 0 | 0 | 1380 | [0, 0, 0, 0, 0, 2, -1, -5, 4] ({"file": "k4_certs_4_n4_3.json.gz", "pos": 258}, k4_certs_4_n4_3.json.gz#258[m=9,idx=12], profile [7, 8, 0, 95]) |
| n4_pure | 219 | 4 | 3197400 | 3366076 | 2 | 1111 | 1 | 0 | 0 | 1262 | [0, 0, 12, 0, -2, 12, 3, -6, 28] ({"file": "k4_certs_4_pure.json.gz", "pos": 213}, k4_certs_4_pure.json.gz#213[m=11,idx=4], profile [52, 10, 64, 72]) |
| n4_pure_k3 | 219 | 4 | 3197400 | 4193903 | 2 | 918 | 1 | 0 | 0 | 1291 | [0, 0, 9, 0, 9, 3, -2, -6, 25] ({"file": "k4_certs_4_pure.json.gz", "pos": 199}, k4_certs_4_pure.json.gz#199[m=10,idx=22], profile [52, 72, 88, 80]) |
| n6 | 600 | 6 | 4440000 | 0 | 0 | 0 | 0 | 0 | 0 | 406 | [0, 0, 0, 0, 0, -1000000, 0, 0, -1000000, 0] ({"file": "k4_certs_6_n4_1.json.gz", "pos": 84}, k4_certs_6_n4_1.json.gz#84[m=5,idx=78], profile [2, 1, 20, 0, 1, 2]) |
| ranked_n4_3 | 200 | 5 | 3880000 | 3183853 | 0 | 0 | 0 | 0 | 0 | 1459 | [0, 0, 0, 0, -1, 0, 2, -4, 3] ({"file": "k4_certs_5_n4_3.json.gz", "pos": 9189, "rank": [0, 0, 133, 4124]}, k4_certs_5_n4_3.json.gz#9189[m=11,idx=62], profile [95, 8, 8, 0, 5]) |
| ranked_n4_4 | 200 | 5 | 3880000 | 3069522 | 1 | 113 | 1 | 0 | 0 | 1422 | [0, 0, 4, 4, -2, 4, 3, -12, 8] ({"file": "k4_certs_5_n4_4.json.gz", "pos": 1121, "rank": [0, 0, 8, 8]}, k4_certs_5_n4_4.json.gz#1121[m=8,idx=211], profile [95, 45, 80, 146, 3]) |
| ranked_pure | 200 | 5 | 3880000 | 45438600 | 4 | 1177 | 1 | 45 | 0 | 12015 | [1, 0, 0, 0, 0, 4, 3, 0, 45] ({"file": "k4_certs_5_pure.json.gz", "pos": 4604, "rank": [0, 0, 298, 23355]}, k4_certs_5_pure.json.gz#4604[m=13,idx=58], profile [44, 118, 8, 8, 158]) |
| shrink_cores | 240 | 5 | 8679642 | 13358728 | 0 | 0 | 0 | 0 | 0 | 4783 | [0, 0, 0, 0, -1, 0, 2, -4, 23] ({"inst": 5, "rep": 0}, core 4604 minus goods [5], profile [95, 138, 36, 8, 3]) |
| shrink_cores_4515 | 84 | 5 | 2032004 | 453103 | 0 | 0 | 0 | 0 | 0 | 638 | [0, 0, 0, 0, -1, 0, 1, -20, 5] ({"inst": 1, "rep": 2}, core 4515 minus goods [1], profile [66, 5, 22, 269, 184]) |
| total | 7484 | | 97355810 | 136150730 | 145 | 336799 | 1 | 4198 | 0 | 51644 | |

### Best objective values reached, and where

- **DL_RC failures (score starting with rcf ≥ 1):**
  - `ranked_pure`: core 4604, best (1, 0, 0, 0, 0, 4, 3, 0, 45), profile (44, 118, 8, 8, 158);
  - `certs_pure_x`: core 4515, best (4, 0, 0, 0, 0, 38, 4, 0, 114), profile (74, 153, 112, 227, 80);
  - the climbs `core4604` and `core4515` started from those failures; their best scores equal these;
  - no run reached a key-form failure (kf = 0 everywhere).
- **Most chain states in one profile:**
  - 41 at n = 6, f = 3: `extend6`, core 5 of the list plus an agent on goods {0, 8, 12, 13};
  - 21 at n = 5, f = 2: `fail10`, core 4170, profile (79, 34, 34, 46, 61);
  - 20 at n = 10, f = 6: `glue`, gluing (6:8, 2:1);
  - 12 at n = 4, f = 2: `n4_pure`, core 213, m = 11.
- **Chain states with least |W| ≥ 2:** none in any run. In every run that reached a chain state, the largest least |W| is 1, so the w2 objective never got past its third term.
- **Chain states also in cores not seeded from failures:**
  - `ranked_n4_4` and `certs_n4_4_x`: n = 5 cores 1121 and 1123 of `k4_certs_5_n4_4`, m = 8, f = 3;
  - `certs_pure`: core 4214.
- **No def > 0 state at all** in the `n6` run.
- **Deficit gap.** The gap is an integer, ≥ 1 wherever DL_RC holds. The smallest least gap at the runs' best profiles is 1, and it is 0 only at the failing profiles.

### Notes on the hunt

- **Big-top bias.** From random starts the climbs reach the known chain states only with a strong big-top bias. In a small experiment (not logged), climbs reached core 2614's chain states at `--bt` = 0.9 but not at 0.5. The `--bt` of each run is on its log's command line:
  - 0.8 to 0.95 for `certs_*`, `*_k3`, `fail10_w2bt`, `shrink_cores_4515` and `core4515`;
  - 0.5 or 0.6 elsewhere.

  The random samples `certs_*_x` used 0.5 and found core 4515, whose failing profile has four big-top agents.
- **n = 6 with one four-good agent is almost vacuous.** The cores of `k4_certs_6_n4_1` have essentially no def > 0 state with f ≥ 1 (`n6_probe.log`):
  - nearly every profile has ω ≤ 0;
  - random profiles across all m give no such state;
  - the 600 n = 6 climbs (4.4 M profiles) met none.
  The n = 6 search that means something is `extend6`, the failing n = 5 cores plus one agent.
- **Gluings.** The glued n = 10 cores keep their chain states (up to 20 per profile, f = 6, least |W| = 1). No climb found a state needing two chain swaps at once.
- **Cut for the time budget.** Two planned batches were not run: `_runs2.sh` and `_runs3.sh` (larger samples with objective w2 / k3). Instead, `_runs_final.sh` and `_runs_extra.sh` ran smaller versions of them, after the failure was found.

## Failures

- **DL_RC (and DL_RT4), core 4604 of `k4_certs_5_pure`:** n = 5, m = 13, f = 1. 369 profiles with one state each. Listing: `rc_failures_n5_all.tsv`; suite form: `rc_failures_n5_all_inst.json`.
- **DL_RC (and DL_RT4), core 4515 of `k4_certs_5_pure`:** n = 5, m = 12, f = 2. 1,076 profiles with 4,304 states. Listing: `rc_failures_4515_all.tsv`; suite form: `rc_failures_4515_all_inst.json`.
- Both are described in `FAILURES.md`. The key form holds at both.
- **Search around them, towards smaller n and m:**
  - deleting goods (m = 10, 11, 12): no failure;
  - every n = 4 core with ≥ 3 four-good agents: no failure;
  - so the smallest known DL_RC failure has n = 5 and m = 12.
- **No other DL_RC failure** in (b), (c), or the rest of the hunt. The two failing cores were found by the ranked hunt (4604) and by the largest random pure-core sample (4515); 4604 was not in that sample.

## Time used

- **Session:** about 22:45 to 03:20 UTC (about 4 h 35 min of wall time), on the container's 4 CPUs. The computing ended at 03:02.
- **(b) validation:** about 3 minutes, plus the later reference checks of found profiles: about 25 minutes, mostly for the 1,076 profiles of core 4515.
- **(c):**
  - `c_purebt`: 42 min wall, 22:57–23:39 (its log reports 2,524 s), sharing the CPUs with the hunt;
  - `c_n4_4`: 23:39–01:24. It was stopped once at the background time limit and resumed, and the hunts were paused (SIGSTOP) from 00:22 to 01:13 so that it could finish on every core rather than every 4th.
- **(d) hunt:** 23:04–03:02 with the pause, 51,644 CPU-s (14.3 CPU-hours, the sum of the CPU s column; inflated by the shared CPUs). It covered 23 runs, 7,484 climbs, 97.4 M profiles evaluated and 136.2 M def > 0 states with f ≥ 1.
- **Not done for the budget:**
  - the w2 / k3 batches at full size (`k4/dlrc_hunt_runs2.sh` and `_runs3.sh` were never run; smaller versions ran);
  - larger n = 6 samples (pointless: no states there);
  - more climbs around core 4515.
