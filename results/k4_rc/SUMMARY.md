# DL_RC on data: summary (compute/k4-rc)

EVIDENCE only. Random and adversarial search proves nothing, and a hunt that finds nothing is no proof either. Every negative claim below about a given input is single-implementation unless a log of `k4/dlrc_ref.py` is named. LEDGER.md is not edited.

## Results

1. **DL_RC is false (EVIDENCE, three implementations).** It fails at n = 5, m = 13, f = 1, in core pos 4604 (idx 58) of `results/k4_certs_5_pure.json.gz`.
   - It fails at 369 profiles, always at the same state P = ({11}, {12}, {3,7}, {4,8}, {5,9}) with def 1.
   - The only improvements of P are role swaps whose helper grows its base by a junk good (distance 3), or that use two helpers (distance 4).
   - At f = 1, R_C = RT4, so this is also a **new DL_RT4 failure at f = 1**.
   - **DL on the key graph holds there:** another state of the same key, with the same deficit, has an improving T3h move.
   - Details are in `FAILURES.md`.
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
4. **The key form never failed:** 0 keys out of every key with def* > 0 evaluated.

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
| later: the 369 DL_RC-failing profiles | `ref_rc_fail_all.log` (+ `ref_rt4_rc_fail_all.log`, dlrt4_ref.py) | 369 | 16,605 | 369 | **369** | 0 |

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
    - after the failure: every n = 4 core with three or four four-good agents (`n4_*`), the cores obtained from core 4604 by deleting one or two goods (`shrink_cores`), and climbs from the failing profiles (`core4604`).

HUNT_TABLE

### Best objective values reached, and where

BEST_VALUES

### Notes on the hunt

- **Big-top bias.** From random starts the climbs reach the known chain states only with a strong big-top bias. In a small experiment (not logged), climbs reached core 2614's chain states at `--bt` = 0.9 but not at 0.5. So the later runs use `--bt` ≥ 0.8, except where stated.
- **n = 6 with one four-good agent is almost vacuous.** The cores of `k4_certs_6_n4_1` have essentially no def > 0 state with f ≥ 1 (`n6_probe.log`):
  - nearly every profile has ω ≤ 0;
  - random profiles across all m give no such state;
  - the 600 n = 6 climbs (4.4 M profiles) met none.
  The n = 6 search that means something is `extend6`, the failing n = 5 cores plus one agent.
- **Gluings.** The glued n = 10 cores keep their chain states (up to 20 per profile, f = 6, least |W| = 1). No climb found a state needing two chain swaps at once.
- **Cut for the time budget.** Two planned batches were not run: `_runs2.sh` and `_runs3.sh` (larger samples with objective w2 / k3). Instead, `_runs_final.sh` and `_runs_extra.sh` ran smaller versions of them, after the failure was found.

## Failures

- **DL_RC (and DL_RT4) at n = 5, m = 13, f = 1:** core 4604 of `k4_certs_5_pure`, 369 profiles, one state each. See `FAILURES.md` (with `rc_failures_n5_all.tsv`, and `rc_failures_n5_all_inst.json` in `k4/suite/instances` form). The key form holds there.
- **No other DL_RC failure** in (b), (c), or the rest of the hunt.

## Time used

TIME_USED
