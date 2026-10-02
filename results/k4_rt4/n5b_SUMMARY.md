# DL_RT4 on the n = 5 cores with three or four 4-good agents (compute/k4-rt4-n5b): summary

EVIDENCE (random sampling; not a ledger change). Tool: `k4/dlrt4.c` sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`
(unchanged), driven by `k4/dlrt4_run.py`, on branch `compute/k4-rt4-n5b` (from `compute/k4-rt4` at 2e9adeb). Conjecture DL_RT4: at f ≥ 1, every
min-frozen P with def(P) > 0 has a min-frozen neighbour P′ with def(P′) < def(P) under RT4 = T1 ∪ T2 ∪ T3 ∪ T4 (`k4/dlrt4.c`'s header,
`k4/dl2.md` §3, `results/k4_dl13/n4_FAILURES.md`).

## Result

- **DL_RT4 fails** at **39** f ≥ 1 states (7 profiles, 4 cores), all on the cores with four 4-good agents (`k4_certs_5_n4_4`): 3 in run
  n5b_4 (cores pos 3206 and 3521, m = 9) and 36 in run n5b_4bt (big-top profiles, cores pos 9004 and 9495, m = 11 and 12). Every failing
  state is confirmed by the Python reference `k4/dlrt4_ref.py` (39 failures, 0 mismatches on the 102 states of the 7 profiles) and listed,
  with its shape, in **`n5b_FAILURES.md`**.
- All 39 have f = 3, def(P) = 1, no better state within distance 2, and every nearest better state (374 of them, at distance 3) is reached by
  **a chain of frozen goods through one frozen intermediary**: x frozen → free gives its good to w, which stays frozen and passes its own
  good to z, free → frozen; NA unchanged (|U| = |Z| = |W| = 1, Y = ∅). That move is neither T3 (z would take x's good, with no W) nor T4
  (every changed agent stays frozen); among `k4/dl2_relations.py`'s relations only RC and R3 contain it.
- No failure on the cores with three 4-good agents (`k4_certs_5_n4_3`, runs n5b_3 and n5b_3bt: 828,445 f ≥ 1 states).
- At f = 0, RT4 never fails (6,285,114 states with def > 0).
- R_13 + T4 fails exactly at the 39 failures plus one state of n5b_4 that only T2 repairs (f = 1, a 2-agent rotation).

Other observations (DL_RT4 holds at all of these):
- States that need T4: 8 / 8 / 11 / 200; in n5b_4bt, 12 of them (f = 4) need a T4 move of size 3 (a 3-cycle), the rest size 2.
- States that only T1 repairs: 43, all in n5b_4bt at f = 2 (none in the other runs).
- States whose nearest better state is at distance 3: 0 / 4 / 4 / 150. Besides the 39 failures they are repaired by a 3-agent T3h move
  (4 in n5b_3bt; 1 in n5b_4; 102 in n5b_4bt, 10 of which also have a 3-agent T2 move) or, in n5b_4bt, by a 3-agent T4 move (the 12 above).
  The two n5b_3bt examples in the dump: f = 3, signature G,O,D2, cores pos 7967 (m = 10) and 9483 (m = 11) of `k4_certs_5_n4_3`.
- No anomalies in any run (dlrt4.c's counters of cases its lemmas exclude: a T1 move with a frozen agent, a T4 candidate that is not a
  permutation).

## Slice, P and time

| run | tag | file | options | cores | profiles per core |
|---|---|---|---|---:|---:|
| 1 | n5b_3 | `results/k4_certs_5_n4_3.json.gz` | `--seed=1` | 9,861 | 16,000 |
| 2 | n5b_3bt | `results/k4_certs_5_n4_3.json.gz` | `--bt=all --seed=2` | 9,861 | 16,000 |
| 3 | n5b_4 | `results/k4_certs_5_n4_4.json.gz` | `--seed=1` | 9,846 | 16,000 |
| 4 | n5b_4bt | `results/k4_certs_5_n4_4.json.gz` | `--bt=all --seed=2` | 9,846 | 16,000 |

Each run: `python3 k4/dlrt4_run.py certs FILE --sample=16000 --seed=S [--bt=all] --jobs=4 --ckpt=results/k4_rt4/ckpt_<tag>.jsonl
--dump=results/k4_rt4/dump_<tag>.jsonl.gz --tables=results/k4_rt4/tables_<tag>.json --progress`, log `results/k4_rt4/<tag>.log` (its first
line is the command). 4 CPUs.

**Choice of P.** Timed first on random core samples (P = 5000, per-core means weighted by the m distribution of each file; the cost is
dominated by the cores with m ≥ 11: about 0.02–0.5 s per core at m = 7–10, 1.2–1.8 s at m = 11, 6–9 s at m = 13): 7.1 / 8.2 / 19.3 / 19.9 min per run at P = 5000 (400-, 400-, 400- and
300-core samples; smaller 80-core samples gave 11.2 / 11.2 / 29.5 / 25.7 min), linear in P (a P = 20,000 check on 200 cores of
`k4_certs_5_n4_4`: 82.8 min). P = 16,000 was chosen for an estimated 3.1 h (up to 3.8 h on the 80-core estimates).
**Actual time: 21.2 + 23.8 + about 59 + 57.0 min ≈ 2.7 h**, a little under the 3-hour target.

¹ Run n5b_4 was killed by a container restart at about 23:02 UTC, 27 units before its end (22:07:36 to about 23:02, no report line), and
resumed from its checkpoint (251 s, the only "[N s]" in its log). Before resuming, the checkpoint was checked to end in a complete line and
the dump to consist of complete gzip members, all of units in the checkpoint, so no unit is counted twice or lost. The units' own times sum
to 14,108 s (3,527 s on 4 CPUs). The other runs ran in one invocation each.

## Files (`results/k4_rt4/`)

- `n5b_<run>.log`, `tables_n5b_<run>.json` (merged counters and tables), `ckpt_n5b_<run>.jsonl` (one line per core),
  `dump_n5b_<run>.jsonl.gz` (dlrt4.c's "D" records: every failing f ≥ 1 state with its better states, the first f ≥ 1 state of each
  (signature, branch) cell per core, every 50th state that needs a branch outside R_13), for the runs 3, 3bt, 4, 4bt.
- `n5b_FAILURES.md`: the 39 failing states, the shape of their nearest better states, the confirmation.
- `n5b_failures.tsv` (one line per failing state), `n5b_failures_inst.json` (the 7 failing profiles as an inst list),
  `n5b_failures_shapes.log` (`k4/dlrt4_failures.py`: every failing state recomputed with `k4/suite/model.py`, its better states, the shape of each
  nearest move), `ref_n5b_failures.log` (`k4/dlrt4_ref.py inst` on the 7 profiles).
- `k4/dlrt4_failures.py` (new): reads the failures from dumps (complete gzip members only), writes the TSV and the inst list, and prints the
  shapes. No existing file was modified.

## Tables (`k4/dlrt4_summary.py` on the four tables JSON and logs; the n5b_4 time corrected as in ¹)

#### 1. Counts

| run | profiles | f >= 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails | R_13 + T4 fails | time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| n5b_3 | 157,776,000 | 196,600 | **0** | 442,508 (0) | 8 | 8 | 0 | 21.2 min |
| n5b_3bt | 157,776,000 | 631,845 | **0** | 0 (0) | 8 | 8 | 0 | 23.8 min |
| n5b_4 | 157,536,000 | 1,122,391 | **3** | 5,842,606 (0) | 16 | 14 | 4 | ≈ 59 min ¹ |
| n5b_4bt | 157,536,000 | 3,576,725 | **36** | 0 (0) | 236 | 236 | 36 | 57.0 min |

#### 2. Repair branches (f >= 1 states)

"with": an improving move of that branch exists; "only": it is the only branch with one (T3 = T3p or T3h). Smallest move size: the least number of agents changed by an improving RT4 move.

| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / >= 4 | anomalies |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|
| n5b_3 | 194,030 | 192,593 | 159,931 | 188,918 | 10,105 | 0 | 0 | 1,805 | 8 | 194,030 / 2,570 / 0 / 0 | 0 |
| n5b_3bt | 622,990 | 618,984 | 620,539 | 628,842 | 44,708 | 0 | 0 | 5,009 | 8 | 622,990 / 8,851 / 4 / 0 | 0 |
| n5b_4 | 1,113,864 | 1,114,443 | 935,759 | 1,084,004 | 45,591 | 0 | 1 | 3,293 | 11 | 1,113,864 / 8,523 / 1 / 0 | 0 |
| n5b_4bt | 3,533,591 | 3,531,071 | 3,516,033 | 3,547,581 | 209,673 | 43 | 0 | 20,449 | 200 | 3,533,591 / 42,984 / 114 / 0 | 0 |

#### 3. T4 cycle types (f >= 1 states with an improving T4 move)

"least size: cycle types": the states by the least |ch| of an improving T4 move and the cycle types of the improving T4 moves of that size; "available": the states with an improving T4 move of each cycle type; "T4 needed": the states at which T4 is the only branch, by their least T4 size and cycle types.

| run | states with T4 | least size: cycle types | available | T4 needed |
|---|---:|---|---|---|
| n5b_3 | 10,105 | 2: 2 (9,751), 3: 3 (354) | 2: 9,751, 3: 1,923, 4: 16, 2+2: 12 | 8 states; size 2: 8; cycle types available: 2: 8, 3: 8 |
| n5b_3bt | 44,708 | 2: 2 (43,015), 3: 3 (1,693) | 2: 43,015, 3: 8,237, 4: 12, 2+2: 8 | 8 states; size 2: 8; cycle types available: 2: 8, 3: 8 |
| n5b_4 | 45,591 | 2: 2 (44,877), 3: 3 (714) | 2: 44,877, 3: 2,447, 4: 62, 2+2: 40 | 11 states; size 2: 11; cycle types available: 2: 11, 3: 11, 4: 4, 2+2: 2 |
| n5b_4bt | 209,673 | 2: 2 (205,866), 3: 3 (3,807) | 2: 205,866, 3: 12,574, 4: 108, 2+2: 60 | 200 states; size 2: 188, size 3: 12; cycle types available: 2: 188, 3: 110, 4: 36, 2+2: 24 |

#### 4. Branch combinations (f >= 1 states: f, branches with an improving move: smallest RT4 move size: states)

| run | f, branch combination: smallest size: states |
|---|---|
| n5b_3 | f = 1, T1+T2+T3p+T3h: 1: 97,932; f = 2, T1+T2+T3p+T3h: 1: 45,583; f = 1, T1+T2+T3h: 1: 24,555; f = 2, T1+T2+T3p+T3h+T4: 1: 6,720; f = 2, T1+T2+T3h: 1: 6,017; f = 1, T1+T2: 1: 5,527; f = 3, T1+T2+T3p+T3h: 1: 2,540; f = 3, T1+T2+T3p+T3h+T4: 1: 2,199; f = 2, T1+T3p+T3h: 1: 747; f = 3, T3p: 2: 727; f = 2, T3p+T3h: 2: 582; f = 3, T3p+T3h: 2: 445; f = 3, T1+T3p+T3h: 1: 385; f = 1, T1+T2+T3p: 1: 382; f = 2, T1+T2: 1: 381; f = 3, T1+T3p+T3h+T4: 1: 351; f = 3, T3p+T4: 2: 238; f = 1, T1+T3p+T3h: 1: 202; f = 2, T1+T2+T3p: 1: 165; f = 3, T3p+T3h+T4: 2: 163; f = 2, T1+T2+T3h+T4: 1: 139; f = 1, T2+T3p+T3h: 2: 106; f = 2, T1+T2+T3p+T4: 1: 91; f = 2, T2+T3p+T3h: 2: 90; f = 2, T1+T3p+T3h+T4: 1: 63; f = 2, T3p: 2: 46; f = 1, T2+T3p: 2: 42; f = 2, T2+T3p+T3h+T4: 2: 42; f = 4, T3p+T4: 2: 28; f = 3, T1+T2+T3h+T4: 1: 27; f = 2, T2+T3p: 2: 18; f = 2, T2+T3p+T4: 2: 17; f = 3, T1+T2+T3h: 1: 9; f = 3, T2+T3p+T3h: 2: 8; f = 4, T4: 2: 8; f = 3, T1+T3p+T4: 1: 7; f = 2, T3p+T3h+T4: 2: 5; f = 1, T3p+T3h: 2: 4; f = 3, T1+T3h+T4: 1: 4; f = 2, T1+T2+T4: 1: 2; f = 1, T3p: 2: 1; f = 3, T1+T2+T3p+T4: 1: 1; f = 3, T1+T3p: 1: 1 |
| n5b_3bt | f = 1, T1+T2+T3p+T3h: 1: 333,448; f = 2, T1+T2+T3p+T3h: 1: 211,878; f = 2, T1+T2+T3p+T3h+T4: 1: 30,185; f = 3, T1+T2+T3p+T3h: 1: 21,138; f = 2, T1+T2+T3h: 1: 10,066; f = 3, T1+T2+T3p+T3h+T4: 1: 9,774; f = 3, T3p+T3h: 2: 2,942; f = 3, T1+T3p+T3h: 1: 2,356; f = 3, T3p+T3h+T4: 2: 1,994; f = 3, T1+T3p+T3h+T4: 1: 1,269; f = 2, T3p+T3h: 2: 1,170; f = 2, T1+T2: 1: 1,156; f = 3, T3p: 2: 893; f = 2, T2+T3p+T3h: 2: 690; f = 1, T1+T3p+T3h: 1: 631; f = 3, T3p+T4: 2: 628; f = 2, T1+T3p+T3h: 1: 515; f = 2, T2+T3p+T3h+T4: 2: 386; f = 2, T1+T3p+T3h+T4: 1: 224; f = 2, T1+T2+T3p: 1: 177; f = 2, T3p+T3h+T4: 2: 102; f = 2, T1+T2+T3p+T4: 1: 50; f = 4, T3p+T4: 2: 34; f = 3, T1+T3h: 1: 28; f = 3, T1+T3h+T4: 1: 24; f = 1, T1+T2+T3p: 1: 20; f = 3, T1+T3p+T4: 1: 17; f = 3, T1+T3p: 1: 10; f = 4, T4: 2: 8; f = 2, T1+T3h: 1: 6; f = 3, T1+T2+T3h: 1: 6; f = 3, T1+T2+T3p+T4: 1: 4; f = 3, T3h: 3: 4; f = 3, T1+T2+T3h+T4: 1: 3; f = 3, T3h+T4: 2: 3; f = 2, T1+T3p: 1: 2; f = 2, T2+T3p+T4: 2: 1; f = 3, T1+T2+T3p: 1: 1; f = 3, T1+T2+T4: 1: 1; f = 3, T1+T4: 1: 1 |
| n5b_4 | f = 1, T1+T2+T3p+T3h: 1: 721,513; f = 2, T1+T2+T3p+T3h: 1: 155,626; f = 1, T1+T2+T3h: 1: 139,961; f = 2, T1+T2+T3p+T3h+T4: 1: 38,293; f = 1, T1+T2: 1: 34,118; f = 2, T1+T2+T3h: 1: 10,232; f = 3, T1+T2+T3p+T3h: 1: 3,558; f = 3, T1+T2+T3p+T3h+T4: 1: 3,224; f = 1, T2+T3p+T3h: 2: 3,056; f = 2, T3p+T3h: 2: 1,331; f = 2, T1+T2+T3h+T4: 1: 1,321; f = 1, T1+T3p+T3h: 1: 1,172; f = 1, T1+T2+T3p: 1: 1,142; f = 3, T3p: 2: 1,056; f = 2, T1+T3p+T3h: 1: 849; f = 2, T1+T2: 1: 837; f = 3, T3p+T3h: 2: 670; f = 3, T1+T3p+T3h: 1: 582; f = 3, T1+T3p+T3h+T4: 1: 545; f = 2, T2+T3p+T3h+T4: 2: 419; f = 3, T3p+T3h+T4: 2: 414; f = 2, T2+T3p+T3h: 2: 388; f = 3, T3p+T4: 2: 349; f = 2, T1+T3p+T3h+T4: 1: 348; f = 2, T3p+T3h+T4: 2: 230; f = 2, T1+T2+T3p: 1: 214; f = 2, T1+T2+T3p+T4: 1: 171; f = 1, T3p+T3h: 2: 134; f = 1, T2+T3p: 2: 96; f = 4, T3p+T4: 2: 84; f = 2, T3p: 2: 81; f = 2, T2+T3p+T4: 2: 74; f = 2, T2+T3p: 2: 72; f = 3, T1+T2+T3h+T4: 1: 41; f = 3, T1+T3h+T4: 1: 26; f = 2, T1+T2+T4: 1: 21; f = 3, T1+T2+T3h: 1: 19; f = 3, T2+T3p+T3h: 2: 15; f = 1, T2+T3h: 2: 13; f = 1, T3p: 2: 10; f = 3, T1+T3h: 1: 10; f = 4, T3p: 2: 10; f = 1, T1+T3p: 1: 9; f = 3, T1+T3p+T4: 1: 7; f = 3, T4: 2: 7; f = 2, T1+T3h: 1: 6; f = 3, T1+T2+T3p+T4: 1: 5; f = 3, T1+T2+T3p: 1: 5; f = 4, T4: 2: 4; f = 2, T1+T3p: 1: 3; f = 2, T2+T3h: 2: 3; f = 3, none: -1: 3; f = 1, T1+T3h: 1: 2; f = 2, T3p+T4: 2: 2; f = 1, T2: 2: 1; f = 2, T1+T4: 1: 1; f = 2, T2+T3h+T4: 2: 1; f = 2, T2+T4: 2: 1; f = 3, T1+T2+T4: 1: 1; f = 3, T1+T3p: 1: 1; f = 3, T1+T4: 1: 1; f = 3, T2+T3h+T4: 2: 1; f = 3, T2+T3p: 2: 1; f = 3, T3h: 3: 1 |
| n5b_4bt | f = 2, T1+T2+T3p+T3h: 1: 1,891,449; f = 1, T1+T2+T3p+T3h: 1: 1,314,635; f = 2, T1+T2+T3p+T3h+T4: 1: 173,422; f = 3, T1+T2+T3p+T3h: 1: 57,526; f = 2, T1+T2+T3h: 1: 34,036; f = 2, T1+T2: 1: 24,716; f = 3, T1+T2+T3p+T3h+T4: 1: 20,398; f = 2, T2+T3p+T3h: 2: 10,733; f = 2, T3p+T3h: 2: 10,642; f = 3, T3p+T3h: 2: 7,655; f = 2, T1+T3p+T3h: 1: 7,160; f = 3, T1+T3p+T3h: 1: 4,400; f = 3, T3p+T3h+T4: 2: 4,335; f = 2, T3p+T3h+T4: 2: 3,661; f = 3, T1+T3p+T3h+T4: 1: 2,430; f = 2, T2+T3p+T3h+T4: 2: 2,186; f = 3, T3p: 2: 2,042; f = 2, T1+T3p+T3h+T4: 1: 1,191; f = 3, T3p+T4: 2: 1,137; f = 1, T1+T2+T3h: 1: 733; f = 2, T1+T2+T3p: 1: 261; f = 1, T1+T3p+T3h: 1: 198; f = 3, T4: 2: 164; f = 3, T1+T2+T3h+T4: 1: 162; f = 2, T2+T3h: 2: 159; f = 3, T1+T2+T3h: 1: 156; f = 4, T3p+T4: 2: 124; f = 3, T1+T2+T3p+T4: 1: 122; f = 3, T1+T2+T4: 1: 109; f = 3, T1+T2+T3p: 1: 98; f = 2, T1+T3h: 1: 78; f = 3, T3h: 3: 60; f = 3, T1+T3p+T4: 1: 54; f = 3, T1+T2: 1: 52; f = 2, T1: 1: 43; f = 3, T1+T3h+T4: 1: 36; f = 3, none: -1: 36; f = 2, T1+T2+T3p+T4: 1: 32; f = 2, T3h: 3: 32; f = 2, T2+T3p: 2: 31; f = 3, T1+T3h: 1: 30; f = 3, T1+T3p: 1: 30; f = 3, T3h+T4: 2: 27; f = 4, T4: 2: 24; f = 2, T1+T3p: 1: 22; f = 3, T2+T3p+T3h+T4: 2: 17; f = 4, T4: 3: 12; f = 2, T2+T3h: 3: 10; f = 3, T2+T3p+T3h: 2: 10; f = 4, T3p: 2: 10; f = 2, T3p+T4: 2: 8; f = 2, T3p: 2: 8; f = 3, T2+T3h+T4: 2: 8; f = 2, T1+T2+T3h+T4: 1: 5; f = 2, T1+T3p+T4: 1: 4; f = 2, T1+T2+T4: 1: 2; f = 2, T2+T3p+T4: 2: 2; f = 3, T1+T4: 1: 1; f = 3, T2+T3h: 2: 1 |

## What this shows and what remains open

- The 39 failures are exact: each is a specific (core, profile, state), recomputed by two independent implementations (dlrt4.c and the
  reference on model.py), so DL_RT4 as stated **has counterexamples** (n = 5, four 4-good agents, f = 3). The zero-failure counts on
  `k4_certs_5_n4_3` are sampling evidence only (16,000 random profiles per core).
- Every nearest repair at the failures is the chain move x → w → z through one frozen intermediary. Whether RT4 plus that chain (|U| = |Z| =
  |W| = 1, Y = ∅, NA kept) always suffices at f ≥ 1, and whether chains with more intermediaries appear for larger n or m, is open; the dumps
  and `k4/dlrt4_failures.py` give the data to test such an extension.
- The failures cluster: 4 cores, and at pos 9495 four profiles with 31 failing states. These cores have 5 · 10⁹ to 2 · 10¹⁰ strict profiles
  each (the products of their domain sizes in the certificate), too many to enumerate here; a much larger sample of just them (`--cores=A:B` with a large P) would show how common the pattern is there. Not done
  here.
- LEDGER.md is not edited (the slice's instructions); the coordinator decides how to record this.
