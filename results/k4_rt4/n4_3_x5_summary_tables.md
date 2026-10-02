<!-- command: python3 k4/dlrt4_summary.py "n4_3_x5 (cores 228..259)=results/k4_rt4/tables_n4_3_x5.json=results/k4_rt4/n4_3_x5.log" "n4_3_x5_split (cores 260..284)=results/k4_rt4/tables_n4_3_x5_split.json=results/k4_rt4/n4_3_x5_split.log" "slice 228..284 (both)=results/k4_rt4/tables_n4_3_x5_all.json=/dev/null" -->

# n4_3_x5: tables (made by k4/dlrt4_summary.py; command above)

The time column is what dlrt4_summary.py reads from the logs' report lines: the main run's final report read every unit from the checkpoint (0 s), and the merged row has no log. Wall and process times are in n4_3_x5_SUMMARY.md.

### 1. Counts

| run | profiles | f >= 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails | R_13 + T4 fails | time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| n4_3_x5 (cores 228..259) | 3,045,703,680 | 11,589,592 | **0** | 0 (0) | 0 | 0 | 0 | 0 s |
| n4_3_x5_split (cores 260..284) | 1,379,524,608 | 16,563,464 | **0** | 0 (0) | 0 | 0 | 0 | 347.9 min |
| slice 228..284 (both) | 4,425,228,288 | 28,153,056 | **0** | 0 (0) | 0 | 0 | 0 | 0 s |

### 2. Repair branches (f >= 1 states)

"with": an improving move of that branch exists; "only": it is the only branch with one (T3 = T3p or T3h). Smallest move size: the least number of agents changed by an improving RT4 move.

| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / >= 4 | anomalies |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|
| n4_3_x5 (cores 228..259) | 11,090,112 | 10,953,480 | 8,275,064 | 11,115,836 | 763,840 | 0 | 0 | 330,840 | 0 | 11,090,112 / 499,480 / 0 / 0 | 0 |
| n4_3_x5_split (cores 260..284) | 15,613,364 | 15,219,472 | 15,422,184 | 16,169,916 | 1,326,800 | 0 | 0 | 435,316 | 0 | 15,613,364 / 950,100 / 0 / 0 | 0 |
| slice 228..284 (both) | 26,703,476 | 26,172,952 | 23,697,248 | 27,285,752 | 2,090,640 | 0 | 0 | 766,156 | 0 | 26,703,476 / 1,449,580 / 0 / 0 | 0 |

### 3. T4 cycle types (f >= 1 states with an improving T4 move)

"least size: cycle types": the states by the least |ch| of an improving T4 move and the cycle types of the improving T4 moves of that size; "available": the states with an improving T4 move of each cycle type; "T4 needed": the states at which T4 is the only branch, by their least T4 size and cycle types.

| run | states with T4 | least size: cycle types | available | T4 needed |
|---|---:|---|---|---|
| n4_3_x5 (cores 228..259) | 763,840 | 2: 2 (763,840) | 2: 763,840 | - |
| n4_3_x5_split (cores 260..284) | 1,326,800 | 2: 2 (1,326,800) | 2: 1,326,800 | - |
| slice 228..284 (both) | 2,090,640 | 2: 2 (2,090,640) | 2: 2,090,640 | - |

### 4. Branch combinations (f >= 1 states: f, branches with an improving move: smallest RT4 move size: states)

| run | f, branch combination: smallest size: states |
|---|---|
| n4_3_x5 (cores 228..259) | f = 1, T1+T2+T3p+T3h: 1: 5,286,896; f = 1, T1+T2+T3h: 1: 2,997,600; f = 2, T1+T2+T3p+T3h: 1: 1,628,468; f = 2, T1+T2+T3p+T3h+T4: 1: 579,740; f = 1, T1+T2: 1: 283,040; f = 2, T3p+T3h: 2: 162,980; f = 2, T3p+T3h+T4: 2: 142,160; f = 1, T3p+T3h: 2: 121,040; f = 1, T1+T2+T3p: 1: 112,592; f = 2, T1+T3p+T3h: 1: 112,120; f = 2, T3p: 2: 44,820; f = 1, T1+T3p+T3h: 1: 29,312; f = 2, T1+T2+T3h+T4: 1: 16,640; f = 2, T1+T2+T3h: 1: 15,696; f = 1, T2+T3p+T3h: 2: 12,272; f = 2, T3p+T4: 2: 11,680; f = 2, T1+T2+T3p: 1: 11,348; f = 2, T1+T3p+T3h+T4: 1: 6,960; f = 2, T1+T2+T3p+T4: 1: 6,660; f = 2, T2+T3p+T3h: 2: 2,400; f = 1, T3p: 2: 2,000; f = 1, T1+T3p: 1: 1,264; f = 1, T1+T3h: 1: 864; f = 2, T1+T3h: 1: 560; f = 2, T1+T3p: 1: 352; f = 1, T2+T3h: 2: 128 |
| n4_3_x5_split (cores 260..284) | f = 1, T1+T2+T3p+T3h: 1: 11,402,288; f = 2, T1+T2+T3p+T3h: 1: 1,723,400; f = 1, T1+T2+T3h: 1: 1,061,264; f = 2, T1+T2+T3p+T3h+T4: 1: 820,120; f = 2, T3p+T3h+T4: 2: 333,540; f = 2, T3p+T3h: 2: 287,056; f = 2, T1+T3p+T3h: 1: 197,420; f = 1, T1+T3p+T3h: 1: 183,184; f = 2, T3p: 2: 120,580; f = 2, T3p+T4: 2: 113,300; f = 1, T1+T2: 1: 69,936; f = 1, T2+T3p+T3h: 2: 67,944; f = 1, T1+T2+T3p: 1: 65,328; f = 2, T1+T3p+T3h+T4: 1: 55,940; f = 1, T3p+T3h: 2: 27,680; f = 1, T1+T3p: 1: 21,600; f = 2, T1+T2+T3h: 1: 5,688; f = 2, T1+T2+T3h+T4: 1: 2,240; f = 1, T1+T3h: 1: 1,600; f = 2, T1+T3p+T4: 1: 1,100; f = 2, T1+T2+T3p: 1: 704; f = 2, T1+T2+T3p+T4: 1: 560; f = 2, T1+T3h: 1: 552; f = 2, T1+T3p: 1: 440 |
| slice 228..284 (both) | f = 1, T1+T2+T3p+T3h: 1: 16,689,184; f = 1, T1+T2+T3h: 1: 4,058,864; f = 2, T1+T2+T3p+T3h: 1: 3,351,868; f = 2, T1+T2+T3p+T3h+T4: 1: 1,399,860; f = 2, T3p+T3h+T4: 2: 475,700; f = 2, T3p+T3h: 2: 450,036; f = 1, T1+T2: 1: 352,976; f = 2, T1+T3p+T3h: 1: 309,540; f = 1, T1+T3p+T3h: 1: 212,496; f = 1, T1+T2+T3p: 1: 177,920; f = 2, T3p: 2: 165,400; f = 1, T3p+T3h: 2: 148,720; f = 2, T3p+T4: 2: 124,980; f = 1, T2+T3p+T3h: 2: 80,216; f = 2, T1+T3p+T3h+T4: 1: 62,900; f = 1, T1+T3p: 1: 22,864; f = 2, T1+T2+T3h: 1: 21,384; f = 2, T1+T2+T3h+T4: 1: 18,880; f = 2, T1+T2+T3p: 1: 12,052; f = 2, T1+T2+T3p+T4: 1: 7,220; f = 1, T1+T3h: 1: 2,464; f = 2, T2+T3p+T3h: 2: 2,400; f = 1, T3p: 2: 2,000; f = 2, T1+T3h: 1: 1,112; f = 2, T1+T3p+T4: 1: 1,100; f = 2, T1+T3p: 1: 792; f = 1, T2+T3h: 2: 128 |
