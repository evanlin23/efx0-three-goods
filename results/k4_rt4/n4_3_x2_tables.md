<!-- command: python3 k4/dlrt4_summary.py "n4_3 cores 57..113, every profile=results/k4_rt4/tables_n4_3_x2.json=results/k4_rt4/n4_3_x2.log" -->

# DL_RT4 run n4_3_x2: full tables (compute/k4-rt4)

### 1. Counts

| run | profiles | f >= 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails | R_13 + T4 fails | time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| n4_3 cores 57..113, every profile | 7,453,016,064 | 4,326,264 | **0** | 0 (0) | 42,240 | 42,240 | 0 | 51.1 min |

### 2. Repair branches (f >= 1 states)

"with": an improving move of that branch exists; "only": it is the only branch with one (T3 = T3p or T3h). Smallest move size: the least number of agents changed by an improving RT4 move.

| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / >= 4 | anomalies |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|
| n4_3 cores 57..113, every profile | 2,845,594 | 1,963,210 | 3,921,016 | 3,268,024 | 1,921,980 | 0 | 0 | 818,510 | 42,240 | 2,845,594 / 1,480,670 / 0 / 0 | 0 |

### 3. T4 cycle types (f >= 1 states with an improving T4 move)

"least size: cycle types": the states by the least |ch| of an improving T4 move and the cycle types of the improving T4 moves of that size; "available": the states with an improving T4 move of each cycle type; "T4 needed": the states at which T4 is the only branch, by their least T4 size and cycle types.

| run | states with T4 | least size: cycle types | available | T4 needed |
|---|---:|---|---|---|
| n4_3 cores 57..113, every profile | 1,921,980 | 2: 2 (1,889,340), 3: 3 (32,640) | 2: 1,889,340, 3: 401,280 | 42,240 states; size 2: 42,240; cycle types available: 2: 42,240, 3: 42,240 |

### 4. Branch combinations (f >= 1 states: f, branches with an improving move: smallest RT4 move size: states)

| run | f, branch combination: smallest size: states |
|---|---|
| n4_3 cores 57..113, every profile | f = 2, T1+T2+T3p+T3h: 1: 998,878; f = 2, T1+T2+T3p+T3h+T4: 1: 575,020; f = 3, T3p+T4: 2: 456,960; f = 2, T1+T3p+T3h+T4: 1: 436,170; f = 2, T1+T3p+T3h: 1: 424,374; f = 2, T3p+T3h: 2: 331,604; f = 2, T3p: 2: 260,538; f = 3, T3p: 2: 226,368; f = 2, T1+T2+T3h+T4: 1: 151,760; f = 2, T1+T3h+T4: 1: 100,290; f = 2, T1+T2+T3h: 1: 87,848; f = 2, T3p+T3h+T4: 2: 56,880; f = 2, T2+T3p+T3h+T4: 2: 44,800; f = 3, T4: 2: 42,240; f = 2, T2+T3p+T3h: 2: 37,440; f = 2, T1+T2+T3p+T4: 1: 29,680; f = 2, T1+T2+T3p: 1: 19,864; f = 2, T1+T3p+T4: 1: 12,510; f = 2, T2+T3h+T4: 2: 9,600; f = 2, T1+T3p: 1: 6,970; f = 2, T3h+T4: 2: 5,920; f = 2, T2+T3h: 2: 5,360; f = 2, T2+T3p: 2: 2,960; f = 2, T1+T3h: 1: 2,080; f = 2, T1+T4: 1: 150 |
