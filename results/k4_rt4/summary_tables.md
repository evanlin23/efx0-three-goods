<!-- command: python3 k4/dlrt4_summary.py "@(a) the DL13 failures and dl13-n4m9-rot" "(a) 1,131 profiles of the 3,062 DL13 failures=results/k4_rt4/tables_a_failures.json=results/k4_rt4/a_dl13_failures.log" "(a) dl13-n4m9-rot, dl13-n4m6-fswap (suite)=results/k4_rt4/tables_a_suite2.json=results/k4_rt4/a_suite2.log" "(a) neighbourhood of dl13-n4m9-rot (radius 2)=results/k4_rt4/tables_a_nbhd123.json=results/k4_rt4/a_nbhd123.log" "@(b), (c) exhaustive" "(b) n4_1, every profile=results/k4_rt4/tables_b_n4_1.json=results/k4_rt4/b_n4_1.log" "(c) n4_2, every profile=results/k4_rt4/tables_c_n4_2.json=results/k4_rt4/c_n4_2.log" "@(d) pure" "(d) pure, 500/core, seed 1=results/k4_rt4/tables_d_pure_s500_1.json=results/k4_rt4/d_pure_s500_1.log" "(d) pure, 500/core, seed 2=results/k4_rt4/tables_d_pure_s500_2.json=results/k4_rt4/d_pure_s500_2.log" "(d) pure, 500/core, seed 3=results/k4_rt4/tables_d_pure_s500_3.json=results/k4_rt4/d_pure_s500_3.log" "(d) #53's gap_n4_pure_s4000=results/k4_rt4/tables_d_cat_gap_n4_pure_s4000.json=results/k4_rt4/d_cat_gap_n4_pure_s4000.log" "@(e) three 4-good agents" "(e) n4_3, 500/core, seed 1=results/k4_rt4/tables_e_n4_3_s500_1.json=results/k4_rt4/e_n4_3_s500_1.log" "(e) n4_3, 500/core, seed 2=results/k4_rt4/tables_e_n4_3_s500_2.json=results/k4_rt4/e_n4_3_s500_2.log" "(e) n4_3, 500/core, seed 3=results/k4_rt4/tables_e_n4_3_s500_3.json=results/k4_rt4/e_n4_3_s500_3.log" -->

# DL_RT4 runs: full tables (compute/k4-rt4)

### 1. Counts

| run | profiles | f >= 1 states (def > 0) | **DL_RT4 fails** | f = 0 states (RT4 fails) | R_13 fails | R_T fails | R_13 + T4 fails | time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| *(a) the DL13 failures and dl13-n4m9-rot* | | | | | | | | |
| (a) 1,131 profiles of the 3,062 DL13 failures | 1,131 | 7,586 | **0** | 0 (0) | 3,062 | 3,062 | 0 | 1 s |
| (a) dl13-n4m9-rot, dl13-n4m6-fswap (suite) | 2 | 7 | **0** | 0 (0) | 3 | 2 | 1 | 0 s |
| (a) neighbourhood of dl13-n4m9-rot (radius 2) | 371,235 | 59,439 | **0** | 0 (0) | 3,971 | 0 | 3,971 | 15 s |
| *(b), (c) exhaustive* | | | | | | | | |
| (b) n4_1, every profile | 7,247,232 | 286 | **0** | 0 (0) | 20 | 20 | 0 | 4 s |
| (c) n4_2, every profile | 724,847,616 | 324,658 | **0** | 0 (0) | 3,040 | 3,040 | 0 | 15.5 min |
| *(d) pure* | | | | | | | | |
| (d) pure, 500/core, seed 1 | 109,500 | 3,141 | **0** | 42,953 (0) | 0 | 0 | 0 | 3 s |
| (d) pure, 500/core, seed 2 | 109,500 | 3,111 | **0** | 44,058 (0) | 2 | 2 | 0 | 3 s |
| (d) pure, 500/core, seed 3 | 109,500 | 3,529 | **0** | 42,384 (0) | 0 | 0 | 0 | 3 s |
| (d) #53's gap_n4_pure_s4000 | 45,101 | 25,018 | **0** | 0 (0) | 1 | 0 | 1 | 4 s |
| *(e) three 4-good agents* | | | | | | | | |
| (e) n4_3, 500/core, seed 1 | 169,500 | 1,110 | **0** | 5,694 (0) | 0 | 0 | 0 | 2 s |
| (e) n4_3, 500/core, seed 2 | 169,500 | 1,047 | **0** | 5,494 (0) | 2 | 2 | 0 | 2 s |
| (e) n4_3, 500/core, seed 3 | 169,500 | 1,037 | **0** | 5,824 (0) | 2 | 2 | 0 | 2 s |

### 2. Repair branches (f >= 1 states)

"with": an improving move of that branch exists; "only": it is the only branch with one (T3 = T3p or T3h). Smallest move size: the least number of agents changed by an improving RT4 move.

| run | T1 | T2 | T3p | T3h | T4 | only T1 | only T2 | only T3 | only T4 | smallest size 1 / 2 / 3 / >= 4 | anomalies |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|
| (a) 1,131 profiles of the 3,062 DL13 failures | 0 | 0 | 4,524 | 0 | 7,586 | 0 | 0 | 0 | 3,062 | 0 / 7,586 / 0 / 0 | 0 |
| (a) dl13-n4m9-rot, dl13-n4m6-fswap (suite) | 0 | 1 | 4 | 0 | 6 | 0 | 1 | 0 | 2 | 0 / 6 / 1 / 0 | 0 |
| (a) neighbourhood of dl13-n4m9-rot (radius 2) | 48,928 | 58,207 | 28,144 | 47,692 | 0 | 32 | 3,971 | 1,104 | 0 | 48,928 / 6,160 / 4,351 / 0 | 0 |
| (b) n4_1, every profile | 0 | 0 | 266 | 0 | 140 | 0 | 0 | 146 | 20 | 0 / 286 / 0 / 0 | 0 |
| (c) n4_2, every profile | 229,032 | 187,344 | 282,138 | 256,772 | 63,560 | 0 | 0 | 45,906 | 3,040 | 229,032 / 95,626 / 0 / 0 | 0 |
| (d) pure, 500/core, seed 1 | 2,976 | 3,017 | 2,890 | 3,095 | 97 | 0 | 0 | 70 | 0 | 2,976 / 165 / 0 / 0 | 0 |
| (d) pure, 500/core, seed 2 | 2,965 | 2,992 | 2,818 | 3,054 | 95 | 0 | 0 | 69 | 2 | 2,965 / 146 / 0 / 0 | 0 |
| (d) pure, 500/core, seed 3 | 3,310 | 3,309 | 3,249 | 3,468 | 129 | 0 | 0 | 133 | 0 | 3,310 / 219 / 0 / 0 | 0 |
| (d) #53's gap_n4_pure_s4000 | 23,876 | 24,163 | 22,720 | 24,835 | 22 | 0 | 1 | 611 | 0 | 23,876 / 1,140 / 2 / 0 | 0 |
| (e) n4_3, 500/core, seed 1 | 1,055 | 1,033 | 926 | 1,079 | 57 | 0 | 0 | 41 | 0 | 1,055 / 55 / 0 / 0 | 0 |
| (e) n4_3, 500/core, seed 2 | 983 | 959 | 916 | 1,011 | 108 | 0 | 0 | 22 | 2 | 983 / 64 / 0 / 0 | 0 |
| (e) n4_3, 500/core, seed 3 | 987 | 974 | 860 | 1,006 | 72 | 0 | 0 | 27 | 2 | 987 / 50 / 0 / 0 | 0 |

### 3. T4 cycle types (f >= 1 states with an improving T4 move)

"least size: cycle types": the states by the least |ch| of an improving T4 move and the cycle types of the improving T4 moves of that size; "available": the states with an improving T4 move of each cycle type; "T4 needed": the states at which T4 is the only branch, by their least T4 size and cycle types.

| run | states with T4 | least size: cycle types | available | T4 needed |
|---|---:|---|---|---|
| (a) 1,131 profiles of the 3,062 DL13 failures | 7,586 | 2: 2 (5,324), 3: 3 (2,262) | 2: 5,324, 3: 5,324 | 3,062 states; size 2: 3,062; cycle types available: 2: 3,062, 3: 3,062 |
| (a) dl13-n4m9-rot, dl13-n4m6-fswap (suite) | 6 | 2: 2 (4), 3: 3 (2) | 2: 4, 3: 4 | 2 states; size 2: 2; cycle types available: 2: 2, 3: 2 |
| (a) neighbourhood of dl13-n4m9-rot (radius 2) | 0 | | | |
| (b) n4_1, every profile | 140 | 2: 2 (120), 3: 3 (20) | 2: 120, 3: 80 | 20 states; size 2: 20; cycle types available: 2: 20, 3: 20 |
| (c) n4_2, every profile | 63,560 | 2: 2 (61,320), 3: 3 (2,240) | 2: 61,320, 3: 32,000 | 3,040 states; size 2: 3,040; cycle types available: 2: 3,040, 3: 3,040 |
| (d) pure, 500/core, seed 1 | 97 | 2: 2 (97) | 2: 97 | - |
| (d) pure, 500/core, seed 2 | 95 | 2: 2 (93), 3: 3 (2) | 2: 93, 3: 14 | 2 states; size 2: 2; cycle types available: 2: 2, 3: 2 |
| (d) pure, 500/core, seed 3 | 129 | 2: 2 (129) | 2: 129, 3: 20 | - |
| (d) #53's gap_n4_pure_s4000 | 22 | 2: 2 (22) | 2: 22 | - |
| (e) n4_3, 500/core, seed 1 | 57 | 2: 2 (57) | 2: 57 | - |
| (e) n4_3, 500/core, seed 2 | 108 | 2: 2 (106), 3: 3 (2) | 2: 106, 3: 12 | 2 states; size 2: 2; cycle types available: 2: 2, 3: 2 |
| (e) n4_3, 500/core, seed 3 | 72 | 2: 2 (70), 3: 3 (2) | 2: 70, 3: 4 | 2 states; size 2: 2; cycle types available: 2: 2, 3: 2 |

### 4. Branch combinations (f >= 1 states: f, branches with an improving move: smallest RT4 move size: states)

| run | f, branch combination: smallest size: states |
|---|---|
| (a) 1,131 profiles of the 3,062 DL13 failures | f = 3, T3p+T4: 2: 4,524; f = 3, T4: 2: 3,062 |
| (a) dl13-n4m9-rot, dl13-n4m6-fswap (suite) | f = 3, T3p+T4: 2: 4; f = 3, T4: 2: 2; f = 1, T2: 3: 1 |
| (a) neighbourhood of dl13-n4m9-rot (radius 2) | f = 1, T1+T2+T3p+T3h: 1: 22,256; f = 1, T1+T2+T3h: 1: 18,320; f = 1, T1+T2: 1: 7,320; f = 1, T2+T3p+T3h: 2: 3,784; f = 1, T2: 3: 2,991; f = 1, T2+T3h: 3: 1,360; f = 2, T3p+T3h: 2: 1,104; f = 1, T2: 2: 980; f = 2, T1+T2+T3p+T3h: 1: 480; f = 1, T1+T2+T3p: 1: 424; f = 1, T2+T3h: 2: 292; f = 1, T1+T3p+T3h: 1: 96; f = 1, T1: 1: 32 |
| (b) n4_1, every profile | f = 2, T3p: 2: 146; f = 3, T3p+T4: 2: 120; f = 3, T4: 2: 20 |
| (c) n4_2, every profile | f = 1, T1+T2+T3p+T3h: 1: 89,520; f = 2, T1+T2+T3p+T3h: 1: 51,416; f = 3, T3p+T4: 2: 36,160; f = 1, T1+T2+T3h: 1: 34,048; f = 2, T1+T3p+T3h: 1: 33,934; f = 2, T3p: 2: 22,584; f = 2, T3p+T3h: 2: 21,450; f = 2, T1+T2+T3p+T3h+T4: 1: 7,400; f = 2, T3p+T3h+T4: 2: 6,820; f = 2, T1+T3p+T3h+T4: 1: 4,840; f = 3, T4: 2: 3,040; f = 2, T1+T3h+T4: 1: 2,800; f = 2, T3p+T4: 2: 2,420; f = 2, T1+T2+T3h: 1: 2,112; f = 3, T3p: 2: 1,872; f = 1, T1+T2+T3p: 1: 1,312; f = 2, T2+T3p+T3h: 2: 1,080; f = 1, T1+T3p+T3h: 1: 832; f = 2, T1+T3h: 1: 360; f = 2, T1+T2+T3p: 1: 336; f = 2, T1+T3p: 1: 122; f = 2, T2+T3h: 2: 80; f = 2, T3h+T4: 2: 80; f = 2, T2+T3p: 2: 40 |
| (d) pure, 500/core, seed 1 | f = 1, T1+T2+T3p+T3h: 1: 2,457; f = 1, T1+T2+T3h: 1: 232; f = 2, T1+T2+T3p+T3h: 1: 178; f = 2, T1+T2+T3p+T3h+T4: 1: 60; f = 1, T2+T3p+T3h: 2: 57; f = 1, T3p+T3h: 2: 47; f = 2, T3p+T3h+T4: 2: 25; f = 1, T1+T2: 1: 16; f = 2, T3p+T3h: 2: 16; f = 1, T1+T3p+T3h: 1: 11; f = 1, T1+T2+T3p: 1: 7; f = 2, T3p: 2: 7; f = 1, T2+T3p: 2: 6; f = 2, T1+T3p+T3h: 1: 6; f = 2, T3p+T4: 2: 6; f = 1, T1+T3p: 1: 3; f = 2, T1+T2+T3h+T4: 1: 2; f = 2, T1+T3p+T3h+T4: 1: 2; f = 2, T1+T2+T3h: 1: 1; f = 2, T1+T3p+T4: 1: 1; f = 2, T2+T3p+T3h+T4: 2: 1 |
| (d) pure, 500/core, seed 2 | f = 1, T1+T2+T3p+T3h: 1: 2,427; f = 1, T1+T2+T3h: 1: 267; f = 2, T1+T2+T3p+T3h: 1: 157; f = 2, T1+T2+T3p+T3h+T4: 1: 63; f = 1, T2+T3p+T3h: 2: 41; f = 1, T3p+T3h: 2: 33; f = 2, T3p+T3h: 2: 29; f = 1, T1+T3p+T3h: 1: 18; f = 3, T3p+T4: 2: 16; f = 1, T1+T2: 1: 15; f = 2, T3p: 2: 7; f = 1, T2+T3p: 2: 6; f = 2, T3p+T3h+T4: 2: 6; f = 1, T1+T2+T3p: 1: 4; f = 2, T1+T2+T3h: 1: 4; f = 2, T1+T3p+T3h: 1: 4; f = 2, T3p+T4: 2: 4; f = 2, T1+T2+T3h+T4: 1: 3; f = 1, T2+T3h: 2: 2; f = 2, T1+T2+T3p: 1: 2; f = 3, T4: 2: 2; f = 2, T1+T2+T3p+T4: 1: 1 |
| (d) pure, 500/core, seed 3 | f = 1, T1+T2+T3p+T3h: 1: 2,764; f = 1, T1+T2+T3h: 1: 263; f = 2, T1+T2+T3p+T3h: 1: 149; f = 1, T3p+T3h: 2: 92; f = 2, T1+T2+T3p+T3h+T4: 1: 72; f = 1, T2+T3p+T3h: 2: 32; f = 2, T3p+T3h: 2: 30; f = 3, T3p+T4: 2: 24; f = 1, T1+T3p+T3h: 1: 23; f = 2, T3p+T3h+T4: 2: 21; f = 2, T3p: 2: 11; f = 2, T1+T3p+T3h: 1: 9; f = 1, T1+T2: 1: 8; f = 1, T1+T2+T3p: 1: 6; f = 2, T3p+T4: 2: 5; f = 2, T1+T2+T3h+T4: 1: 4; f = 2, T1+T2+T3h: 1: 4; f = 1, T1+T3p: 1: 3; f = 2, T1+T2+T3p: 1: 2; f = 2, T1+T3p+T3h+T4: 1: 2; f = 2, T2+T3p+T3h: 2: 2; f = 1, T2+T3h: 2: 1; f = 1, T2+T3p: 2: 1; f = 2, T1+T2+T3p+T4: 1: 1 |
| (d) #53's gap_n4_pure_s4000 | f = 1, T1+T2+T3p+T3h: 1: 21,019; f = 1, T1+T2+T3h: 1: 2,188; f = 1, T3p+T3h: 2: 569; f = 1, T2+T3p+T3h: 2: 487; f = 2, T1+T2+T3p+T3h: 1: 268; f = 1, T1+T3p+T3h: 1: 202; f = 1, T1+T2: 1: 106; f = 1, T1+T2+T3p: 1: 39; f = 2, T3p+T3h: 2: 33; f = 2, T1+T3p+T3h: 1: 28; f = 1, T2+T3p: 2: 19; f = 2, T2+T3p+T3h: 2: 17; f = 2, T1+T2+T3p+T3h+T4: 1: 13; f = 1, T1+T3p: 1: 6; f = 1, T3p: 2: 5; f = 2, T3p+T3h+T4: 2: 4; f = 2, T3p: 2: 4; f = 2, T1+T3p+T3h+T4: 1: 3; f = 2, T1+T2+T3p: 1: 2; f = 1, T1+T3h: 1: 1; f = 1, T2+T3h: 2: 1; f = 1, T2+T3h: 3: 1; f = 1, T2: 3: 1; f = 2, T1+T2+T3p+T4: 1: 1; f = 2, T2+T3p+T3h+T4: 2: 1 |
| (e) n4_3, 500/core, seed 1 | f = 1, T1+T2+T3p+T3h: 1: 691; f = 1, T1+T2+T3h: 1: 170; f = 2, T1+T2+T3p+T3h: 1: 108; f = 2, T1+T2+T3p+T3h+T4: 1: 36; f = 1, T3p+T3h: 2: 16; f = 2, T1+T3p+T3h: 1: 16; f = 2, T3p+T3h: 2: 16; f = 2, T3p: 2: 9; f = 1, T1+T2: 1: 8; f = 2, T3p+T3h+T4: 2: 7; f = 2, T1+T3p+T3h+T4: 1: 6; f = 1, T1+T2+T3p: 1: 4; f = 2, T1+T2+T3p: 1: 4; f = 1, T1+T3p+T3h: 1: 3; f = 1, T2+T3p+T3h: 2: 3; f = 2, T1+T2+T3h+T4: 1: 3; f = 2, T1+T2+T3h: 1: 3; f = 2, T3p+T4: 2: 3; f = 2, T1+T2+T3p+T4: 1: 2; f = 1, T1+T3p: 1: 1; f = 2, T2+T3p+T3h: 2: 1 |
| (e) n4_3, 500/core, seed 2 | f = 1, T1+T2+T3p+T3h: 1: 679; f = 1, T1+T2+T3h: 1: 114; f = 2, T1+T2+T3p+T3h: 1: 93; f = 2, T1+T2+T3p+T3h+T4: 1: 53; f = 2, T3p+T3h+T4: 2: 21; f = 2, T3p+T3h: 2: 15; f = 3, T3p+T4: 2: 14; f = 2, T1+T3p+T3h: 1: 11; f = 2, T1+T2+T3h+T4: 1: 7; f = 1, T1+T2+T3p: 1: 6; f = 1, T1+T3p+T3h: 1: 6; f = 2, T1+T3p+T3h+T4: 1: 5; f = 2, T3p: 2: 5; f = 2, T3p+T4: 2: 4; f = 1, T1+T2: 1: 3; f = 2, T1+T2+T3h: 1: 3; f = 2, T1+T3h+T4: 1: 2; f = 3, T4: 2: 2; f = 1, T1+T3p: 1: 1; f = 1, T2+T3p+T3h: 2: 1; f = 1, T3p+T3h: 2: 1; f = 1, T3p: 2: 1 |
| (e) n4_3, 500/core, seed 3 | f = 1, T1+T2+T3p+T3h: 1: 608; f = 1, T1+T2+T3h: 1: 164; f = 2, T1+T2+T3p+T3h: 1: 129; f = 2, T1+T2+T3p+T3h+T4: 1: 51; f = 2, T3p+T3h: 2: 15; f = 2, T1+T3p+T3h: 1: 10; f = 2, T3p+T3h+T4: 2: 10; f = 1, T1+T2+T3p: 1: 6; f = 1, T1+T2: 1: 6; f = 3, T3p: 2: 6; f = 1, T1+T3p+T3h: 1: 5; f = 1, T2+T3p+T3h: 2: 5; f = 2, T1+T2+T3h: 1: 4; f = 2, T3p: 2: 4; f = 3, T3p+T4: 2: 4; f = 1, T3p+T3h: 2: 2; f = 2, T1+T3p+T3h+T4: 1: 2; f = 2, T3p+T4: 2: 2; f = 3, T4: 2: 2; f = 1, T1+T3p: 1: 1; f = 2, T1+T2+T3h+T4: 1: 1 |
