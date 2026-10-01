# DL2 classification tables (generated)

command: `python3 k4/dl2_classify_table.py results/k4_dl2_classify/gap_n2_e1.jsonl.gz results/k4_dl2_classify/gap_n3_e1.jsonl.gz results/k4_dl2_classify/gap_n4_1_e10.jsonl.gz results/k4_dl2_classify/gap_n4_2_s4000_e10.jsonl.gz results/k4_dl2_classify/gap_n4_3_s4000_e10.jsonl.gz results/k4_dl2_classify/gap_n4_pure_s4000_e10.jsonl.gz results/k4_dl2_classify/gap_n5_1_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_2_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_3_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_4_s100_e20.jsonl.gz results/k4_dl2_classify/gap_n5_pure_s100_e20.jsonl.gz results/k4_dl2_classify/hard_hunt_e1.jsonl.gz results/k4_dl2_classify/suite.jsonl.gz`

Every min-frozen P with def(P) > 0 of every profile in the inputs is one *state*. k = the least number of agents
whose bases change to reach a min-frozen P' with a smaller deficit. Obstruction signature: the H3/H7 classes
(e1, e2, e3, G, G1, L; fU/fU2: a free exposed agent violating (U)/(U2); fO, O: other) of the agents exposed
w.r.t. the best owner with the fewest exposures; suffix 2: a frozen agent exposed w.r.t. two or more free
agents (the double threat of Lemma D). Repair kind: `k4/dl2_classify.py` `repair_kind` (primary kind of the
minimal repairs: release > unblock > owner > need-transfer for k = 1).

## Inputs

| input | profiles with a def > 0 state | states | k = 1 | k = 2 | k = 3 | profiles with k* = 3 |
|---|---|---|---|---|---|---|
| gap_n2_e1 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n3_e1 | 14718 | 47080 | 34732 | 12037 | 311 | 89 |
| gap_n4_1_e10 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n4_2_s4000_e10 | 50 | 68 | 68 | 0 | 0 | 0 |
| gap_n4_3_s4000_e10 | 342 | 681 | 680 | 1 | 0 | 0 |
| gap_n4_pure_s4000_e10 | 629 | 2804 | 2599 | 205 | 0 | 0 |
| gap_n5_1_s100_e20 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n5_2_s100_e20 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n5_3_s100_e20 | 20 | 32 | 32 | 0 | 0 | 0 |
| gap_n5_4_s100_e20 | 100 | 300 | 299 | 1 | 0 | 0 |
| gap_n5_pure_s100_e20 | 128 | 650 | 639 | 11 | 0 | 0 |
| hard_hunt_e1 | 76 | 192 | 121 | 71 | 0 | 0 |
| suite | 51 | 359 | 296 | 63 | 0 | 0 |
| **total (cores)** | | 52166 | 39466 | 12389 | 311 | |

Not cores (suite, counted apart): 20 states, k histogram {1: 8, 2: 11, 3: 1}, instances ['lil-noncore-n3'].

## A. Obstruction group × k

| obstruction group | k = 1 | k = 2 | k = 3 | example of the largest k |
|---|---|---|---|---|
| H7 only, double threat (Lemma D) | 22022 | 7902 | 0 | gap_n3:k4_certs_3.json.gz#2:44,10,6 P=[[5], [3], [2, 4]] |
| free exposed agent violating (U)/(U2) | 9742 | 1492 | 150 | gap_n3:k4_certs_3.json.gz#0:6,62,212 P=[[3], [2, 4], [6]] |
| H7 only, single threats | 4970 | 1128 | 161 | gap_n3:k4_certs_3.json.gz#0:6,62,212 P=[[3], [2, 4], [5, 6]] |
| other: frozen exposure not G/G1/L | 1949 | 1428 | 0 | gap_n3:k4_certs_3.json.gz#2:2,11,6 P=[[5], [4], [2, 3]] |
| H3 only (e1) | 602 | 47 | 0 | gap_n3:k4_certs_3.json.gz#2:2,11,6 P=[[5], [2, 3], [4]] |
| H3 only (e2) | 170 | 361 | 0 | gap_n3:k4_certs_3.json.gz#14:14,15,233 P=[[2], [3, 5], [4]] |
| H3 + H7 mixed, double threat | 2 | 29 | 0 | gap_n3:k4_certs_3.json.gz#0:7,15,278 P=[[3], [4, 6], [5]] |
| H3 + H7 mixed | 9 | 1 | 0 | gap_n3:k4_certs_3.json.gz#8:9,11,85 P=[[5], [3, 4], [6]] |
| H3 only (e3) | 0 | 1 | 0 | induct-g-r1 P=[[3, 4], [1, 2]] |

## A′. The same, Pareto-maximal states only (where Lemmas H3 and H7 of `k4/hall.md` apply)

| obstruction group | k = 1 | k = 2 | k = 3 |
|---|---|---|---|
| H7 only, double threat (Lemma D) | 2368 | 203 | 0 |
| H7 only, single threats | 821 | 315 | 80 |
| H3 only (e2) | 100 | 75 | 0 |

## B. Obstruction signature × repair kind (primary kind of the minimal repairs)

Repair kinds (columns): `R1:release` (36892), `R1:unblock` (1386), `R1:owner` (1188), `R2:role-swap/needer/J` (10716), `R2:two-free` (1123), `R2:role-swap/needer/T` (550), `R3:F>f,f>F,f>f` (311).

| signature | states | `R1:release` | `R1:unblock` | `R1:owner` | `R2:role-swap/needer/J` | `R2:two-free` | `R2:role-swap/needer/T` | `R3:F>f,f>F,f>f` |
|---|---|---|---|---|---|---|---|---|
| G2 | 29873 | 21554 | 416 | 5 | 7898 |  |  |  |
| fU2 | 7974 | 7528 |  | 48 | 111 | 137 |  | 150 |
| L | 5397 | 3587 | 437 | 101 | 388 | 723 |  | 161 |
| O2 | 3116 | 1625 |  | 154 | 835 |  | 502 |  |
| G2+fU | 1987 | 562 | 200 |  | 1225 |  |  |  |
| G1 | 855 | 289 |  | 556 | 10 |  |  |  |
| fU | 711 | 378 | 333 |  |  |  |  |  |
| e1 | 649 | 472 |  | 130 | 26 | 3 | 18 |  |
| e2 | 531 | 145 |  | 25 | 100 | 259 | 2 |  |
| G2+fU2 | 505 | 487 |  |  | 18 |  |  |  |
| O | 179 | 64 |  | 91 | 20 |  | 4 |  |
| G1+fU2 | 159 | 104 |  | 55 |  |  |  |  |
| O2+fU | 81 |  |  | 14 | 44 |  | 23 |  |
| L2 | 41 | 40 |  |  | 1 |  |  |  |
| fU+fU2 | 39 | 39 |  |  |  |  |  |  |
| G2+e2 | 31 | 2 |  |  | 29 |  |  |  |
| G1+e2 | 10 |  |  | 9 |  |  | 1 |  |
| G2+L | 9 | 6 |  |  | 3 |  |  |  |
| G | 7 |  |  |  | 7 |  |  |  |
| L2+fU | 2 | 2 |  |  |  |  |  |  |
| G2+fU+fU2 | 2 | 2 |  |  |  |  |  |  |
| L+fU2 | 2 | 2 |  |  |  |  |  |  |
| L+fU | 2 | 1 |  |  | 1 |  |  |  |
| G2+O2 | 1 | 1 |  |  |  |  |  |  |
| L2+fU2 | 1 | 1 |  |  |  |  |  |  |
| G1+G2 | 1 | 1 |  |  |  |  |  |  |
| e3 | 1 |  |  |  |  | 1 |  |  |

### Examples (first state of each cell)

- G2 × `R1:release` (21554): gap_n3:k4_certs_3.json.gz#2:27,156,8 P=[[4], [2, 3], [5]]
- G2 × `R1:unblock` (416): gap_n3:k4_certs_3.json.gz#0:6,37,212 P=[[3], [4], [5, 6]]
- G2 × `R1:owner` (5): gap_n3:k4_certs_3.json.gz#8:44,42,6 P=[[6], [3, 4], [5]]
- G2 × `R2:role-swap/needer/J` (7898): gap_n3:k4_certs_3.json.gz#2:44,10,6 P=[[5], [3], [2, 4]]
- fU2 × `R1:release` (7528): gap_n3:k4_certs_3.json.gz#10:30,67,4 P=[[0, 4], [1, 3], [2]]
- fU2 × `R1:owner` (48): gap_n3:k4_certs_3.json.gz#13:30,125,241 P=[[2], [4, 5], [3]]
- fU2 × `R2:role-swap/needer/J` (111): gap_n3:k4_certs_3.json.gz#0:20,52,227 P=[[3], [2, 5], [4]]
- fU2 × `R2:two-free` (137): gap_n3:k4_certs_3.json.gz#0:7,55,275 P=[[3], [2, 4], [6]]
- fU2 × `R3:F>f,f>F,f>f` (150): gap_n3:k4_certs_3.json.gz#0:6,62,212 P=[[3], [2, 4], [6]]
- L × `R1:release` (3587): gap_n3:k4_certs_3.json.gz#10:0,180,1 P=[[0, 5], [1, 4], [3]]
- L × `R1:unblock` (437): gap_n3:k4_certs_3.json.gz#0:6,198,212 P=[[3], [2], [4, 5]]
- L × `R1:owner` (101): gap_n3:k4_certs_3.json.gz#0:6,244,212 P=[[3], [2], [4, 6]]
- L × `R2:role-swap/needer/J` (388): gap_n3:k4_certs_3.json.gz#0:20,52,227 P=[[3], [2, 4], [5, 6]]
- L × `R2:two-free` (723): gap_n3:k4_certs_3.json.gz#0:6,87,214 P=[[3], [2, 6], [4, 5]]
- L × `R3:F>f,f>F,f>f` (161): gap_n3:k4_certs_3.json.gz#0:6,62,212 P=[[3], [2, 4], [5, 6]]
- O2 × `R1:release` (1625): gap_n3:k4_certs_3.json.gz#8:0,18,246 P=[[0, 4], [3], [5]]
- O2 × `R1:owner` (154): gap_n3:k4_certs_3.json.gz#8:6,146,100 P=[[4], [1, 3], [5]]
- O2 × `R2:role-swap/needer/J` (835): gap_n3:k4_certs_3.json.gz#8:6,6,232 P=[[4], [1, 3], [5]]
- O2 × `R2:role-swap/needer/T` (502): gap_n3:k4_certs_3.json.gz#8:6,11,134 P=[[4], [1, 3], [5]]
- G2+fU × `R1:release` (562): gap_n3:k4_certs_3.json.gz#8:80,88,246 P=[[0], [1], [5]]
- G2+fU × `R1:unblock` (200): gap_n3:k4_certs_3.json.gz#0:6,37,212 P=[[3], [4], [6]]
- G2+fU × `R2:role-swap/needer/J` (1225): gap_n3:k4_certs_3.json.gz#2:44,10,6 P=[[5], [3], [4]]
- G1 × `R1:release` (289): gap_n3:k4_certs_3.json.gz#8:6,2,155 P=[[6], [3, 4], [5]]
- G1 × `R1:owner` (556): gap_n3:k4_certs_3.json.gz#8:6,47,42 P=[[6], [3, 4], [5]]
- G1 × `R2:role-swap/needer/J` (10): gap_n3:k4_certs_3.json.gz#8:40,0,49 P=[[5], [3, 4], [6]]
- fU × `R1:release` (378): gap_n3:k4_certs_3.json.gz#8:8,160,84 P=[[0, 2], [6], [5]]
- fU × `R1:unblock` (333): gap_n3:k4_certs_3.json.gz#0:6,198,212 P=[[3], [2], [6]]
- e1 × `R1:release` (472): gap_n3:k4_certs_3.json.gz#2:0,187,6 P=[[5], [2, 3], [4]]
- e1 × `R1:owner` (130): gap_n3:k4_certs_3.json.gz#2:2,188,6 P=[[5], [2, 3], [4]]
- e1 × `R2:role-swap/needer/J` (26): gap_n3:k4_certs_3.json.gz#2:2,11,6 P=[[5], [2, 3], [4]]
- e1 × `R2:two-free` (3): gap_n3:k4_certs_3.json.gz#13:4,17,236 P=[[2], [3, 5], [4]]
- e1 × `R2:role-swap/needer/T` (18): gap_n3:k4_certs_3.json.gz#2:43,157,44 P=[[4], [2, 3], [5]]
- e2 × `R1:release` (145): gap_n3:k4_certs_3.json.gz#10:3,37,30 P=[[0, 3], [5, 6], [4]]
- e2 × `R1:owner` (25): gap_n3:k4_certs_3.json.gz#13:38,119,227 P=[[2], [4, 5], [3]]
- e2 × `R2:role-swap/needer/J` (100): gap_n3:k4_certs_3.json.gz#14:30,227,40 P=[[1], [3], [4, 5]]
- e2 × `R2:two-free` (259): gap_n3:k4_certs_3.json.gz#14:14,15,233 P=[[2], [3, 5], [4]]
- e2 × `R2:role-swap/needer/T` (2): gap_n3:k4_certs_3.json.gz#14:72,261,18 P=[[1], [5], [3, 4]]
- G2+fU2 × `R1:release` (487): gap_n3:k4_certs_3.json.gz#0:6,111,212 P=[[3], [4, 5], [6]]
- G2+fU2 × `R2:role-swap/needer/J` (18): gap_n3:k4_certs_3.json.gz#0:6,113,240 P=[[3], [5, 6], [4]]
- O × `R1:release` (64): gap_n3:k4_certs_3.json.gz#2:0,11,150 P=[[5], [4], [2, 3]]
- O × `R1:owner` (91): gap_n3:k4_certs_3.json.gz#2:0,42,80 P=[[5], [4], [2, 3]]
- O × `R2:role-swap/needer/J` (20): gap_n3:k4_certs_3.json.gz#2:2,11,6 P=[[5], [4], [2, 3]]
- O × `R2:role-swap/needer/T` (4): gap_n3:k4_certs_3.json.gz#2:43,157,44 P=[[4], [5], [2, 3]]
- G1+fU2 × `R1:release` (104): gap_n3:k4_certs_3.json.gz#11:8,234,84 P=[[4], [3, 5], [2]]
- G1+fU2 × `R1:owner` (55): gap_n3:k4_certs_3.json.gz#8:8,252,8 P=[[5], [3, 4], [6]]
- O2+fU × `R1:owner` (14): gap_n3:k4_certs_3.json.gz#13:6,159,10 P=[[4], [5], [3]]
- O2+fU × `R2:role-swap/needer/J` (44): gap_n3:k4_certs_3.json.gz#8:11,26,186 P=[[4], [3], [5]]
- O2+fU × `R2:role-swap/needer/T` (23): gap_n3:k4_certs_3.json.gz#8:8,137,14 P=[[5], [4], [3]]
- L2 × `R1:release` (40): gap_n4_3_s4000:k4_certs_4_n4_3.json.gz#63:93,157,3,133 P=[[0, 5], [1, 3], [2, 7], [6]]
- L2 × `R2:role-swap/needer/J` (1): gap_n4_pure_s4000:k4_certs_4_pure.json.gz#41:16,46,88,221 P=[[0, 7], [4, 6], [2, 5], [8]]
- fU+fU2 × `R1:release` (39): gap_n4_3_s4000:k4_certs_4_n4_3.json.gz#3:50,12,88,4 P=[[0, 2], [1, 8], [3], [7]]
- G2+e2 × `R1:release` (2): gap_n4_pure_s4000:k4_certs_4_pure.json.gz#0:36,9,73,107 P=[[10], [8], [3, 9], [4, 7]]
- G2+e2 × `R2:role-swap/needer/J` (29): gap_n3:k4_certs_3.json.gz#0:7,15,278 P=[[3], [4, 6], [5]]
- G1+e2 × `R1:owner` (9): gap_n3:k4_certs_3.json.gz#8:14,47,44 P=[[5], [3, 4], [6]]
- G1+e2 × `R2:role-swap/needer/T` (1): gap_n3:k4_certs_3.json.gz#8:9,11,85 P=[[5], [3, 4], [6]]
- G2+L × `R1:release` (6): hard_hunt:k4_certs_4_pure.json.gz#1:22,20,212,146 P=[[4], [9], [7], [5, 6]]
- G2+L × `R2:role-swap/needer/J` (3): hard_hunt:k4_certs_4_pure.json.gz#0:102,22,44,8 P=[[7], [5], [3, 6], [8]]
- G × `R2:role-swap/needer/J` (7): c4min-tlam-n3-m6 P=[[5], [4], [3]]
- L2+fU × `R1:release` (2): gap_n4_pure_s4000:k4_certs_4_pure.json.gz#3:62,36,41,136 P=[[2, 7], [9], [3, 5], [8]]
- G2+fU+fU2 × `R1:release` (2): gap_n4_pure_s4000:k4_certs_4_pure.json.gz#5:116,56,74,43 P=[[0, 2], [1, 5], [3], [9]]
- L+fU2 × `R1:release` (2): gap_n4_pure_s4000:k4_certs_4_pure.json.gz#6:71,77,6,109 P=[[0, 7], [1, 10], [8], [4]]
- L+fU × `R1:release` (1): gap-ipoollocal-n5-m12-n5pc4202 P=[[0, 7], [9], [3, 6], [8], [10]]
- L+fU × `R2:role-swap/needer/J` (1): hard_hunt:k4_certs_4_pure.json.gz#1:46,68,88,44 P=[[8], [7], [4], [9]]
- G2+O2 × `R1:release` (1): gap_n4_3_s4000:k4_certs_4_n4_3.json.gz#80:9,17,0,92 P=[[0, 3], [1, 4], [7], [6]]
- L2+fU2 × `R1:release` (1): gap_n5_pure_s100:k4_certs_5_pure.json.gz#44:91,69,20,97,223 P=[[0, 9], [1, 10], [3, 6], [5, 7], [11]]
- G1+G2 × `R1:release` (1): hard_hunt:k4_certs_4_pure.json.gz#26:46,46,38,84 P=[[5], [8], [7, 9], [6]]
- e3 × `R2:two-free` (1): induct-g-r1 P=[[3, 4], [1, 2]]

## C. Coverage of the k = 1 states by the lemmas of `k4/dl2.md` §3

Each lemma's hypotheses are checked at every state; whenever they hold, its conclusion is asserted against
the exact deficits (no violation in any input), and no lemma applies at a state with k > 1.

| input | k = 1 states | Cor 4 structural | Cor 4 (release) | Cor 5 (unblocking) | Lemma 2 at a best owner | Lemma 2 at another owner | Lemma 3 (owner re-base) | Lemma 2 or 3 | none |
|---|---|---|---|---|---|---|---|---|---|
| gap_n2_e1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n3_e1 | 34732 | 19580 (56.4%) | 22008 (63.4%) | 2131 (6.1%) | 33099 (95.3%) | 1019 (2.9%) | 4094 (11.8%) | 34732 (100.0%) | 0 (0.0%) |
| gap_n4_1_e10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n4_2_s4000_e10 | 68 | 52 (76.5%) | 60 (88.2%) | 0 (0.0%) | 64 (94.1%) | 0 (0.0%) | 9 (13.2%) | 68 (100.0%) | 0 (0.0%) |
| gap_n4_3_s4000_e10 | 680 | 623 (91.6%) | 650 (95.6%) | 11 (1.6%) | 676 (99.4%) | 0 (0.0%) | 10 (1.5%) | 680 (100.0%) | 0 (0.0%) |
| gap_n4_pure_s4000_e10 | 2599 | 2213 (85.1%) | 2306 (88.7%) | 116 (4.5%) | 2597 (99.9%) | 10 (0.4%) | 18 (0.7%) | 2598 (100.0%) | 1 (0.0%) |
| gap_n5_1_s100_e20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n5_2_s100_e20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n5_3_s100_e20 | 32 | 31 (96.9%) | 31 (96.9%) | 1 (3.1%) | 32 (100.0%) | 0 (0.0%) | 0 (0.0%) | 32 (100.0%) | 0 (0.0%) |
| gap_n5_4_s100_e20 | 299 | 283 (94.6%) | 290 (97.0%) | 12 (4.0%) | 299 (100.0%) | 3 (1.0%) | 1 (0.3%) | 299 (100.0%) | 0 (0.0%) |
| gap_n5_pure_s100_e20 | 639 | 597 (93.4%) | 629 (98.4%) | 30 (4.7%) | 639 (100.0%) | 10 (1.6%) | 1 (0.2%) | 639 (100.0%) | 0 (0.0%) |
| hard_hunt_e1 | 121 | 107 (88.4%) | 114 (94.2%) | 0 (0.0%) | 121 (100.0%) | 0 (0.0%) | 4 (3.3%) | 121 (100.0%) | 0 (0.0%) |
| suite | 296 | 233 (78.7%) | 236 (79.7%) | 53 (17.9%) | 294 (99.3%) | 18 (6.1%) | 2 (0.7%) | 296 (100.0%) | 0 (0.0%) |
| **all** | 39466 | 23719 (60.1%) | 26324 (66.7%) | 2354 (6.0%) | 37821 (95.8%) | 1060 (2.7%) | 4139 (10.5%) | 39465 (100.0%) | 1 (0.0%) |
| Pareto-maximal only | 3289 | 2580 (78.4%) | 2606 (79.2%) | 0 (0.0%) | 3044 (92.6%) | 0 (0.0%) | 365 (11.1%) | 3289 (100.0%) | 0 (0.0%) |

k = 1 states that no lemma covers, by primary kind: {'R1:release': 1}; first examples:
- gap_n4_pure_s4000:k4_certs_4_pure.json.gz#5:83,6,64,235 P=[[0, 2], [1, 5], [10], [4, 8]] (R1:release)

## C′. Certificates for the states with k ≥ 2 (Lemma 2*, extension through any move; Lemma 7)

A state is certified if some minimal repair satisfies the hypotheses of Lemma 2* at a best owner that does not
move (E2) or of Lemma 7 with a gain over Val*(P) (L7); the conclusion is asserted against the exact deficits.

| input | k | states | Lemma 2* | Lemma 7 | either | neither |
|---|---|---|---|---|---|---|
| gap_n3_e1 | 2 | 12037 | 10441 (86.7%) | 9444 (78.5%) | 10905 (90.6%) | 1132 (9.4%) |
| gap_n4_3_s4000_e10 | 2 | 1 | 1 (100.0%) | 1 (100.0%) | 1 (100.0%) | 0 (0.0%) |
| gap_n4_pure_s4000_e10 | 2 | 205 | 175 (85.4%) | 157 (76.6%) | 205 (100.0%) | 0 (0.0%) |
| gap_n5_4_s100_e20 | 2 | 1 | 1 (100.0%) | 0 (0.0%) | 1 (100.0%) | 0 (0.0%) |
| gap_n5_pure_s100_e20 | 2 | 11 | 11 (100.0%) | 0 (0.0%) | 11 (100.0%) | 0 (0.0%) |
| hard_hunt_e1 | 2 | 71 | 28 (39.4%) | 71 (100.0%) | 71 (100.0%) | 0 (0.0%) |
| suite | 2 | 63 | 25 (39.7%) | 53 (84.1%) | 56 (88.9%) | 7 (11.1%) |
| **all** | 2 | 12389 | 10682 (86.2%) | 9726 (78.5%) | 11250 (90.8%) | 1139 (9.2%) |
| gap_n3_e1 | 3 | 311 | 0 (0.0%) | 311 (100.0%) | 311 (100.0%) | 0 (0.0%) |
| **all** | 3 | 311 | 0 (0.0%) | 311 (100.0%) | 311 (100.0%) | 0 (0.0%) |

## D. The states with k ≥ 2: kinds of their minimal repairs

k = 2 (12389 states):

- 6469: R2:role-swap/needer/J | R2:role-swap/needer/T
- 3264: R2:role-swap/needer/J
- 1123: R2:two-free
- 618: R2:role-swap/needer/J | R2:two-free
- 364: R2:role-swap/needer/T
- 353: R2:role-swap/needer/J | R2:role-swap/needer/T | R2:two-free
- 186: R2:role-swap/needer/T | R2:two-free
- 5: R2:role-swap/needer/J | R2:role-swap/other/J
- 5: R2:role-swap/needer/J | R2:role-swap/other/J | R2:role-swap/other/T
- 2: R2:role-swap/needer/J | R2:role-swap/other/J | R2:role-swap/other/T | R2:two-free

k = 3 (311 states):

- 311: R3:F>f,f>F,f>f

