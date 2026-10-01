# DL_R on the data (generated)

command: `python3 k4/dl2_relations_table.py results/k4_dl2_relations/attempts.log results/k4_dl2_relations/certs_2_all.log results/k4_dl2_relations/certs_3_r400.log results/k4_dl2_relations/certs_4_n4_1_r20.log results/k4_dl2_relations/certs_4_n4_2_r20.log results/k4_dl2_relations/certs_4_n4_3_r20.log results/k4_dl2_relations/certs_4_pure_r20.log results/k4_dl2_relations/gap_n2_e1.log results/k4_dl2_relations/gap_n3_e1.log results/k4_dl2_relations/gap_n4_1_e10.log results/k4_dl2_relations/gap_n4_2_s4000_e10.log results/k4_dl2_relations/gap_n4_3_s4000_e10.log results/k4_dl2_relations/gap_n4_pure_s4000_e10.log results/k4_dl2_relations/gap_n5_1_s100_e20.log results/k4_dl2_relations/gap_n5_2_s100_e20.log results/k4_dl2_relations/gap_n5_3_s100_e20.log results/k4_dl2_relations/gap_n5_4_s100_e20.log results/k4_dl2_relations/gap_n5_pure_s100_e20.log results/k4_dl2_relations/hard_hunt_e1.log results/k4_dl2_relations/hunt_n4_2_all_e1.log results/k4_dl2_relations/hunt_n4_3_s400k_e1.log results/k4_dl2_relations/hunt_n4_pure_s400k_e1.log results/k4_dl2_relations/hunt_n5_3_s2000_e1.log results/k4_dl2_relations/hunt_n5_4_s2000_e1.log results/k4_dl2_relations/hunt_n5_pure_s2000_e1.log results/k4_dl2_relations/suite.log results/k4_dl2_relations/trapped_n3_compute.log results/k4_dl2_relations/xcheck.log`

Entries: states (profiles) at which DL_R fails, i.e. a min-frozen P with def(P) > 0 has no min-frozen R-neighbour
with a smaller deficit. Relations: `k4/dl2_relations.py` RELATIONS; R_T is `RTr`, R_T2 is `RT`. A dash: the
run predates the relation (for RTr: RT ⊆ RTr, a trade being a rotation of two agents, and RT holds at every
state of those inputs, so RTr does too).

| input | profiles | def > 0 states | nearest distance | R2 | R3 | RB | RB2 | RS1 | RS1+2 | RSR+2 | RC | RSY | RSYa | RSY+2 | RSYg+2 | RSYz+2 | RSYgz+2 | RSYg | RT | RTr |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| certs_2_all | 189216 | 171432 | {1: 158616, 2: 12816} | 0 | 0 | 12816 (8912) | 0 | 12816 (8912) | 0 | 0 | 0 | 12816 (8912) | 12816 (8912) | 0 | 0 | 0 | 0 | 12816 (8912) | 0 | 0 |
| certs_3_r400 | 20400 | 2862 | {1: 2782, 2: 77, 3: 3} | 3 (2) | 0 | 32 (15) | 3 (2) | 32 (15) | 3 (2) | 3 (2) | 3 (2) | 31 (14) | 31 (14) | 3 (2) | 3 (2) | 3 (2) | 3 (2) | 31 (14) | 3 (2) | 0 |
| certs_4_n4_1_r20 | 2700 | 0 | {} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| certs_4_n4_2_r20 | 6180 | 3 | {1: 3} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| certs_4_n4_3_r20 | 6780 | 303 | {1: 287, 2: 16} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| certs_4_pure_r20 | 4380 | 1863 | {1: 1863} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| gap_n2_e1 | 1296 | 0 | {} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n3_e1 | 74256 | 47080 | {1: 34732, 2: 12037, 3: 311} | 311 (89) | 0 | 1427 (749) | 311 (89) | 1212 (655) | 152 (51) | 152 (51) | 152 (51) | 0 | 0 | 0 | 0 | 13 (7) | 13 (7) | 0 | 0 | – |
| gap_n4_1_e10 | 4439 | 0 | {} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n4_2_s4000_e10 | 3617 | 68 | {1: 68} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n4_3_s4000_e10 | 5837 | 681 | {1: 680, 2: 1} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n4_pure_s4000_e10 | 4511 | 2804 | {1: 2599, 2: 205} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n5_1_s100_e20 | 28 | 0 | {} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n5_2_s100_e20 | 386 | 0 | {} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n5_3_s100_e20 | 1560 | 32 | {1: 32} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n5_4_s100_e20 | 2364 | 300 | {1: 299, 2: 1} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| gap_n5_pure_s100_e20 | 1455 | 650 | {1: 639, 2: 11} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hard_hunt_e1 | 117 | 192 | {1: 121, 2: 71} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hunt_n4_2_all_e1 | 32124 | 0 | {} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hunt_n4_3_s400k_e1 | 41024 | 3552 | {1: 3537, 2: 15} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hunt_n4_pure_s400k_e1 | 69353 | 35023 | {1: 32751, 2: 2272} | 0 | 0 | 3 (2) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hunt_n5_3_s2000_e1 | 2839 | 113 | {1: 113} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hunt_n5_4_s2000_e1 | 7731 | 1003 | {1: 966, 2: 37} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | – |
| hunt_n5_pure_s2000_e1 | 8207 | 4538 | {1: 4492, 2: 46} | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| suite | 147 | 359 | {1: 296, 2: 63} | 0 | 0 | 7 (3) | 0 | 7 (3) | 0 | 0 | 0 | 5 (2) | 5 (2) | 0 | 0 | 0 | 0 | 5 (2) | 0 | – |
| **total** | 490947 | 272858 | | 314 (91) | 0 | 14285 (9681) | 314 (91) | 14067 (9585) | 155 (53) | 155 (53) | 155 (53) | 12852 (8928) | 12852 (8928) | 3 (2) | 3 (2) | 16 (9) | 16 (9) | 12852 (8928) | 3 (2) | 0 |
