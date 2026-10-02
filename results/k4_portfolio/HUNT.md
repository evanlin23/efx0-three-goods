# The adversarial hunt (k4/portfolio_hunt.py)

EVIDENCE only: adversarial search over strict profiles of fixed cores. Files: `hunt_f1focus.jsonl`, `hunt_f1focus_n4.jsonl`, `hunt_main.jsonl`.
Objective "count": the number of repairs (edges to better keys) at the worst state (key); "edge": (the number of repairs by the next stronger predicate INNER, the number by the predicate) at the worst state, lexicographic. 1000000 = no state (key) reached. A predicate dies when a task reaches 0 repairs; the failure is re-derived by k4/portfolio_ref.py before it counts.

| predicate | objective | INNER | tasks | profiles evaluated | CPU s | least objective reached | seed kinds | dead |
|---|---|---|---:|---:|---:|---|---|---|
| RC3_noT4 | count | - | 4 | 140,040 | 270 | [2, 0] | fail10, hard |  |
| RC3_noT4 | edge | RT4 | 5 | 113,184 | 360 | [0, 8] | fail10, hard, rcores |  |
| K3b_noT4 | count | - | 6 | 121,032 | 450 | [16, 0] | ext, fail10, hard |  |
| K3b_noT4 | edge | K1 | 6 | 116,208 | 450 | [0, 16] | fail10, hard |  |
| RC3 | count | - | 10 | 1,687,680 | 1860 | [1, 0] | fail10, hard, rcores |  |
| RC3 | edge | RT4 | 9 | 1,546,968 | 1560 | [0, 10] | fail10, hard, rcores |  |
| K3b | count | - | 6 | 194,184 | 450 | [8, 0] | fail10, hard, rcores |  |
| K3b | edge | K1 | 7 | 185,592 | 540 | [0, 70] | ext, fail10, hard, rcores |  |
| NA3 | count | - | 9 | 1,168,200 | 1591 | [1, 0] | hard, rcores |  |
| NA3 | edge | RC3 | 9 | 1,498,176 | 1591 | [2, 3] | ext, hard, rcores |  |
| RC_W1 | count | - | 6 | 249,096 | 450 | [3, 0] | ext, hard, rcores |  |
| RC_W1 | edge | RC3 | 6 | 433,824 | 450 | [3, 3] | ext, hard, rcores |  |
| K3 | count | - | 7 | 146,328 | 540 | [12, 0] | fail10, hard, rcores |  |
| K3 | edge | K3b | 7 | 167,904 | 540 | [7, 7] | fail10, hard, rcores |  |
| RC | count | - | 6 | 248,400 | 450 | [5, 0] | ext, fail10, hard, rcores |  |
| RC | edge | RC_W1 | 5 | 479,208 | 360 | [8, 16] | ext, fail10, rcores |  |
| K2 | count | - | 7 | 178,320 | 540 | [52, 0] | fail10, hard, rcores |  |
| K2 | edge | K3 | 7 | 409,320 | 540 | [39, 39] | fail10, hard, rcores |  |
| RC_noneed | count | - | 5 | 420,432 | 361 | [2, 0] | ext, fail10, rcores |  |
| RC_noneed | edge | RC | 4 | 79,392 | 300 | [11, 11] | ext, fail10, rcores |  |
| RC_Yfree | count | - | 4 | 176,088 | 300 | [9, 0] | ext, fail10, rcores |  |
| RC_Yfree | edge | RC | 4 | 221,688 | 300 | [1, 1] | ext, fail10, hard, rcores |  |
| RC_Yany | count | - | 4 | 172,608 | 300 | [8, 0] | ext, fail10, hard, rcores |  |
| RC_Yany | edge | RC | 4 | 209,208 | 300 | [2, 2] | ext, fail10, hard |  |
| K2_noneed | count | - | 6 | 130,440 | 480 | [16, 0] | ext, fail10, hard |  |
| K2_noneed | edge | K2 | 6 | 122,016 | 480 | [7, 7] | ext, fail10, hard |  |
| K2_Yany | count | - | 6 | 118,848 | 481 | [21, 0] | ext, fail10, hard |  |
| K2_Yany | edge | K2 | 6 | 129,456 | 480 | [16, 16] | ext, fail10, hard |  |
| RC_U0 | count | - | 4 | 238,344 | 300 | [5, 0] | fail10, hard |  |
| RC_U0 | edge | RC | 4 | 201,480 | 300 | [3, 3] | fail10, hard, rcores |  |
| NA1 | count | - | 4 | 282,576 | 300 | [8, 0] | fail10, hard, rcores |  |
| NA1 | edge | RC_U0 | 4 | 275,352 | 300 | [2, 66] | fail10, hard, rcores |  |
| K4 | count | - | 6 | 238,032 | 480 | [7, 0] | fail10, hard |  |
| K4 | edge | K2 | 5 | 185,256 | 390 | [52, 64] | fail10, hard |  |
| D3 | count | - | 8 | 1,224,144 | 1500 | [3, 0] | fail10, hard, rcores |  |
| D3 | edge | D2 | 8 | 1,408,272 | 1500 | [0, 4] | hard, rcores |  |
| FR3 | count | - | 4 | 280,920 | 300 | [5, 0] | hard, rcores |  |
| FR3 | edge | D3 | 4 | 279,024 | 300 | [4, 4] | hard, rcores |  |
| U1Z1 | count | - | 4 | 198,456 | 300 | [8, 0] | hard, rcores |  |
| U1Z1 | edge | NA1 | 4 | 311,088 | 300 | [10, 10] | hard, rcores |  |
| NAall | count | - | 4 | 225,480 | 300 | [5, 0] | hard, rcores |  |
| NAall | edge | NA1 | 4 | 148,920 | 300 | [5, 5] | hard, rcores |  |
| K5 | count | - | 5 | 157,200 | 390 | [14, 0] | fail10, hard, rcores |  |
| K5 | edge | K4 | 5 | 130,920 | 390 | [29, 130] | ext, fail10, hard, rcores |  |
| KU1 | count | - | 5 | 134,160 | 390 | [16, 0] | fail10, hard, rcores |  |
| KU1 | edge | K4 | 5 | 134,736 | 390 | [56, 56] | fail10, hard, rcores |  |
| D4 | count | - | 3 | 84,312 | 210 | [17, 0] | ext, rcores |  |
| D4 | edge | D3 | 3 | 58,416 | 210 | [5, 26] | ext, fail10, rcores |  |

Total: 264 tasks, 17,060,928 profiles evaluated (each for every alive predicate), 25634 CPU s; dead: none.
