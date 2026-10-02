# The adversarial hunt (k4/portfolio_hunt.py)

EVIDENCE only: adversarial search over strict profiles of fixed cores. Files: `hunt_f1focus.jsonl`, `hunt_f1focus_n4.jsonl`, `hunt_main.jsonl`.
Objective "count": the number of repairs (edges to better keys) at the worst state (key); "edge": (the number of repairs by the next stronger predicate INNER, the number by the predicate) at the worst state, lexicographic. 1000000 = no state (key) reached. A predicate dies when a task reaches 0 repairs; the failure is re-derived by k4/portfolio_ref.py before it counts.

| predicate | objective | INNER | tasks | profiles evaluated | CPU s | least objective reached | seed kinds | dead |
|---|---|---|---:|---:|---:|---|---|---|
| RC3_noT4 | count | - | 3 | 117,552 | 180 | [2, 0] | fail10, hard |  |
| RC3_noT4 | edge | RT4 | 3 | 45,576 | 180 | [0, 8] | fail10, hard |  |
| K3b_noT4 | count | - | 4 | 76,656 | 270 | [16, 0] | fail10, hard |  |
| K3b_noT4 | edge | K1 | 4 | 84,168 | 270 | [0, 16] | fail10, hard |  |
| RC3 | count | - | 8 | 1,588,752 | 1680 | [1, 0] | fail10, hard |  |
| RC3 | edge | RT4 | 7 | 1,506,528 | 1380 | [0, 10] | fail10, hard |  |
| K3b | count | - | 4 | 137,040 | 270 | [8, 0] | fail10, hard, rcores |  |
| K3b | edge | K1 | 4 | 113,640 | 270 | [22, 35] | hard, rcores |  |
| NA3 | count | - | 6 | 1,024,680 | 1320 | [1, 0] | hard |  |
| NA3 | edge | RC3 | 6 | 1,389,768 | 1320 | [2, 3] | hard |  |
| RC_W1 | count | - | 4 | 210,480 | 270 | [3, 0] | hard, rcores |  |
| RC_W1 | edge | RC3 | 4 | 277,080 | 270 | [3, 3] | hard, rcores |  |
| K3 | count | - | 4 | 89,256 | 270 | [12, 0] | fail10, hard, rcores |  |
| K3 | edge | K3b | 4 | 105,192 | 270 | [12, 12] | fail10, hard, rcores |  |
| RC | count | - | 4 | 207,528 | 270 | [5, 0] | hard, rcores |  |
| RC | edge | RC_W1 | 3 | 427,896 | 180 | [19, 19] | rcores |  |
| K2 | count | - | 4 | 92,976 | 270 | [60, 0] | fail10, rcores |  |
| K2 | edge | K3 | 4 | 348,240 | 270 | [46, 46] | fail10, rcores |  |
| RC_noneed | count | - | 3 | 357,600 | 180 | [2, 0] | ext, rcores |  |
| RC_noneed | edge | RC | 2 | 28,104 | 120 | [11, 11] | ext, rcores |  |
| RC_Yfree | count | - | 2 | 79,056 | 120 | [12, 0] | ext, rcores |  |
| RC_Yfree | edge | RC | 2 | 34,992 | 120 | [15, 15] | ext, rcores |  |
| RC_Yany | count | - | 2 | 30,312 | 120 | [11, 0] | ext, rcores |  |
| RC_Yany | edge | RC | 2 | 30,528 | 120 | [2, 2] | ext |  |
| K2_noneed | count | - | 3 | 71,472 | 210 | [16, 0] | ext, fail10 |  |
| K2_noneed | edge | K2 | 3 | 54,696 | 210 | [16, 16] | ext, fail10 |  |
| K2_Yany | count | - | 3 | 44,496 | 210 | [84, 0] | ext, fail10 |  |
| K2_Yany | edge | K2 | 3 | 38,136 | 210 | [75, 75] | ext, fail10 |  |
| RC_U0 | count | - | 2 | 41,112 | 120 | [11, 0] | fail10 |  |
| RC_U0 | edge | RC | 2 | 44,664 | 120 | [10, 10] | fail10 |  |
| NA1 | count | - | 2 | 131,808 | 120 | [9, 0] | fail10, hard |  |
| NA1 | edge | RC_U0 | 2 | 67,848 | 120 | [2, 66] | fail10, hard |  |
| K4 | count | - | 3 | 155,688 | 210 | [64, 0] | fail10, hard |  |
| K4 | edge | K2 | 3 | 143,160 | 210 | [52, 64] | fail10, hard |  |
| D3 | count | - | 5 | 1,010,880 | 1020 | [3, 0] | fail10, hard |  |
| D3 | edge | D2 | 5 | 1,005,168 | 1020 | [0, 4] | hard |  |
| FR3 | count | - | 2 | 119,928 | 120 | [5, 0] | hard |  |
| FR3 | edge | D3 | 2 | 180,624 | 120 | [4, 25] | hard |  |
| U1Z1 | count | - | 3 | 138,480 | 210 | [8, 0] | hard, rcores |  |
| U1Z1 | edge | NA1 | 3 | 163,296 | 210 | [10, 10] | hard, rcores |  |
| NAall | count | - | 3 | 131,784 | 210 | [5, 0] | hard, rcores |  |
| NAall | edge | NA1 | 3 | 114,360 | 210 | [5, 5] | hard, rcores |  |
| K5 | count | - | 3 | 96,552 | 210 | [14, 0] | fail10, hard, rcores |  |
| K5 | edge | K4 | 3 | 85,560 | 210 | [48, 48] | hard, rcores |  |
| KU1 | count | - | 3 | 83,856 | 210 | [64, 0] | hard, rcores |  |
| KU1 | edge | K4 | 3 | 102,264 | 210 | [56, 56] | hard, rcores |  |
| D4 | count | - | 2 | 39,192 | 120 | [17, 0] | ext, rcores |  |
| D4 | edge | D3 | 2 | 38,904 | 120 | [11, 26] | ext, rcores |  |

Total: 161 tasks, 12,507,528 profiles evaluated (each for every alive predicate), 15937 CPU s; dead: none.
