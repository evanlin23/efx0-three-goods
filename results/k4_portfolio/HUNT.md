# The adversarial hunt (k4/portfolio_hunt.py)

EVIDENCE only: adversarial search over strict profiles of fixed cores. Files: `hunt_f1focus.jsonl`, `hunt_f1focus_n4.jsonl`, `hunt_main.jsonl`, `hunt_not4focus.jsonl`.
Objective "count": the number of repairs (edges to better keys) at the worst state (key); "edge": (the number of repairs by the next stronger predicate INNER, the number by the predicate) at the worst state, lexicographic. 1000000 = no state (key) reached. A predicate dies when a task reaches 0 repairs; the failure is re-derived by k4/portfolio_ref.py before it counts.

Profiles generated: every neighbour is passed to portfolio_dump.c; those with an f >= 1 state are evaluated for every alive predicate.

| predicate | objective | INNER | tasks | profiles generated | CPU s | least objective reached | seed kinds | dead |
|---|---|---|---:|---:|---:|---|---|---|
| RC3_noT4 | count | - | 14 | 886,416 | 2072 | [2, 0] | ext, fail10, hard, rcores |  |
| RC3_noT4 | edge | RT4 | 14 | 624,312 | 1921 | [0, 8] | ext, fail10, hard, rcores |  |
| K3b_noT4 | count | - | 15 | 496,632 | 2011 | [12, 0] | ext, fail10, hard |  |
| K3b_noT4 | edge | K1 | 15 | 533,256 | 2011 | [0, 16] | ext, fail10, hard |  |
| RC3 | count | - | 14 | 1,870,776 | 2222 | [1, 0] | ext, fail10, hard, rcores |  |
| RC3 | edge | RT4 | 13 | 1,773,960 | 1920 | [0, 6] | ext, fail10, hard, rcores |  |
| K3b | count | - | 10 | 277,824 | 811 | [7, 0] | fail10, hard, rcores |  |
| K3b | edge | K1 | 11 | 264,024 | 900 | [0, 16] | ext, fail10, hard, rcores |  |
| NA3 | count | - | 13 | 1,360,080 | 1951 | [1, 0] | ext, fail10, hard, rcores |  |
| NA3 | edge | RC3 | 13 | 1,763,328 | 1951 | [2, 3] | ext, fail10, hard, rcores |  |
| RC_W1 | count | - | 10 | 464,496 | 810 | [3, 0] | ext, fail10, hard, rcores |  |
| RC_W1 | edge | RC3 | 10 | 567,960 | 811 | [3, 3] | ext, fail10, hard, rcores |  |
| K3 | count | - | 11 | 254,280 | 900 | [12, 0] | ext, fail10, hard, rcores |  |
| K3 | edge | K3b | 11 | 255,096 | 901 | [7, 7] | fail10, hard, rcores |  |
| RC | count | - | 10 | 446,088 | 811 | [5, 0] | ext, fail10, hard, rcores |  |
| RC | edge | RC_W1 | 8 | 665,496 | 630 | [3, 3] | ext, fail10, hard, rcores |  |
| K2 | count | - | 10 | 280,440 | 811 | [36, 0] | fail10, hard, rcores |  |
| K2 | edge | K3 | 10 | 494,256 | 810 | [21, 21] | ext, fail10, hard, rcores |  |
| RC_noneed | count | - | 8 | 633,720 | 631 | [2, 0] | ext, fail10, hard, rcores |  |
| RC_noneed | edge | RC | 7 | 262,224 | 570 | [5, 5] | ext, fail10, hard, rcores |  |
| RC_Yfree | count | - | 7 | 440,640 | 570 | [9, 0] | ext, fail10, hard, rcores |  |
| RC_Yfree | edge | RC | 7 | 352,296 | 570 | [1, 1] | ext, fail10, hard, rcores |  |
| RC_Yany | count | - | 7 | 295,560 | 570 | [6, 0] | ext, fail10, hard, rcores |  |
| RC_Yany | edge | RC | 7 | 296,328 | 570 | [2, 2] | ext, fail10, hard, rcores |  |
| K2_noneed | count | - | 9 | 194,280 | 751 | [16, 0] | ext, fail10, hard |  |
| K2_noneed | edge | K2 | 9 | 195,216 | 750 | [7, 7] | ext, fail10, hard |  |
| K2_Yany | count | - | 9 | 187,992 | 751 | [21, 0] | ext, fail10, hard |  |
| K2_Yany | edge | K2 | 9 | 186,696 | 751 | [16, 16] | ext, fail10, hard |  |
| RC_U0 | count | - | 7 | 303,336 | 571 | [5, 0] | ext, fail10, hard, rcores |  |
| RC_U0 | edge | RC | 7 | 291,408 | 570 | [3, 3] | ext, fail10, hard, rcores |  |
| NA1 | count | - | 7 | 399,768 | 570 | [8, 0] | ext, fail10, hard, rcores |  |
| NA1 | edge | RC_U0 | 7 | 454,944 | 570 | [2, 66] | ext, fail10, hard, rcores |  |
| K4 | count | - | 9 | 330,312 | 750 | [7, 0] | fail10, hard |  |
| K4 | edge | K2 | 9 | 325,392 | 750 | [16, 16] | fail10, hard |  |
| D3 | count | - | 12 | 1,374,912 | 1860 | [3, 0] | ext, fail10, hard, rcores |  |
| D3 | edge | D2 | 12 | 1,554,888 | 1860 | [0, 4] | ext, fail10, hard, rcores |  |
| FR3 | count | - | 8 | 495,336 | 660 | [5, 0] | ext, fail10, hard, rcores |  |
| FR3 | edge | D3 | 8 | 505,680 | 661 | [4, 4] | ext, fail10, hard, rcores |  |
| U1Z1 | count | - | 8 | 302,976 | 660 | [8, 0] | ext, fail10, hard, rcores |  |
| U1Z1 | edge | NA1 | 8 | 419,664 | 660 | [10, 10] | ext, fail10, hard, rcores |  |
| NAall | count | - | 8 | 497,784 | 660 | [5, 0] | ext, fail10, hard, rcores |  |
| NAall | edge | NA1 | 8 | 382,296 | 663 | [5, 5] | ext, fail10, hard, rcores |  |
| K5 | count | - | 9 | 275,400 | 750 | [14, 0] | fail10, hard, rcores |  |
| K5 | edge | K4 | 9 | 238,968 | 750 | [29, 130] | ext, fail10, hard, rcores |  |
| KU1 | count | - | 9 | 257,664 | 751 | [7, 0] | fail10, hard, rcores |  |
| KU1 | edge | K4 | 9 | 275,232 | 751 | [16, 16] | fail10, hard, rcores |  |
| D4 | count | - | 7 | 468,696 | 570 | [5, 0] | ext, fail10, hard, rcores |  |
| D4 | edge | D3 | 7 | 287,760 | 570 | [2, 18] | ext, fail10, hard, rcores |  |

Total: 459 tasks, 25,766,088 profiles generated, 46351 CPU s; dead: none.
